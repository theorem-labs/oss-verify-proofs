(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its numbers changed; 1527 of its 1633 lines of code are new or changed and 558 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass1w.v, with its module paths and module names changed; 1947 of its 2108 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5L2.v, with its module paths, module names and addresses changed; 1158 of its 1291 lines of code are new or changed and 1975 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import
  Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack MemNorm AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotMove SlotResReply SlotExitMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotExitRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotExitWip SlotEntry RelayCap SlotExitFinAux SlotExitFin SlotExitScanAux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import list_drop_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotRI3 SlotNcWt ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition scan_E (hj : list (hsrc * nat)) (a : Z) : Prop :=
  exists p, In p hj /\
    ((G_S + SRC_SIZE * Z.of_nat (snd p) + 88 <= a < G_S + SRC_SIZE * Z.of_nat (snd p) + 92) \/
     (0 < hl_cap (hs_held (fst p)) /\
      hl_v (hs_held (fst p)) <= a < hl_v (hs_held (fst p)) + 16 * hl_cap (hs_held (fst p)))).

Definition scan_F (hj : list (hsrc * nat)) (q : Z) : Prop :=
  exists p, In p hj /\ In q (map fst (hl_recs (hs_held (fst p)))).

Definition hl0 : hlist := HL 0 0 [] [].
Definition src0 : hsrc := HS 0 0 0 0 hl0 0 0 [] 0 0 [] hl0 hl0.
Definition pd0 : hsrc * nat := (src0, 0%nat).

Section Mid2.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable E : sstart.
Variable RI : res_inv.
Variables t k : Z.
Let segs := ms_segs B.

Definition exit_mid2 (c : config) : Prop :=
  exists (fx' : FPState) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (m0 : word -> option byte) (md0 : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
         (tail : list byte) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (OUT' CAP' : Z) (junk' : list byte) (Hs : nat -> hlist),
    let TOT := entries_total es in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd TOT in
    let off := send_off cl br TOT in
    let b := slot_sp E in
    let acc := if gn =? 0 then TOT else 0 in
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x14744) mem (seg_rom segs)) md /\
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 acc /\
    frm_zero (@fp_csr fx') /\
    exit_state B API E RI t k L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out es hj /\
    table_at B m0 G es tail /\
    rmid B API SLOT_STACK (spZ (ss_regs E)) (fun a => exit_fin_E live OUT CAP G a \/ scan_E hj a)
      (fun q => exit_fin_F live OUT es q \/ scan_F hj q) L0 A0 m0 md0 L A mem md /\
    st_init_done A = true /\ ro_agree segs mem /\
    (forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 20 \/ 25 <= r <= 27) ->
       YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)) /\
    rw_cells segs mem (b + 88) (saved_cells (ss_regs E)) /\
    rw_cells segs mem b [C8 (Z_to_bv 64 CLIENT_BASE)] /\
    rw_cells segs mem (b + 16) [C8 (Z_to_bv 64 acc)] /\
    (forall i, (i < length es)%nat ->
       rw_cells segs mem (b + 40 + 4 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]) /\
    rw_cells segs mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
    rw_cells segs mem G_GONE [C1 (Z_to_bv 8 gn)] /\
    rw_cells segs mem G_NFD [C4 (Z_to_bv 64 nfd)] /\
    rw_cells segs mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
    rw_cells segs mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] /\
    rw_cells segs mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
    (forall p, (p < length hj)%nat ->
       hl_v (Hs p) = hl_v (hs_held (fst (nth p hj pd0))) /\ hl_cap (Hs p) = hl_cap (hs_held (fst (nth p hj pd0))) /\
       hl_recs (Hs p) = [] /\
       src_at B L A mem (G_S + SRC_SIZE * Z.of_nat (snd (nth p hj pd0))) (set_held (fst (nth p hj pd0)) (Hs p))) /\
    (forall i, (i < 4)%nat -> slot_open hj i = false ->
       rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
    table_at B mem G (map entry_cleared es) tail /\ In (G, SRC_TABLE) (blocks L A) /\
    (forall q m, In (q, m) (blocks L A) <->
       ((In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))) \/
        (live = true /\ q = OUT' /\ m = CAP') \/ (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP)) /\
       ~ scan_F hj q) /\
    (live = false -> rw_cells segs mem G_OUTV [C8 mx; C8 (Z_to_bv 64 0); C8 cap; C8 out]) /\
    (live = true ->
       TOT <= CAP' /\ CAP' = relay_finish_cap live (bv_unsigned mx) 0 CAP es /\ CAP' <= Z.max CAP (2 * TOT) /\
       fresh_block B OUT' CAP' /\
       (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
          q <> OUT') /\
       bytes_at segs mem OUT' (entries_out es ++ junk') /\ Z.of_nat (length junk') = CAP' - TOT /\
       rw_cells segs mem G_OUTV [C8 mx; C8 (Z_to_bv 64 TOT); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]) /\
    RI E k (view_of G (if live then OUT' else OUT) [] hj) L A.
End Mid2.

Section Scan.
Context {rc : RunCeil} {fx : FPState} {B : malloc_syms} {API : AllocAPI B} {F : ResFormT} {E : sstart}
  {RI : res_inv} {t k : Z} {L0 : layout} {A0 : astate} {regs0 : bvmap 5 word} {m0 : word -> option byte}
  {md0 : Model} {cl br gn dd ei G nfd : Z} {mx nout cap out : word} {es : list rentry}
  {hj : list (hsrc * nat)} {tail : list byte} {OUT' CAP' : Z} {junk' : list byte}.

Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis HAX : AllocExtra B (aa_MR API).
Hypothesis HBW : blocks_writable B API.
Hypothesis HPLG : forall a, 0x318a0 <= a < 0x31aa0 \/ 0x21620 <= a < 0x21630 -> img_plain B a.
Hypothesis HEA : errno_addr B = 0x31acc.
Hypothesis HTPE : YK11.getr (ss_regs E) 4 = Z_to_bv 64 (ms_tp B).
Hypothesis HB1 : @YM05.alloc_ceiling rc <= spZ (ss_regs E) - SLOT_STACK.
Hypothesis HB2 : slot_sp E + 192 < 2 ^ 63.
Hypothesis HB3 : slot_sp E mod 16 = 0.
Hypothesis HB4 : spZ (ss_regs E) = slot_sp E + 192.
Hypothesis HCSE : @check_shape_ends_contract fx rc B API F.
Hypothesis HRES : forall k' L A gone (rs : list (Z * list byte)) d G' out' es' hj',
  RI E k' (view_of G' out' es' hj') L A -> (gone = 0 \/ gone = 1) ->
  Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) rs -> List.NoDup (map fst rs) ->
  res_tr F (exit_RV_s RI E k' L A G' out' es' hj' [] []) A (check_shape_ends_tr (known_at L A) gone [] rs d).
Hypothesis HNDB : blocks_nodup B API.
Hypothesis HFZ : frm_zero (@fp_csr fx).
Hypothesis HEXS : exit_state (rc := rc) B API E RI t k L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out es hj.
Hypothesis HTB : table_at B m0 G es tail.
Hypothesis HLIVE : send_live cl br dd (entries_total es) = true ->
  entries_total es <= CAP' /\
  CAP' = relay_finish_cap (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es /\
  CAP' <= Z.max (bv_unsigned cap) (2 * entries_total es) /\ fresh_block B OUT' CAP' /\
  (forall q m, In (q, m) (blocks L0 A0) -> q <> bv_unsigned out -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
     q <> OUT') /\
  Z.of_nat (length junk') = CAP' - entries_total es.

Definition sN : nat := length es.
Definition sTOT : Z := entries_total es.
Definition sOUT : Z := bv_unsigned out.
Definition sCAP : Z := bv_unsigned cap.
Definition slive : bool := send_live cl br dd sTOT.
Definition soff : bool := send_off cl br sTOT.
Definition sb : Z := slot_sp E.
Definition sh (p : nat) : hsrc := fst (nth p hj pd0).
Definition ss (p : nat) : nat := snd (nth p hj pd0).
Definition sHA (p : nat) : Z := G_S + SRC_SIZE * Z.of_nat (ss p).
Definition scnt (i jj : nat) : nat := (i + if Nat.ltb (ss i) jj then 1 else 0)%nat.
Definition sacc (d : nat) : Z := if gn =? 0 then entries_total (firstn d es) else 0.
Definition scur (Hs : nat -> hlist) (d p : nat) : hsrc := if Nat.ltb p d then set_held (sh p) (Hs p) else sh p.
Definition sbase (q m : Z) : Prop :=
  (In (q, m) (blocks L0 A0) /\ q <> sOUT /\ ~ In q (concat (map entry_blocks es))) \/
  (slive = true /\ q = OUT' /\ m = CAP') \/ (slive = false /\ 0 < sCAP /\ q = sOUT /\ m = sCAP).
Definition sfreed (d : nat) (q : Z) : Prop :=
  exists p, (p < d)%nat /\ (p < sN)%nat /\ In q (map fst (hl_recs (hs_held (sh p)))).
Definition sNO : word := Z_to_bv 64 (if slive then sTOT else 0).
Definition sCAPw : word := if slive then Z_to_bv 64 CAP' else cap.
Definition sOUTw : word := if slive then Z_to_bv 64 OUT' else out.
Definition sOB : list byte := if slive then entries_out es else [].
Definition sV : rview := view_of G (if slive then OUT' else sOUT) [] hj.

Definition sglob (mem : word -> option byte) : Prop :=
  rw_cells (ms_segs B) mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_GONE [C1 (Z_to_bv 8 gn)] /\
  rw_cells (ms_segs B) mem G_NFD [C4 (Z_to_bv 64 nfd)] /\
  rw_cells (ms_segs B) mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
  rw_cells (ms_segs B) mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells (ms_segs B) mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
  rw_cells (ms_segs B) mem G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells (ms_segs B) mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_BROKEN [C1 (Z_to_bv 8 (if soff then br else dd))] /\
  rw_cells (ms_segs B) mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells (ms_segs B) mem G_EINTR [C1 (Z_to_bv 8 (if soff then ei else 0))] /\
  rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 sNO; C8 sCAPw; C8 sOUTw] /\
  (forall i, (i < 4)%nat -> slot_open hj i = false ->
     rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]).

Definition sstack (mem : word -> option byte) : Prop :=
  rw_cells (ms_segs B) mem (sb + 88) (saved_cells (ss_regs E)) /\
  rw_cells (ms_segs B) mem sb [C8 (Z_to_bv 64 CLIENT_BASE)] /\
  (forall i, (i < sN)%nat ->
     rw_cells (ms_segs B) mem (sb + 40 + 4 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]).

Definition sfacts (d : nat) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (Hs : nat -> hlist)
    : Prop :=
  rmid B API SLOT_STACK (spZ (ss_regs E)) (fun a => exit_fin_E slive sOUT sCAP G a \/ scan_E hj a)
    (fun q => exit_fin_F slive sOUT es q \/ scan_F hj q) L0 A0 m0 md0 L A mem md /\
  st_init_done A = true /\ ro_agree (ms_segs B) mem /\ RI E k sV L A /\
  sstack mem /\
  rw_cells (ms_segs B) mem (sb + 16) [C8 (Z_to_bv 64 (sacc d))] /\
  sglob mem /\
  (forall p, (p < sN)%nat -> src_at B L A mem (sHA p) (scur Hs d p)) /\
  (forall p, (p < d)%nat -> (p < sN)%nat ->
     hl_v (Hs p) = hl_v (hs_held (sh p)) /\ hl_cap (Hs p) = hl_cap (hs_held (sh p)) /\ hl_recs (Hs p) = []) /\
  table_at B mem G (map entry_cleared es) tail /\
  (slive = true -> bytes_at (ms_segs B) mem OUT' (entries_out es ++ junk')) /\
  (forall q m, In (q, m) (blocks L A) <-> sbase q m /\ ~ sfreed d q).

Definition rg_keep (regs : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 20 \/ 25 <= r <= 27) ->
    YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r).

Definition rg_loop (i jj : nat) (regs : bvmap 5 word) : Prop :=
  rg_keep regs /\
  YK11.getr regs (Z_to_bv 5 8) = Z_to_bv 64 0x102e9 /\
  YK11.getr regs (Z_to_bv 5 9) = Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat jj) /\
  YK11.getr regs (Z_to_bv 5 18) = Z_to_bv 64 (Z.of_nat i) /\
  YK11.getr regs (Z_to_bv 5 19) = Z_to_bv 64 (Z.of_nat sN) /\
  YK11.getr regs (Z_to_bv 5 21) = Z_to_bv 64 (sb + 40) /\
  YK11.getr regs (Z_to_bv 5 22) = Z_to_bv 64 0x31920 /\
  YK11.getr regs (Z_to_bv 5 23) = Z_to_bv 64 0x31aa0 /\
  YK11.getr regs (Z_to_bv 5 24) = Z_to_bv 64 (sb + 40 + 4 * Z.of_nat i).

Definition at_loop (i jj : nat) (c : config) : Prop :=
  exists L A regs mem md Hs,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x146fc) mem (seg_rom (ms_segs B))) md /\
    rg_loop i jj regs /\ sfacts (scnt i jj) L A mem md Hs.

Definition at_ret (i jj : nat) (c : config) : Prop :=
  exists L A regs mem md Hs,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14720) mem (seg_rom (ms_segs B))) md /\
    rg_loop i jj regs /\ sfacts (scnt i (S jj)) L A mem md Hs.

Definition mid2_state (c : config) : Prop :=
  exists L A regs mem md Hs,
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14744) mem (seg_rom (ms_segs B))) md /\
    YK11.getr regs (Z_to_bv 5 10) = Z_to_bv 64 (sacc sN) /\
    rg_keep regs /\ sfacts sN L A mem md Hs.

Ltac exs := pose proof HEXS as (Ht & Hk & Hn & HX & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK &
  HGL & Hnfd & HOUT & HREL & Hes & Hcost & HRI).

Lemma sN_le : (sN <= 4)%nat.
Proof. exs. exact Hes. Qed.

Lemma len_hj : length hj = sN.
Proof.
  exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & HPA & _). symmetry. exact (Forall2_length HPA).
Qed.

Lemma gn01 : gn = 0 \/ gn = 1.
Proof. exs. pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RGN & _). exact RGN. Qed.

Lemma live_gn : slive = true -> gn = 0.
Proof.
  intros HL. exs.
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RCL & RBR & RGN & RDD & _ & (_ & G1) & _).
  destruct RGN as [|E1]; [assumption|]. exfalso. unfold slive, send_live, send_off in HL.
  apply andb_prop in HL as [H1 H2]. apply negb_true_iff in H1. apply orb_false_iff in H1 as [H1 H3].
  apply orb_false_iff in H1 as [H1 H4]. apply Z.ltb_ge in H1. apply Z.eqb_neq in H4. apply Z.eqb_eq in H2.
  destruct (G1 E1) as [X|[X|X]]; lia.
Qed.

Lemma live_tot : gn = 0 -> slive = false -> sTOT = 0.
Proof.
  intros H0 HL. exs.
  pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (G0 & _) & _).
  destruct (G0 H0) as (E1 & E2 & E3). unfold slive, send_live, send_off in HL. rewrite E1, E2, E3 in HL.
  destruct (Z.eqb_spec sTOT 0) as [X|X]; [exact X|].
  try rewrite (proj2 (Z.eqb_neq _ _) X) in HL. cbn in HL. discriminate.
Qed.

Lemma tot_bound : 0 <= sTOT <= k.
Proof.
  exs. pose proof HREL as (_ & _ & _ & HES & _ & _ & HPA & _).
  split; [apply exit_entries_nonneg|]. eapply Z.le_trans; [|exact Hcost].
  apply exit_entries_cost; [exact (Forall2_length HPA)|]. eapply Forall_impl; [|exact HES].
  intros e (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia.
Qed.

Lemma k_bound : k < 2 ^ 26.
Proof. exs. unfold INPUT_MAX in Hn. lia. Qed.

Lemma pair_at : forall p, (p < sN)%nat -> exists e, nth_error es p = Some e /\
  CF.RelayRep.entry_ok (rc := rc) B L0 A0 m0 e /\ pair_ok (rc := rc) B L0 A0 m0 t e (nth p hj pd0).
Proof.
  intros p Hp. exs. pose proof HREL as (_ & _ & _ & HES & _ & _ & HPA & _).
  destruct (nth_error es p) as [e|] eqn:He; [|apply nth_error_None in He; unfold sN in Hp; lia].
  exists e. split; [reflexivity|].
  assert (EE : nth p es e = e) by (apply nth_error_nth; exact He).
  split.
  - rewrite Forall_forall in HES. apply HES. exact (nth_error_In _ _ He).
  - rewrite <- EE at 1. apply f2_nth; [exact HPA|unfold sN in Hp; exact Hp].
Qed.

Lemma ss_lt : forall p, (p < sN)%nat -> (ss p < 4)%nat.
Proof. intros p Hp. destruct (pair_at p Hp) as (e & _ & _ & _ & H4 & _). exact H4. Qed.

Lemma fd_nth : forall i e, nth_error es i = Some e -> nth i (map re_fd es) 0 = re_fd e.
Proof. intros i e He. apply nth_error_nth. rewrite nth_error_map, He. reflexivity. Qed.

Lemma fd_inj : forall p p' e e', nth_error es p = Some e -> nth_error es p' = Some e' -> re_fd e = re_fd e' -> p = p'.
Proof.
  intros p p' e e' He He' Hf. exs. pose proof HREL as (_ & _ & _ & _ & HND & _).
  apply NoDup_ListNoDup in HND. apply (proj1 (List.NoDup_nth_error _) HND p p').
  - rewrite length_map. apply nth_error_Some. rewrite He. discriminate.
  - rewrite !nth_error_map, He, He'. cbn. rewrite Hf. reflexivity.
Qed.

Lemma ss_inj : forall p p', (p < sN)%nat -> (p' < sN)%nat -> ss p = ss p' -> p = p'.
Proof.
  intros p p' Hp Hp' Hs. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & NDH & _).
  apply NoDup_ListNoDup in NDH. pose proof len_hj as LH.
  apply (proj1 (List.NoDup_nth_error _) NDH p p').
  - rewrite length_map. lia.
  - rewrite !nth_error_map. rewrite (nth_error_nth' hj pd0 (n := p)) by lia.
    rewrite (nth_error_nth' hj pd0 (n := p')) by lia.
    cbn. unfold ss in Hs. rewrite Hs. reflexivity.
Qed.

Lemma target_nodup : NoDup (target_addrs G sOUT es hj).
Proof. exs. pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NDA). exact NDA. Qed.

Lemma blk_disj : forall p p' q, (p < sN)%nat -> (p' < sN)%nat -> p <> p' ->
  In q (hs_blocks (sh p)) -> In q (hs_blocks (sh p')) -> False.
Proof.
  intros p p' q Hp Hp' Hne H1 H2. pose proof target_nodup as ND. apply NoDup_ListNoDup in ND.
  unfold target_addrs in ND. apply List.NoDup_cons_iff in ND as [_ ND]. apply List.NoDup_cons_iff in ND as [_ ND].
  apply List.NoDup_app_remove_l in ND. pose proof len_hj as LH.
  apply (nodup_concat_nth (fun p => hs_blocks (fst p)) hj pd0 p p' q ND); [lia|lia|exact Hne|exact H1|exact H2].
Qed.

Lemma blk_tg : forall p q, (p < sN)%nat -> In q (hs_blocks (sh p)) ->
  q <> G /\ q <> sOUT /\ ~ In q (concat (map entry_blocks es)).
Proof.
  intros p q Hp Hq. destruct (fin_target G sOUT es hj target_nodup) as (_ & _ & _ & _ & TPH).
  apply (TPH (nth p hj pd0) q); [apply nth_In; rewrite len_hj; exact Hp|exact Hq].
Qed.

Lemma src_m0 : forall p, (p < sN)%nat -> src_at B L0 A0 m0 (sHA p) (sh p).
Proof. intros p Hp. destruct (pair_at p Hp) as (e & _ & _ & S & _). exact S. Qed.

Lemma blk_pos : forall L A mem HA h q, src_at B L A mem HA h -> In q (hs_blocks h) ->
  exists m, 0 < m /\ In (q, m) (blocks L A).
Proof.
  intros L A mem HA h q HS Hq. apply src_at_iff in HS. destruct HS as (SB & LE & LH & _).
  unfold hs_blocks in Hq. rewrite app_assoc, app_assoc in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - rewrite <- app_assoc in Hq. destruct (src_parts_pos B L A mem HA h SB LE q Hq) as (m & M1 & M2).
    exists m. split; assumption.
  - destruct (hf_list_pos B L A mem _ _ _ q LH Hq) as (m & M1 & M2). exists m. split; assumption.
Qed.

Lemma blk_OUT : slive = true -> forall p q, (p < sN)%nat -> In q (hs_blocks (sh p)) -> q <> OUT'.
Proof.
  intros HL p q Hp Hq. destruct (HLIVE HL) as (_ & _ & _ & _ & HQ & _).
  destruct (blk_pos _ _ _ _ _ q (src_m0 p Hp) Hq) as (m & M1 & M2).
  destruct (blk_tg p q Hp Hq) as (_ & T2 & T3). exact (HQ q m M2 T2 T3 M1).
Qed.

Lemma recs_nc : forall i, (i < sN)%nat -> forall q, In q (map fst (hl_recs (hs_held (sh i)))) -> ~ In q (rv_nc sV).
Proof.
  intros i Hi q Hq.
  assert (HB : In q (hs_blocks (sh i))) by (apply held_in_blocks; unfold list_blocks; apply in_or_app; right; exact Hq).
  destruct (blk_tg i q Hi HB) as (T1 & T2 & _).
  assert (NDi : List.NoDup (hs_blocks (sh i))).
  { pose proof (src_m0 i Hi) as S. apply src_at_iff in S. destruct S as (_ & _ & _ & ND).
    first [exact (proj1 (NoDup_ListNoDup _) ND)|exact ND]. }
  unfold sV, view_of. cbn [rv_nc map concat app]. intros [X|[X|X]].
  - exact (T1 (eq_sym X)).
  - destruct slive eqn:HL; [exact (blk_OUT HL i q Hi HB (eq_sym X))|exact (T2 (eq_sym X))].
  - apply in_concat in X as (l & Hl & Hq'). apply in_map_iff in Hl as (p & <- & Hp). cbv beta in Hq'.
    destruct (In_nth _ _ pd0 Hp) as (p' & Hp' & Ep). rewrite len_hj in Hp'.
    assert (Hs : fst p = sh p') by (unfold sh; rewrite Ep; reflexivity).
    rewrite Hs in Hq'.
    destruct (Nat.eq_dec p' i) as [->|Hne].
    + exact (mv_rec_nc (sh i) NDi q Hq Hq').
    + exact (blk_disj i p' q Hi Hp' (fun E => Hne (eq_sym E)) HB (mv_snc_hb _ _ Hq')).
Qed.

Lemma slot_open_ss : forall p, (p < sN)%nat -> slot_open hj (ss p) = true.
Proof.
  intros p Hp. unfold slot_open. apply existsb_exists. exists (ss p). split; [|apply Nat.eqb_refl].
  unfold ss. apply (in_map snd). apply nth_In. rewrite len_hj. exact Hp.
Qed.

Lemma slot_open_inv : forall jj, slot_open hj jj = true -> exists p, (p < sN)%nat /\ ss p = jj.
Proof.
  intros jj H. unfold slot_open in H. apply existsb_exists in H as (x & Hx & Ex). apply Nat.eqb_eq in Ex. subst x.
  destruct (In_nth _ _ (snd pd0) Hx) as (p & Hp & Ep). rewrite length_map, len_hj in Hp.
  exists p. split; [exact Hp|]. unfold ss. rewrite <- Ep. symmetry. apply (map_nth snd).
Qed.

Lemma scnt_call : forall i, scnt i (S (ss i)) = S i.
Proof. intros i. unfold scnt. rewrite (proj2 (Nat.ltb_lt _ _) (Nat.lt_succ_diag_r _)). lia. Qed.

Lemma scnt_here : forall i, scnt i (ss i) = i.
Proof. intros i. unfold scnt. rewrite Nat.ltb_irrefl. lia. Qed.

Lemma scnt_skip : forall i jj, jj <> ss i -> scnt i (S jj) = scnt i jj.
Proof.
  intros i jj H. unfold scnt. destruct (Nat.ltb_spec (ss i) (S jj)); destruct (Nat.ltb_spec (ss i) jj); lia.
Qed.

Lemma scnt_wrap : forall i, (i < sN)%nat -> scnt i 4 = S i /\ scnt (S i) 0 = S i.
Proof.
  intros i Hi. pose proof (ss_lt i Hi). unfold scnt.
  rewrite (proj2 (Nat.ltb_lt _ _) H). destruct (ss (S i)); cbn; lia.
Qed.

Lemma scnt_zero : scnt 0 0 = 0%nat.
Proof. unfold scnt. destruct (ss 0); reflexivity. Qed.

Lemma scnt_le : forall i jj, (scnt i jj <= S i)%nat /\ (i <= scnt i jj)%nat.
Proof. intros i jj. unfold scnt. destruct (Nat.ltb (ss i) jj); lia. Qed.

Lemma acc_bound : forall d, 0 <= sacc d <= (if slive then sTOT else 0).
Proof.
  intros d. unfold sacc. destruct (Z.eqb_spec gn 0) as [E0|E0].
  - pose proof (exit_entries_nonneg (firstn d es)). pose proof (entries_total_le es d).
    destruct slive eqn:HL; [unfold sTOT; lia|]. pose proof (live_tot E0 HL). unfold sTOT in *. lia.
  - destruct slive; [pose proof tot_bound|]; lia.
Qed.

Lemma ob_gone : gn = 0 -> sOB = entries_out es.
Proof.
  intros H0. unfold sOB. destruct slive eqn:HL; [reflexivity|].
  pose proof (live_tot H0 HL) as T. pose proof (exit_entries_length es) as L. unfold sTOT in T.
  destruct (entries_out es); [reflexivity|cbn in L; lia].
Qed.

Lemma rg_sp : forall regs, rg_keep regs -> YK11.getr regs (Z_to_bv 5 2) = Z_to_bv 64 sb.
Proof. intros regs KP. rewrite (KP 2 ltac:(lia)). exs. destruct HR as (B2 & _). exact B2. Qed.

Lemma rg_s4 : forall regs, rg_keep regs -> YK11.getr regs (Z_to_bv 5 20) = Z_to_bv 64 0x318a0.
Proof. intros regs KP. rewrite (KP 20 ltac:(lia)). exs. destruct HR as (_ & _ & _ & B20 & _). exact B20. Qed.

Lemma rg_tp : forall regs, rg_keep regs -> YK11.getr regs (Z_to_bv 5 4) = Z_to_bv 64 (ms_tp B).
Proof.
  intros regs KP. rewrite (KP 4 ltac:(lia)). exs. destruct HR as (_ & _ & B4 & _).
  transitivity (YK11.getr (ss_regs E) 4); [exact B4|exact HTPE].
Qed.

Lemma rg_spZ : forall regs, rg_keep regs -> spZ regs = sb.
Proof.
  intros regs KP. unfold spZ. transitivity (bv_unsigned (YK11.getr regs (Z_to_bv 5 2))); [reflexivity|].
  rewrite (rg_sp regs KP). apply unsigned_lit. pose proof (@YM05.alloc_ceiling_value rc).
  pose proof HB1 as X. unfold SLOT_STACK in X. unfold sb. lia.
Qed.

Lemma rg_pres : forall i jj regs regs', regs_preserved regs regs' -> rg_loop i jj regs -> rg_loop i jj regs'.
Proof.
  intros i jj regs regs' PR (KP & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24). unfold regs_preserved in PR.
  split; [intros r Hr; rewrite (PR r ltac:(unfold callee_saved; lia)); exact (KP r Hr)|].
  split; [rewrite (PR 8 ltac:(unfold callee_saved; lia)); exact G8|].
  split; [rewrite (PR 9 ltac:(unfold callee_saved; lia)); exact G9|].
  split; [rewrite (PR 18 ltac:(unfold callee_saved; lia)); exact G18|].
  split; [rewrite (PR 19 ltac:(unfold callee_saved; lia)); exact G19|].
  split; [rewrite (PR 21 ltac:(unfold callee_saved; lia)); exact G21|].
  split; [rewrite (PR 22 ltac:(unfold callee_saved; lia)); exact G22|].
  split; [rewrite (PR 23 ltac:(unfold callee_saved; lia)); exact G23|].
  rewrite (PR 24 ltac:(unfold callee_saved; lia)); exact G24.
Qed.

Lemma ac_facts : @YM05.alloc_ceiling rc + 65344 <= sb /\ 2 ^ 40 <= @YM05.alloc_ceiling rc /\
  sb + 192 < 2 ^ 63 /\ sb mod 16 = 0 /\ spZ (ss_regs E) = sb + 192.
Proof.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc).
  unfold sb. split; [pose proof HB1 as X; rewrite HB4 in X; unfold SLOT_STACK in X; lia|]. split; [lia|].
  split; [exact HB2|].
  split; [exact HB3|exact HB4].
Qed.

Lemma stack_keep : forall K Ee Ff L A mem md L' A' mem' md',
  aa_MR API L A mem md -> rmid B API K sb Ee Ff L A mem md L' A' mem' md' ->
  (forall a, Ee a -> a < sb \/ sb + 16 <= a < sb + 24) ->
  sstack mem -> sstack mem'.
Proof.
  intros K Ee Ff L A mem md L' A' mem' md' HM R HE (S1 & S2 & S3).
  pose proof ac_facts as (A1 & A2 & A3 & _). pose proof sN_le as NL4.
  assert (T : forall a cs, rw_cells (ms_segs B) mem a cs -> sb <= a -> a + Z.of_nat (cells_size cs) <= sb + 192 ->
     (a + Z.of_nat (cells_size cs) <= sb + 16 \/ sb + 24 <= a) -> rw_cells (ms_segs B) mem' a cs).
  { intros a cs H H1 H2 H3.
    apply (rmid_rw_hi B API K sb Ee Ff L A mem md L' A' mem' md' a cs); [lia|rewrite HEA; lia|exact HM|exact R|
      exact H|exact H1|lia|].
    intros i Hi X. destruct (HE _ X); lia. }
  split; [apply T; [exact S1|lia|unfold saved_cells; cbn [cells_size csize]; lia|right; lia]|].
  split; [apply T; [exact S2|lia|cbn [cells_size csize]; lia|left; cbn [cells_size csize]; lia]|].
  intros i Hi. apply T; [exact (S3 i Hi)|lia|cbn [cells_size csize]; lia|right; lia].
Qed.

Lemma glob_tr : forall mem mem', (forall a cs, rw_cells (ms_segs B) mem a cs -> rw_cells (ms_segs B) mem' a cs) ->
  sglob mem -> sglob mem'.
Proof.
  intros mem mem' T (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
  repeat (split; [apply T; assumption|]). intros i Hi Hc. apply T. exact (Q14 i Hi Hc).
Qed.

Lemma glob_keep : forall K sp Ee Ff L A mem md L' A' mem' md' x C V,
  (x < sN)%nat -> @YM05.alloc_ceiling rc <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp Ee Ff L A mem md L' A' mem' md' ->
  (forall a, Ee a -> (sHA x + 80 <= a < sHA x + 96) \/ (0 < C /\ V <= a < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A)) ->
  sglob mem -> sglob mem'.
Proof.
  intros K sp Ee Ff L A mem md L' A' mem' md' x C V Hx HK HM R HE HV
    (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14).
  pose proof (ss_lt x Hx) as Sx. pose proof (slot_open_ss x Hx) as Ox.
  assert (T : forall a cs, rw_cells (ms_segs B) mem a cs ->
     (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
        (0x318a0 <= a + i < 0x31aa0 \/ 0x21620 <= a + i < 0x21630) /\ ~ (sHA x + 80 <= a + i < sHA x + 96)) ->
     rw_cells (ms_segs B) mem' a cs).
  { intros a cs H D.
    apply (img_keep B API HAX HSEG K sp Ee Ff L A mem md L' A' mem' md' (sHA x + 80) (sHA x + 96) C V a cs
      HK HM R HE HV H).
    intros i Hi. destruct (D i Hi) as [D1 D2]. split; [apply HPLG; exact D1|exact D2]. }
  unfold sHA in T.
  Local Ltac gk T Q := apply T; [exact Q|]; intros i Hi; cbn [cells_size csize] in Hi;
    unfold G_WAKE0, G_GONE, G_NFD, G_LOCK, G_THREAD_UP, G_NSRC, G_SRC, G_LISTEN, G_BROKEN, G_DEAD, G_EINTR,
      G_OUTV, G_S, SRC_SIZE; lia.
  split; [gk T Q1|]. split; [gk T Q2|]. split; [gk T Q3|]. split; [gk T Q4|]. split; [gk T Q5|].
  split; [gk T Q6|]. split; [gk T Q7|]. split; [gk T Q8|]. split; [gk T Q9|]. split; [gk T Q10|].
  split; [gk T Q11|]. split; [gk T Q12|]. split; [gk T Q13|].
  intros i Hi Hc. apply T; [exact (Q14 i Hi Hc)|]. intros a' Ha'. cbn [cells_size csize] in Ha'.
  assert (i <> ss x) by (intros X; subst i; rewrite Ox in Hc; discriminate). unfold G_S, SRC_SIZE. lia.
Qed.

Lemma src_keep : forall K sp Ee Ff L A mem md L' A' mem' md' x C V p h,
  (x < sN)%nat -> (p < sN)%nat -> p <> x -> @YM05.alloc_ceiling rc <= sp - K -> aa_MR API L A mem md ->
  rmid B API K sp Ee Ff L A mem md L' A' mem' md' ->
  (forall a, Ee a -> (sHA x + 80 <= a < sHA x + 96) \/ (0 < C /\ V <= a < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A) /\ In V (hs_blocks (sh x))) ->
  (forall q, Ff q -> In q (hs_blocks (sh x))) ->
  (forall q, In q (hs_blocks h) -> In q (hs_blocks (sh p))) ->
  src_at B L A mem (sHA p) h -> src_at B L' A' mem' (sHA p) h.
Proof.
  intros K sp Ee Ff L A mem md L' A' mem' md' x C V p h Hx Hp Hpx HK HM R HE HV HF HSUB HS.
  pose proof (ss_lt x Hx). pose proof (ss_lt p Hp).
  assert (Hs : ss p <> ss x) by (intros X; exact (Hpx (ss_inj p x Hp Hx X))).
  apply (fin_src rc B API K sp Ee Ff L A mem md L' A' mem' md' (sHA p) h HAX HBW HSEG HK HM R); [| |exact HS].
  - intros i Hi. assert (P : img_plain B (sHA p + i)) by (apply HPLG; unfold sHA, G_S, SRC_SIZE; lia).
    split; [exact P|].
    exact (hf_img_notE B API HAX Ee (sHA x + 80) (sHA x + 96) C V (sHA p + i) L A mem md HM HE
             (fun Hc => proj1 (HV Hc)) (proj1 P) ltac:(unfold sHA, G_S, SRC_SIZE; lia)).
  - intros q Hq. apply (hf_kept B API HAX L A mem md Ee Ff (sHA x + 80) (sHA x + 96) C V q HM).
    + intros a Ha. apply HPLG. unfold sHA, G_S, SRC_SIZE in *. lia.
    + exact HE.
    + intros Hc. exact (proj1 (HV Hc)).
    + intros X. exact (blk_disj p x q Hp Hx Hpx (HSUB q Hq) (HF q X)).
    + intros Hc EQ. subst q. exact (blk_disj p x V Hp Hx Hpx (HSUB V Hq) (proj2 (HV Hc))).
Qed.

Lemma live_pos : slive = true -> 0 < sTOT.
Proof.
  intros HL. pose proof (exit_entries_nonneg es). unfold slive, send_live, send_off in HL.
  destruct (Z.eqb_spec sTOT 0) as [X|X]; [|unfold sTOT in *; lia].
  try rewrite (proj2 (Z.eqb_eq _ _) X) in HL. rewrite !orb_true_r in HL. cbn in HL. discriminate.
Qed.

Lemma heap_keep : forall K sp Ee Ff L A mem md L' A' mem' md' x C V,
  (x < sN)%nat -> aa_MR API L A mem md -> rmid B API K sp Ee Ff L A mem md L' A' mem' md' ->
  (forall a, Ee a -> (sHA x + 80 <= a < sHA x + 96) \/ (0 < C /\ V <= a < V + 16 * C)) ->
  (0 < C -> In (V, 16 * C) (blocks L A) /\ In V (hs_blocks (sh x))) ->
  (forall q, Ff q -> In q (hs_blocks (sh x))) ->
  In (G, SRC_TABLE) (blocks L A) -> (slive = true -> In (OUT', CAP') (blocks L A)) ->
  table_at B mem G (map entry_cleared es) tail ->
  (slive = true -> bytes_at (ms_segs B) mem OUT' (entries_out es ++ junk')) ->
  table_at B mem' G (map entry_cleared es) tail /\
  (slive = true -> bytes_at (ms_segs B) mem' OUT' (entries_out es ++ junk')).
Proof.
  intros K sp Ee Ff L A mem md L' A' mem' md' x C V Hx HM R HE HV HF HG HO (TL & TC) OB.
  pose proof (ss_lt x Hx) as Sx.
  assert (NE : forall q kq i, In (q, kq) (blocks L A) -> 0 <= i < kq -> (0 < C -> q <> V) -> ~ Ee (q + i)).
  { intros q kq i Hq Hi HqV X. destruct (HE _ X) as [D|(Hc & D)].
    - apply (hf_blk_img B API HAX L A mem md q kq i HM Hq Hi).
      apply (proj1 (HPLG (q + i) ltac:(unfold sHA, G_S, SRC_SIZE in D; lia))).
    - destruct (blocks_disjoint B API L A mem md V (16 * C) q kq HM (proj1 (HV Hc)) Hq (fun e => HqV Hc (eq_sym e)));
        lia. }
  split.
  - split; [exact TL|].
    apply (rmid_rw_block B API HBW K sp Ee Ff L A mem md L' A' mem' md' G SRC_TABLE G _ R HG
             ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)); [ |exact TC|lia|cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia|].
    + intros X. destruct (blk_tg x G Hx (HF G X)) as [N1 _]. exact (N1 eq_refl).
    + intros i Hi. cbn [cells_size csize] in Hi. apply (NE G SRC_TABLE i HG ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)).
      intros Hc EQ. subst V. destruct (blk_tg x G Hx (proj2 (HV Hc))) as [N1 _]. exact (N1 eq_refl).
  - intros HL. pose proof (HLIVE HL) as (T1 & _ & _ & FR & _ & JL). pose proof (live_pos HL) as TP.
    pose proof (exit_entries_length es) as EL.
    apply (rmid_bytes_block B API HBW K sp Ee Ff L A mem md L' A' mem' md' OUT' CAP' OUT' _ R (HO HL)
             ltac:(unfold sTOT in *; lia)); [ |exact (OB HL)|lia|rewrite length_app; unfold sTOT in *; lia|].
    + intros X. exact (blk_OUT HL x OUT' Hx (HF OUT' X) eq_refl).
    + intros i Hi. rewrite length_app in Hi. apply (NE OUT' CAP' i (HO HL) ltac:(unfold sTOT in *; lia)).
      intros Hc EQ. exact (blk_OUT HL x V Hx (proj2 (HV Hc)) (eq_sym EQ)).
Qed.

Lemma cum_step : forall Ee Ff L A mem md L' A' mem' md',
  rmid B API SLOT_STACK (spZ (ss_regs E)) (fun a => exit_fin_E slive sOUT sCAP G a \/ scan_E hj a)
    (fun q => exit_fin_F slive sOUT es q \/ scan_F hj q) L0 A0 m0 md0 L A mem md ->
  rmid B API SLOT_STACK (spZ (ss_regs E)) Ee Ff L A mem md L' A' mem' md' ->
  (forall a, Ee a -> scan_E hj a) -> (forall q, Ff q -> scan_F hj q) ->
  rmid B API SLOT_STACK (spZ (ss_regs E)) (fun a => exit_fin_E slive sOUT sCAP G a \/ scan_E hj a)
    (fun q => exit_fin_F slive sOUT es q \/ scan_F hj q) L0 A0 m0 md0 L' A' mem' md'.
Proof.
  intros Ee Ff L A mem md L' A' mem' md' R1 R2 HE HF. exs.
  eapply rmid_EF; [exact (rmid_seq B API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF R1 R2)| |].
  - intros a [[X|X]|X]; [left; exact X|right; exact X|right; exact (HE a X)].
  - intros q [[X|X]|X]; [left; exact X|right; exact X|right; exact (HF q X)].
Qed.

Lemma sf_nowrite : forall d L A mem md Hs m1, sfacts d L A mem md Hs ->
  mem_rel rsegs m1 (normalize rsegs mem) -> ro_same rsegs mem m1 -> sfacts d L A m1 md Hs.
Proof.
  intros d L A mem md Hs m1 SF MREL ROS.
  destruct SF as (RMC & INIT & RO & HRI & (S1 & S2 & S3) & ACC & GL & SRCS & HSD & TAB & OBY & BLK).
  pose proof RMC as (HM & HWF' & HBD & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  pose proof ac_facts as (A1 & A2 & A3 & A4 & A5).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  assert (HK : @YM05.alloc_ceiling rc <= sb - CHECK_SHAPE_ENDS_K)
    by (unfold CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK; lia).
  destruct (rmid_norm B API CHECK_SHAPE_ENDS_K sb (fun _ => False) (fun _ => False) L A mem md
              (normalize rsegs mem) m1 [] HSEG RO' MREL ROS (munch_refl _ _) (wmono_refl _ _) HM HWF' HBD HK)
    as (RMn & MU & WM).
  { intros a Ha. apply SC. unfold sk in *. rewrite A5.
    unfold SLOT_STACK, CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK in *. lia. }
  { intros x Hx O. exfalso. exact (O I). }
  { intros a Ho. exact I. }
  { intros p n i Hp Hi O. exfalso. exact (O I). }
  assert (WM' : wmono (ms_segs B) mem m1) by (rewrite HSEG; exact WM).
  assert (TR : forall a cs, rw_cells (ms_segs B) mem a cs -> rw_cells (ms_segs B) m1 a cs)
    by (intros a cs H; exact (rw_cells_transport (ms_segs B) [] mem m1 a cs H MU WM' I)).
  assert (TB : forall a bs, bytes_at (ms_segs B) mem a bs -> bytes_at (ms_segs B) m1 a bs)
    by (intros a bs H; exact (bytes_at_transport (ms_segs B) [] mem m1 a bs H MU I)).
  assert (RMw : rmid B API SLOT_STACK (spZ (ss_regs E)) (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (rmid_widen B API CHECK_SHAPE_ENDS_K sb); [exact HM| | | | | |intros a _ X; exact X|exact RMn].
    - rewrite A5. unfold SLOT_STACK, CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK. lia.
    - lia.
    - rewrite A5. unfold SLOT_STACK. lia.
    - lia.
    - intros a Ha. apply SC. unfold sk. left. exact Ha. }
  split; [exact (cum_step _ _ L A mem md L A m1 md RMC RMw (fun a X => match X with end)
                   (fun q X => match X with end))|].
  split; [exact INIT|].
  split; [rewrite HSEG; exact (ro_agree_same rsegs mem m1 RO' ROS)|].
  split; [exact HRI|].
  split; [split; [exact (TR _ _ S1)|split; [exact (TR _ _ S2)|intros i Hi; exact (TR _ _ (S3 i Hi))]]|].
  split; [exact (TR _ _ ACC)|].
  split; [exact (glob_tr mem m1 TR GL)|].
  split.
  { intros p Hp. pose proof (ss_lt p Hp).
    apply (fin_src rc B API CHECK_SHAPE_ENDS_K sb (fun _ => False) (fun _ => False) L A mem md L A m1 md (sHA p) _
             HAX HBW HSEG HK HM RMn); [| |exact (SRCS p Hp)].
    - intros i Hi. split; [apply HPLG; unfold sHA, G_S, SRC_SIZE; lia|intros []].
    - intros q _. split; [intros []|intros kq i _ _ []]. }
  split; [exact HSD|].
  split; [split; [exact (proj1 TAB)|exact (TR _ _ (proj2 TAB))]|].
  split; [intros HL; exact (TB _ _ (OBY HL))|].
  exact BLK.
Qed.

Lemma g_in : forall d L A, (forall q m, In (q, m) (blocks L A) <-> sbase q m /\ ~ sfreed d q) ->
  In (G, SRC_TABLE) (blocks L A).
Proof.
  intros d L A BLK. apply BLK. split.
  - left. exs. pose proof HREL as (_ & GIN & _). destruct (fin_target G sOUT es hj target_nodup) as (T1 & T2 & _).
    split; [exact GIN|]. split; [exact T1|exact T2].
  - intros (p & _ & Hp & Hq). apply in_map_iff in Hq as (r & Er & Hr).
    assert (Hb : In G (hs_blocks (sh p))).
    { apply held_in_blocks. unfold list_blocks. apply in_or_app. right. rewrite <- Er. apply in_map. exact Hr. }
    destruct (blk_tg p G Hp Hb) as [N1 _]. exact (N1 eq_refl).
Qed.

Lemma out_in : forall d L A, (forall q m, In (q, m) (blocks L A) <-> sbase q m /\ ~ sfreed d q) ->
  slive = true -> In (OUT', CAP') (blocks L A).
Proof.
  intros d L A BLK HL. apply BLK. split.
  - right. left. split; [exact HL|split; reflexivity].
  - intros (p & _ & Hp & Hq). apply in_map_iff in Hq as (r & Er & Hr).
    assert (Hb : In OUT' (hs_blocks (sh p))).
    { apply held_in_blocks. unfold list_blocks. apply in_or_app. right. rewrite <- Er. apply in_map. exact Hr. }
    exact (blk_OUT HL p OUT' Hp Hb eq_refl).
Qed.

Lemma scan_src_wt : forall d L A mem Hs, List.NoDup (map fst (blocks L A)) ->
  (forall p, (p < sN)%nat -> src_at B L A mem (sHA p) (scur Hs d p)) ->
  (forall p, (p < d)%nat -> (p < sN)%nat ->
     hl_v (Hs p) = hl_v (hs_held (sh p)) /\ hl_cap (Hs p) = hl_cap (hs_held (sh p)) /\ hl_recs (Hs p) = []) ->
  zsum (CF.SlotRI3.nc_sz L A) (concat (map (fun p => src_nc (fst p)) hj)) <= zsum (fun p => nw_src (fst p)) hj.
Proof.
  intros d L A mem Hs HN SR HD. rewrite CF.SlotNcWt.nw_zsum_concat. apply CF.SlotNcWt.nw_zsum_le.
  intros y Hy. destruct (In_nth _ _ pd0 Hy) as (p & Hp & <-). rewrite len_hj in Hp.
  change (fst (nth p hj pd0)) with (sh p).
  pose proof (SR p Hp) as S0. unfold scur in S0.
  destruct (Nat.ltb_spec p d) as [Hd|Hd].
  - change (src_at B L A mem (sHA p) (set_held (sh p) (Hs p))) in S0.
    pose proof (CF.SlotNcWt.nw_src_le B L A mem (sHA p) _ HN S0) as X.
    destruct (HD p Hd Hp) as (E1 & E2 & E3).
    assert (SN : src_nc (set_held (sh p) (Hs p)) = src_nc (sh p)).
    { unfold src_nc, arr_nc, set_held. cbn [hs_pending hs_partial hs_expected hs_held]. rewrite E1, E2. reflexivity. }
    rewrite SN in X. eapply Z.le_trans; [exact X|].
    unfold nw_src, nw_list, set_held, pending_stream, hl_n. cbn [hs_pending hs_off hs_expected hs_held].
    rewrite E2, E3. cbn [length]. unfold NC_PER, DATA_PER. lia.
  - change (src_at B L A mem (sHA p) (sh p)) in S0.
    exact (CF.SlotNcWt.nw_src_le B L A mem (sHA p) _ HN S0).
Qed.

Lemma scan_ncs : forall d L A mem Hs, List.NoDup (map fst (blocks L A)) ->
  (forall q m, In (q, m) (blocks L A) <-> sbase q m /\ ~ sfreed d q) ->
  (forall p, (p < sN)%nat -> src_at B L A mem (sHA p) (scur Hs d p)) ->
  (forall p, (p < d)%nat -> (p < sN)%nat ->
     hl_v (Hs p) = hl_v (hs_held (sh p)) /\ hl_cap (Hs p) = hl_cap (hs_held (sh p)) /\ hl_recs (Hs p) = []) ->
  CF.SlotRI3.ncs sV L A <= nc_wt [] hj.
Proof.
  intros d L A mem Hs HN BLK SR HD. unfold sV.
  apply fin_ncs_view; [exact HN|exact (g_in d L A BLK)| |exact (scan_src_wt d L A mem Hs HN SR HD)|
    rewrite len_hj; exact sN_le].
  exs. pose proof HOUT as (_ & HCB). pose proof (bv_unsigned_in_range _ cap) as [C0 _].
  destruct slive eqn:HL.
  - apply fin_sz_le; [exact HN|unfold TBBYTES; lia|]. intros m Hm.
    destruct (HLIVE HL) as (T1 & _ & T3 & _ & HQ & _).
    pose proof tot_bound as TB. pose proof k_bound as KB.
    apply BLK in Hm as [Hb _]. unfold sbase in Hb.
    destruct Hb as [(H0 & NO & NE)|[(_ & _ & ->)|(X & _)]].
    + destruct (Z_lt_le_dec 0 m) as [P|P]; [exfalso; exact (HQ OUT' m H0 NO NE P eq_refl)|unfold TBBYTES; lia].
    + unfold sTOT in TB. unfold TBBYTES in *. lia.
    + rewrite HL in X. discriminate X.
  - apply Z.le_trans with sCAP; [apply fin_sz_le; [exact HN|unfold sCAP; lia|]|unfold sCAP; exact HCB].
    intros m Hm. apply BLK in Hm as [Hb _]. unfold sbase in Hb.
    destruct Hb as [(_ & NO & _)|[(X & _)|(_ & _ & _ & ->)]]; [exfalso; exact (NO eq_refl)| |lia].
    rewrite HL in X. discriminate X.
Qed.

Lemma zero_cells : forall segs m a, rw_cells segs m a [CB 96%nat (nulbytes 96)] ->
  rw_cells segs m a [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m a H.
  assert (H2 : rw_cells segs m a ([CB 8 (nulbytes 8)] ++ [CB 88 (nulbytes 88)])).
  { apply (rw_cells_retype segs m a _ _ H); [cbn; split; [reflexivity|split; [reflexivity|exact I]]|reflexivity]. }
  destruct (hg_cut _ _ _ _ _ H2) as [H3 _].
  apply (rw_cells_retype segs m a _ _ H3); [cbn; tauto|vm_compute; reflexivity].
Qed.

Lemma slot_cells : forall d L A mem md Hs i jj, sfacts d L A mem md Hs -> (i < sN)%nat -> (jj < 4)%nat ->
  exists fd o, rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat jj) [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 o)] /\
    0 <= fd < 2 ^ 31 /\ 0 <= o < 2 ^ 31 /\
    (o <> 0 -> fd = nth i (map re_fd es) 0 -> jj = ss i) /\
    (jj = ss i -> o <> 0 /\ fd = nth i (map re_fd es) 0).
Proof.
  intros d L A mem md Hs i jj SF Hi Hjj.
  destruct SF as (_ & _ & _ & _ & _ & _ & GL & SRCS & _).
  destruct (pair_at i Hi) as (eI & HeI & _ & _).
  rewrite (fd_nth i eI HeI).
  destruct (slot_open hj jj) eqn:Ho.
  - destruct (slot_open_inv jj Ho) as (p & Hp & <-). pose proof (SRCS p Hp) as S.
    apply src_at_iff in S. destruct S as ((C1 & _ & _ & HO & HF & _) & _).
    destruct (pair_at p Hp) as (ep & Hep & _ & POp). unfold pair_ok in POp. cbv zeta in POp.
    destruct POp as (_ & _ & FDp & _).
    assert (FDc : hs_fd (scur Hs d p) = re_fd ep) by (unfold scur; destruct (Nat.ltb p d); exact FDp).
    exists (hs_fd (scur Hs d p)), (hs_open (scur Hs d p)).
    split; [exact (proj1 (hg_cut _ _ _ [_; _] [_; _] C1))|].
    split; [lia|]. split; [lia|]. rewrite FDc.
    split.
    + intros _ X. rewrite (fd_inj p i ep eI Hep HeI X). reflexivity.
    + intros X. pose proof (ss_inj p i Hp Hi X) as <-. rewrite Hep in HeI. injection HeI as <-. split; [lia|reflexivity].
  - destruct GL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ZH).
    exists 0, 0. split; [exact (zero_cells _ _ _ (ZH jj Hjj Ho))|].
    split; [lia|]. split; [lia|]. split; [intros X; lia|].
    intros X. subst jj. rewrite (slot_open_ss i Hi) in Ho. discriminate.
Qed.

Definition mid1_body (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    : Prop :=
  rmid B API SLOT_STACK (spZ (ss_regs E)) (exit_fin_E slive sOUT sCAP G) (exit_fin_F slive sOUT es)
    L0 A0 m0 md0 L A mem md /\
  st_init_done A = true /\ ro_agree (ms_segs B) mem /\
  (forall r, callee_saved r -> r <> 8 -> YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)) /\
  (0 < Z.of_nat (length es) -> YK11.getr regs (Z_to_bv 5 8) = Z_to_bv 64 (Z.of_nat (length es))) /\
  rw_cells (ms_segs B) mem (sb + 88) (saved_cells (ss_regs E)) /\
  rw_cells (ms_segs B) mem sb [C8 (Z_to_bv 64 CLIENT_BASE)] /\
  rw_cells (ms_segs B) mem (sb + 16) [C8 (Z_to_bv 64 0)] /\
  (forall i, (i < length es)%nat ->
     rw_cells (ms_segs B) mem (sb + 40 + 4 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]) /\
  rw_cells (ms_segs B) mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_GONE [C1 (Z_to_bv 8 gn)] /\
  rw_cells (ms_segs B) mem G_NFD [C4 (Z_to_bv 64 nfd)] /\
  rw_cells (ms_segs B) mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
  rw_cells (ms_segs B) mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
  rw_cells (ms_segs B) mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
  rw_cells (ms_segs B) mem G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells (ms_segs B) mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
  rw_cells (ms_segs B) mem G_BROKEN [C1 (Z_to_bv 8 (if soff then br else dd))] /\
  rw_cells (ms_segs B) mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells (ms_segs B) mem G_EINTR [C1 (Z_to_bv 8 (if soff then ei else 0))] /\
  (exists ev, rw_cells (ms_segs B) mem (errno_addr B) [C4 ev]) /\
  Forall2 (pair_ok (rc := rc) B L A mem t) es hj /\
  (forall i, (i < 4)%nat -> slot_open hj i = false ->
     rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
  table_at B mem G (map entry_cleared es) tail /\ In (G, SRC_TABLE) (blocks L A) /\
  (forall q m, In (q, m) (blocks L A) <-> sbase q m) /\
  (slive = false -> rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 (Z_to_bv 64 0); C8 cap; C8 out]) /\
  (slive = true ->
     sTOT <= CAP' /\ CAP' = relay_finish_cap slive (bv_unsigned mx) 0 sCAP es /\ CAP' <= Z.max sCAP (2 * sTOT) /\
     fresh_block B OUT' CAP' /\
     (forall q m, In (q, m) (blocks L0 A0) -> q <> sOUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
        q <> OUT') /\
     bytes_at (ms_segs B) mem OUT' (entries_out es ++ junk') /\ Z.of_nat (length junk') = CAP' - sTOT /\
     rw_cells (ms_segs B) mem G_OUTV [C8 mx; C8 (Z_to_bv 64 sTOT); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]) /\
  RI E k sV L A.

Lemma mid1_sf : forall L A regs mem md, mid1_body L A regs mem md -> sfacts 0 L A mem md (fun _ => hl0).
Proof.
  intros L A regs mem md (RM & INIT & RO & KEEP & R19 & S1 & S2 & S3 & S4 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 &
    Q9 & Q10 & Q11 & Q12 & ER & PA & ZH & TB' & GIN & BLK & NL & YL & HRI).
  split; [eapply rmid_EF; [exact RM|intros a X; left; exact X|intros q X; left; exact X]|].
  split; [exact INIT|]. split; [exact RO|]. split; [exact HRI|].
  split; [split; [exact S1|split; [exact S2|exact S4]]|].
  split; [unfold sacc; destruct (gn =? 0); exact S3|].
  split.
  { split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|].
    split; [exact Q11|]. split; [exact Q12|]. split; [|exact ZH].
    unfold sNO, sCAPw, sOUTw. destruct slive eqn:HL.
    - destruct (YL ltac:(first [exact HL|reflexivity])) as (_ & _ & _ & _ & _ & _ & _ & X). exact X.
    - exact (NL ltac:(first [exact HL|reflexivity])). }
  split.
  { intros p Hp. destruct (pair_at p Hp) as (e & He & _ & _).
    pose proof (f2_nth _ _ _ e pd0 p PA Hp) as X. unfold pair_ok in X. cbv zeta in X. destruct X as (X & _).
    exact X. }
  split; [intros p Hp; lia|].
  split; [exact TB'|].
  split; [intros HL; destruct (YL HL) as (_ & _ & _ & _ & _ & X & _); exact X|].
  intros q m. rewrite BLK. split; [intros X; split; [exact X|intros (p & Hp & _); lia]|intros [X _]; exact X].
Qed.

Lemma freed_F : forall q, sfreed sN q <-> scan_F hj q.
Proof.
  intros q. split.
  - intros (p & _ & Hp & Hq). exists (nth p hj pd0). split; [apply nth_In; rewrite len_hj; exact Hp|exact Hq].
  - intros (pr & Hpr & Hq). destruct (In_nth _ _ pd0 Hpr) as (p & Hp & Ep). rewrite len_hj in Hp.
    exists p. split; [exact Hp|]. split; [exact Hp|]. unfold sh. rewrite Ep. exact Hq.
Qed.

Lemma pack : forall c, mid2_state c -> exit_mid2 (rc := rc) B API E RI t k c.
Proof.
  intros c (L & A & regs & mem & md & Hs & -> & RA & KEEP & SF).
  pose proof SF as (RMC & INIT & RO & HRI & (S1 & S2 & S3) & ACC & GL & SRCS & HSD & TAB & OBY & BLK).
  pose proof GL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & ZH).
  assert (AC : sacc sN = (if gn =? 0 then entries_total es else 0)) by (unfold sacc, sN; rewrite firstn_all; reflexivity).
  exists fx, L0, A0, regs0, m0, md0, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj, tail, L, A, regs, mem, md,
    OUT', CAP', junk', Hs.
  cbv zeta.
  split; [reflexivity|]. split; [rewrite RA, AC; reflexivity|]. split; [exact HFZ|]. split; [exact HEXS|].
  split; [exact HTB|]. split; [exact RMC|]. split; [exact INIT|]. split; [exact RO|]. split; [exact KEEP|].
  split; [exact S1|]. split; [exact S2|]. split; [rewrite <- AC; exact ACC|]. split; [exact S3|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
  split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q10|].
  split; [exact Q11|]. split; [exact Q12|].
  split.
  { intros p Hp. rewrite len_hj in Hp. destruct (HSD p Hp Hp) as (V1 & V2 & V3).
    split; [exact V1|]. split; [exact V2|]. split; [exact V3|].
    pose proof (SRCS p Hp) as X. unfold scur in X. rewrite (proj2 (Nat.ltb_lt p sN) Hp) in X. exact X. }
  split; [exact ZH|]. split; [exact TAB|]. split; [exact (g_in sN L A BLK)|].
  split.
  { intros q m. rewrite BLK, freed_F. reflexivity. }
  split.
  { intros HL. unfold sNO, sCAPw, sOUTw in Q13. change (send_live cl br dd (entries_total es)) with slive in HL.
    rewrite HL in Q13. exact Q13. }
  split; [|exact HRI].
  intros HL. change (send_live cl br dd (entries_total es)) with slive in HL.
  destruct (HLIVE HL) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
  unfold sNO, sCAPw, sOUTw in Q13. rewrite HL in Q13.
  split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5|].
  split; [exact (OBY HL)|]. split; [exact Y6|]. exact Q13.
Qed.

Definition mid1_state (c : config) : Prop :=
  exists (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
    c = mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (if Z.of_nat (length es) =? 0 then 0x14740 else 0x146d4)) mem
                 (seg_rom (ms_segs B))) md /\
    mid1_body L A regs mem md.

Lemma sacc_gone : gn = 0 -> forall d, sacc d = entries_total (firstn d es).
Proof. intros G0 d. unfold sacc. rewrite (proj2 (Z.eqb_eq gn 0) G0). reflexivity. Qed.

Lemma rw1 : forall segs m a x, rw_cells segs m a [C1 x] -> bytes_at segs m a [x].
Proof. intros segs m a x [[_ H] _]. cbn [cells_bytes cbytes app] in H. exact H. Qed.

Lemma outv_bytes : forall segs m a b c d, rw_cells segs m G_OUTV [C8 a; C8 b; C8 c; C8 d] ->
  bytes_at segs m 0x318e0 (le8 b) /\ bytes_at segs m 0x318f0 (le8 d).
Proof.
  intros segs m a b c d [[_ BB] _]. cbn [cells_bytes cbytes] in BB.
  apply bytes_at_app in BB as [_ BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [BB1 BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [_ BB]. rewrite length_le8 in BB.
  apply bytes_at_app in BB as [BB2 _].
  assert (E1 : G_OUTV + Z.of_nat 8 = 0x318e0) by (unfold G_OUTV; reflexivity).
  assert (E2 : G_OUTV + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 = 0x318f0) by (unfold G_OUTV; reflexivity).
  rewrite E1 in BB1. rewrite E2 in BB2. split; assumption.
Qed.

Lemma bytes_nil : forall segs m a, 0 <= a <= 2 ^ 64 -> bytes_at segs m a [].
Proof. intros segs m a Ha. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia. Qed.

Lemma rg_from : forall i jj regs regs1, rg_loop i jj regs ->
  (forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 18 <= r <= 27) ->
     YK11.getr regs1 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  rg_loop i jj regs1.
Proof.
  intros i jj regs regs1 (KP & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24) K1.
  split; [intros r Hr; rewrite (K1 r ltac:(lia)); exact (KP r Hr)|].
  split; [rewrite (K1 8 ltac:(lia)); exact G8|]. split; [rewrite (K1 9 ltac:(lia)); exact G9|].
  split; [rewrite (K1 18 ltac:(lia)); exact G18|]. split; [rewrite (K1 19 ltac:(lia)); exact G19|].
  split; [rewrite (K1 21 ltac:(lia)); exact G21|]. split; [rewrite (K1 22 ltac:(lia)); exact G22|].
  split; [rewrite (K1 23 ltac:(lia)); exact G23|]. rewrite (K1 24 ltac:(lia)); exact G24.
Qed.

Ltac creg GR := intros r Hr; rewrite GR;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.

Ltac kreg GR KP := intros r Hr; rewrite GR, <- (KP r Hr);
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 20 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity.

Lemma scan_call : forall i L A regs mem md Hs, (i < sN)%nat -> rg_loop i (ss i) regs ->
  getr regs 1 = Z_to_bv 64 0x14720 -> getr regs 10 = Z_to_bv 64 (sHA i) -> getr regs 11 = Z_to_bv 64 0x102e9 ->
  getr regs 12 = Z_to_bv 64 (sb + 16) -> sfacts i L A mem md Hs ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x14a78) mem (seg_rom (ms_segs B))) md) (at_ret i (ss i)).
Proof.
  intros i L A regs mem md Hs Hi RG R1 R10 R11 R12 SF.
  pose proof SF as (RMC & INIT & RO & HRI & ST & ACC & GL & SRCS & HSD & TAB & OBY & BLK).
  pose proof RMC as (HM & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC).
  pose proof ac_facts as (A1 & A2 & A3 & A4 & A5).
  pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof (ss_lt i Hi) as Si. pose proof sN_le as NL4. pose proof tot_bound as TB. pose proof k_bound as KB.
  destruct (pair_at i Hi) as (e & He & EO & PO).
  pose proof PO as PO'. unfold pair_ok in PO'. cbv zeta in PO'.
  destruct PO' as (_ & _ & _ & _ & _ & NDT & _ & _ & _ & _ & _ & HCAP).
  pose proof (SRCS i Hi) as SRCi. unfold scur in SRCi. rewrite Nat.ltb_irrefl in SRCi.
  pose proof SRCi as SRCi'. apply src_at_iff in SRCi'. destruct SRCi' as (SB & LE & LH & NDB).
  pose proof LH as (LHc & LHn & LHar & LHnd1 & LHnd2 & LHfa).
  pose proof (hf_list_head B L A mem _ _ _ LH) as (_ & _ & V0 & V1).
  assert (FB : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (blocks L A)) (hl_recs (hs_held (sh i)))).
  { eapply Forall_impl; [|exact LHfa]. intros r X. exact (proj1 X). }
  destruct (HRES k L A gn (hl_recs (hs_held (sh i))) (skipn (Z.to_nat (sacc i)) sOB)
              G (if slive then OUT' else sOUT) [] hj HRI gn01 FB
              ltac:(first [exact (proj1 (NoDup_ListNoDup _) LHnd1)|exact LHnd1]))
    as (bnd & ROK & ROOM & RIK).
  assert (SPZ : spZ regs = sb) by exact (rg_spZ regs (proj1 RG)).
  assert (PFv : bv_unsigned (getr regs 11) = 0x102e9) by (rewrite R11; reflexivity).
  assert (ATv : bv_unsigned (getr regs 12) = sb + 16) by (rewrite R12; apply unsigned_lit; lia).
  assert (NOv : bv_unsigned sNO = (if slive then sTOT else 0)) by (unfold sNO; apply unsigned_lit; destruct slive; lia).
  assert (OUTv : bv_unsigned sOUTw = (if slive then OUT' else sOUT)).
  { unfold sOUTw. destruct slive eqn:HL; [|reflexivity].
    destruct (HLIVE ltac:(first [exact HL|reflexivity])) as (T1 & _ & _ & (F0 & F1 & _) & _).
    apply unsigned_lit. unfold sTOT in *. lia. }
  pose proof (HCSE L A regs mem md bnd (sh i) (ss i) gn (sacc i) sNO sOUTw sOB [] EMPTY_SLACK) as HC.
  cbv zeta in HC. rewrite PFv, ATv, NOv, OUTv, SPZ in HC.
  pose proof GL as (_ & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q13 & _).
  eapply SR_bind.
  { apply HC; clear HC.
    - exact HSEG.
    - eapply (cpk_of_rmid B API _ _ _ _ L0 A0 m0 md0 L A mem md regs CHECK_SHAPE_ENDS_K RMC INIT).
      + change (YK11.getr regs 1) with (getr regs 1). rewrite R1. apply ret_ok_even. vm_compute. reflexivity.
      + transitivity (YK11.getr regs (Z_to_bv 5 4)); [reflexivity|exact (rg_tp regs (proj1 RG))].
      + rewrite SPZ. exact A4.
      + rewrite SPZ, A5. unfold SLOT_STACK, CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME,
          ALLOC_STACK. lia.
      + rewrite SPZ, A5. lia.
      + unfold CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK. lia.
      + rewrite SPZ. unfold CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK. lia.
      + rewrite SPZ. lia.
    - exact INIT.
    - exact RO.
    - intros a Ha. apply HPLG.
      unfold G_GONE, G_S, CF.check_shape_ends_c.G_GONE, CF.check_shape_ends_c.G_S, SRC_SIZE, SOURCES_MAX in Ha. lia.
    - exact Si.
    - transitivity (YK11.getr regs (Z_to_bv 5 10)); [reflexivity|exact R10].
    - exact SRCi.
    - exact NDT.
    - change (fst (nth i hj pd0)) with (sh i) in HCAP. unfold hl_n in *. lia.
    - rewrite HSEG. rewrite HSEG in RO. exact (empty_at mem RO).
    - exact empty_nz.
    - apply Z.leb_le. vm_compute. reflexivity.
    - right. split; [lia|]. split; [cbn; lia|]. intros j0 Hj0. rewrite HSEG. exact (empty_ro j0 Hj0).
    - Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - right. cbn. lia.
    - exact ACC.
    - destruct gn01; lia.
    - exact (rw1 _ _ _ _ Q2).
    - exact (proj1 (outv_bytes _ _ _ _ _ _ Q13)).
    - exact (proj2 (outv_bytes _ _ _ _ _ _ Q13)).
    - unfold sOB. destruct slive eqn:HL.
      + pose proof (OBY ltac:(first [exact HL|reflexivity])) as X. apply bytes_at_app in X. exact (proj1 X).
      + apply bytes_nil. unfold sOUT. pose proof (bv_unsigned_in_range 64 out) as R. unfold bv_modulus in R.
        cbn in R. lia.
    - unfold sOB. destruct slive; [rewrite exit_entries_length; reflexivity|reflexivity].
    - unfold sOB. destruct slive eqn:HL; [right|left; reflexivity].
      destruct (HLIVE ltac:(first [exact HL|reflexivity])) as (T1 & _ & _ & FR & _).
      exists CAP'. split; [exact T1|]. split; [exact (out_in i L A BLK HL)|]. split; [exact FR|].
      intros X. exact (blk_OUT HL i OUT' Hi X eq_refl).
    - exact (acc_bound i).
    - intros G0. rewrite (ob_gone G0), (sacc_gone G0 i), (entries_out_split es i e He).
      destruct (exit_keys_run rc B L0 A0 m0 t e (nth i hj pd0) (entries_out (skipn (S i) es)) EO PO)
        as (rs0 & ds0 & EK).
      change (fst (nth i hj pd0)) with (sh i) in EK. rewrite EK. discriminate.
    - exact ROK. }
  intros c' (L' & A' & regs' & mem' & md' & H' & ds & c0 & EC & RP & INIT' & (qs & QLEN & QOK) & RO' & SRC' & HV' &
    HC' & NDT' & CASE & ACC' & PFB & GON & NOUT & GOUT & OBY' & BK1 & BK2).
  destruct (rp_split B API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RMn PR]. rewrite SPZ in RMn.
  assert (POST : hl_recs H' = [] /\ (forall q, In q (map fst ds) <-> In q (map fst (hl_recs (hs_held (sh i))))) /\
                 c0 = (if gn =? 0 then keys_total (re_keys e) else 0)).
  { destruct CASE as [(G1 & R' & D' & C')|(G0 & ER)].
    - rewrite R', filter_nil_none. split; [reflexivity|]. split; [intros q; rewrite D', filter_nil_all; tauto|].
      rewrite (proj2 (Z.eqb_neq gn 0) G1). exact C'.
    - rewrite (ob_gone G0), (sacc_gone G0 i), (entries_out_split es i e He) in ER.
      destruct (exit_keys_run rc B L0 A0 m0 t e (nth i hj pd0) (entries_out (skipn (S i) es)) EO PO)
        as (rs0 & ds0 & EK).
      change (fst (nth i hj pd0)) with (sh i) in EK.
      rewrite EK in ER. injection ER as ER1 ER2 ER3.
      destruct (ends_run_len _ _ _ _ _ _ _ EK) as [LN IN]. rewrite want_of_nil in LN.
      assert (R0 : rs0 = []) by (destruct rs0; [reflexivity|cbn in LN; lia]).
      split; [rewrite <- ER1; exact R0|]. split.
      + intros q. rewrite <- ER2. split; intros X; apply in_map_iff in X as (r & <- & Hr); apply in_map.
        * apply IN. right. exact Hr.
        * apply IN in Hr. rewrite R0 in Hr. destruct Hr as [[]|Hr]. exact Hr.
      + rewrite (proj2 (Z.eqb_eq gn 0) G0). symmetry. exact ER3. }
  destruct POST as (RECS & DS & C0).
  assert (ACCV : sacc i + c0 = sacc (S i)).
  { rewrite C0. unfold sacc. destruct (Z.eqb_spec gn 0); [rewrite (entries_total_S es i e He); reflexivity|lia]. }
  set (Ew := fun a => sHA i + 88 <= a < sHA i + 92 \/
    (0 < hl_cap (hs_held (sh i)) /\ hl_v (hs_held (sh i)) <= a < hl_v (hs_held (sh i)) + 16 * hl_cap (hs_held (sh i)))).
  assert (RMw : rmid B API SLOT_STACK (spZ (ss_regs E)) Ew (fun q => In q (map fst (hl_recs (hs_held (sh i)))))
                  L A mem md L' A' mem' md').
  { lazymatch type of RMn with rmid _ _ _ _ ?Ee ?Ff _ _ _ _ _ _ _ _ =>
      apply (rmid_widen_E B API CHECK_SHAPE_ENDS_K sb SLOT_STACK (spZ (ss_regs E)) Ee Ew Ff L A mem md L' A' mem' md' HM);
      [| | | | | | | |exact RMn] end.
    - rewrite A5. unfold SLOT_STACK, CHECK_SHAPE_ENDS_K, CHECK_SHAPE_ENDS_FRAME, LIST_DROP_K, LIST_DROP_FRAME, ALLOC_STACK. lia.
    - rewrite A5. lia.
    - exact HB1.
    - rewrite A5. lia.
    - intros a Ha. apply SC. unfold sk. left. exact Ha.
    - intros a. cbv beta. lia.
    - intros a X. cbv beta in X. unfold Ew. destruct X as [X|[X|X]].
      + right. left. exact X.
      + left. rewrite A5. unfold SLOT_STACK. lia.
      + right. right. exact X.
    - intros a Ha X. cbv beta in X. rewrite A5 in Ha. unfold SLOT_STACK in Ha. destruct X as [X|[X|(Xc & X)]].
      + exfalso. unfold G_S, CF.check_shape_ends_c.G_S, CF.check_shape_ends_c.G_GONE, SRC_SIZE in X. lia.
      + replace a with (sb + 16 + (a - (sb + 16))) by lia. apply (rw_writable _ _ _ _ _ ACC'). cbn [cells_size csize].
        lia.
      + exfalso. specialize (V1 Xc). lia. }
  assert (INi : In (nth i hj pd0) hj) by (apply nth_In; rewrite len_hj; exact Hi).
  pose proof (cum_step _ _ L A mem md L' A' mem' md' RMC RMw (fun a X => ex_intro _ (nth i hj pd0) (conj INi X))
                (fun q X => ex_intro _ (nth i hj pd0) (conj INi X))) as RMC'.
  assert (ST' : sstack mem').
  { apply (stack_keep CHECK_SHAPE_ENDS_K _ _ L A mem md L' A' mem' md' HM RMn); [|exact ST].
    intros a X. cbv beta in X. destruct X as [X|[X|(Xc & X)]].
    - left. unfold G_S, CF.check_shape_ends_c.G_S, CF.check_shape_ends_c.G_GONE, SRC_SIZE in X. lia.
    - right. lia.
    - left. specialize (V1 Xc). lia. }
  assert (HEw : forall a, Ew a -> (sHA i + 80 <= a < sHA i + 96) \/
      (0 < hl_cap (hs_held (sh i)) /\ hl_v (hs_held (sh i)) <= a < hl_v (hs_held (sh i)) + 16 * hl_cap (hs_held (sh i)))).
  { intros a [X|X]; [left; lia|right; exact X]. }
  assert (HVw : 0 < hl_cap (hs_held (sh i)) ->
      In (hl_v (hs_held (sh i)), 16 * hl_cap (hs_held (sh i))) (blocks L A) /\ In (hl_v (hs_held (sh i))) (hs_blocks (sh i))).
  { intros Hc. destruct (hf_list_v B L A mem _ _ _ LH Hc) as [X1 X2]. split; [exact X1|exact (held_in_blocks _ _ X2)]. }
  assert (HFw : forall q, In q (map fst (hl_recs (hs_held (sh i)))) -> In q (hs_blocks (sh i))).
  { intros q X. apply held_in_blocks. unfold list_blocks. apply in_or_app. right. exact X. }
  pose proof (glob_keep _ _ _ _ L A mem md L' A' mem' md' i _ _ Hi HB1 HM RMw HEw (fun Hc => proj1 (HVw Hc)) GL)
    as GL'.
  pose proof (heap_keep _ _ _ _ L A mem md L' A' mem' md' i _ _ Hi HM RMw HEw HVw HFw (g_in i L A BLK)
                (out_in i L A BLK) TAB OBY) as [TAB' OBY''].
  set (Hs' := fun p => if Nat.eqb p i then H' else Hs p).
  assert (SRCS' : forall p, (p < sN)%nat -> src_at B L' A' mem' (sHA p) (scur Hs' (S i) p)).
  { intros p Hp. destruct (Nat.eq_dec p i) as [->|Hpi].
    - unfold scur, Hs'. rewrite (proj2 (Nat.ltb_lt i (S i)) (Nat.lt_succ_diag_r i)), Nat.eqb_refl. exact SRC'.
    - assert (CUR : scur Hs' (S i) p = scur Hs i p).
      { unfold scur, Hs'. rewrite (proj2 (Nat.eqb_neq p i) Hpi).
        destruct (Nat.ltb_spec p (S i)); destruct (Nat.ltb_spec p i); try reflexivity; lia. }
      rewrite CUR.
      apply (src_keep _ _ _ _ L A mem md L' A' mem' md' i _ _ p (scur Hs i p) Hi Hp Hpi HB1 HM RMw HEw HVw HFw).
      + intros q Hq. unfold scur in Hq. destruct (Nat.ltb_spec p i); [|exact Hq].
        destruct (HSD p ltac:(lia) Hp) as (E1 & E2 & E3). exact (held_done_blocks _ _ q E1 E2 E3 Hq).
      + exact (SRCS p Hp). }
  assert (HSD' : forall p, (p < S i)%nat -> (p < sN)%nat ->
      hl_v (Hs' p) = hl_v (hs_held (sh p)) /\ hl_cap (Hs' p) = hl_cap (hs_held (sh p)) /\ hl_recs (Hs' p) = []).
  { intros p Hp1 Hp2. unfold Hs'. destruct (Nat.eq_dec p i) as [->|Hpi].
    - rewrite Nat.eqb_refl. split; [exact HV'|]. split; [exact HC'|exact RECS].
    - rewrite (proj2 (Nat.eqb_neq p i) Hpi). apply HSD; lia. }
  assert (BLK' : forall q m, In (q, m) (blocks L' A') <-> sbase q m /\ ~ sfreed (S i) q).
  { intros q m. split.
    - intros X. destruct (BK2 q m X) as [Y NY]. destruct (proj1 (BLK q m) Y) as [Z NZ]. split; [exact Z|].
      intros (p & Hp1 & Hp2 & Hq). destruct (Nat.eq_dec p i) as [->|Hpi].
      + apply NY. apply (proj2 (DS q)). exact Hq.
      + apply NZ. exists p. split; [lia|]. split; [exact Hp2|exact Hq].
    - intros [Z NZ]. apply BK1.
      + apply BLK. split; [exact Z|]. intros (p & Hp1 & Hp2 & Hq). apply NZ. exists p.
        split; [lia|]. split; [exact Hp2|exact Hq].
      + intros X. apply NZ. exists i. split; [lia|]. split; [exact Hi|]. apply (proj1 (DS q)). exact X. }
  assert (MOVE : nc_move sV L A sV L' A' [] []).
  { pose proof RMC' as (HM' & _).
    apply (mv_scan sV L A L' A' (map fst ds)).
    - pose proof (HNDB L A mem md HM) as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X].
    - pose proof (HNDB L' A' mem' md' HM') as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X].
    - intros q m Hq. exact (proj1 (mv_blk B API L A mem md q m HM Hq)).
    - intros [q m]. cbn [fst]. split; [intros X; exact (BK2 q m X)|intros [X1 X2]; exact (BK1 q m X1 X2)].
    - intros q Hq. apply (recs_nc i Hi). apply (proj1 (DS q)). exact Hq. }
  assert (NDn : List.NoDup (map fst (blocks L' A'))).
  { pose proof RMC' as (HM' & _). pose proof (HNDB L' A' mem' md' HM') as X.
    first [exact (proj1 (NoDup_ListNoDup _) X)|exact X]. }
  pose proof RMw as (_ & _ & _ & LYw & _).
  apply SR_ret. exists L', A', regs', mem', md', Hs'.
  split; [rewrite EC, R1; reflexivity|].
  split; [exact (rg_pres i (ss i) regs regs' PR RG)|].
  rewrite scnt_call.
  split; [exact RMC'|]. split; [exact INIT'|]. split; [exact RO'|].
  split; [exact (RIK L' A' qs QLEN QOK G (if slive then OUT' else sOUT) [] hj
                   (fun q m X => or_introl (proj1 (BK2 q m X))) eq_refl eq_refl (Nat.le_0_l 4)
                   ltac:(rewrite len_hj; exact sN_le) MOVE NDn
                   ltac:(intros p n n' H1 H2 H3; try intros _;
                         rewrite (CF.ListFrame.lf_addr A L L' p n HWF1 LYw H1); exact H3)
                   (scan_ncs (S i) L' A' mem' Hs' NDn BLK' SRCS' HSD') (Z.le_refl _))|].
  split; [exact ST'|]. split; [rewrite <- ACCV; exact ACC'|]. split; [exact GL'|]. split; [exact SRCS'|].
  split; [exact HSD'|]. split; [exact TAB'|]. split; [exact OBY''|]. exact BLK'.
Qed.

Lemma scan_iter : forall i jj c, (i < sN)%nat -> (jj < 4)%nat -> at_loop i jj c -> SR (ms_segs B) c (at_ret i jj).
Proof.
  intros i jj c Hi Hjj (L & A & regs & mem & md & Hs & -> & RG & SF).
  destruct (slot_cells _ _ _ _ _ _ i jj SF Hi Hjj) as (fd & o & SCs & FB & OB & IMP1 & IMP2).
  pose proof SF as (RMC & _ & RO & _ & (S1 & S2 & S3) & _).
  pose proof RMC as (HM & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  pose proof ac_facts as (A1 & A2 & A3 & A4 & A5). pose proof sN_le as NL4.
  destruct (pair_at i Hi) as (eI & HeI & EOi & _).
  assert (FIB : 0 <= nth i (map re_fd es) 0 < 2 ^ 31).
  { rewrite (fd_nth i eI HeI). destruct EOi as (_ & _ & _ & _ & X & _). exact X. }
  pose proof RG as (KP & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24).
  assert (SCn : rw_cells rsegs (normalize rsegs mem) (G_S + SRC_SIZE * Z.of_nat jj)
                  [C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 o)]).
  { rewrite HSEG in SCs. apply rw_cells_normalize; [exact RO'|exact SCs|].
    intros x Hx. cbn [cells_size csize] in Hx. apply hf_ro_glob. unfold G_S, SRC_SIZE. lia. }
  assert (FDn : rw_cells rsegs (normalize rsegs mem) (sb + 40 + 4 * Z.of_nat i)
                  [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]).
  { pose proof (S3 i Hi) as X. rewrite HSEG in X. apply rw_cells_normalize; [exact RO'|exact X|].
    intros x Hx. cbn [cells_size csize] in Hx. apply ro_addr_hi. lia. }
  rewrite HSEG.
  eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
  { unfold Regs6ss.mkR_of.
    eapply exit_scan_test with (b := sb) (HA := G_S + SRC_SIZE * Z.of_nat jj) (P8 := sb + 40 + 4 * Z.of_nat i)
      (fd := fd) (o := o) (fi := nth i (map re_fd es) 0).
    - transitivity (YK11.getr regs (Z_to_bv 5 2)); [reflexivity|exact (rg_sp regs KP)].
    - transitivity (YK11.getr regs (Z_to_bv 5 8)); [reflexivity|exact G8].
    - transitivity (YK11.getr regs (Z_to_bv 5 9)); [reflexivity|exact G9].
    - transitivity (YK11.getr regs (Z_to_bv 5 24)); [reflexivity|exact G24].
    - lia.
    - lia.
    - unfold G_S, SRC_SIZE. lia.
    - unfold G_S, SRC_SIZE. lia.
    - lia.
    - lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact FB.
    - exact OB.
    - exact FIB.
    - exact SCn.
    - exact FDn. }
  { intros s0 [(_ & _ & ->)|(_ & x10 & x11 & ->)]; do 3 eexists; reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR MREL ROS.
  assert (EM : m0' = normalize rsegs mem).
  { destruct HQ as [(_ & _ & EQ)|(_ & x10 & x11 & EQ)]; injection EQ as _ _ X; exact X. }
  subst m0'. pose proof (sf_nowrite _ _ _ _ _ _ m1 SF MREL ROS) as SF1.
  rewrite <- HSEG.
  destruct HQ as [(O & FD & EQ)|(SK & x10 & x11 & EQ)]; injection EQ as ER EP; subst R pc'.
  - pose proof (IMP1 O FD) as Hj. subst jj. rewrite (scnt_here i) in SF1.
    apply (scan_call i L A regs1 m1 md Hs Hi).
    + apply (rg_from i (ss i) regs regs1 RG). creg GR.
    + transitivity (YK11.getr regs1 (Z_to_bv 5 1)); [reflexivity|rewrite GR; reflexivity].
    + transitivity (YK11.getr regs1 (Z_to_bv 5 10)); [reflexivity|rewrite GR; reflexivity].
    + transitivity (YK11.getr regs1 (Z_to_bv 5 11)); [reflexivity|rewrite GR; reflexivity].
    + transitivity (YK11.getr regs1 (Z_to_bv 5 12)); [reflexivity|rewrite GR; reflexivity].
    + exact SF1.
  - assert (Hj : jj <> ss i).
    { intros X. destruct (IMP2 X) as [X1 X2]. destruct SK as [SK|SK]; [exact (X1 SK)|exact (SK X2)]. }
    apply SR_ret. exists L, A, regs1, m1, md, Hs. split; [reflexivity|].
    split; [apply (rg_from i jj regs regs1 RG); creg GR|].
    rewrite (scnt_skip i jj Hj). exact SF1.
Qed.

Lemma scan_next : forall i jj c, (i < sN)%nat -> (jj < 4)%nat -> at_ret i jj c ->
  SR (ms_segs B) c (fun c' => mid2_state c' \/ ((S jj < 4)%nat /\ at_loop i (S jj) c') \/
                              (jj = 3%nat /\ (S i < sN)%nat /\ at_loop (S i) 0 c')).
Proof.
  intros i jj c Hi Hjj (L & A & regs & mem & md & Hs & -> & RG & SF).
  pose proof SF as (RMC & _ & RO & _ & _ & ACC & _).
  pose proof RMC as (HM & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  pose proof ac_facts as (A1 & A2 & A3 & A4 & A5). pose proof sN_le as NL4.
  pose proof RG as (KP & G8 & G9 & G18 & G19 & G21 & G22 & G23 & G24).
  assert (ACn : rw_cells rsegs (normalize rsegs mem) (sb + 16) [C8 (Z_to_bv 64 (sacc (scnt i (S jj))))]).
  { pose proof ACC as X. rewrite HSEG in X. apply rw_cells_normalize; [exact RO'|exact X|].
    intros x Hx. cbn [cells_size csize] in Hx. apply ro_addr_hi. lia. }
  rewrite HSEG.
  eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
  { unfold Regs6ss.mkR_of.
    eapply exit_scan_next with (b := sb) (HA := G_S + SRC_SIZE * Z.of_nat jj) (i := Z.of_nat i) (N := Z.of_nat sN)
      (acc := Z_to_bv 64 (sacc (scnt i (S jj)))).
    - transitivity (YK11.getr regs (Z_to_bv 5 2)); [reflexivity|exact (rg_sp regs KP)].
    - transitivity (YK11.getr regs (Z_to_bv 5 9)); [reflexivity|exact G9].
    - transitivity (YK11.getr regs (Z_to_bv 5 18)); [reflexivity|exact G18].
    - transitivity (YK11.getr regs (Z_to_bv 5 19)); [reflexivity|exact G19].
    - transitivity (YK11.getr regs (Z_to_bv 5 21)); [reflexivity|exact G21].
    - transitivity (YK11.getr regs (Z_to_bv 5 22)); [reflexivity|exact G22].
    - transitivity (YK11.getr regs (Z_to_bv 5 23)); [reflexivity|exact G23].
    - lia.
    - lia.
    - unfold G_S, SRC_SIZE. lia.
    - unfold G_S, SRC_SIZE. lia.
    - lia.
    - lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact ACn. }
  { intros s0 [(_ & ->)|[(_ & _ & ->)|(_ & _ & ->)]]; do 3 eexists; reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR MREL ROS.
  assert (EM : m0' = normalize rsegs mem).
  { destruct HQ as [(_ & EQ)|[(_ & _ & EQ)|(_ & _ & EQ)]]; injection EQ as _ _ X; exact X. }
  subst m0'. pose proof (sf_nowrite _ _ _ _ _ _ m1 SF MREL ROS) as SF1.
  rewrite <- HSEG. apply SR_ret.
  destruct HQ as [(Q1 & EQ)|[(Q1 & Q2 & EQ)|(Q1 & Q2 & EQ)]]; injection EQ as ER EP; subst R pc'.
  - right. left. split; [unfold G_S, SRC_SIZE in Q1; lia|].
    exists L, A, regs1, m1, md, Hs. split; [reflexivity|]. split; [|exact SF1].
    split; [kreg GR KP|].
    split; [rewrite GR; exact G8|].
    split; [rewrite GR; transitivity (Z_to_bv 64 (G_S + SRC_SIZE * Z.of_nat jj + 96)); [reflexivity|f_equal; unfold SRC_SIZE; lia]|].
    split; [rewrite GR; exact G18|]. split; [rewrite GR; exact G19|]. split; [rewrite GR; exact G21|].
    split; [rewrite GR; exact G22|]. split; [rewrite GR; exact G23|]. rewrite GR; exact G24.
  - assert (J3 : jj = 3%nat) by (unfold G_S, SRC_SIZE in Q1; lia). subst jj.
    right. right. split; [reflexivity|]. split; [lia|].
    destruct (scnt_wrap i Hi) as [W1 W2].
    exists L, A, regs1, m1, md, Hs. split; [reflexivity|]. split; [|rewrite W2; rewrite W1 in SF1; exact SF1].
    split; [kreg GR KP|].
    split; [rewrite GR; exact G8|].
    split; [rewrite GR; reflexivity|].
    split; [rewrite GR; transitivity (Z_to_bv 64 (Z.of_nat i + 1)); [reflexivity|f_equal; lia]|].
    split; [rewrite GR; exact G19|]. split; [rewrite GR; exact G21|].
    split; [rewrite GR; exact G22|]. split; [rewrite GR; exact G23|].
    rewrite GR; transitivity (Z_to_bv 64 (sb + 40 + 4 * (Z.of_nat i + 1))); [reflexivity|f_equal; lia].
  - assert (J3 : jj = 3%nat) by (unfold G_S, SRC_SIZE in Q1; lia). subst jj.
    destruct (scnt_wrap i Hi) as [W1 _]. rewrite W1 in SF1.
    assert (NS : S i = sN) by lia.
    left. exists L, A, regs1, m1, md, Hs. split; [reflexivity|].
    split; [rewrite GR; transitivity (Z_to_bv 64 (sacc (scnt i 4))); [reflexivity|rewrite W1, NS; reflexivity]|].
    split; [kreg GR KP|]. rewrite <- NS. exact SF1.
Qed.

Lemma scan_loop : forall i jj c, (i < sN)%nat -> (jj < 4)%nat -> at_loop i jj c -> SR (ms_segs B) c mid2_state.
Proof.
  intros i jj c Hi Hjj HL.
  refine (SR_loop (ms_segs B) (nat * nat) (fun w => (4 * sN - (4 * fst w + snd w))%nat)
            (fun w c => (fst w < sN)%nat /\ (snd w < 4)%nat /\ at_loop (fst w) (snd w) c) mid2_state _ (i, jj) c
            (conj Hi (conj Hjj HL))).
  intros [i' jj'] c' (Hi' & Hjj' & HL'). cbn [fst snd] in *.
  eapply SR_bind; [exact (scan_iter i' jj' c' Hi' Hjj' HL')|].
  intros c1 H1. eapply SR_mono; [exact (scan_next i' jj' c1 Hi' Hjj' H1)|].
  intros c2 [H2|[(H3 & H2)|(H3 & H4 & H2)]].
  - left. exact H2.
  - right. exists (i', S jj'). cbn [fst snd]. split; [lia|]. split; [exact Hi'|]. split; [exact H3|exact H2].
  - right. exists (S i', 0%nat). cbn [fst snd]. split; [lia|]. split; [exact H4|]. split; [lia|exact H2].
Qed.

Lemma scan_start : forall c, mid1_state c -> SR (ms_segs B) c mid2_state.
Proof.
  intros c (L & A & regs & mem & md & -> & M1).
  pose proof (mid1_sf L A regs mem md M1) as SF.
  pose proof M1 as (RM & _ & RO & KEEP & R8 & _).
  pose proof RM as (HM & _).
  destruct (mr_model _ _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (RO' : ro_agree rsegs mem) by (rewrite <- HSEG; exact RO).
  pose proof ac_facts as (A1 & A2 & A3 & A4 & A5). pose proof sN_le as NL4.
  assert (KP : rg_keep regs) by (intros r Hr; apply KEEP; [unfold callee_saved; lia|lia]).
  destruct (Nat.eq_dec sN 0) as [N0|N0].
  - assert (PC : (Z.of_nat (length es) =? 0) = true) by (unfold sN in N0; rewrite N0; reflexivity). rewrite PC.
    rewrite HSEG. eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
    { unfold Regs6ss.mkR_of. apply exit_zero_next. }
    { intros s0 ->. do 3 eexists. reflexivity. }
    intros R pc' m0' regs1 m1 HQ GR MREL ROS. injection HQ as ER EP EM. subst R pc' m0'.
    pose proof (sf_nowrite _ _ _ _ _ _ m1 SF MREL ROS) as SF1.
    rewrite <- HSEG. apply SR_ret. exists L, A, regs1, m1, md, (fun _ => hl0). split; [reflexivity|].
    split; [rewrite GR; unfold sacc; rewrite N0; destruct (gn =? 0); reflexivity|].
    split; [kreg GR KP|]. rewrite N0. exact SF1.
  - assert (PC : (Z.of_nat (length es) =? 0) = false) by (apply Z.eqb_neq; unfold sN in N0; lia). rewrite PC.
    rewrite HSEG. eapply kseg; [exact wx_apart_rsegs|exact RO'|exact Hh|exact Hl| | |].
    { unfold Regs6ss.mkR_of. eapply exit_scan_init with (b := sb) (N := Z.of_nat sN).
      - transitivity (YK11.getr regs (Z_to_bv 5 2)); [reflexivity|exact (rg_sp regs KP)].
      - transitivity (YK11.getr regs (Z_to_bv 5 8)); [reflexivity|exact (R8 ltac:(unfold sN in N0; lia))].
      - transitivity (YK11.getr regs (Z_to_bv 5 20)); [reflexivity|exact (rg_s4 regs KP)].
      - lia.
      - lia.
      - unfold sN in *. lia. }
    { intros s0 ->. do 3 eexists. reflexivity. }
    intros R pc' m0' regs1 m1 HQ GR MREL ROS. injection HQ as ER EP EM. subst R pc' m0'.
    pose proof (sf_nowrite _ _ _ _ _ _ m1 SF MREL ROS) as SF1.
    rewrite <- HSEG. apply (scan_loop 0 0 _ ltac:(lia) ltac:(lia)).
    exists L, A, regs1, m1, md, (fun _ => hl0). split; [reflexivity|]. split; [|rewrite scnt_zero; exact SF1].
    split; [kreg GR KP|].
    split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    split; [rewrite GR; reflexivity|]. rewrite GR. transitivity (Z_to_bv 64 (sb + 40)); [reflexivity|f_equal; lia].
Qed.

Lemma scan_main : forall c, mid1_state c -> SR (ms_segs B) c (exit_mid2 (rc := rc) B API E RI t k).
Proof. intros c H. eapply SR_mono; [exact (scan_start c H)|exact pack]. Qed.

End Scan.

Theorem exit_scan : forall CS RI (F : ResFormT),
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @check_shape_ends_contract fx rc B (API rc) F) ->
  exit_res_ends_s F RI CS ->
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall t k c,
      exit_mid1 (rc := rc) B (API rc) E RI t k c ->
      SR (ms_segs B) c (exit_mid2 (rc := rc) B (API rc) E RI t k).
Proof.
  intros CS RI F HCF HRES B API LS SH SK ra empty rc fx j E HF t k c HM1.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (FG : forall a, in_globals frame_G a -> img_plain B a)
    by (unfold frame_facts, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (EA : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  assert (PLG : forall a, 0x318a0 <= a < 0x31aa0 \/ 0x21620 <= a < 0x21630 -> img_plain B a).
  { intros a [Ha|Ha]; apply FG.
    - apply in_G_bss. lia.
    - exists 0x21620, 16. split; [left; reflexivity|lia]. }
  destruct (proj1 (proj1 PRE)) as (MRE & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TPE & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (HB1 : @YM05.alloc_ceiling rc + 65000 <= slot_sp E) by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (HB2 : slot_sp E + 192 < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME in *; lia).
  assert (HB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HB4 : spZ (ss_regs E) = slot_sp E + 192) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (HSL : @YM05.alloc_ceiling rc <= spZ (ss_regs E) - SLOT_STACK) by lia.
  assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  pose proof (HRES B API LS SH SK ra empty rc fx j E HF) as HRES'.
  destruct HM1 as (fx' & L0 & A0 & regs0 & m0 & md0 & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es &
    hj & tail & L & A & regs & mem & md & OUT' & CAP' & junk' & HM1).
  cbv zeta in HM1. destruct HM1 as (Hc & FZ & EXS & TB & REST).
  pose proof (HCF B API LS SH SK ra empty rc fx' FF) as HCSE.
  assert (HLIVE : send_live cl br dd (entries_total es) = true ->
    entries_total es <= CAP' /\
    CAP' = relay_finish_cap (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es /\
    CAP' <= Z.max (bv_unsigned cap) (2 * entries_total es) /\ fresh_block B OUT' CAP' /\
    (forall q m, In (q, m) (blocks L0 A0) -> q <> bv_unsigned out -> ~ In q (concat (map entry_blocks es)) ->
       0 < m -> q <> OUT') /\
    Z.of_nat (length junk') = CAP' - entries_total es).
  { intros HL.
    pose proof REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & YL & _).
    destruct (YL HL) as (Y1 & Y2 & Y3 & Y4 & Y5 & _ & Y7 & _).
    exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 (conj Y5 Y7))))). }
  eapply (@scan_main rc fx' B (API rc) F E RI t k L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out es hj tail
            OUT' CAP' junk'); try eassumption.
  unfold mid1_state. exists L, A, regs, mem, md. split; [exact Hc|exact REST].
Qed.
