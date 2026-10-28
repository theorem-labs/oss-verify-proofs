(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnSct W_sct_print_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma arr_facts : forall s L m adr o (pbio : bptr) out,
  RHEAP s L m -> arr_rep m L adr o -> In (pbio, out, BIO_SIZE) L ->
  (forall q n, o = Some (q, n) -> q <> pbio) -> olen o <= MAX_SCT_SIZE ->
  exists bs, Z.of_nat (length bs) = olen o /\ 0 <= olen o < 2^31
    /\ frozen (0 < olen o -> bytes_at ctusegs m (optr adr o) bs)
    /\ frozen (0 < olen o -> 0 < optr adr o /\ optr adr o + olen o <= alloc_ceiling /\ (optr adr o + olen o <= out \/ out + 128 <= optr adr o))
    /\ 0 <= optr adr o < 2^64.
Proof.
  intros s L m adr [[q n]|] pbio out HEAP AR HBIN NE OL; cbn [olen optr] in *.
  - destruct AR as (Hn & HIN & bs & HB). exists bs.
    pose proof HB as [[W B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn in W. destruct W as [W _].
    pose proof (blk_bounds _ _ _ _ _ _ HEAP HIN) as (B1 & B2 & B3 & B4 & B5).
    pose proof (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP HIN HBIN (NE q n eq_refl)) as DJ. unfold BIO_SIZE, MAX_SCT_SIZE in *.
    split; [rewrite W; lia|]. split; [lia|]. split; [intros _; exact B|]. split; [intros _; lia|]. lia.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [intros H; exfalso; lia|]. split; [intros H; exfalso; lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma sct_v1_of_rep : forall s L m adr x (pbio : bptr) out,
  RHEAP s L m -> sct_rep m L adr x -> sc_version x = 0 ->
  In (pbio, out, BIO_SIZE) L -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
  let A := adr (sc_blk x) in
  let LI := optr adr (osz32 (sc_logid x)) in let lin := logid_len (sc_logid x) in
  let EX := optr adr (sc_ext x) in let exn := sc_extlen x in
  let SG := optr adr (sc_sig x) in let sgn := sc_siglen x in
  (0 < A /\ A + 104 <= alloc_ceiling /\ (A + 104 <= out \/ out + 128 <= A))
  /\ sct_v1_cells A LI lin (sc_ts x) EX exn (sc_hash x) (sc_sigalg x) SG sgn m
  /\ (0 <= LI < 2^64 /\ 0 <= EX < 2^64 /\ 0 <= SG < 2^64 /\ 0 <= sc_ts x < 2^64 /\ 0 <= sc_hash x < 256 /\ 0 <= sc_sigalg x < 256)
  /\ sig_nid 0 (sc_hash x) (sc_sigalg x) <> NID_undef
  /\ (exists lib, Z.of_nat (length lib) = lin /\ 0 <= lin < 2^31 /\ frozen (0 < lin -> bytes_at ctusegs m LI lib)
        /\ frozen (0 < lin -> 0 < LI /\ LI + lin <= alloc_ceiling /\ (LI + lin <= out \/ out + 128 <= LI)))
  /\ (exists exb, Z.of_nat (length exb) = exn /\ 0 <= exn < 2^31 /\ frozen (0 < exn -> bytes_at ctusegs m EX exb)
        /\ frozen (0 < exn -> 0 < EX /\ EX + exn <= alloc_ceiling /\ (EX + exn <= out \/ out + 128 <= EX)))
  /\ (exists sgb, Z.of_nat (length sgb) = sgn /\ 0 <= sgn < 2^31 /\ frozen (0 < sgn -> bytes_at ctusegs m SG sgb)
        /\ frozen (0 < sgn -> 0 < SG /\ SG + sgn <= alloc_ceiling /\ (SG + sgn <= out \/ out + 128 <= SG))).
Proof.
  intros s L m adr x pbio out HEAP REP V0 HBIN HID. cbn zeta.
  destruct REP as (HIN & CELLS & AL & AE & AS & AB & ND & RV & NID & RH & RSA & RTS & REL & LE & LS & LB0).
  pose proof (blk_bounds _ _ _ _ _ _ HEAP HIN) as (B1 & B2 & B3 & B4 & B5). unfold SCT_SIZE in *.
  assert (NE : sc_blk x <> pbio).
  { intros E. apply HID. rewrite <- E. apply in_map_iff. exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [reflexivity|].
    unfold sct_blocks. do 4 (apply in_or_app; right). left. reflexivity. }
  pose proof (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP HIN HBIN NE) as DJ. unfold BIO_SIZE in DJ.
  split; [lia|].
  (* [comment removed for export] *)
  assert (NEL : forall q n, osz32 (sc_logid x) = Some (q, n) -> q <> pbio).
  { intros q n Hq ->. apply HID. apply in_map_iff. exists (pbio, adr pbio, n). split; [reflexivity|]. unfold sct_blocks. rewrite Hq. cbn. left. reflexivity. }
  assert (NEE : forall q n, sc_ext x = Some (q, n) -> q <> pbio).
  { intros q n Hq ->. apply HID. apply in_map_iff. exists (pbio, adr pbio, n). split; [reflexivity|]. unfold sct_blocks. rewrite Hq. rewrite !in_app_iff. cbn. tauto. }
  assert (NES : forall q n, sc_sig x = Some (q, n) -> q <> pbio).
  { intros q n Hq ->. apply HID. apply in_map_iff. exists (pbio, adr pbio, n). split; [reflexivity|]. unfold sct_blocks. rewrite Hq. rewrite !in_app_iff. cbn. tauto. }
  assert (OLL : olen (osz32 (sc_logid x)) = logid_len (sc_logid x)) by (destruct (sc_logid x); reflexivity).
  assert (OLL' : olen (osz32 (sc_logid x)) <= MAX_SCT_SIZE) by (unfold MAX_SCT_SIZE; destruct (sc_logid x); cbn; lia).
  destruct (arr_facts _ _ _ _ _ _ _ HEAP AL HBIN NEL OLL') as (lib & L1 & L2 & L3 & L4 & L5). rewrite OLL in *.
  destruct (arr_facts _ _ _ _ _ _ _ HEAP AE HBIN NEE LE) as (exb & E1 & E2 & E3 & E4 & E5).
  destruct (arr_facts _ _ _ _ _ _ _ HEAP AS HBIN NES LS) as (sgb & S1 & S2 & S3 & S4 & S5).
  rewrite <- sc_siglen_olen in *. rewrite <- REL in *.
  split.
  { (* [comment removed for export] *)
    unfold sct_cells in CELLS. rewrite V0 in CELLS. change (u32 0) with 0 in CELLS.
    unfold sct_v1_cells.
    lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?rest) =>
      pose proof (proj1 (proj1 (rw_cells_app m _ [c0] (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: rest)) CELLS)) as X0;
      pose proof (proj2 (proj1 (rw_cells_app m _ [c0; c1; c2; c3] (c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: rest)) CELLS)) as X1;
      pose proof (proj1 (proj1 (rw_cells_app m _ [c4; c5] (c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: rest)) X1)) as X24;
      pose proof (proj2 (proj1 (rw_cells_app m _ [c4; c5] (c6 :: c7 :: c8 :: c9 :: c10 :: c11 :: c12 :: c13 :: rest)) X1)) as X2;
      pose proof (proj1 (proj1 (rw_cells_app m _ [c6; c7; c8] (c9 :: c10 :: c11 :: c12 :: c13 :: rest)) X2)) as X40;
      pose proof (proj2 (proj1 (rw_cells_app m _ [c6; c7; c8] (c9 :: c10 :: c11 :: c12 :: c13 :: rest)) X2)) as X3;
      pose proof (proj1 (proj1 (rw_cells_app m _ [c9; c10] (c11 :: c12 :: c13 :: rest)) X3)) as X64;
      pose proof (proj2 (proj1 (rw_cells_app m _ [c9; c10; c11] (c12 :: c13 :: rest)) X3)) as X4;
      pose proof (proj1 (proj1 (rw_cells_app m _ [c12; c13] rest) X4)) as X72
    end.
    cbn [cells_size csize Nat.add] in X1, X24, X2, X40, X3, X64, X4, X72.
    replace (adr (sc_blk x) + Z.of_nat 24) with (adr (sc_blk x) + 24) in X24 by lia.
    replace (adr (sc_blk x) + Z.of_nat 24 + Z.of_nat 16) with (adr (sc_blk x) + 40) in X40 by lia.
    replace (adr (sc_blk x) + Z.of_nat 24 + Z.of_nat 16 + Z.of_nat 24) with (adr (sc_blk x) + 64) in X64 by lia.
    replace (adr (sc_blk x) + Z.of_nat 24 + Z.of_nat 16 + Z.of_nat 24 + Z.of_nat 8) with (adr (sc_blk x) + 72) in X72 by lia.
    split; [apply ro_of_rw; unfold MallocRep.wz in X0 |- *; exact X0|].
    split.
    { apply ro_of_rw. pose proof (rw_C8_as_C4C4 m _ [C8 (wz (optr adr (osz32 (sc_logid x))))] (logid_len (sc_logid x)) [] ltac:(lia) X24) as Y. cbn [app] in Y.
      unfold MallocRep.wz in Y |- *. exact (proj1 (proj1 (rw_cells_app m _ [C8 (Z_to_bv 64 (optr adr (osz32 (sc_logid x)))); C4 (Z_to_bv 64 (logid_len (sc_logid x)))] [C4 (Z_to_bv 64 0)]) Y)). }
    split; [apply ro_of_rw; unfold MallocRep.wz in X40 |- *; exact X40|].
    split; [apply ro_of_rw; exact X64|].
    apply ro_of_rw. pose proof (rw_C8_as_C4C4 m _ [C8 (wz (optr adr (sc_sig x)))] (sc_siglen x) [] ltac:(lia) X72) as Y. cbn [app] in Y.
    unfold MallocRep.wz in Y |- *. exact (proj1 (proj1 (rw_cells_app m _ [C8 (Z_to_bv 64 (optr adr (sc_sig x))); C4 (Z_to_bv 64 (sc_siglen x))] [C4 (Z_to_bv 64 0)]) Y)). }
  split; [lia|].
  split; [unfold sct_nid in NID; rewrite V0 in NID; exact (NID eq_refl)|].
  split; [exists lib; auto|]. split; [exists exb; auto|]. exists sgb; auto.
Qed.

(* [comment removed for export] *)
Lemma sct_rep_munch : forall s L m m' adr x (pbio : bptr) out lo q,
  RHEAP s L m -> sct_rep m L adr x -> In (pbio, out, BIO_SIZE) L -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
  alloc_ceiling <= lo ->
  munch [(lo, q); (out, out + 128)] m m' -> wmono ctusegs m m' -> sct_rep m' L adr x.
Proof.
  intros s L m m' adr x pbio out lo q HEAP REP HBIN HID CEIL MU WM.
  eapply (sct_rep_pres m m' L (sct_blocks adr x) (2^64)); [| intros b Hb; exact Hb| exact REP].
  eapply heap_pres_of_munch; [exact MU| exact WM|].
  intros a Ha Hc. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| |].
  - pose proof (blk_bounds _ _ _ _ _ _ HEAP HBIN). unfold BIO_SIZE in *. cbn. lia.
  - destruct b as [[qb A] n]. cbn [blk_addr blk_size fst snd] in Hr.
    pose proof (sct_rep_blocks_in _ _ _ _ REP _ Hb) as HbL.
    pose proof (blk_bounds _ _ _ _ _ _ HEAP HbL) as (B1 & B2 & B3 & B4 & B5).
    assert (NE : qb <> pbio) by (intros ->; apply HID; apply in_map_iff; exists (pbio, A, n); split; [reflexivity| exact Hb]).
    pose proof (blk_disjoint _ _ _ _ _ _ _ _ _ HEAP HbL HBIN NE) as DJ. unfold BIO_SIZE in *. cbn. lia.
Qed.

End WithCeiling0.
