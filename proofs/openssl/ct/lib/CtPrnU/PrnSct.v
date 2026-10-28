(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg PrintfModel PrintfModelX CtSizes CtWire.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string W_sct_print_nv1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma Z_to_le_bytes_split : forall a b z, Z_to_le_bytes (a + b) z = Z_to_le_bytes a z ++ Z_to_le_bytes b (Z.shiftr z (8 * Z.of_nat a)).
Proof.
  induction a as [|a IH]; intros b z.
  - cbn [Nat.add app]. replace (8 * Z.of_nat 0) with 0 by std_lia__. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes Nat.add app]. f_equal. rewrite IH. f_equal. rewrite Z.shiftr_shiftr by std_lia__. replace (8 * Z.of_nat (S a)) with (8 + 8 * Z.of_nat a) by std_lia__. reflexivity.
Qed.

Lemma le8_small_split : forall n, 0 <= n < 2^32 -> le8 (wz n) = le4 (wz n) ++ le4 (wz 0).
Proof.
  intros n Hn. unfold le8, le4, word_to_le_bytes, MallocRep.wz. rewrite !unsigned_lit by lia.
  rewrite (Z_to_le_bytes_split 4 4 n : Z_to_le_bytes 8 n = _). f_equal. f_equal.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 4)) with (2^32). rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma le4_u32 : forall z, le4 (wz (u32 z)) = le4 (wz z).
Proof.
  intros z. unfold le4, u32, MallocRep.wz. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite <- (Z_to_le_bytes_mod 4 ((z mod 2^32) mod 2^64) 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (z mod 2^64) 32) by (cbn; lia).
  f_equal. rewrite (Z.mod_small (z mod 2^32) (2^64)) by (pose proof (Z.mod_pos_bound z (2^32)); lia).
  rewrite Z.mod_mod by lia. symmetry. apply Z.mod_mod_divide. exists (2^32). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rw_C8_as_C4C4 : forall m A pre n post,
  0 <= n < 2^32 -> rw_cells ctusegs m A (pre ++ C8 (wz n) :: post) -> rw_cells ctusegs m A (pre ++ C4 (wz n) :: C4 (wz 0) :: post).
Proof.
  intros m A pre n post Hn H. eapply Lib_kit.rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app' in W. destruct W as [W1 W2]. cbn in W2. apply cells_wf_app'. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes app]. rewrite (le8_small_split n Hn). rewrite <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rw_C4_u32 : forall m A v post,
  rw_cells ctusegs m A (C4 (wz (u32 v)) :: post) -> rw_cells ctusegs m A (C4 (wz v) :: post).
Proof.
  intros m A v post H. eapply Lib_kit.rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. cbn in W |- *. exact W.
  - cbn [cells_bytes cbytes app]. rewrite le4_u32. reflexivity.
  - reflexivity.
Qed.

Lemma ro_of_rw : forall m A cs, rw_cells ctusegs m A cs -> ro_cells ctusegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma arr_bytes : forall s OW LB m adr q n,
  RHEAP s (OW ++ LB) m -> arr_rep m OW adr (Some (q, n)) ->
  exists bs, bytes_at ctusegs m (adr q) bs /\ Z.of_nat (length bs) = n /\ 0 < n /\ rblock_range (adr q) n.
Proof.
  intros s OW LB m adr q n HEAP (Hn & HIN & bs & HB).
  exists bs. pose proof HB as [[W B] _]. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. cbn in W.
  split; [exact B|]. split; [destruct W as [W _]; rewrite W; lia|]. split; [exact Hn|]. exact (RH_range _ _ _ _ _ _ _ HEAP HIN).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sct_nv1_of_rep : forall s OW LB m adr x (pbio : bptr) (out : Z),
  RHEAP s (OW ++ LB) m -> sct_rep m OW adr x -> sc_version x <> 0 ->
  In (pbio, out, BIO_SIZE) OW -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
  let A := adr (sc_blk x) in let SB := optr adr (sc_blob x) in let sbn := sc_bloblen x in
  (0 < A /\ A + 104 <= alloc_ceiling /\ (A + 104 <= out \/ out + 128 <= A)) /\ A mod 16 = 0
  /\ (-2^31 <= sc_version x < 2^31 /\ sc_version x <> 0)
  /\ sct_nv1_cells A (sc_version x) SB sbn m
  /\ 0 <= SB < 2^64 /\ 0 <= sbn < 2^31
  /\ exists sbs, Z.of_nat (length sbs) = sbn /\ (0 < sbn -> bytes_at ctusegs m SB sbs)
       /\ (0 < sbn -> 0 < SB /\ SB + sbn <= alloc_ceiling /\ (SB + sbn <= out \/ out + 128 <= SB)).
Proof.
  intros s OW LB m adr x pbio out HEAP REP NV HBIO HID. cbn zeta.
  destruct REP as (HIN & CELLS & AL & AE & AS & AB & ND & RV & RH & RSA & RTS & REL & LE & LS & LB0).
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HIN) as RR. unfold rblock_range, SCT_SIZE in RR.
  assert (NE : pbio <> sc_blk x).
  { intros E. apply HID. rewrite E. apply in_map_iff. exists (sc_blk x, adr (sc_blk x), SCT_SIZE). split; [reflexivity|].
    unfold sct_blocks. do 4 (apply in_or_app; right). left. reflexivity. }
  pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HBIO HIN NE) as DJ. unfold BIO_SIZE, SCT_SIZE in DJ.
  split; [lia|]. split; [lia|]. split; [lia|].
  (* [comment removed for export] *)
  unfold sct_cells in CELLS.
  assert (BL : 0 <= sc_bloblen x < 2^31) by (rewrite sc_bloblen_olen; unfold MAX_SCT_SIZE in *; unfold olen in *; destruct (sc_blob x) as [[q n]|]; cbn in *; [destruct AB as (Hn & _); lia| lia]).
  split.
  { split.
    - apply ro_of_rw. lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?rest) =>
        pose proof (proj1 (proj1 (rw_cells_app m _ [c0] rest) CELLS)) as V end.
      apply (rw_C4_u32 m _ (sc_version x) []). exact V.
    - apply ro_of_rw. lazymatch type of CELLS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
        pose proof (proj2 (proj1 (rw_cells_app m _ [c0; c1] (c2 :: c3 :: rest)) CELLS)) as V;
        pose proof (proj1 (proj1 (rw_cells_app m _ [c2; c3] rest) V)) as V2 end.
      cbn [cells_size csize Nat.add] in V2. replace (adr (sc_blk x) + Z.of_nat 8) with (adr (sc_blk x) + 8) in V2 by lia.
      pose proof (rw_C8_as_C4C4 m _ [C8 (wz (optr adr (sc_blob x)))] (sc_bloblen x) [] ltac:(lia) V2) as V3. cbn [app] in V3.
      exact (proj1 (proj1 (rw_cells_app m _ [C8 (wz (optr adr (sc_blob x))); C4 (wz (sc_bloblen x))] [C4 (wz 0)]) V3)). }
  (* [comment removed for export] *)
  destruct (sc_blob x) as [[q n]|] eqn:EB; cbn [optr].
  - destruct (arr_bytes _ _ _ _ _ _ _ HEAP AB) as (bs & BY & LEN & Hn & RB). unfold rblock_range in RB.
    assert (NEq : pbio <> q).
    { intros E. apply HID. rewrite E. apply in_map_iff. exists (q, adr q, n). split; [reflexivity|].
      unfold sct_blocks. do 3 (apply in_or_app; right). apply in_or_app; left. rewrite EB. cbn [oblk]. left. reflexivity. }
    destruct AB as (_ & HINq & _).
    pose proof (RH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HBIO HINq NEq) as DJq. unfold BIO_SIZE in DJq.
    replace (sc_bloblen x) with n in * by (unfold sc_bloblen; rewrite EB; reflexivity).
    split; [lia|]. split; [lia|]. exists bs. split; [exact LEN|]. split; [intros _; exact BY|]. intros _. lia.
  - replace (sc_bloblen x) with 0 in * by (unfold sc_bloblen; rewrite EB; reflexivity). split; [lia|]. split; [lia|]. exists []. split; [reflexivity|]. split; [intros H; exfalso; lia|]. intros H; exfalso; lia.
Qed.
(* [comment removed for export] *)
Theorem SCT_print_nv1_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (OW LB : list block) (adr : bptr -> Z) (x : sctr bptr) (pbio : bptr)
    (out pv nw lo : Z) (canary : word),
  RHEAP s (OW ++ LB) m -> sct_rep m OW adr x -> sc_version x <> 0 ->
  In (pbio, out, BIO_SIZE) OW -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SCT_PRINT_NV1_STACK ->
  bv_unsigned sp < 2^63 -> bv_unsigned sp mod 16 = 0 -> ssp_cells m canary -> frm0 fc ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 -> null_meth_cells m ->
  a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
  evt ctusegs (hexstring_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo out pv canary m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz SCT_PRINT) fc None m (seg_rom ctusegs)).
Proof.
  intros until canary. intros HEAP REP NV HBIO HID ST MI GLO CEIL LO SP63 SP16 SSP FRM HB NW NM -> -> -> ->.
  unfold SCT_PRINT_NV1_STACK, HX_STACK, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (RH_range _ _ _ _ _ _ _ HEAP HBIO) as OBR. unfold rblock_range, BIO_SIZE in OBR.
  destruct (sct_nv1_of_rep _ _ _ _ _ _ _ _ HEAP REP NV HBIO HID) as (HA & AA16 & HVER & CELLS & SBW & SBN0 & sbs & LEN & HS & SBR).
  eapply (sct_print_nv1 sp gp tp F m lo out pv canary (adr (sc_blk x)) (sc_version x) (optr adr (sc_blob x)) (sc_bloblen x) sbs);
    [lia| lia| lia| exact SP16| lia| clear - OBR; Z.div_mod_to_equations; lia| lia| clear - AA16; Z.div_mod_to_equations; lia
    | exact HVER| split; [exact LEN| lia]| intros Hn; pose proof (SBR Hn); lia| exact SBW
    | exact ST| exact MI| exact SSP| exact FRM| exact HB| exact NW| exact NM| exact HS| exact CELLS].
Qed.
End WithCeiling0.
