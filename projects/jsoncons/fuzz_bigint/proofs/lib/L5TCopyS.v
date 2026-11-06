(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Ref Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import StoreOk TMemcpy L5Defs L5TStrS.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Module TCS.
Import TSS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition COPY : Z := 0x21b98.
Definition COPYA : Z := 0x22848.
Definition ACOPY : Z := 0x21be8.
Definition OPNEW : Z := 0x5a0b0.
Definition MEMCPY : Z := 0x58924.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.

Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | MG : mem_grows ?mq m |- _ => apply (mem_grows_write' mq m (wa a) bs) in MG
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* [comment removed for export] *)
Definition cfb (fbo fb' : Z) (dyn : bool) : Z := Z.lor (Z.lor (Z.land fbo 252) (if dyn then 1 else 0)) (Z.land fb' 2).

(* [comment removed for export] *)
Definition wci_stmt (pc : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (o o' fbo fb' : Z) (lenw v0w v1w : word) (junkO : list byte),
  0x91000 <= o -> o + 32 <= 2^47 -> 0 <= o' -> o' + 32 <= 2^47 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  0 <= fbo < 256 -> 0 <= fb' < 256 -> Z.testbit fb' 0 = false ->
  rw_cells rsegs m o [C1 (b8 fbo); CB 31 junkO] ->
  ro_cells rsegs m o' [C1 (b8 fb')] -> ro_cells rsegs m (o' + 8) [C8 lenw] -> ro_cells rsegs m (o' + 16) [C8 v0w] -> ro_cells rsegs m (o' + 24) [C8 v1w] ->
  evt rsegs (fun ms' => exists a1' a2' a3' m' j7,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' o [C1 (b8 (cfb fbo fb' false)); CB 7 j7; C8 lenw; C8 v0w; C8 v1w]
      /\ munch [(o, o + 32)] m m' /\ wmono rsegs m m' /\ mem_grows m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 o') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma land1_bit0 : forall fb, 0 <= fb -> Z.land fb 1 = (if Z.testbit fb 0 then 1 else 0).
Proof.
  intros fb Hfb. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.bit0_odd. rewrite Zmod_odd. destruct (Z.odd fb); reflexivity.
Qed.

Lemma wci : wci_stmt COPY.
Proof.
  unfold wci_stmt, COPY. intros until junkO. intros OLO OHI O0' OHI' SEP FBO FB' TB OB YB YL Y0 Y1.
  pose proof (munch_refl [(o, o + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (mem_grows_refl m) as MG.
  st1. st1. rewrite (land1_bit0 fb' ltac:(lia)), TB. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. rewrite le1_wz. mem_after_store.
  st1. st1. st1. st1. st1. rewrite le1_wz. mem_after_store.
  do 7 st1.
  pose proof (zr_land_l fb' 2 ltac:(unfold inr64; lia) ltac:(lia)) as R1. pose proof (zr_land_l fbo 252 ltac:(unfold inr64; lia) ltac:(lia)) as R2. unfold inr64 in R1, R2.
  repeat match goal with H : rw_cells _ _ o _ |- _ => rewrite !unsigned_lit in H by lia end.
  replace (Z.lor (Z.land fb' 2) (Z.land fbo 252)) with (cfb fbo fb' false) in * by (unfold cfb; rewrite Z.lor_0_r; apply Z.lor_comm).
  finish. all: eassumption.
Qed.
Lemma wcia : wci_stmt COPYA.
Proof.
  unfold wci_stmt, COPYA. intros until junkO. intros OLO OHI O0' OHI' SEP FBO FB' TB OB YB YL Y0 Y1.
  pose proof (munch_refl [(o, o + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (mem_grows_refl m) as MG.
  st1. st1. rewrite (land1_bit0 fb' ltac:(lia)), TB. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. st1. rewrite le1_wz. mem_after_store.
  st1. st1. st1. st1. st1. rewrite le1_wz. mem_after_store.
  do 7 st1.
  pose proof (zr_land_l fb' 2 ltac:(unfold inr64; lia) ltac:(lia)) as R1. pose proof (zr_land_l fbo 252 ltac:(unfold inr64; lia) ltac:(lia)) as R2. unfold inr64 in R1, R2.
  repeat match goal with H : rw_cells _ _ o _ |- _ => rewrite !unsigned_lit in H by lia end.
  replace (Z.lor (Z.land fb' 2) (Z.land fbo 252)) with (cfb fbo fb' false) in * by (unfold cfb; rewrite Z.lor_0_r; apply Z.lor_comm).
  finish. all: eassumption.
Qed.

(* [comment removed for export] *)
Definition wcd0_stmt (pc : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (o o' fb' : Z),
  0 <= o' -> o' + 32 <= 2^47 -> 0 <= fb' < 256 -> Z.testbit fb' 0 = true -> ro_cells rsegs m o' [C1 (b8 fb')] ->
  evt rsegs (fun ms' => exists a2' a3', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 o') a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 ACOPY) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 o') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Lemma wcd0 : wcd0_stmt COPY.
Proof.
  unfold wcd0_stmt. intros until fb'. intros O0' OHI' FB' TB YB. unfold COPY, ACOPY.
  st1. st1. rewrite (land1_bit0 fb' ltac:(lia)), TB. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. st1. apply evt_done. eexists _, _. reflexivity.
Qed.
Lemma wcd0a : wcd0_stmt COPYA.
Proof.
  unfold wcd0_stmt. intros until fb'. intros O0' OHI' FB' TB YB. unfold COPYA, ACOPY.
  st1. st1. rewrite (land1_bit0 fb' ltac:(lia)), TB. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. apply evt_done. eexists _, _. reflexivity.
Qed.

Lemma testbit_1 : forall i, 0 <= i -> Z.testbit 1 i = (0 =? i).
Proof. intros i Hi. exact (Z.pow2_bits_eqb 0 i ltac:(lia)). Qed.

Lemma land_lor1_253 : forall fbo, Z.land (Z.lor fbo 1) 253 = Z.lor (Z.land fbo 252) 1.
Proof.
  intros fbo. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, !Z.lor_spec, Z.land_spec, (testbit_1 i Hi).
  replace 253 with (Z.lor 252 1) by reflexivity. rewrite Z.lor_spec, (testbit_1 i Hi).
  destruct (Z.eqb_spec 0 i) as [<-|NE].
  - cbn. rewrite !Bool.orb_true_r. reflexivity.
  - rewrite !Bool.orb_false_r. reflexivity.
Qed.

Lemma cfb_true_eq : forall fbo fb', Z.lor (Z.land fb' 2) (Z.land (Z.lor fbo 1) 253) = cfb fbo fb' true.
Proof. intros. unfold cfb. rewrite land_lor1_253. apply Z.lor_comm. Qed.

Lemma lor1_byte : forall fbo, 0 <= fbo < 256 -> 0 <= Z.lor fbo 1 < 256.
Proof.
  intros fbo H. split. apply Z.lor_nonneg; lia.
  destruct (Z.testbit fbo 0) eqn:B.
  - replace (Z.lor fbo 1) with fbo; [lia|]. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, (testbit_1 i Hi).
    destruct (Z.eqb_spec 0 i) as [<-|NE]; [rewrite B; reflexivity| symmetry; apply Bool.orb_false_r].
  - replace (Z.lor fbo 1) with (fbo + 1). 2:{ symmetry. rewrite <- Z.lxor_lor. 2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, (testbit_1 i Hi). destruct (Z.eqb_spec 0 i) as [<-|NE]; [rewrite B; reflexivity| apply Bool.andb_false_r]. }
      rewrite <- Z.add_nocarry_lxor. reflexivity. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, (testbit_1 i Hi). destruct (Z.eqb_spec 0 i) as [<-|NE]; [rewrite B; reflexivity| apply Bool.andb_false_r]. }
    assert (fbo <> 255). { intros ->. cbn in B. discriminate. } lia.
Qed.

(* [comment removed for export] *)
Lemma wcd1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo o o' fbo fb' cap q : Z) (lenw : word) (junkO : list byte),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 64 ->
  bv_unsigned sp <= o -> o + 32 <= 2^47 -> 0 <= o' -> o' + 32 <= 2^47 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  (o' + 32 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= o') ->
  0 <= fbo < 256 -> 0 <= fb' < 256 -> 1 <= cap <= 2^27 -> 0 <= q < 2^64 ->
  rw_cells rsegs m o [C1 (b8 fbo); CB 31 junkO] ->
  ro_cells rsegs m o' [C1 (b8 fb')] -> ro_cells rsegs m (o' + 8) [C8 lenw] -> ro_cells rsegs m (o' + 16) [C8 (Z_to_bv 64 cap)] -> ro_cells rsegs m (o' + 24) [C8 (Z_to_bv 64 q)] ->
  evt rsegs (fun ms' => exists a1' m' junk j7,
      ms' = MS (mkR (wz 0x21c48) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 o') (Z_to_bv 64 o) (Z_to_bv 64 (cap * 8)) a1' a2 a3 a4 a5 a6 a7
                   lenw s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 OPNEW) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 32 junk; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells rsegs m' o [C1 (b8 (cfb fbo fb' true)); CB 7 j7; C8 lenw; C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 0)]
      /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (o, o + 32)] m m' /\ wmono rsegs m m' /\ mem_grows m m' /\ stk rsegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 o') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ACOPY) fc None m (seg_rom rsegs)).
Proof.
  intros until junkO. intros ST CLO LO SPO OHI O0' OHI' SEP SEPF FBO FB' CAP Q OB YB YL YC YQ. unfold ACOPY, OPNEW.
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp); (o, o + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM. pose proof (mem_grows_refl m) as MG.
  carve_frame 64%nat ST.
  do 5 st1. (* [comment removed for export] *)
  st1. st1. (* [comment removed for export] *)
  st1. st1. st1. rewrite le1_wz. mem_after_store.   (* [comment removed for export] *)
  st1. st1. st1. st1. st1. rewrite le1_wz. mem_after_store.   (* [comment removed for export] *)
  st1. st1. st1. st1.  (* [comment removed for export] *)
  st1. st1. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.  (* [comment removed for export] *)
  st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. rewrite Z.shiftr_div_pow2 in K by lia. assert (cap / 2 ^ 61 = 0) by (apply Z.div_small; lia). lia. }
  st1. st1.
  pose proof (zr_land_l fb' 2 ltac:(unfold inr64; lia) ltac:(lia)) as R1.
  pose proof (lor1_byte fbo FBO) as LB1.
  pose proof (zr_land_l (Z.lor fbo 1) 253 ltac:(unfold inr64; lia) ltac:(lia)) as R2.
  unfold inr64 in R1, R2.
  match goal with H : rw_cells _ _ o _ |- _ =>
    rewrite (unsigned_lit (Z.lor fbo 1)) in H by lia; rewrite (unsigned_lit (Z.land (Z.lor fbo 1) 253)) in H by lia;
    rewrite (unsigned_lit (Z.land fb' 2)) in H by lia end.
  replace (Z.lor (Z.land fb' 2) (Z.land (Z.lor fbo 1) 253)) with (cfb fbo fb' true) in * by (symmetry; apply cfb_true_eq).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  finish. all: eassumption.
Qed.
(* [comment removed for export] *)
Lemma blk_split : forall m A cap len (w : word) jr,
  1 <= cap -> 0 <= len <= cap -> rw_cells rsegs m A [C8 w; CB (Z.to_nat (cap * 8 - 8)) jr] ->
  exists J1 J2, rw_cells rsegs m A [CB (Z.to_nat (len * 8)) J1] /\ rw_cells rsegs m (A + len * 8) [CB (Z.to_nat (cap * 8 - len * 8)) J2].
Proof.
  intros m A cap len w jr CAP LEN RW. pose proof (proj1 (proj1 RW)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & L & _).
  assert (RW' : rw_cells rsegs m A [CB (Z.to_nat (len * 8) + Z.to_nat (cap * 8 - len * 8)) (le8 w ++ jr)]).
  { eapply rw_recell; [exact RW| | |]; cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize app].
    - rewrite length_app, L. change (length (le8 w)) with 8%nat. split; [lia| exact I].
    - rewrite !app_nil_r. reflexivity.
    - lia. }
  destruct (CB_cut _ _ _ _ _ RW') as [R1 R2]. rewrite Z2Nat.id in R2 by lia. eexists _, _. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
Lemma CB_cut1 : forall m A (k1 k2 : nat) bs, rw_cells rsegs m A [CB (k1 + k2) bs] ->
  rw_cells rsegs m A [CB k1 (firstn k1 bs); CB k2 (skipn k1 bs)].
Proof.
  intros m A k1 k2 bs RW. pose proof (proj1 (proj1 RW)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as [L _].
  eapply rw_recell; [exact RW| | |]; cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize app].
  - rewrite length_firstn, length_skipn. repeat split; lia.
  - rewrite !app_nil_r. apply firstn_skipn.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma wcd2 : forall (rax sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rao s0o s1o s2o : word) F fc m (o o' A cap len q : Z) (fbw : byte) (j7 junk j0 jr : list byte) (capw dw : word) (sbytes : list byte),
  1 <= cap <= 2^27 -> 0 <= len <= cap -> 4096 <= A -> (A + cap * 8 <= 0x10000 \/ 0x91000 <= A) -> A + cap * 8 <= bv_unsigned sp - 64 ->
  0x7fff7f800000 + 64 <= bv_unsigned sp -> bv_unsigned sp <= o -> o + 32 <= 2^47 -> 0 <= o' -> o' + 32 <= 2^47 ->
  1 <= q -> q + len * 8 <= bv_unsigned sp - 64 -> (q + len * 8 <= A \/ A + cap * 8 <= q) -> (o + 32 <= o' \/ o' + 32 <= o) ->
  length sbytes = Z.to_nat (len * 8) ->
  rw_cells rsegs m (bv_unsigned sp + -64) [CB 32 junk; C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  rw_cells rsegs m o [C1 fbw; CB 7 j7; C8 (Z_to_bv 64 len); C8 capw; C8 dw] ->
  ro_cells rsegs m (o' + 24) [C8 (Z_to_bv 64 q)] ->
  rw_cells rsegs m A [CB 8 j0; CB (Z.to_nat (cap * 8 - 8)) jr] ->
  bytes_at rsegs m q sbytes ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' J2,
      ms' = MS (mkR rao sp gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 A) a1' a2' a3' a4' a5' a6' a7'
                   s2o s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc rao) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' o [C1 fbw; CB 7 j7; C8 (Z_to_bv 64 len); C8 capw; C8 (Z_to_bv 64 A)]
      /\ rw_cells rsegs m' A [CB (Z.to_nat (len * 8)) sbytes]
      /\ rw_cells rsegs m' (A + len * 8) [CB (Z.to_nat (cap * 8 - len * 8)) J2]
      /\ bytes_at rsegs m' q sbytes
      /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 32 junk; C8 s2o; C8 s1o; C8 s0o; C8 rao]
      /\ munch [(o, o + 32); (A, A + cap * 8)] m m' /\ wmono rsegs m m' /\ mem_grows m m')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 o') (Z_to_bv 64 o) (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 len) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21c48) fc None m (seg_rom rsegs)).
Proof.
  intros until sbytes. intros CAP LEN ALO AHI2 AHI SPLO SPO OHI O0' OHI' Q1 QHI SEPQ SEP SLEN FR OB YQ PB SB. unfold MEMCPY.
  pose proof (munch_refl [(o, o + 32); (A, A + cap * 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  st1.                                         (* [comment removed for export] *)
  st1.                                         (* [comment removed for export] *)
  st1. change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)). mem_after_store.   (* [comment removed for export] *)
  match goal with H : rw_cells _ ?mx A _ |- _ => destruct (blk_split mx A cap len _ _ ltac:(lia) LEN H) as (J1 & J2 & DST & BT); clear H end.
  st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  do 5 st1. st1.
  call (memcpy_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A q (len * 8) sbytes J1).
  all: try lia. all: try assumption.
  finish. { exact BT. }
  eapply mem_grows_of_cover2; [exact MU|]. intros xq [Hx|Hx].
  - match goal with H : rw_cells _ _ o _ |- _ => eapply (rw_cells_defined _ _ _ xq H); cbn [cells_size csize Nat.add]; lia end.
  - destruct (Z_lt_le_dec xq (A + len * 8)).
    + match goal with H : rw_cells _ _ A _ |- _ => eapply (rw_cells_defined _ _ _ xq H); cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia end.
    + eapply (rw_cells_defined _ _ _ xq BT); cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia.
Qed.
(* [comment removed for export] *)
Lemma wcd01 : forall pc, wcd0_stmt pc ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc m (lo o o' fbo fb' cap q : Z) (lenw : word) (junkO : list byte),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 64 ->
  bv_unsigned sp <= o -> o + 32 <= 2^47 -> 0 <= o' -> o' + 32 <= 2^47 -> (o + 32 <= o' \/ o' + 32 <= o) ->
  (o' + 32 <= bv_unsigned sp - 64 \/ bv_unsigned sp <= o') ->
  0 <= fbo < 256 -> 0 <= fb' < 256 -> Z.testbit fb' 0 = true -> 1 <= cap <= 2^27 -> 0 <= q < 2^64 ->
  rw_cells rsegs m o [C1 (b8 fbo); CB 31 junkO] ->
  ro_cells rsegs m o' [C1 (b8 fb')] -> ro_cells rsegs m (o' + 8) [C8 lenw] -> ro_cells rsegs m (o' + 16) [C8 (Z_to_bv 64 cap)] -> ro_cells rsegs m (o' + 24) [C8 (Z_to_bv 64 q)] ->
  evt rsegs (fun ms' => exists a1' a2' a3' m' junk j7,
      ms' = MS (mkR (wz 0x21c48) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 o') (Z_to_bv 64 o) (Z_to_bv 64 (cap * 8)) a1' a2' a3' a4 a5 a6 a7
                   lenw s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 OPNEW) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -64) [CB 32 junk; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells rsegs m' o [C1 (b8 (cfb fbo fb' true)); CB 7 j7; C8 lenw; C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 0)]
      /\ munch [(bv_unsigned sp + -64, bv_unsigned sp); (o, o + 32)] m m' /\ wmono rsegs m m' /\ mem_grows m m' /\ stk rsegs m' lo (bv_unsigned sp + -64))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 o') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc WCD0. intros until junkO. intros ST CLO LO SPO OHI O0' OHI' SEP SEPF FBO FB' TB CAP Q OB YB YL YC YQ.
  eapply evt_cut; [eapply WCD0; [exact O0'| exact OHI'| exact FB'| exact TB| exact YB]|].
  intros ms' (a2' & a3' & ->).
  eapply evt_mono; [eapply (wcd1 ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo o o' fbo fb' cap q lenw junkO); assumption|].
  intros ms'' (a1' & m' & junk & j7 & PO). exists a1', a2', a3', m', junk, j7. exact PO.
Qed.
End TCS.
