(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Tgt Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import StoreOk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Module TSU.
(* [comment removed for export] *)
Definition ENTRY : Z := 0x207e8.
Definition STRINIT : Z := 0x20a84.
Definition CSTR : Z := 0x20b4c.
Definition STRCTOR : Z := 0x20c1c.
Definition COPY : Z := 0x222d0.
Definition OPMODF : Z := 0x20ce8.
Definition OPDELS : Z := 0x3f724.
Definition BEGIN_CATCH : Z := 0x3f80c.
Definition ALIT : Z := 0x127ab.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.

(* [comment removed for export] *)
Lemma mem_grows_write' : forall m0 m a bs, mem_grows m0 m -> mem_grows m0 (write_to_mem m a bs).
Proof. intros m0 m a bs H. eapply mem_grows_trans; [exact H| apply write_to_mem_grows]. Qed.

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
Lemma s1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> 0x7fff7f800000 <= lo -> lo <= bv_unsigned sp - 240 ->
  evt rsegs (fun ms' => exists (junk : list byte) m',
      ms' = MS (mkR (wz 0x2080c) (wz (bv_unsigned sp + -240)) gp tp t0 t1 t2 a1 s1 (wz (bv_unsigned sp + -240 + 192)) a0 a1 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 STRINIT) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -240) [CB 216 junk; C8 s1; C8 s0; C8 ra]
      /\ munch [(bv_unsigned sp + -240, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_grows m m' /\ stk rsegs m' lo (bv_unsigned sp + -240))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST CLO LO. unfold ENTRY, STRINIT.
  pose proof (munch_refl [(bv_unsigned sp + -240, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (mem_grows_refl m) as MG.
  carve_frame 240%nat ST.
  do 9 step. finish. exact FR.
Qed.

Section AFTER.
(* [comment removed for export] *)
Variables (sp : word).
Hypothesis SR : 0x7fff7f800000 <= bv_unsigned sp /\ bv_unsigned sp + 240 <= 2^47.

(* [comment removed for export] *)
Lemma s2_big : forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (len : Z),
  5000 <= len < 2^32 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (Z.shiftr len 3)) s1 (wz 624) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x20930) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz len) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2080c) fc None m (seg_rom rsegs)).
Proof.
  intros until len. intros Hlen.
  st1. st1. st1. if_cases K; zify_cond K.
  - apply evt_done. reflexivity.
  - exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by (try (rewrite Z.shiftr_div_pow2 by lia); lia). rewrite Z.shiftr_div_pow2 in K by lia. change (2^3) with 8 in K. lia.
Qed.

Lemma s2_small : forall (ra gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (len : Z),
  0 <= len < 5000 ->
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x2082c) sp gp tp t0 t1 t2 (wz (Z.shiftr len 3)) s1 (wz ((bv_unsigned sp) + 160)) (wz ALIT) (wz ((bv_unsigned sp) + 128)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 CSTR) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (wz len) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2080c) fc None m (seg_rom rsegs)).
Proof.
  intros until len. intros Hlen. unfold CSTR, ALIT.
  st1. st1. st1. if_cases K; zify_cond K.
  - exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K by (try (rewrite Z.shiftr_div_pow2 by lia); lia). rewrite Z.shiftr_div_pow2 in K by lia. change (2^3) with 8 in K. lia.
  - st1. st1. st1. st1. st1. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma s3 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x20838) sp gp tp t0 t1 t2 s0 s1 (wz ((bv_unsigned sp) + 128)) (wz ((bv_unsigned sp) + 192)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 STRCTOR) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2082c) fc None m (seg_rom rsegs)).
Proof. intros. unfold STRCTOR. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s4 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x20844) sp gp tp t0 t1 t2 s0 s1 (wz ((bv_unsigned sp) + 64)) (wz ((bv_unsigned sp) + 160)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 COPY) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20838) fc None m (seg_rom rsegs)).
Proof. intros. unfold COPY. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s5 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x20854) sp gp tp t0 t1 t2 s0 s1 (wz ((bv_unsigned sp) + 96)) (wz ((bv_unsigned sp) + 64)) (wz ((bv_unsigned sp) + 128)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 OPMODF) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20844) fc None m (seg_rom rsegs)).
Proof. intros. unfold OPMODF. st1. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Definition dtor_stmt (pc off k : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (fb cap q : Z),
  ro_cells rsegs m ((bv_unsigned sp) + off) [C1 (b8 fb)] -> 0 <= fb < 256 ->
  (Z.testbit fb 0 = true -> ro_cells rsegs m ((bv_unsigned sp) + off + 16) [C8 (wz cap); C8 (wz q)] /\ 0 <= cap < 2^61 /\ 0 < q < 2^64) ->
  evt rsegs (fun ms' => exists a0' a1',
         (Z.testbit fb 0 = false /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                               F (Z_to_bv 64 k) fc None m (seg_rom rsegs))
      \/ (Z.testbit fb 0 = true /\ a0' = wz q /\ a1' = wz (8 * cap)
          /\ ms' = MS (mkR (wz k) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 OPDELS) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma land1_bit0 : forall fb, 0 <= fb -> Z.land fb 1 = (if Z.testbit fb 0 then 1 else 0).
Proof.
  intros fb Hfb. change 1 with (Z.ones 1) at 1. rewrite Z.land_ones by lia. change (2^1) with 2.
  rewrite Z.bit0_odd. rewrite Zmod_odd. destruct (Z.odd fb); reflexivity.
Qed.

Ltac dtor_tac fb :=
  let FB := fresh "FB" in let Hfb := fresh "Hfb" in let DYN := fresh "DYN" in let K := fresh "K" in let K2 := fresh "K2" in
  let B0 := fresh "B0" in let CQ := fresh "CQ" in let Hcap := fresh "Hcap" in let Hq := fresh "Hq" in
  intros FB Hfb DYN;
  st1; st1; rewrite (land1_bit0 fb ltac:(lia));
  destruct (Z.testbit fb 0) eqn:B0;
  [ destruct (DYN eq_refl) as (CQ & Hcap & Hq);
    try match type of CQ with context [bv_unsigned ?spx + ?a + ?b] => let c := eval vm_compute in (Z.add a b) in
      replace (bv_unsigned spx + a + b) with (bv_unsigned spx + c) in CQ by lia end;
    st1; if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|];
    st1; st1; if_cases K2; zify_cond K2; [exfalso; rewrite ?wz_unsigned in K2 by lia; lia|];
    st1; st1; st1; rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8;
    apply evt_done; eexists _, _; right; repeat split; reflexivity
  | st1; if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia];
    apply evt_done; eexists _, _; left; split; reflexivity ].

Lemma d_x : dtor_stmt 0x20854 64 0x20874.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma d_y : dtor_stmt 0x20890 0 0x208b0.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma d_d : dtor_stmt 0x208b0 32 0x208d0.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma d_c : dtor_stmt 0x208d0 96 0x208f0.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma d_b : dtor_stmt 0x208f0 128 0x20910.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma d_a : dtor_stmt 0x20910 160 0x20930.
Proof. unfold dtor_stmt, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
(* [comment removed for export] *)
Definition dtor_stmtj (pc off kret k : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (fb cap q : Z),
  ro_cells rsegs m ((bv_unsigned sp) + off) [C1 (b8 fb)] -> 0 <= fb < 256 ->
  (Z.testbit fb 0 = true -> ro_cells rsegs m ((bv_unsigned sp) + off + 16) [C8 (wz cap); C8 (wz q)] /\ 0 <= cap < 2^61 /\ 0 < q < 2^64) ->
  evt rsegs (fun ms' => exists a0' a1',
         (Z.testbit fb 0 = false /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                               F (Z_to_bv 64 k) fc None m (seg_rom rsegs))
      \/ (Z.testbit fb 0 = true /\ a0' = wz q /\ a1' = wz (8 * cap)
          /\ ms' = MS (mkR (wz kret) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 OPDELS) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Lemma pd_b : dtor_stmtj 0x209e8 128 0x20a08 0x20a14.
Proof. unfold dtor_stmtj, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
Lemma pd_a : dtor_stmtj 0x20a14 160 0x20a34 0x20a40.
Proof. unfold dtor_stmtj, OPDELS. intros until q. replace (8 * cap) with (cap * 8) by lia. dtor_tac fb. Qed.
(* [comment removed for export] *)
Definition jmp_stmt (pc k : Z) : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 k) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Lemma j_x : jmp_stmt 0x209dc 0x209e8. Proof. unfold jmp_stmt. intros. st1. apply evt_done. reflexivity. Qed.
Lemma j_b : jmp_stmt 0x20a08 0x20a14. Proof. unfold jmp_stmt. intros. st1. apply evt_done. reflexivity. Qed.
Lemma j_a : jmp_stmt 0x20a34 0x20a40. Proof. unfold jmp_stmt. intros. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s8 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x20880) sp gp tp t0 t1 t2 s0 s1 sp (wz (bv_unsigned sp + 128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 COPY) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20874) fc None m (seg_rom rsegs)).
Proof. intros. unfold COPY. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s9 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR (wz 0x20890) sp gp tp t0 t1 t2 s0 s1 (wz (bv_unsigned sp + 32)) sp (wz (bv_unsigned sp + 160)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 OPMODF) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20880) fc None m (seg_rom rsegs)).
Proof. intros. unfold OPMODF. st1. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s16 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (b0 w0 p : Z),
  ro_cells rsegs m (bv_unsigned sp + 192) [C1 (b8 b0)] -> 0 <= b0 < 256 ->
  (Z.testbit b0 0 = true -> ro_cells rsegs m (bv_unsigned sp + 192) [C8 (wz w0)] /\ ro_cells rsegs m (bv_unsigned sp + 208) [C8 (wz p)] /\ 0 <= w0 < 2^64 /\ 0 <= p < 2^64) ->
  evt rsegs (fun ms' => exists a0' a1',
         (Z.testbit b0 0 = false /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                               F (Z_to_bv 64 0x2094c) fc None m (seg_rom rsegs))
      \/ (Z.testbit b0 0 = true /\ a0' = wz p /\ a1' = wz (Z.land w0 (2^64 - 2))
          /\ ms' = MS (mkR (wz 0x2094c) sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 OPDELS) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20930) fc None m (seg_rom rsegs)).
Proof.
  intros until p. intros FB Hb0 DYN. unfold OPDELS.
  st1. st1. rewrite (land1_bit0 b0 ltac:(lia)).
  destruct (Z.testbit b0 0) eqn:B0.
  - destruct (DYN eq_refl) as (CQ & CP & Hw0 & Hp). clear FB.
    st1. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
    st1. st1. st1. st1.
    apply evt_done; eexists _, _; right. repeat split; try reflexivity.
  - st1. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    apply evt_done; eexists _, _; left; split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma s17 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (rao s0o s1o : word),
  ro_cells rsegs m (bv_unsigned sp + 216) [C8 s1o; C8 s0o; C8 rao] ->
  evt rsegs (fun ms' => ms' = MS (mkR rao (wz (bv_unsigned sp + 240)) gp tp t0 t1 t2 s0o s1o (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (ret_pc rao) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2094c) fc None m (seg_rom rsegs)).
Proof. intros until s1o. intros FR. st1. st1. st1. st1. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p1 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 a0 a1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x20a14) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20a0c) fc None m (seg_rom rsegs)).
Proof. intros. st1. st1. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p3 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (fb cap q : Z),
  ro_cells rsegs m (bv_unsigned sp + 64) [C1 (b8 fb)] -> 0 <= fb < 256 ->
  (Z.testbit fb 0 = true -> ro_cells rsegs m (bv_unsigned sp + 64 + 16) [C8 (wz cap); C8 (wz q)] /\ 0 <= cap < 2^61 /\ 0 < q < 2^64) ->
  evt rsegs (fun ms' => exists a0' a1',
         (Z.testbit fb 0 = false /\ ms' = MS (mkR ra sp gp tp t0 t1 t2 a0 a1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                               F (Z_to_bv 64 0x209e8) fc None m (seg_rom rsegs))
      \/ (Z.testbit fb 0 = true /\ a0' = wz q /\ a1' = wz (8 * cap)
          /\ ms' = MS (mkR (wz 0x209dc) sp gp tp t0 t1 t2 a0 a1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 OPDELS) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x209b4) fc None m (seg_rom rsegs)).
Proof.
  intros until q. intros FB Hfb DYN. unfold OPDELS. replace (8 * cap) with (cap * 8) by lia.
  st1. st1. st1. rewrite (land1_bit0 fb ltac:(lia)). st1.
  destruct (Z.testbit fb 0) eqn:B0.
  - destruct (DYN eq_refl) as (CQ & Hcap & Hq).
    replace (bv_unsigned sp + 64 + 16) with (bv_unsigned sp + 80) in CQ by lia.
    st1. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|].
    st1. st1. if_cases K2; zify_cond K2; [exfalso; rewrite ?wz_unsigned in K2 by lia; lia|].
    st1. st1. st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
    apply evt_done; eexists _, _; right; repeat split; reflexivity.
  - st1. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit in K by lia; lia].
    apply evt_done; eexists _, _; left; split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma c1' : forall (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 1) s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x20a50) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz 1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20a40) fc None m (seg_rom rsegs)).
Proof.
  intros. st1. st1. st1. if_cases K; zify_cond K. { exfalso. revert K. vm_compute. lia. }
  st1. replace (bv_swrap 32 1) with 1 by (vm_compute; reflexivity). apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma j1 : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x20930) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20a58) fc None m (seg_rom rsegs)).
Proof. intros. st1. apply evt_done. reflexivity. Qed.

End AFTER.
End TSU.
