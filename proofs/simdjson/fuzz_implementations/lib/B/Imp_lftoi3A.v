(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_activewA Atp_pidiA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_lftoi1A Imp_lftoi2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition IMP_DLOOP_A : Z := 0xb5544.
Definition IMP_ODRET_A : Z := 0xb5560.
Definition IMP_PDRET_A : Z := 0xb5568.
Definition IMP_SSXRET_A : Z := 0xb5580.
Definition IMP_SFRET_A : Z := 0xb55a0.
Definition SH_ACTIVE_A : Z := 2148333604.
Lemma SH_ACTIVE_eq : SH_ACTIVE_A = shad SJ_ACTIVE.
Proof. reflexivity. Qed.

Definition imp_localsK (j0 j8 : list byte) (f : Z) (szw : word) (d : Z) (ne : Z) (j160 : list byte) : list cell :=
  [CB 8 j0; CB 16 j8; C8 (Z_to_bv 64 (shad f + 20)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); C8 szw; C8 (Z_to_bv 64 1)] ++ imp_locals f 1 d ++
  [C8 (Z_to_bv 64 (Z.lnot (f + 160))); CB 24 j160; C8 (Z_to_bv 64 f)].
Lemma imp_localsK_size : forall j0 j8 f szw d ne j160, cells_size (imp_localsK j0 j8 f szw d ne j160) = 192%nat.
Proof. intros. reflexivity. Qed.
Lemma imp_localsL_KR : forall j0 j8 f szw d ne j160 j192, imp_localsL j0 j8 f szw d ne j160 j192 = imp_localsK j0 j8 f szw d ne j160 ++ [CB 24 j192].
Proof. intros. reflexivity. Qed.

Definition dtor_st (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f s2 s4 : Z)
    (s6 s7 s8 s9 s11 : word) (t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 s2) (Z_to_bv 64 (shad f)) (Z_to_bv 64 s4) (Z_to_bv 64 (-8)) s6 s7 s8 s9 (Z_to_bv 64 (f + 160)) s11 t3 t4 t5 t6)
     Fr (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Lemma rw_cells_recastA : forall (m : mem) A cs cs',
  rw_cells bsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells bsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma out_longA_bytes : forall (m : mem) A S L DATA, rw_cells bsegs m A (out_longA S L DATA) ->
  rw_cells bsegs m A [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (S + 1)))); CB 7 (Z_to_le_bytes 7 (Z.shiftr (bv_unsigned (Z_to_bv 64 (S + 1))) 8)); C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 DATA)].
Proof.
  intros m A S L DATA H. eapply rw_cells_recastA; [exact H| | reflexivity| reflexivity].
  cbn. repeat split. all: apply length_Z_to_le_bytes.
Qed.
Lemma land1_byte : forall x, Z.land (bv_unsigned (Z_to_bv 8 x)) 1 = Z.land x 1.
Proof.
  intros x. rewrite Z_to_bv_unsigned, bv_wrap8_mod, <- (Z.land_ones x 8) by lia. rewrite <- Z.land_assoc.
  change (Z.land (Z.ones 8) 1) with 1. reflexivity.
Qed.

Lemma testbit_capmaskA : forall n, 0 <= n -> Z.testbit 18446744073709551614 n = ((1 <=? n) && (n <? 64))%bool.
Proof.
  intros n Hn. change 18446744073709551614 with (2 * Z.ones 63).
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + rewrite Z.ones_spec_low by lia. symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite Z.ones_spec_high by lia. symmetry. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma long_capmaskA : forall cap, cap mod 2 = 0 -> 0 <= cap -> cap < 2^63 -> Z.land (cap + 1) 18446744073709551614 = cap.
Proof.
  intros cap HE H0 H1. set (h := cap / 2). assert (EC : cap = 2 * h) by (subst h; Z.div_mod_to_equations; lia). rewrite EC.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, testbit_capmaskA by lia.
  destruct (Z.eq_dec n 0) as [->|NZ].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    destruct (Z.lt_ge_cases (n - 1) 63).
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia]). apply Bool.andb_true_r.
    + replace ((1 <=? Z.succ (n - 1)) && (Z.succ (n - 1) <? 64))%bool with false
        by (symmetry; apply Bool.andb_false_intro2; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
      destruct (Z.eq_dec h 0) as [->|HZ]; [rewrite Z.bits_0; reflexivity|].
      symmetry. apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 62); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma land1_mod2A : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma imp_walk7 : forall (usp sp' f d n : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s9 s10 s11 t3 t4 t5 t6 : word) (w : word) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> SJ_ACTIVE + 8 <= sp' -> sp' + 216 < 2^63 -> 0 <= d < 2^64 ->
  ro_cells bsegs m SH_ACTIVE_A [C1 z8] ->
  rw_cells bsegs m SJ_ACTIVE [C8 w] ->
  rw_cells bsegs m (sp' + 120) [C8 (Z_to_bv 64 d)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = imp_regsA e_pid (Z_to_bv 64 IMP_PARSE_RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (sp' + 192)) (Z_to_bv 64 (f + 168)) (Z_to_bv 64 (f + 192)) (Z_to_bv 64 d) (Z_to_bv 64 n)
             (Z_to_bv 64 1) a6 a7 f (Z_to_bv 64 SJ_SINGLETON) (Z_to_bv 64 SHB) s6 (Z_to_bv 64 (f + 160)) (Z_to_bv 64 n) s9 s10 s11 t3 t4 t5 t6 Fr fc m1
      /\ munch [(SJ_ACTIVE, SJ_ACTIVE + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 SJ_ACTIVE [C8 (Z_to_bv 64 SJ_SINGLETON)])
    (imp_regsA IMP_GARET_A (Z_to_bv 64 IMP_GARET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 SJ_ACTIVE) a1 a2 a3 a4 a5 a6 a7 f (Z_to_bv 64 SJ_SINGLETON) (Z_to_bv 64 SHB)
       s6 (Z_to_bv 64 (f + 160)) (Z_to_bv 64 n) s9 s10 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH DR SHA ACT SD MI.
  unfold imp_regsA, IMP_GARET_A, IMP_PARSE_RET_A, e_pid, SJ_ACTIVE, SJ_SINGLETON, SH_ACTIVE_A, TPV_A, shad, SHB in *.
  pose proof (munch_refl [(7061792, 7061792 + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  apply proj1 in SD. change (ro_cells bsegs m (sp' + 120) [C8 (Z_to_bv 64 d)]) in SD.
  repeat (first [zstep | ls]).
  rewrite lbu_z8. if_false.
  repeat (first [ apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|];
                  split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; eassumption
                | ls | zstep ]).
Qed.

Lemma imp_walk8_ok : forall (usp sp' f : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j20 : list byte) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= sp' -> sp' + 216 < 2^63 ->
  rw_cells bsegs m (sp' + 192) (res_cellsA (f + 192) (Z_to_bv 64 0) j20) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists a1', ms = imp_regsA IMP_OKARM_A x1 sp' gp t0 t1 t2 usp (Z_to_bv 64 0) a1' a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s10 s11
                                        t3 t4 t5 t6 Fr fc m)
    (imp_regsA IMP_PARSE_RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RC MI. unfold imp_regsA, res_cellsA, IMP_PARSE_RET_A, IMP_OKARM_A, TPV_A, shad, SHB in *.
  rewrite bv_eqb_refl in RC.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  repeat zstep.
  rewrite ?sx32_small by lia. if_false.
  repeat zstep.
  if_true.
  apply evt_done. eexists. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk8_err : forall (usp sp' f ne : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s8 s10 s11 t3 t4 t5 t6 : word) (r e0 : word) (j20 : list byte)
    Fr fc (m : mem),
  0 < f -> f + 2048 <= sp' -> 0 <= sp' -> sp' + 216 < 2^63 -> 1 <= bv_unsigned r < 64 -> 0 <= ne -> ne + 1 < 2^64 ->
  rw_cells bsegs m (sp' + 192) (res_cellsA (f + 192) r j20) ->
  rw_cells bsegs m (f + 264) [C4 e0] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a0' a1' e1 : word),
      ms = imp_regsA IMP_OKARM_END_A x1 sp' gp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 a7 f s2 s4 s6 (Z_to_bv 64 (f + 160)) s8 (Z_to_bv 64 (ne + 1)) s10 s11
                     t3 t4 t5 t6 Fr fc m1
      /\ munch [(f + 264, f + 268)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (f + 264) [C4 e1])
    (imp_regsA IMP_PARSE_RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 (Z_to_bv 64 (f + 160)) s8 (Z_to_bv 64 ne) s10 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH RR NE0 NEH RC FE MI.
  unfold imp_regsA, res_cellsA, IMP_PARSE_RET_A, IMP_OKARM_END_A, TPV_A, shad, SHB in *.
  assert (NZ : bv_eqb r (Z_to_bv 64 0) = false).
  { destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [| reflexivity]. exfalso. apply bv_eqb_eq in E. subst r. rewrite unsigned_lit in RR by lia. lia. }
  rewrite NZ in RC.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [C4 r; CB 4 j20] [16]%nat) in RC; [| reflexivity]. cbn [mk_CB_cells app] in RC.
  assert (ER : r = Z_to_bv 64 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ER in RC.
  pose proof (munch_refl [(f + 264, f + 268)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  repeat zstep.
  if_cases K; zify_cond K; [exfalso; rewrite ER in K; rewrite sx32_small in K by lia; rewrite unsigned_lit in K by lia; lia|].
  repeat (first [ls | zstep]).
  if_cases K2; zify_cond K2; [exfalso; rewrite ER in K2; rewrite sx32_small in K2 by lia; rewrite unsigned_lit in K2 by lia; lia|].
  repeat (first [ apply evt_done; do 4 eexists; split; [cbv delta [mkR]; rewrite ?unsigned_lit by lia; reflexivity|];
                  split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; eassumption
                | ls | zstep ]).
Qed.

Lemma imp_walk9 : forall (usp sp' f d n ne : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s4x s7x s11x t3 t4 t5 t6 : word) (j0 j8 j160 : list byte) (szw : word) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= sp' -> sp' + 216 < 2^63 -> 0 <= shad f -> shad f + 156 < 2^63 -> (ne = 0 \/ ne = 1) ->
  rw_cells bsegs m sp' (imp_localsK j0 j8 f szw d ne j160) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (a0' a1' s11' : word),
      ms = dtor_st IMP_DLOOP_A x1 sp' gp t0 t1 t2 usp a0' a1' a2 a3 a4 a5 a6 a7 f (f + 576) (-544) (Z_to_bv 64 1) s7x (Z_to_bv 64 n) (Z_to_bv 64 ne) s11'
                   t3 t4 t5 t6 Fr fc m)
    (imp_regsA IMP_OKARM_END_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2x s4x (Z_to_bv 64 0) s7x (Z_to_bv 64 n) (Z_to_bv 64 ne) (Z_to_bv 64 0) s11x
       t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH SH0 SHH NE FRl MI.
  unfold imp_regsA, dtor_st, imp_localsK, imp_locals, IMP_OKARM_END_A, IMP_DLOOP_A, TPV_A, shad, SHB in *.
  cbn [app] in FRl. apply proj1 in FRl. lazymatch type of FRl with cells_at _ _ _ ?l => change (ro_cells bsegs m sp' l) in FRl end.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  repeat zstep.
  if_false.
  destruct NE as [-> | ->].
  all: repeat (first [ apply evt_done; do 3 eexists; cbv delta [mkR]; rewrite ?unsigned_lit by lia; reflexivity
                     | zstep | if_true | if_false ]).
Qed.

Lemma imp_walk10s : forall (usp sp' f k : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (b0 : byte) (j23 : list byte) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= k <= 3 -> Z.land (bv_unsigned b0) 1 = 0 ->
  rw_cells bsegs m (f + 160 + 136 * k + 112) (out_shortA b0 j23) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists a0', ms = dtor_st e_pdtor (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1 t2 usp a0' a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * k + 8) (-544 + 136 * (3 - k)) s6 s7 s8 s9 s11
                                      t3 t4 t5 t6 Fr fc m /\ a0' = Z_to_bv 64 (f + 160 + 136 * k + 8))
    (dtor_st IMP_DLOOP_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * k + 8) (-544 + 136 * (3 - k)) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH KR EVEN OC MI.
  unfold dtor_st, out_shortA, IMP_DLOOP_A, IMP_PDRET_A, e_pdtor, TPV_A, shad, SHB in *.
  set (I8 := f + 160 + 136 * k + 8) in *. replace (f + 160 + 136 * k + 112) with (I8 + 104) in OC by lia.
  assert (EI : bv_unsigned (Z_to_bv 64 I8) = I8) by (apply unsigned_lit; lia).

  zstep. cbv beta. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; clear - K EVEN; try rewrite unsigned_lit in K by lia; lia].
  zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity| reflexivity].
Qed.

Lemma imp_walk10l : forall (usp sp' f : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (SZ L DATA : Z) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> Z.land (SZ + 1) 1 = 1 -> 0 < SZ < 2^32 -> 0 < DATA < 2^64 -> 0 <= L < 2^64 ->
  rw_cells bsegs m (f + 272) (out_longA SZ L DATA) ->
  mem_inv bsegs m ->
  evt bsegs (eq (dtor_st OPDEL_A (Z_to_bv 64 IMP_ODRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 DATA) (Z_to_bv 64 SZ) a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * 0 + 8) (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11
                 t3 t4 t5 t6 Fr fc m))
    (dtor_st IMP_DLOOP_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * 0 + 8) (-544 + 136 * (3 - 0)) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH ODD SZR DR LR OC MI.
  unfold dtor_st, IMP_DLOOP_A, IMP_ODRET_A, OPDEL_A, TPV_A, shad, SHB in *.
  replace (f + 160 + 136 * 0 + 8) with (f + 168) by lia.
  pose proof (out_longA_bytes _ _ _ _ _ OC) as OB. unfold out_longA in OC. rewrite (unsigned_lit (SZ + 1)) in OB by lia.
  assert (EI : bv_unsigned (Z_to_bv 64 (f + 168)) = f + 168) by (apply unsigned_lit; lia).

  zstep. cbv beta. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite land1_byte in K; clear - K ODD; lia| clear K].

  zstep. zstep. zstep.
  rewrite (long_capmaskA SZ) by (first [rewrite land1_mod2A in ODD; Z.div_mod_to_equations; lia | lia]).
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk10b : forall (usp sp' f s2 s4 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
  evt bsegs (eq (dtor_st e_pdtor (Z_to_bv 64 IMP_PDRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 s2) a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m))
    (dtor_st IMP_ODRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros. unfold dtor_st, IMP_ODRET_A, IMP_PDRET_A, e_pdtor, TPV_A, shad, SHB in *.
  zstep. zstep. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk10c : forall (usp sp' f k : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
  0 <= k <= 3 ->
  evt bsegs (eq (dtor_st (if Z.ltb 0 k then IMP_DLOOP_A else IMP_EXIT_A) x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f
                 (f + 160 + 136 * (k - 1) + 8) (-544 + 136 * (3 - (k - 1))) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m))
    (dtor_st IMP_PDRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f (f + 160 + 136 * k + 8) (-544 + 136 * (3 - k)) s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros KR. unfold dtor_st, IMP_PDRET_A, IMP_DLOOP_A, IMP_EXIT_A, TPV_A, shad, SHB in *.
  zstep. zstep.
  replace (-544 + 136 * (3 - k) + 136) with (-544 + 136 * (3 - (k - 1))) by lia.
  assert (C : 0 < k \/ k = 0) by lia. destruct C as [C|C].
  - rewrite (proj2 (Z.ltb_lt 0 k) C). step. if_cases K; zify_cond K;
      [| exfalso; revert K; rewrite ?unsigned_lit_wrap; clear - C KR; intros K; Z.div_mod_to_equations; lia].
    replace (f + 160 + 136 * k + -128) with (f + 160 + 136 * (k - 1) + 8) by lia.
    apply evt_done. cbv delta [mkR]. reflexivity.
  - subst k. cbn [Z.ltb]. step. if_cases K; zify_cond K; [exfalso; revert K; rewrite ?unsigned_lit_wrap; clear; intros K; Z.div_mod_to_equations; lia|].
    match goal with |- evt _ (eq ?X) ?Y => replace Y with X; [apply evt_done; reflexivity|] end.
    cbv delta [mkR]. repeat first [reflexivity | progress f_equal]. all: try (f_equal; lia).
Qed.

Lemma imp_walk11a : forall (usp sp' f d ne s2 s4 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (j0 j8 j160 : list byte) (szw : word) Fr fc (m : mem),
  0 <= sp' -> sp' + 216 < 2^63 ->
  rw_cells bsegs m sp' (imp_localsK j0 j8 f szw d ne j160) ->
  mem_inv bsegs m ->
  evt bsegs (eq (dtor_st (e_set_shadow 0xf8) (Z_to_bv 64 IMP_SSXRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (shad f + 20)) (Z_to_bv 64 68) a2 a3 a4 a5 a6 a7 f s2 s4
                 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m))
    (dtor_st IMP_EXIT_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros SP0 SPH FRl MI.
  unfold dtor_st, imp_localsK, imp_locals, IMP_EXIT_A, IMP_SSXRET_A, e_set_shadow, TPV_A, shad, SHB in *.
  cbn [app] in FRl. apply proj1 in FRl. lazymatch type of FRl with cells_at _ _ _ ?l => change (ro_cells bsegs m sp' l) in FRl end.
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  repeat (first [ apply evt_done; cbv delta [mkR]; rewrite ?unsigned_lit by lia; reflexivity | zstep ]).
Qed.

Lemma imp_walk11b : forall (usp sp' f d ne s2 s4 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (h3 j0 j8 j160 : list byte) (szw : word) Fr fc (m : mem),
  0 < f -> f + 2048 <= sp' -> 0 <= sp' -> sp' + 216 < 2^63 ->
  rw_cells bsegs m f (fz_hdr (C8 (Z_to_bv 64 IMP_MAGIC0)) (C8 (Z_to_bv 64 IMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3) ->
  rw_cells bsegs m sp' (imp_localsK j0 j8 f szw d ne j160) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = dtor_st e_stack_free_5 (Z_to_bv 64 IMP_SFRET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 f) (Z_to_bv 64 1248) a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11
                   t3 t4 t5 t6 Fr fc m1
      /\ munch [(f, f + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 f (fz_hdr (C8 (Z_to_bv 64 IMP_MAGIC1)) (C8 (Z_to_bv 64 IMP_HDR_DESC_A)) (C8 (Z_to_bv 64 e_fuzz)) h3))
    (dtor_st IMP_SSXRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH SP0 SPH FHD FRl MI.
  unfold dtor_st, fz_hdr, imp_localsK, imp_locals, IMP_SSXRET_A, IMP_SFRET_A, e_stack_free_5, e_fuzz, IMP_MAGIC0, IMP_MAGIC1, IMP_HDR_DESC_A, TPV_A, shad, SHB in *.
  cbn [app] in FRl. apply proj1 in FRl. lazymatch type of FRl with cells_at _ _ _ ?l => change (ro_cells bsegs m sp' l) in FRl end.
  pose proof (munch_refl [(f, f + 8)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  repeat (first [ apply evt_done; eexists; split; [cbv delta [mkR]; rewrite ?unsigned_lit by lia; reflexivity|];
                  split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; eassumption
                | ls | zstep | (if_cases K; zify_cond K; [exfalso; try rewrite unsigned_lit in K by lia; lia|]) ]).
Qed.

Lemma imp_walk11c : forall (usp sp' f lo s2 s4 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) Fr fc (m : mem),
  0x6a9000 <= lo -> lo <= sp' -> cells_size LC = 216%nat -> sp' + 216 <= usp - 104 -> usp < 2^63 ->
  stk bsegs m lo sp' -> rw_cells bsegs m sp' LC -> stk bsegs m (sp' + 216) (usp - 104) ->
  rw_cells bsegs m (usp - 104) (imp_savedA xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => ret_st xra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 0) m ms
                      /\ ms_fcsr ms = fc /\ stk bsegs m lo usp)
    (dtor_st IMP_SFRET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s2 s4 s6 s7 s8 s9 s11 t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros GLO LSP SZ LUSP SPH ST FRl STp FRs MI.
  unfold dtor_st, imp_savedA, IMP_SFRET_A, TPV_A, shad, SHB in *.
  assert (EUS : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).

  zstep. zstep. zstep.
  replace (usp - 104) with (usp + -104) in FRs by lia.

  do 13 zstep. zstep.
  replace (usp + -104) with (usp - 104) in FRs by lia. try replace (usp + -320 + 320) with usp by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 216%nat) with 216 in ST1.
  pose proof (stk_merge bsegs _ _ _ _ ST1 STp ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (usp - 104 + Z.of_nat 104) with usp in ST3 by lia.

  zstep.
  apply evt_done. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity| exact ST3].
Qed.
