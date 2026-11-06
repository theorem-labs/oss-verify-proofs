(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA
     Atp_defsA Atp_activewA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_lftoi1A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma lbu_z8 : Z_to_bv 64 (bv_unsigned z8) = Z_to_bv 64 0.
Proof. reflexivity. Qed.

Definition IMP_MS1RET_A : Z := 0xb4ed4.
Definition IMP_MS2RET_A : Z := 0xb4ef0.
Definition IMP_MS3RET_A : Z := 0xb4f00.
Definition IMP_CTORS_END_A : Z := 0xb4f08.
Definition IMP_GARET_A : Z := 0xb4fc8.

Definition implA_cells (c0 c32 c56 c64 : cell) (j9 j25 j65 : list byte) (c72 : cell) (j108 : list byte) (c112 : cell) : list cell :=
  [c0; C1 (Z_to_bv 8 0); CB 7 j9; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 j25; C4 (Z_to_bv 64 12); c32; c56; c64; CB 7 j65; c72; CB 4 j108; c112].
Definition z24 : list byte := repeat z8 24.
Definition z36 : list byte := repeat z8 36.

Definition impl0A (w : word) (j9 j25 j65 j108 : list byte) : list cell :=
  implA_cells (C8 w) (CB 24 z24) (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) j9 j25 j65 (CB 36 z36) j108 (CB 24 z24).
Lemma implA_cells_size : forall c0 c32 c56 c64 j9 j25 j65 c72 j108 c112,
  csize c0 = 8%nat -> csize c32 = 24%nat -> csize c56 = 8%nat -> csize c64 = 1%nat -> csize c72 = 36%nat -> csize c112 = 24%nat ->
  cells_size (implA_cells c0 c32 c56 c64 j9 j25 j65 c72 j108 c112) = 136%nat.
Proof. intros. cbn [implA_cells cells_size]. rewrite H, H0, H1, H2, H3, H4. reflexivity. Qed.
Lemma impl0A_size : forall w j9 j25 j65 j108, cells_size (impl0A w j9 j25 j65 j108) = 136%nat.
Proof. intros. reflexivity. Qed.

Definition ctor_st (pc : Z) (ra : word) (sp' : Z) (gp t0 t1 t2 : word) (usp : Z) (a0 a1 a2 a3 a4 a5 a6 a7 : word) (f A8 : Z) (s2 s7 : word) (s8 : Z)
    (t3 t4 t5 t6 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR ra (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          s2 (Z_to_bv 64 (shad f)) (Z_to_bv 64 A8) (Z_to_bv 64 544) (Z_to_bv 64 (A8 + 8)) s7 (Z_to_bv 64 s8) (Z_to_bv 64 (f + 160))
          (Z_to_bv 64 12) (Z_to_bv 64 4294967295) t3 t4 t5 t6)
     Fr (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Lemma imp_walk4pre : forall (usp sp' f d A8 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10x s11x t3 t4 t5 t6 : word) Fr fc (m : mem),
  evt asegs (eq (ctor_st IMP_CTORS_A x1 sp' gp t0 t1 t2 usp (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 f A8 (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f + 20)) 0 t3 t4 t5 t6 Fr fc m))
    (MS (mkR x1 (Z_to_bv 64 sp') gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-8)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 A8) (Z_to_bv 64 f) (Z_to_bv 64 (A8 + 8)) (Z_to_bv 64 (shad f + 20)) (Z_to_bv 64 d)
             (Z_to_bv 64 (f + 160)) s10x s11x t3 t4 t5 t6)
        Fr (Z_to_bv 64 IMP_SS00RET_A) fc None m (seg_rom asegs)).
Proof.
  intros. unfold ctor_st, IMP_SS00RET_A, IMP_CTORS_A, TPV_A, shad, SHB in *.

  zstep. zstep. zstep. zstep.
  try change (Z.shiftr (bv_unsigned (Z_to_bv 64 (-1))) 32) with 4294967295.
  try replace (Z.shiftr 18446744073709551615 32) with 4294967295 by reflexivity.
  zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk4a : forall (usp sp' f A8 i : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 : word) (j : list byte) Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= i <= 3 ->
  rw_cells asegs m (f + 160 + 136 * i) [CB 136 j] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j9 j25 j32 j56 j64 j65 j72 j108 j112 : list byte),
      ms = ctor_st e_asan_memset (Z_to_bv 64 IMP_MS1RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (f + 160 + 136 * i + 32)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
             f A8 s2x (Z_to_bv 64 (f + 160 + 136 * i)) (136 * i) t3 t4 t5 t6 Fr fc m1
      /\ munch [(f + 160 + 136 * i, f + 160 + 136 * i + 32)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 160 + 136 * i)
           (implA_cells (C8 (Z_to_bv 64 0)) (CB 24 j32) (CB 8 j56) (CB 1 j64) j9 j25 j65 (CB 36 j72) j108 (CB 24 j112)))
    (ctor_st IMP_CTORS_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x s7x (136 * i) t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH IR FI MI.
  unfold ctor_st, IMP_CTORS_A, IMP_MS1RET_A, e_asan_memset, implA_cells, TPV_A, shad, SHB in *.
  set (I := f + 160 + 136 * i) in *.

  apply (rw_cells_split_CB asegs _ _ [] 136 j [] [8; 1; 7; 8; 1; 3; 4; 24; 8; 1; 7; 36; 4; 24]%nat) in FI; [| reflexivity]. cbn [mk_CB_cells app] in FI.
  repeat match type of FI with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let jj := fresh "j" in set (jj := t) in FI; clearbody jj end.
  pose proof (munch_refl [(I, I + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EI : bv_unsigned (Z_to_bv 64 I) = I) by (apply unsigned_lit; lia).

  zstep. try replace (f + 160 + 136 * i) with I by lia.

  ls. ls. ls. ls. ls.

  zstep. zstep. zstep. zstep.
  apply evt_done. eexists _, _, _, _, _, _, _, _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma imp_walk4b : forall (usp sp' f A8 i : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) (c32 c72 c112 : cell) (j9 j25 j56 j64 j65 j108 : list byte)
    Fr fc (m : mem),
  0 < f -> f + 2048 < 2^63 -> 0 <= i <= 3 -> csize c32 = 24%nat -> csize c72 = 36%nat -> csize c112 = 24%nat ->
  rw_cells asegs m (f + 160 + 136 * i) (implA_cells (C8 (Z_to_bv 64 0)) c32 (CB 8 j56) (CB 1 j64) j9 j25 j65 c72 j108 c112) ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem),
      ms = ctor_st e_asan_memset (Z_to_bv 64 IMP_MS2RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (f + 160 + 136 * i + 112)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3 a4 a5 a6 a7
             f A8 (Z_to_bv 64 (f + 160 + 136 * i + 72)) (Z_to_bv 64 (f + 160 + 136 * i)) (136 * i) t3 t4 t5 t6 Fr fc m1
      /\ munch [(f + 160 + 136 * i + 56, f + 160 + 136 * i + 65)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 (f + 160 + 136 * i)
           (implA_cells (C8 (Z_to_bv 64 0)) c32 (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) j9 j25 j65 c72 j108 c112))
    (ctor_st IMP_MS1RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x (Z_to_bv 64 (f + 160 + 136 * i)) (136 * i) t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FH IR S32 S72 S112 FI MI.
  unfold ctor_st, IMP_MS1RET_A, IMP_MS2RET_A, e_asan_memset, implA_cells, TPV_A, shad, SHB in *.
  set (I := f + 160 + 136 * i) in *.
  destruct c32 as [| | | |k32 b32]; try discriminate S32. destruct c72 as [| | | |k72 b72]; try discriminate S72. destruct c112 as [| | | |k112 b112]; try discriminate S112.
  cbn [csize] in S32, S72, S112. subst k32 k72 k112.
  pose proof (munch_refl [(I + 56, I + 65)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EI : bv_unsigned (Z_to_bv 64 I) = I) by (apply unsigned_lit; lia).

  ls. ls.

  zstep. zstep. zstep. zstep. zstep.
  apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. eassumption.
Qed.

Lemma imp_walk4c : forall (usp sp' f A8 i : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) Fr fc (m : mem),
  evt asegs (eq (ctor_st e_asan_memset (Z_to_bv 64 IMP_MS3RET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (f + 160 + 136 * i + 72)) (Z_to_bv 64 0) (Z_to_bv 64 36) a3 a4 a5 a6 a7
                 f A8 (Z_to_bv 64 (f + 160 + 136 * i + 72)) (Z_to_bv 64 (f + 160 + 136 * i)) (136 * i) t3 t4 t5 t6 Fr fc m))
    (ctor_st IMP_MS2RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 (Z_to_bv 64 (f + 160 + 136 * i + 72)) (Z_to_bv 64 (f + 160 + 136 * i)) (136 * i)
       t3 t4 t5 t6 Fr fc m).
Proof.
  intros. unfold ctor_st, IMP_MS2RET_A, IMP_MS3RET_A, e_asan_memset, TPV_A, shad, SHB in *.
  zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma imp_walk4d : forall (usp sp' f A8 i : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 : word) Fr fc (m : mem),
  0 <= i <= 3 ->
  evt asegs (eq (ctor_st (if Z.ltb i 3 then IMP_CTORS_A else IMP_CTORS_END_A) x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7
                 f A8 s2x s7x (136 * (i + 1)) t3 t4 t5 t6 Fr fc m))
    (ctor_st IMP_MS3RET_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x s7x (136 * i) t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros IR. unfold ctor_st, IMP_MS3RET_A, IMP_CTORS_A, IMP_CTORS_END_A, TPV_A, shad, SHB in *.
  zstep. replace (136 * i + 136) with (136 * (i + 1)) by lia.
  assert (C : i < 3 \/ i = 3) by lia. destruct C as [C|C].
  - rewrite (proj2 (Z.ltb_lt i 3) C). step. if_cases K; zify_cond K; [| exfalso; lia]. apply evt_done. cbv delta [mkR]. reflexivity.
  - subst i. cbn [Z.ltb]. step. if_cases K; zify_cond K; [exfalso; lia|]. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Definition imp_localsL (j0 j8 : list byte) (f : Z) (szw : word) (d : Z) (ne : Z) (j160 j192 : list byte) : list cell :=
  [CB 8 j0; CB 16 j8; C8 (Z_to_bv 64 (f + 96)); C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 (f + 832)); C8 (Z_to_bv 64 (shad f + 20)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f);
   C8 (Z_to_bv 64 1);
   C8 (Z_to_bv 64 (f + 832 + 112)); C8 (Z_to_bv 64 (f + 832 + 16)); C8 (Z_to_bv 64 (f + 832 + 8)); C8 (Z_to_bv 64 (shad f + 12));
   C8 szw; C8 (Z_to_bv 64 (f + 32)); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 (f + 1168)); C8 (Z_to_bv 64 (f + 160)); C8 (Z_to_bv 64 ne);
   CB 24 j160; C8 (Z_to_bv 64 f); CB 24 j192].
Lemma imp_localsL_size : forall j0 j8 f szw d ne j160 j192, cells_size (imp_localsL j0 j8 f szw d ne j160 j192) = 216%nat.
Proof. intros. reflexivity. Qed.

Definition imp_W5 (sp' f : Z) : list ivl := [(sp' + 24, sp' + 32); (sp' + 80, sp' + 112); (sp' + 144, sp' + 160); (f + 160, f + 168)].

Lemma imp_walk5 : forall (usp sp' f lo d n A8 : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x t3 t4 t5 t6 : word) (w0 : word)
    (j0 j8 j80 j144 j192 : list byte) Fr fc (m : mem),
  0 < f -> f + 2048 <= lo -> shad f + 156 <= lo -> 0 <= shad f ->
  0x6a9000 <= lo -> lo <= sp' -> sp' + 216 <= usp - 104 -> usp < 2^63 -> 0 <= d < 2^64 -> 0 <= n < 2^64 -> 0 < A8 -> A8 + 8 <= lo -> A8 mod 8 = 0 ->
  rw_cells asegs m sp' (imp_locals3 j0 j8 f j80 (Z_to_bv 64 n) d j144 j192) ->
  ro_cells asegs m A8 [C8 (Z_to_bv 64 SJ_SINGLETON)] ->
  ro_cells asegs m (shad A8) [C1 z8] ->
  ro_cells asegs m (shad f + 20) [C1 z8] ->
  rw_cells asegs m (f + 160) [C8 w0] ->
  mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (j8a j160 : list byte),
      ms = imp_regsA e_getact (Z_to_bv 64 IMP_GARET_A) sp' gp t0 t1 t2 usp (Z_to_bv 64 (shad f + 12)) (Z_to_bv 64 (f + 96)) (Z_to_bv 64 (shad A8 + 1)) (Z_to_bv 64 (f + 160 + 136))
             (Z_to_bv 64 SJ_SINGLETON) a5 a6 a7 f (Z_to_bv 64 SJ_SINGLETON) (Z_to_bv 64 n) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 d) t3 t4 t5 t6 Fr fc m1
      /\ munch (imp_W5 sp' f) m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ rw_cells asegs m1 sp' (imp_localsL j0 j8a f (Z_to_bv 64 n) d 0 j160 j192)
      /\ rw_cells asegs m1 (f + 160) [C8 (Z_to_bv 64 SJ_SINGLETON)])
    (ctor_st IMP_CTORS_END_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x (Z_to_bv 64 (f + 160 + 136 * 3)) (136 * (3 + 1)) t3 t4 t5 t6 Fr fc m).
Proof.
  intros until m. intros F0 FLO SLO SH0 GLO LSP LUSP SPH DR NR A0 AH A8M FRl VW VS FS20 FI MI.
  unfold ctor_st, imp_regsA, imp_W5, imp_locals3, imp_localsL, IMP_CTORS_END_A, IMP_LOOP_A, IMP_GARET_A, e_getact, SJ_SINGLETON, TPV_A, shad, SHB in *.
  change (136 * (3 + 1)) with 544 in *. replace (f + 160 + 136 * 3) with (f + 568) in * by lia.

  replace (f / 8 + 2147450880 + 20) with (f / 8 + 2147450900) in * by lia.
  replace (f / 8 + 2147450880 + 12) with (f / 8 + 2147450892) in * by lia.
  replace (A8 / 8 + 2147450880 + 1) with (A8 / 8 + 2147450881) in * by lia.

  apply (rw_cells_split_CB asegs _ _ [CB 8 j0] 24 j8 _ [16; 8]%nat) in FRl; [| reflexivity]. cbn [mk_CB_cells app] in FRl.
  lazymatch type of FRl with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: CB 32 j80 :: ?rest) =>
    apply (rw_cells_split_CB asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8] 32 j80 rest [8; 8; 8; 8]%nat) in FRl; [| reflexivity]; cbn [mk_CB_cells app] in FRl end.
  lazymatch type of FRl with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: CB 40 j144 :: ?rest) =>
    apply (rw_cells_split_CB asegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] 40 j144 rest [8; 8; 24]%nat) in FRl; [| reflexivity];
    cbn [mk_CB_cells app] in FRl end.
  repeat match type of FRl with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let jj := fresh "j" in set (jj := t) in FRl; clearbody jj end.
  pose proof (munch_refl [(sp' + 24, sp' + 32); (sp' + 80, sp' + 112); (sp' + 144, sp' + 160); (f + 160, f + 168)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 A8) = A8) by (apply unsigned_lit; lia).

  zstep. zstep. step. if_cases K; zify_cond K; [exfalso; lia|].

  zstep. rewrite shr3_div. zstep. zstep. replace (2147450880 + A8 / 8) with (A8 / 8 + 2147450880) by lia.
  zstep. zstep. zstep. zstep. zstep.

  zstep. cbv beta. rewrite lbu_z8. zstep. if_false.
  zstep. rewrite shr3_div. zstep. replace ((f + 160) / 8 + 2147450880) with (f / 8 + 2147450900) by (Z.div_mod_to_equations; lia).
  zstep. cbv beta. rewrite lbu_z8. zstep. if_false.

  zstep. zstep. zstep. zstep. ls. zstep. zstep. step. if_cases K2; zify_cond K2; [exfalso; lia|].

  ls. zstep. ls. zstep. zstep. zstep. ls. zstep. ls. zstep. ls.

  zstep. zstep. zstep. ls. zstep. rewrite shr3_div. zstep. replace ((f + 96) / 8 + 2147450880) with (f / 8 + 2147450892) by (Z.div_mod_to_equations; lia).
  ls. zstep.

  zstep. zstep. try replace (f + 160 + 0) with (f + 160) by lia. zstep. zstep.
  apply evt_done. eexists _, _, _. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [| eassumption]. eassumption.
Qed.

