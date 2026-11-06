(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Gq_thr_iface Gq_thr2_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Fixpoint zfill (zs : list Z) (j : nat) (k : nat) (v : Z) : list Z :=
  match k with O => zs | S k' => zfill (upd zs j v) (S j) k' v end.

Lemma upd_map : forall (zs : list Z) (n : nat) (v : Z), upd (map (Z_to_bv 64) zs) n (Z_to_bv 64 v) = map (Z_to_bv 64) (upd zs n v).
Proof. induction zs as [|z zs IH]; intros [|n] v; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma zfill_length : forall zs j k v, length (zfill zs j k v) = length zs.
Proof. intros zs j k; revert zs j; induction k as [|k IH]; intros zs j v; cbn; [reflexivity|]. rewrite IH, upd_length. reflexivity. Qed.

(* [comment removed for export] *)
Lemma qtab_fills : zfill (zfill (zfill (zfill (zfill (repeat 0 256) 0 45 0) 45 30 1) 75 40 2) 115 70 3) 185 71 4 = QTAB_VALS.
Proof. vm_compute. reflexivity. Qed.

Lemma u32s_zero256 : u32s (map (Z_to_bv 64) (repeat 0 256)) = repeat (Z_to_bv 8 0) (Z.to_nat (256 * 4)).
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition qfill1_exit (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (tab val : Z) (zs' : list Z) : machine_state -> Prop :=
  fun ms' => exists (a2' a3' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tab + 4 * val)) (Z_to_bv 64 (tab + 4 * val)) a2' a3' a4 a5 a6 a7
                  (Z_to_bv 64 val) s3 s4 s5 s6 s7 (Z_to_bv 64 val) s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F (Z_to_bv 64 0xa0490) fc None m' (seg_rom asegs)
    /\ munch [(tab, tab + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' tab (map (Z_to_bv 64) zs').

(* [comment removed for export] *)
Lemma qfill1_loop : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem)
    (tab pv val i : Z) (zs : list Z),
  Z.of_nat k = val - j -> 0 <= j -> (1 <= k)%nat -> val <= 256 -> 0 <= i < 256 ->
  u32arr asegs m tab (map (Z_to_bv 64) zs) -> Z.of_nat (length zs) = 256 -> acc asegs m tab 1024 ->
  0 < tab -> tab mod 16 = 0 -> tab + 1024 <= 2^47 -> (tab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tab) -> (tab + 1024 <= 0x10000 \/ SEGTOP_A <= tab) ->
  rw_cells asegs m pv [C4 (Z_to_bv 64 val)] -> 0 < pv -> pv mod 8 = 0 -> pv + 8 <= 2^47 -> (pv + 4 <= tab \/ tab + 1024 <= pv) ->
  mem_inv asegs m ->
  evt asegs (qfill1_exit ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s3 s4 (Z_to_bv 64 i) (Z_to_bv 64 pv) s7 s9 s10 t3 t4 t5 t6 F fc m tab val (zfill zs (Z.to_nat j) k i))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tab + 4 * j)) (Z_to_bv 64 (tab + 4 * j)) a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 val) s3 s4 (Z_to_bv 64 i) (Z_to_bv 64 pv) s7 (Z_to_bv 64 j) s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa0468) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s3 s4 s7 s9 s10 t3 t4 t5 t6 F fc m tab pv val i zs
    HK HJ HK1 HV HI UA UAL ACCT T0 T16 THI TSH TSEG PVC PV0 PV8 PVHI PVT MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(tab, tab + 1024)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0xa0478; 0xa0494; 0xa0490].
  (* [comment removed for export] *)
  unpark TSH. unpark PVT.
  pose proof (u32arr_store_ok asegs m tab (map (Z_to_bv 64) zs) j (wa (tab + 4 * j)) UA ltac:(rewrite length_map; lia) ltac:(f_equal; lia)) as SOK.
  zstep.
  assert (UA1 : u32arr asegs (write_to_mem m (wa (tab + 4 * j)) (le4 (Z_to_bv 64 i))) tab (map (Z_to_bv 64) (upd zs (Z.to_nat j) i)))
    by (rewrite <- upd_map; apply (u32arr_write asegs m tab (map (Z_to_bv 64) zs) j (Z_to_bv 64 i) UA); rewrite length_map; lia).
  clear UA. store_done. rename UA1 into UA.
  rewrite <- (upd_length zs (Z.to_nat j) i) in UAL.
  set (zs1 := upd zs (Z.to_nat j) i) in *.
  park TSH. park PVT.
  (* [comment removed for export] *)
  lwalk [0xa0468; 0xa0490].
  rewrite (sx32_small val) by lia.
  replace (tab + 4 * j + 4) with (tab + 4 * (j + 1)) by lia.
  destruct k as [|k].
  - assert (EJ : j + 1 = val) by lia. rewrite EJ in *.
    brF. apply evt_done. unfold qfill1_exit. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    subst zs1. replace (Z.to_nat (val - 1)) with (Z.to_nat j) by lia. cbn [zfill]. exact UA.
  - brT.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (zs := zs1); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold qfill1_exit in PO |- *.
      destruct PO as (a2' & a3' & m' & E & MU' & WM' & MI' & UA').
      exists a2', a3', m'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')|]. split; [exact MI'|].
      subst zs1. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in UA' by lia. exact UA'.
Qed.

(* [comment removed for export] *)
Definition qfill2_exit (ra sp gp tp t0 t1 t2 s0 s1 a2 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (tab : Z) (zs' : list Z) : machine_state -> Prop :=
  fun ms' => exists (a4' a5' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tab + 4 * 256)) (Z_to_bv 64 (tab + 4 * 256)) a2 (Z_to_bv 64 256) a4' a5' a6 a7
                  (Z_to_bv 64 257) s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
             F (Z_to_bv 64 0xa06c4) fc None m' (seg_rom asegs)
    /\ munch [(tab, tab + 1024)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' tab (map (Z_to_bv 64) zs').

(* [comment removed for export] *)
Lemma qfill2_loop : forall (k : nat) (j : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) F fc (m : mem)
    (tab nv : Z) (zs : list Z),
  Z.of_nat k = 256 - j -> 0 <= j -> (1 <= k)%nat -> 0 <= nv < 256 ->
  u32arr asegs m tab (map (Z_to_bv 64) zs) -> Z.of_nat (length zs) = 256 -> acc asegs m tab 1024 ->
  0 < tab -> tab mod 16 = 0 -> tab + 1024 <= 2^47 -> (tab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tab) -> (tab + 1024 <= 0x10000 \/ SEGTOP_A <= tab) ->
  mem_inv asegs m ->
  evt asegs (qfill2_exit ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 256) a6 a7 s3 (Z_to_bv 64 nv) s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m tab (zfill zs (Z.to_nat j) k nv))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tab + 4 * j)) (Z_to_bv 64 (tab + 4 * j)) (Z_to_bv 64 256) a3 a4 a5 a6 a7
             (Z_to_bv 64 (j + 1)) s3 (Z_to_bv 64 nv) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 SHB) t3 t4 t5 t6)
        F (Z_to_bv 64 0xa069c) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m tab nv zs
    HK HJ HK1 HNV UA UAL ACCT T0 T16 THI TSH TSEG MI.
  { lia. }
  unfold SEGTOP_A, SHB in *.
  pose proof (munch_refl [(tab, tab + 1024)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  park_disj.
  lwalk [0xa06b0; 0xa06c8; 0xa06c4].
  (* [comment removed for export] *)
  unpark TSH.
  pose proof (u32arr_store_ok asegs m tab (map (Z_to_bv 64) zs) j (wa (tab + 4 * j)) UA ltac:(rewrite length_map; lia) ltac:(f_equal; lia)) as SOK.
  zstep.
  assert (UA1 : u32arr asegs (write_to_mem m (wa (tab + 4 * j)) (le4 (Z_to_bv 64 nv))) tab (map (Z_to_bv 64) (upd zs (Z.to_nat j) nv)))
    by (rewrite <- upd_map; apply (u32arr_write asegs m tab (map (Z_to_bv 64) zs) j (Z_to_bv 64 nv) UA); rewrite length_map; lia).
  clear UA. store_done. rename UA1 into UA.
  rewrite <- (upd_length zs (Z.to_nat j) nv) in UAL.
  set (zs1 := upd zs (Z.to_nat j) nv) in *.
  park TSH.
  lwalk [0xa069c; 0xa06c4].
  swrap32_fix.
  replace (tab + 4 * j + 4) with (tab + 4 * (j + 1)) by lia.
  destruct k as [|k].
  - subst zs1. assert (EJ : j = 255) by lia. subst j.
    brF. apply evt_done. unfold qfill2_exit. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    cbn [zfill]. exact UA.
  - brT.
    replace (j + 2) with (j + 1 + 1) by lia.
    eapply evt_cut.
    + eapply (IH (j + 1)) with (zs := zs1); try eassumption; try lia.
    + intros ms' PO. apply evt_done. unfold qfill2_exit in PO |- *.
      destruct PO as (a4' & a5' & m' & E & MU' & WM' & MI' & UA').
      exists a4', a5', m'.
      split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')|]. split; [exact MI'|].
      subst zs1. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) in UA' by lia. exact UA'.
Qed.
