(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_iface D_defs D_kit D_libiface D_libiface_pem D_clx D_main R_m2s R_thread R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs I_consts I_qck F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf X_xdefs X_open X_close X_exit RT_state RT_rep RT_census RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require F_fwritex.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import HandoffLIB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ro_cells_app' : forall (m : mem) A cs1 cs2,
  ro_cells asegs m A (cs1 ++ cs2) <-> ro_cells asegs m A cs1 /\ ro_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_split1 : forall (m : mem) A c cs, ro_cells asegs m A (c :: cs) ->
  ro_cells asegs m A [c] /\ ro_cells asegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply ro_cells_app' in H as [H1 H2].
  split; [exact H1|]. cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma ro_join1 : forall (m : mem) A c cs, ro_cells asegs m A [c] -> ro_cells asegs m (A + Z.of_nat (csize c)) cs ->
  ro_cells asegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply ro_cells_app'. split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma stk_sub' : forall (m : mem) lo hi a b, stk asegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk asegs m a b.
Proof.
  intros m lo hi a b H H1 H2 H3. destruct (stk_split asegs m lo a hi H ltac:(lia)) as [_ H4].
  destruct (stk_split asegs m a b hi H4 ltac:(lia)) as [H5 _]. exact H5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consts.
Hypothesis AF : art_facts RTA.
Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

(* [comment removed for export] *)
Lemma rta_drv : forall Σ m, ART RTA Σ m -> drv_consts m.
Proof using AF IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (af_got_lib RTA AF Σ m HA) as (_ & GSSP).
  pose proof (io_ro_at m IO 0x5a5238 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0x5a44a8 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x44040 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x21280 128 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub asegs m 0x44040 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub asegs m 0x21280 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

(* [comment removed for export] *)
Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  (* [comment removed for export] *)
  pose proof (io_rw_at m IO 0x5a7620 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0x52d808); C8 (Z_to_bv 64 0x521b44); C8 (Z_to_bv 64 0x521fa4)]
    with ([C8 (Z_to_bv 64 0x52d808)] ++ [C8 (Z_to_bv 64 0x521b44)] ++ [C8 (Z_to_bv 64 0x521fa4)]) in R1.
  apply F_fwritex.rw_cells_app in R1 as [R1 R2]. apply F_fwritex.rw_cells_app in R2 as [_ R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0xb8f180 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x44040 128 ltac:(io_in)) | exact (io_acc_at m IO 0x21280 128 ltac:(io_in))].
Qed.

(* [comment removed for export] *)
Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0x52e860 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x5a6548 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x5a4588 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0x5a75c0); exact (io_ro_at m IO 0x5a75c0 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x5a6500 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ G1)|].
  split.
  { apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
    change [C8 (Z_to_bv 64 0x66cb38); C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820); C8 (Z_to_bv 64 0x5a77f0)]
      with ([C8 (Z_to_bv 64 0x66cb38); C8 (Z_to_bv 64 0x66d828); C8 (Z_to_bv 64 0x66d830); C8 (Z_to_bv 64 0x66d820)] ++ [C8 (Z_to_bv 64 0x5a77f0)]).
    apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
  split; [exact (io_ro_at m IO 0x66a350 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0x66a3f0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x6fe9e0 _ ltac:(io_in))|].
  (* [comment removed for export] *)
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x80170c00) by reflexivity.
  rewrite E1, E2 in SHW. exact SHW.
Qed.

(* [comment removed for export] *)
Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
  pose proof (io_ro_at m IO 0x5a7658 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x21280 128 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x6fe6bc _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x1dae0 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x121eb 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x11a1d0 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x488e8 7 ltac:(io_in))|].
  split; [apply (acc_sub asegs m 0x21280 128 0x212a2 17 B2); lia|].
  split; [exact (io_acc_at m IO 0x3cc6f 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x3cc84 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x2ef43 33 ltac:(io_in)).
Qed.

End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma LIB_D_FP : forall x, in_ranges LIB_D x -> in_ranges LIB_FP x.
Proof.
  intros x (lo & hi & Hin & Hx). exists lo, hi. split; [| exact Hx].
  unfold LIB_D in Hin. unfold LIB_FP. cbn in Hin |- *. tauto.
Qed.

Lemma LIBpre_loc : forall C : cli_sigA, lib0_local_d (ca_lib0 C) -> fp_local LIB_FP (LIBpre C).
Proof.
  intros C LOC0 m m' [L0 LT] AG. split.
  - apply (LOC0 m m' L0). intros a Ha. apply AG. apply LIB_D_FP. exact Ha.
  - apply (rw_cells_agree_nw asegs m m' _ _ LT). intros a Ha. apply AG.
    exists 0xb9f190, 0xb9f191. split; [unfold LIB_FP; cbn; tauto|]. unfold TR_INIT in Ha. cbn [cells_size csize] in Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma XENVA_fp_ax : forall x, (0xbc3f40 <= x < 0xbc3f70 \/ 0xbc4060 <= x < 0xbc4070 \/ x = TR_INCB) -> in_ranges XENV_FPA x.
Proof.
  intros x Hx. unfold XENV_FPA, TR_INCB in *.
  destruct Hx as [Hx|[Hx|Hx]].
  - exists 0xbc3f40, 0xbc3f70. split; [cbn; tauto| lia].
  - exists 0xbc4060, 0xbc4070. split; [cbn; tauto| lia].
  - exists 0xb9f194, 0xb9f195. split; [cbn; tauto| lia].
Qed.

(* [comment removed for export] *)
Theorem main_rta : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  forall C : cli_sigA,
  fuzz_init_cps RTA (ca_lib0 C) (ca_lib C) (ca_sites C) (ca_calls C) -> fuzz_one_cps RTA (ca_lib C) (ca_sites C) (ca_calls C) ->
  lib0_local_d (ca_lib0 C) -> lib_local_d (ca_lib C) -> cg_has CENSUS (ca_sites C) (ca_calls C) ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA (XENVA false) (LIBpre C) CENSUS argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof.
  intros RC IOC C INITC FUZZC LOC0 LOCP CGH argvb fs VARGV.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA (XENVA false) XENV_FPA (LIBpre C) CENSUS (ca_lib0 C) (ca_lib C) (ca_sites C) (ca_calls C) argvb fs AF AF_DRV
           (rc_malloc RTA RC) (rc_free RTA RC) (rc_free_null RTA RC) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF) (exit_ok RTA AF AF_XIT false)
           INITC FUZZC VARGV OUT_locA ERR_locA (XENV_locA false) (LIBpre_loc C LOC0) IO_imgA XENV_imgA
           (XENVA true) (XENV_locA true) (XENVA_ax false) (XENVA_libc false) (XENVA_incb false) XENVA_step XENVA_fp_ax
           (XENVA_ax true) (XENVA_incb true) (XENVA_upd true) (exit_ok RTA AF AF_XIT true)
           (LIBpre_pre C) LOC0 LOCP CGH).
Qed.
