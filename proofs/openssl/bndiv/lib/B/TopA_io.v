(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_main R_m2s R_thread R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs I_consts I_qck F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf X_xdefs X_open X_close X_exit D_libkit RT_state RT_rep RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs D_trpro D_atiface D_trdefs X_atreg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.          (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ro_cells_app' : forall (m : mem) A cs1 cs2,
  ro_cells bsegs m A (cs1 ++ cs2) <-> ro_cells bsegs m A cs1 /\ ro_cells bsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold ro_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, bytes_at_app.
  split.
  - intros ((W1 & W2) & (B1 & B2)). rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros ((W1 & B1) & (W2 & B2)). rewrite (cells_bytes_length cs1 W1). tauto.
Qed.

Lemma ro_split1 : forall (m : mem) A c cs, ro_cells bsegs m A (c :: cs) ->
  ro_cells bsegs m A [c] /\ ro_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply ro_cells_app' in H as [H1 H2].
  split; [exact H1|]. cbn [cells_size] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

Lemma ro_join1 : forall (m : mem) A c cs, ro_cells bsegs m A [c] -> ro_cells bsegs m (A + Z.of_nat (csize c)) cs ->
  ro_cells bsegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. change (c :: cs) with ([c] ++ cs). apply ro_cells_app'. split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

Lemma stk_sub' : forall (m : mem) lo hi a b, stk bsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk bsegs m a b.
Proof.
  intros m lo hi a b H H1 H2 H3. destruct (stk_split bsegs m lo a hi H ltac:(lia)) as [_ H4].
  destruct (stk_split bsegs m a b hi H4 ltac:(lia)) as [H5 _]. exact H5.
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
  pose proof (io_ro_at m IO 0x5e1958 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0x5e0bc8 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x44540 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x210c0 128 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub bsegs m 0x44540 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub bsegs m 0x210c0 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

(* [comment removed for export] *)
Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (io_rw_at m IO 0x5e3d40 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0x56a398); C8 (Z_to_bv 64 0x55e48c); C8 (Z_to_bv 64 0x55e8ec)]
    with ([C8 (Z_to_bv 64 0x56a398)] ++ [C8 (Z_to_bv 64 0x55e48c)] ++ [C8 (Z_to_bv 64 0x55e8ec)]) in R1. apply F_fwritex.rw_cells_app in R1 as [R1 R2]. apply F_fwritex.rw_cells_app in R2 as [_ R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0xbc6040 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x44540 128 ltac:(io_in)) | exact (io_acc_at m IO 0x210c0 128 ltac:(io_in))].
Qed.

(* [comment removed for export] *)
Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0x56b3f0 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x5e2c70 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x5e0ca8 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0x5e3ce0); exact (io_ro_at m IO 0x5e3ce0 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x6a1210 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0x6a12b0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact (ro_of_rw _ _ _ T1)|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x7358a0 _ ltac:(io_in))|].
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x80177a00) by reflexivity.
  rewrite E1, E2 in SHW. exact SHW.
Qed.

(* [comment removed for export] *)
Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
  pose proof (io_ro_at m IO 0x5e3d80 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x210c0 128 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x73557c _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x1d8ea 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x121e9 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1134e8 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x48d09 7 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x210ec 17 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x3d197 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x3d1ac 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x2ef35 33 ltac:(io_in)).
Qed.


End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem main_rta : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  forall (LIBA : rts RTA -> list (Z * Z) -> mem -> Prop), init_cps RTA LIBA -> fuzz_one_cps' RTA LIBA -> liba_frame RTA LIBA -> liba_exit RTA LIBA ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA XENVA lib_startA argvb fs c -> realizes bsegs c (canonT (argv_Z argvb) fs).
Proof.
  intros RC IOC LIBA INIT FUZZ LFR LEX argvb fs VARGV.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENV_FPA1 XENVA2 LIBA argvb fs AF AF_DRV
           (malloc_contract_ok_of RTA (rc_malloc RTA RC)) (free_contract_ok_of RTA (rc_free RTA RC)) (free_null_contract_ok_of RTA (rc_free_null RTA RC)) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF)
           (exit_ok0 RTA AF AF_XIT lib_startA lib_startA_exit) (exit_ok1 RTA AF AF_XIT lib_exit_cells (fun m H => H))
           (atexit_ok RTA AF)
           INIT FUZZ LFR LEX VARGV OUT_locA ERR_locA XENV_locA IO_imgA XENV_imgA XENV1_locA1 XENV2_locA XENV1_imgA
           (fun m H => proj2 H) (fun m H I0 => conj H I0) INCB_offA ATXW_offA).
Qed.

(* [comment removed for export] *)
