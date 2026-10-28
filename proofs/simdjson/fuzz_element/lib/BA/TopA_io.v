(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_iface D_defs D_kit D_libiface D_clx. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import D_main. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_consts I_qck. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf X_xdefs X_open X_close X_exit D_client RT_state RT_rep RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require F_fwritex.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.
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

Section Consts.
Hypothesis AF : art_facts RTA.
Hypothesis IOC : forall Σ m, ART RTA Σ m -> io_consts m.

Lemma rta_drv : forall Σ m, ART RTA Σ m -> drv_consts m.
Proof using AF IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (af_got_lib RTA AF Σ m HA) as (_ & GSSP).
  pose proof (io_ro_at m IO 0x16ae98 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0x16a128 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x21d40 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x16380 128 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub asegs m 0x21d40 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub asegs m 0x16380 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (io_rw_at m IO 0x16c098 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0x162fec); C8 (Z_to_bv 64 0x153924)]
    with ([C8 (Z_to_bv 64 0x162fec)] ++ [C8 (Z_to_bv 64 0x153924)]) in R1. apply (F_fwritex.rw_cells_app asegs) in R1 as [R1 R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0x696280 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x21d40 128 ltac:(io_in)) | exact (io_acc_at m IO 0x16380 128 ltac:(io_in))].
Qed.

Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0x164170 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x16b008 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x16a200 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0x16c048); exact (io_ro_at m IO 0x16c048 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0x16af20 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ G1)|].
  split.
  { apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
    change [C8 (Z_to_bv 64 0x173c38); C8 (Z_to_bv 64 0x174928); C8 (Z_to_bv 64 0x174930); C8 (Z_to_bv 64 0x174920); C8 (Z_to_bv 64 0x16c250)]
      with ([C8 (Z_to_bv 64 0x173c38); C8 (Z_to_bv 64 0x174928); C8 (Z_to_bv 64 0x174930); C8 (Z_to_bv 64 0x174920)] ++ [C8 (Z_to_bv 64 0x16c250)]).
    apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
  split; [exact (io_ro_at m IO 0x171450 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0x1714f0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x205ae0 _ ltac:(io_in))|].
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x800d1400) by reflexivity.
  rewrite E1, E2 in SHW.
  split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
  split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
  apply (stk_sub' m _ _ _ _ SHW); lia.
Qed.

Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
  pose proof (io_ro_at m IO 0x16c0c8 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x16380 128 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x2057bc _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x14ffe 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x10dd9 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x350b0 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x22e7d 7 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x16390 17 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1f5f2 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1f607 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x1ae0b 33 ltac:(io_in)).
Qed.

End Consts.

Theorem main_rta : forall CL : client_B, rt_contracts2 RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA XENVA (cl_LIB CL) argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof.
  intros CL RC2 IOC argvb fs VARGV. pose proof (rc2_rt RTA RC2) as RC.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA (cl_LIB CL) argvb fs AF AF_DRV
           (rc_malloc RTA RC) (rc_free RTA RC) (rc_free_null RTA RC) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF) (exit_ok RTA AF AF_XIT)
           (cl_fuzz CL RC2) VARGV OUT_locA ERR_locA XENV_lawsA (cl_loc CL) IO_imgA XENV_imgA).
Qed.

