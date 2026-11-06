(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import ImageA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import Layout.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.K5.B16 Require Import RT_iface D_iface D_defs D_kit D_libiface D_clx D_main R_m2s R_thread R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs I_consts I_qck F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf I_vsnw2 X_xdefs X_open X_close X_exit RT_state RT_rep RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma wr_at_app : forall (m : mem) a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at asegs m a (n1 + n2) <-> wr_at asegs m a n1 /\ wr_at asegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : forall (m : mem) A cs1 cs2,
  rw_cells asegs m A (cs1 ++ cs2) <-> rw_cells asegs m A cs1 /\ rw_cells asegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

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
  pose proof (io_ro_at m IO 0xc9d68 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0xc9000 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x21300 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x16000 192 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub asegs m 0x21300 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub asegs m 0x16000 192 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

(* [comment removed for export] *)
Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (io_rw_at m IO 0xcaea0 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0xc4b48); C8 (Z_to_bv 64 0xbba4c)]
    with ([C8 (Z_to_bv 64 0xc4b48)] ++ [C8 (Z_to_bv 64 0xbba4c)]) in R1. apply rw_cells_app in R1 as [R1 R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0x5f4d40 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x21300 128 ltac:(io_in)) | apply (acc_sub asegs m 0x16000 192 0x16040 128 (io_acc_at m IO 0x16000 192 ltac:(io_in))); lia].
Qed.

(* [comment removed for export] *)
Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0xc5cc8 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xc9e10 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xc90d8 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0xcae60); exact (io_ro_at m IO 0xcae60 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xc9d88 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ G1)|].
  split.
  { apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
    change [C8 (Z_to_bv 64 0xd26f8); C8 (Z_to_bv 64 0xd33e8); C8 (Z_to_bv 64 0xd33f0); C8 (Z_to_bv 64 0xd33e0); C8 (Z_to_bv 64 0xcafe0)]
      with ([C8 (Z_to_bv 64 0xd26f8); C8 (Z_to_bv 64 0xd33e8); C8 (Z_to_bv 64 0xd33f0); C8 (Z_to_bv 64 0xd33e0)] ++ [C8 (Z_to_bv 64 0xcafe0)]).
    apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
  split; [exact (io_ro_at m IO 0xcff10 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0xcffb0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x1645a0 _ ltac:(io_in))|].
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = 0x800bd000) by reflexivity.
  rewrite E1, E2 in SHW.
  split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
  split; [apply (stk_sub' m _ _ _ _ SHW); lia|].
  apply (stk_sub' m _ _ _ _ SHW); lia.
Qed.

(* [comment removed for export] *)
Lemma rta_pf : forall Σ m, ART RTA Σ m -> pf_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & (P1 & _) & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (rta_ic Σ m HA) as (IC1 & IC2 & _ & IC4 & IC5).
  pose proof (io_ro_at m IO 0xcaec8 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x16000 192 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x16427c _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x14d2d 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x10cbe 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x26f38 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x2231d 7 ltac:(io_in))|].
  split; [apply (acc_sub asegs m 0x16000 192 0x16033 17 B2); lia|].
  split; [exact (io_acc_at m IO 0x1ed4d 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1ed62 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x1a6f1 33 ltac:(io_in)).
Qed.

(* [comment removed for export] *)
Lemma rta_vsn : forall Σ m, ART RTA Σ m -> vsncells m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (io_ro_at m IO 0xcaec8 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [_ V2]. apply ro_split1 in V2 as [_ V3].
  exact V3.
Qed.

End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LIB_locA : fp_local LIB_FP LIB_A.
Proof.
  intros m m' ((V1 & V2 & V3) & (h & V4)) AG. split; [split; [|split]|].
  - apply (rw_cells_agree_nw asegs m m' _ _ V1). intros a Ha. apply AG.
    exists 0xcd720, 0xcd724. split; [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
  - apply (rw_cells_agree_nw asegs m m' _ _ V2). intros a Ha. apply AG.
    exists 0xcd760, 0xcd768. split; [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
  - apply (rw_cells_agree_nw asegs m m' _ _ V3). intros a Ha. apply AG.
    exists 0xcd780, 0xcd788. split; [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
  - exists h. apply (rw_cells_agree_nw asegs m m' _ _ V4). intros a Ha. apply AG.
    exists 0xcd740, 0xcd748. split; [cbn; tauto|]. cbn [cells_size csize] in Ha. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem main_rta : fuzz_one_cps RTA LIB_A -> rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA XENVA LIB_A argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof.
  intros FUZZ RC IOC argvb fs VARGV.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENVA1x LIB_A argvb fs AF AF_DRV
           (rc_malloc RTA RC) (rc_free RTA RC) (rc_free_null RTA RC) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF) (exit_ok RTA AF AF_XIT) (exit_ok1 RTA AF AF_XIT) XENVA1x_of
           FUZZ VARGV OUT_locA ERR_locA XENV_locA XENV_locA1 LIB_locA IO_imgA XENV_imgA XENVA_reg_out XENVA_reg_in REG_fpA).
Qed.

(* [comment removed for export] *)
