(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_iface D_defs D_kit D_libiface D_clx D_main R_m2s R_thread R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs I_consts I_qck F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf X_xdefs X_open X_close X_exit L_libA RT_state RT_rep RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require F_fwritex.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_clx.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_main.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_achk.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_fwrite.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_vprintfw.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_vprintf.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_fprintf.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_xdefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_open.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_close.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.X_exit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iclifts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_isPoisoned.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_iodefs.TwinB__.
(* [comment removed for export] *)          (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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
  assert (GSSP : ro_cells bsegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)]).
  { pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
    repeat match type of IC with _ /\ _ => let X := fresh "X" in destruct IC as [X IC] end.
    match goal with H : rw_cells bsegs m _ _ |- _ => exact (ro_of_rw _ _ _ H) end. }
  pose proof (io_ro_at m IO 0xcda98 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0xccd30 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x1f980 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x15940 128 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub bsegs m 0x1f980 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub bsegs m 0x15940 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

(* [comment removed for export] *)
Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (io_rw_at m IO 0xceb80 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0xcb868); C8 (Z_to_bv 64 0xc276c)]
    with ([C8 (Z_to_bv 64 0xcb868)] ++ [C8 (Z_to_bv 64 0xc276c)]) in R1. apply OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.F_fwritex.TwinB__.rw_cells_app in R1 as [R1 R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0x5f8b80 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x1f980 128 ltac:(io_in)) | exact (io_acc_at m IO 0x15940 128 ltac:(io_in))].
Qed.

(* [comment removed for export] *)
Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0xcc8c0 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xcdb00 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xcce08 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0xceb40); exact (io_ro_at m IO 0xceb40 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xcdac0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ G1)|].
  split.
  { apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
    change [C8 (Z_to_bv 64 0xd6538); C8 (Z_to_bv 64 0xd7228); C8 (Z_to_bv 64 0xd7230); C8 (Z_to_bv 64 0xd7220); C8 (Z_to_bv 64 0xcecb0)]
      with ([C8 (Z_to_bv 64 0xd6538); C8 (Z_to_bv 64 0xd7228); C8 (Z_to_bv 64 0xd7230); C8 (Z_to_bv 64 0xd7220)] ++ [C8 (Z_to_bv 64 0xcecb0)]).
    apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
  split; [exact (io_ro_at m IO 0xd3d50 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0xd3df0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x1683e0 _ ltac:(io_in))|].
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = ltac:(let v := eval vm_compute in (shad SEGTOP_A) in exact v)) by reflexivity.
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
  pose proof (io_ro_at m IO 0xceba0 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x15940 128 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x1680bc _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x148af 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x10bc0 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x234e0 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x20752 7 ltac:(io_in))|].
  split; [apply (acc_sub bsegs m 0x15940 128 0x1595e 17 B2); lia|].
  split; [exact (io_acc_at m IO 0x1d821 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1d836 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x197df 33 ltac:(io_in)).
Qed.


End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem main_rta : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA XENVA LIB_A argvb fs c -> realizes bsegs c (canonT (argv_Z argvb) fs).
Proof.
  intros RC IOC FUZZ argvb fs VARGV.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENVA1x LIB_A argvb fs AF AF_DRV
           (malloc_contract_ok_of RTA (rc_malloc RTA RC)) (free_contract_ok_of RTA (rc_free RTA RC)) (free_null_contract_ok_of RTA (rc_free_null RTA RC)) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF) (exit_ok RTA AF AF_XIT) (exit_ok1 RTA AF AF_XIT) XENVA1x_of
           FUZZ VARGV OUT_locA ERR_locA XENV_locA XENV_locA1 LIB_locA IO_imgA XENV_imgA XENVA_reg_out XENVA_reg_in REG_fpA).
Qed.

(* [comment removed for export] *)
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS NodesA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prelim Canon Stdio Prog.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_iface D_defs D_kit D_libiface D_clx D_main
  R_m2s R_thread R_prim_defs R_poison R_setshadow R_tlsgetaddr R_fs_defs
  I_consts I_qck F_achk I_iodefs I_read I_fwrite I_vprintfw I_vprintf I_fprintf X_xdefs X_open X_close X_exit
  L_libA RT_state RT_rep RT_facts0 RT_iclifts R_isPoisoned TopA_iodefs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require F_fwritex.          (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
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
  assert (GSSP : ro_cells asegs m GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)]).
  { pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
    repeat match type of IC with _ /\ _ => let X := fresh "X" in destruct IC as [X IC] end.
    match goal with H : rw_cells asegs m _ _ |- _ => exact (ro_of_rw _ _ _ H) end. }
  pose proof (io_ro_at m IO 0xc06b8 _ ltac:(io_in)) as G1. apply ro_split1 in G1 as [G1 G2].
  pose proof (io_ro_at m IO 0xbf950 _ ltac:(io_in)) as G3.
  pose proof (io_acc_at m IO 0x1f980 128 ltac:(io_in)) as B1. pose proof (io_acc_at m IO 0x15940 128 ltac:(io_in)) as B2.
  unfold drv_consts, stderr_cells. split; [split; [exact G1 | exact G3]|]. split; [exact GSSP|]. split; [exact G2|].
  split; [apply (acc_sub asegs m 0x1f980 128 S_SHORT 31 B1); unfold S_SHORT; lia|].
  apply (acc_sub asegs m 0x15940 128 S_OVER 31 B2); unfold S_OVER; lia.
Qed.

(* [comment removed for export] *)
Lemma rta_icpt : forall Σ m, ART RTA Σ m -> icpt_consts m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (io_rw_at m IO 0xc17a0 _ ltac:(io_in)) as R1. change [C8 (Z_to_bv 64 0xbe488); C8 (Z_to_bv 64 0xb538c)]
    with ([C8 (Z_to_bv 64 0xbe488)] ++ [C8 (Z_to_bv 64 0xb538c)]) in R1. apply F_fwritex.rw_cells_app in R1 as [R1 R2].
  unfold icpt_consts. split; [exact T1|]. split; [exact R1|]. split; [exact M2S|].
  split; [exact (io_acc_at m IO 0x5eb780 16 ltac:(io_in))|]. split; [exact R2|].
  split; [exact (io_acc_at m IO 0x1f980 128 ltac:(io_in)) | exact (io_acc_at m IO 0x15940 128 ltac:(io_in))].
Qed.

(* [comment removed for export] *)
Lemma rta_xit : forall Σ m, ART RTA Σ m -> xit_rt m.
Proof using IOC.
  intros Σ m HA. pose proof (IOC Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & _) & _ & (M1 & M2 & _) & (P1 & _ & (S1 & S2) & P3 & P4) & _ & _ & (_ & _ & _ & X4 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof (ART_shadow Σ m HA) as (_ & _ & SHW & _).
  unfold xit_rt.
  split; [exact (io_ro_at m IO 0xbf4e0 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xc0720 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xbfa28 _ ltac:(io_in))|].
  split; [exists (Z_to_bv 64 0xc1760); exact (io_ro_at m IO 0xc1760 _ ltac:(io_in))|].
  split; [exact (io_ro_at m IO 0xc06e0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ G1)|].
  split.
  { apply ro_join1; [exact (ro_of_rw _ _ _ P1)|]. apply ro_join1; [exact X4|].
    change [C8 (Z_to_bv 64 0xc9138); C8 (Z_to_bv 64 0xc9e28); C8 (Z_to_bv 64 0xc9e30); C8 (Z_to_bv 64 0xc9e20); C8 (Z_to_bv 64 0xc18d0)]
      with ([C8 (Z_to_bv 64 0xc9138); C8 (Z_to_bv 64 0xc9e28); C8 (Z_to_bv 64 0xc9e30); C8 (Z_to_bv 64 0xc9e20)] ++ [C8 (Z_to_bv 64 0xc18d0)]).
    apply ro_cells_app'. split; [exact (ro_of_rw _ _ _ M1)|]. exact (ro_of_rw _ _ _ S1). }
  split; [exact (io_ro_at m IO 0xc6950 _ ltac:(io_in))|].
  split; [exact (io_rw_at m IO 0xc69f0 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  split; [exact (ro_of_rw _ _ _ P3)|].
  split; [exact (ro_of_rw _ _ _ P4)|].
  split; [exact (ro_of_rw _ _ _ S2)|].
  split; [exact (io_ro_at m IO 0x15afe0 _ ltac:(io_in))|].
  assert (E1 : pg_dn (shad 0x10000) = 0x7fffa000) by reflexivity. assert (E2 : shad SEGTOP_A = ltac:(let v := eval vm_compute in (shad SEGTOP_A) in exact v)) by reflexivity.
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
  pose proof (io_ro_at m IO 0xc17c0 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [V1 V2]. apply ro_split1 in V2 as [V2 _].
  pose proof (io_acc_at m IO 0x15940 128 ltac:(io_in)) as B2.
  unfold pf_consts, pfcells. split.
  { split; [exact T1|]. split; [exact (ro_of_rw _ _ _ P1)|]. split; [exact (io_ro_at m IO 0x15acbc _ ltac:(io_in))|].
    split; [exact V1 | exact V2]. }
  split; [unfold ictx; split; [exact IC1|]; split; [exact IC2|]; split; [exact IC4 | exact IC5]|].
  split; [exact (io_acc_at m IO 0x148af 4 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x10bc0 10 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x235f0 16 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x20752 7 ltac:(io_in))|].
  split; [apply (acc_sub asegs m 0x15940 128 0x1595e 17 B2); lia|].
  split; [exact (io_acc_at m IO 0x1d821 21 ltac:(io_in))|].
  split; [exact (io_acc_at m IO 0x1d836 23 ltac:(io_in))|].
  exact (io_acc_at m IO 0x197df 33 ltac:(io_in)).
Qed.


End Consts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem main_rta : rt_contracts RTA -> (forall Σ m, ART RTA Σ m -> io_consts m) -> fuzz_one_cps RTA LIB_A ->
  forall argvb fs, valid_argv argvb ->
  forall c, START RTA OUT_repA ERR_repA XENVA LIB_A argvb fs c -> realizes asegs c (canonT (argv_Z argvb) fs).
Proof.
  intros RC IOC FUZZ argvb fs VARGV.
  pose proof (rc_facts RTA RC) as AF.
  pose proof (rip_proof) as RIP.
  pose proof (rta_drv AF IOC) as AF_DRV.
  pose proof (rta_icpt IOC) as AF_ICPT.
  pose proof (rta_xit IOC) as AF_XIT.
  pose proof (rta_pf IOC) as AF_PF.
  exact (main_realizesA RTA OUT_repA ERR_repA IO_FPA XENVA XENV_FPA XENVA1 XENVA1x LIB_A argvb fs AF AF_DRV
           (malloc_contract_ok_of RTA (rc_malloc RTA RC)) (free_contract_ok_of RTA (rc_free RTA RC)) (free_null_contract_ok_of RTA (rc_free_null RTA RC)) (rc_memcpy RTA RC)
           (read_file_ok RTA AF AF_ICPT RIP) (read_dir_ok RTA AF AF_ICPT)
           (fprintf_ok RTA AF RIP rta_shw AF_PF) (fwrite_ok RTA AF AF_ICPT) (vprintf_ok RTA AF RIP rta_shw AF_PF)
           (open_ok RTA AF) (open_refused_ok RTA AF) (close_ok RTA AF) (exit_ok RTA AF AF_XIT) (exit_ok1 RTA AF AF_XIT) XENVA1x_of
           FUZZ VARGV OUT_locA ERR_locA XENV_locA XENV_locA1 LIB_locA IO_imgA XENV_imgA XENVA_reg_out XENVA_reg_in REG_fpA).
Qed.

(* [comment removed for export] *)
