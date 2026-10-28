(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface R_m2s R_setshadow R_poison R_tlsgetaddr RT_state RT_rep RT_facts0 RT_facts RT_sep TopA_iodefs RT_io RT_iclifts D_clx I_memcpyw F_fwritex X_ixdefs X_ixdefs2 Imp_ios_exitA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.

Local Ltac flatten H := repeat match type of H with _ /\ _ => let H1 := fresh "K" in destruct H as [H1 H] end.
Local Ltac flatten_all := repeat match goal with
  | K : _ /\ _ |- _ => let H1 := fresh "K" in let H2 := fresh "K" in destruct K as [H1 H2]
  | K : exists _ : Z, _ |- _ => let H1 := fresh "K" in destruct K as [? H1] end.

Theorem rta_iosx : forall Σ m, ART_A Σ m -> iosx_img_facts m.
Proof.
  intros Σ m HA. pose proof (rta_io Σ m HA) as IO. unfold iosx_img_facts.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); apply (io_rw_at m IO); io_in.
Qed.

Theorem rta_ixit : forall Σ m, ART_A Σ m -> ixit_rt (rtA_sp0 Σ) m.
Proof.
  intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as C. unfold consts_rep, icells_rep in C. flatten C. flatten_all.
  pose proof (ART_fs Σ m HA) as FS. unfold fs_rep in FS. flatten FS. flatten_all. unfold tga_cells in *. flatten_all.
  pose proof (rta_mtab Σ m HA) as (M1 & M2 & M3 & M4).
  pose proof (geo_grant Σ m HA (l_MT (lay Σ)) 0x38e000 ltac:(unfold startup_grants; do 8 right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  unfold ixit_rt, g_asan_inited, g_GOT_lsan_off, LSAN_CTR, g_GOT_flags, g_REAL_cxa_atexit, e_musl_cxa_atexit, g_REAL_fflush, e_musl_fflush,
    g_REAL_wcrtomb, e_musl_wcrtomb, g_GOT_mbstate_t_sz, g_mbstate_t_sz, g_flags_cio.
  split; [assumption|].
  split; [assumption|]. split; [assumption|].
  split; [assumption|].
  split; [apply (io_rw_at m IO); io_in|].
  split; [apply (io_rw_at m IO); io_in|].
  split; [apply (io_rw_at m IO); io_in|].
  split; [apply (io_ro_at m IO); io_in|]. split; [apply (io_rw_at m IO); io_in|].
  split; [apply (io_rw_at m IO); io_in|].
  split.
  { exists (l_MT (lay Σ)). unfold mtab_at, g_icpt_mdmap, g_mdmem, MT_SIZE, MT_OFF_OUT, MT_OFF_ERR.
    split; [exact M1|]. split; [exact M2|].
    unfold l_ACEIL, rtA_sp0 in *.
    split; [unfold SEGTOP_A in *; lia|]. split; [lia|]. split; [exact G2|].
    split; [exact M3 | exact M4]. }
  unfold g_flags_dco, g_GOT_verbosity, g_verbosity. replace (0x187178 + 96) with 0x1871d8 by reflexivity.
  split; [apply (io_ro_at m IO); io_in |].
  unfold dtls_cells in *.
  match goal with K : context [rw_cells bsegs m R_tlsgetaddr.g_got_verbosity _] |- _ => flatten K end.
  unfold R_tlsgetaddr.g_got_verbosity, R_tlsgetaddr.g_current_verbosity in *.
  split; [assumption|]. split; [assumption|].
  unfold ps_cells, m2s_cells, setshadow_cells, R_poison.g_got_common_flags, R_poison.g_can_poison, R_poison.g_cf_clear_shadow_mmap_threshold, R_setshadow.g_got_real_memset, R_setshadow.g_real_memset in *.
  repeat match goal with K : _ /\ _ |- _ => let H1 := fresh "K" in let H2 := fresh "K" in destruct K as [H1 H2] end.
  refine (conj _ (conj (conj _ (conj _ _)) (conj (conj _ _) (conj _ _)))); assumption.
Qed.

Theorem rta_xcells : forall Σ m, ART_A Σ m -> xcells (rtA_sp0 Σ) m.
Proof.
  intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
  pose proof (ART_consts Σ m HA) as C. unfold consts_rep, icells_rep in C. flatten C. flatten_all.
  pose proof (rta_ic Σ m HA) as (IC & _).
  pose proof (rta_sp0_range Σ m HA) as R1. pose proof (rta_sp0_win Σ m HA) as R2.
  unfold xcells, g_REAL_fwrite, e_musl_fwrite, g_GOT_REAL_memcpy, IOSBLK, IOSBLK_LEN.
  split; [split; [exact R2| lia]|].
  split.
  { pose proof (io_rw_at m IO 0x181d88 _ ltac:(io_in)) as R. change [C8 (Z_to_bv 64 0x178858); C8 (Z_to_bv 64 0x168e70)]
      with ([C8 (Z_to_bv 64 0x178858)] ++ [C8 (Z_to_bv 64 0x168e70)]) in R. apply (F_fwritex.rw_cells_app bsegs) in R as [_ R]. exact R. }
  split; [exact IC|].
  split; [assumption|].
  split.
  { apply (rta_acc_static Σ m _ _ HA); [lia|]. intros i Hi. split; [apply client_static_intro; lia| lia]. }
  apply (rta_acc_stack Σ m HA); unfold l_ACEIL, rtA_sp0 in *; lia.
Qed.

Theorem rta_ixit2 : forall Σ m, ART_A Σ m -> ixit2 (rtA_sp0 Σ) m.
Proof. intros Σ m HA. split; [exact (rta_ixit Σ m HA)| exact (rta_xcells Σ m HA)]. Qed.

End GWIN.
