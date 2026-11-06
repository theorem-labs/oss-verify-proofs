(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_state RT_rep RT_facts0 RT_sep RT_facts RT_artfacts
  RT_malcore_stmt RT_refillstmt RT_sys_stmt RT_sys_fixed RT_sys_grant RT_sys_madvise RT_sys_munmap RT_refill RT_contracts RT_malsec
  RT_freestmt RT_drain_ldefs RT_drain_istmt RT_drain_fin RT_freeFin RT_dsec RT_malcore_m RT_malloc RT_calcore_m RT_calloc
  RT_stackmalloc RT_stackfree6 RT_iclifts RT_io R_isPoisoned TopA_io I_vsnlift_lept RT_traces RT_gaps_iface D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RF_ok : refill_stmt := refill_ok fixed_commit_ok.
Definition CS_ok : core_stmt_sec := mal_core_sec grant_node_ok fixed_commit_pab_ok.
Definition DR_ok : drain_stmt := drain_ok fixed_commit_ok ((fun MN AN p HOK => item_sec_ok p MN AN HOK) munmap_ok madvise_ok).

Theorem rta_rc : rt_contracts RTA.
Proof. exact (rta_contracts RF_ok CS_ok (rta_free DR_ok fixed_commit_ok)). Qed.

(* [comment removed for export] *)
Lemma gpA_malloc : malloc_contractC RTA.
Proof. exact (rta_mallocC (core_prim RF_ok) CS_ok). Qed.

Lemma gpA_free : free_contractC RTA.
Proof. exact (rta_freeC DR_ok fixed_commit_ok). Qed.

Lemma gpA_calloc : calloc_contract RTA.
Proof. exact (rta_calloc (core_prim0 RF_ok)). Qed.

Lemma gpA_stack_malloc : forall k, In k [0%nat; 1%nat; 4%nat; 6%nat] -> stack_malloc_contract' RTA k.
Proof. intros k [<-|[<-|[<-|[<-|[]]]]]; [exact rta_stack_malloc_0 | exact rta_stack_malloc_1 | exact rta_stack_malloc_4 | exact rta_stack_malloc_6]. Qed.

Lemma gpA_stack_free_6 : stack_free_contract RTA.
Proof. exact rta_stack_free_6. Qed.

Lemma gpA_vsnprintf : vsnprintf_lept_icontract RTA.
Proof. exact (vsnprintf_lept_ok RTA rta_art_facts rip_proof rta_shw (rta_pf rta_io) (rta_vsn rta_io)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pair_inb (r : Z * Z) (l : list (Z * Z)) : bool := existsb (fun q => (fst q =? fst r) && (snd q =? snd r)) l.
Lemma pair_inb_sound : forall r l, pair_inb r l = true -> In r l.
Proof.
  intros [a n] l H. unfold pair_inb in H. apply existsb_exists in H as ([a' n'] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst. exact Hin.
Qed.

Lemma lept_lits_incl : forallb (fun r => pair_inb r ACC_LITS) LEPT_LITS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma gpA_acc_lits : forall Σ m, ART RTA Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_LITS.
Proof.
  intros Σ m HA. pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F |- *. intros r Hr. apply F.
  apply pair_inb_sound. exact (proj1 (forallb_forall _ _) lept_lits_incl r Hr).
Qed.

Lemma gpA_acc_globals : forall Σ m, ART RTA Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_GLOBALS.
Proof.
  intros Σ m HA. unfold LEPT_GLOBALS.
  repeat (apply Forall_cons; [cbv beta; cbn [fst snd]|]); [| | | | apply Forall_nil].
  - apply (rta_acc_static_cs Σ m HA (0x1c81f0, 0x1c8424)); [unfold CS_ACC; cbn; tauto | cbn; lia | cbn; lia].
  - apply (rta_acc_static_cs Σ m HA (0x1c8440, 0x1c8448)); [unfold CS_ACC; cbn; tauto | cbn; lia | cbn; lia].
  - apply (rta_acc_static_cs Σ m HA (0x1c8480, 0x1c8488)); [unfold CS_ACC; cbn; tauto | cbn; lia | cbn; lia].
  - apply (rta_acc_static_cs Σ m HA (0x1c84a0, 0x1c84a8)); [unfold CS_ACC; cbn; tauto | cbn; lia | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma client_static_range : forall lo hi a, lo <= a < hi ->
  existsb (fun r => (fst r <=? lo) && (hi <=? snd r)) CLIENT_STATIC = true ->
  forallb (fun r => (hi <=? fst r) || (snd r <=? lo)) RT_STATIC = true -> client_static a.
Proof.
  intros lo hi a Ha H1 H2. split.
  - apply existsb_exists in H1 as ([l h] & Hin & E). cbn [fst snd] in E. apply andb_prop in E as [E1 E2].
    apply Z.leb_le in E1, E2. exists l, h. split; [exact Hin | lia].
  - intros (l & h & Hin & Hr). pose proof (proj1 (forallb_forall _ _) H2 (l, h) Hin) as E. cbn [fst snd] in E.
    apply orb_prop in E as [E|E]; apply Z.leb_le in E; lia.
Qed.

Lemma gpA_globals_client : forall a, in_ranges (map (fun r => (fst r, fst r + snd r)) LEPT_GLOBALS) a -> client_static a.
Proof.
  intros a (lo & hi & Hin & Hr). unfold LEPT_GLOBALS in Hin. cbn [map fst snd] in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-;
    (eapply client_static_range; [exact Hr | vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.

Lemma gpA_got_lib : forall Σ m, ART RTA Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0x1c8420)].
Proof. intros Σ m HA. exact (proj1 (rta_got_lib Σ m HA)). Qed.

Lemma gpA_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RTA Σ' m' ->
  (forall a : word, client_static (bv_unsigned a) -> m' a = m a) -> io_ssp m'.
Proof.
  intros Σ' m m' (g & _ & G2) HA AG. exists g. split; [exact (proj2 (rta_got_lib Σ' m' HA))|].
  apply (D_kit.ro_cells_agree asegs m m' _ _ G2). intros a Ha. apply AG. cbn [cells_size csize] in Ha.
  eapply (client_static_range 0x72c478 0x72c480); [lia | vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma gpA_live_hi : forall Σ m p n, ART RTA Σ m -> In (p, n) (rt_live RTA Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p.
Proof.
  intros Σ m p n HA Hin.
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn & -> & X1 & X5)].
  - pose proof (geo_grant Σ m HA (l_PRB (lay Σ)) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
    pose proof (geo_prb Σ m HA) as (P1 & P2 & _). unfold R_prim_defs.rb, kUserCap in X3, X4. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4.
    assert (0 <= c * 2 ^ 32 /\ c * 2 ^ 32 + 0xE0000000 <= 2 ^ 37) by lia. lia.
  - pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & (_ & _ & _ & G4 & _) & _).
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in G4. unfold s_ubeg. rewrite <- Hn in X1. lia.
Qed.

(* [comment removed for export] *)
Lemma gpA_acc_rmask : forall Σ m, ART RTA Σ m -> acc asegs m LEPT_RMASK32 132.
Proof.
  intros Σ m HA. pose proof (rta_acc_lits Σ m HA) as F. rewrite Forall_forall in F.
  apply (F (LEPT_RMASK32, 132)). apply pair_inb_sound. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem rta_gaps : rt_gaps RTA.
Proof.
  exact (mkGaps RTA gpA_malloc gpA_free gpA_calloc
           (gpA_stack_malloc 0%nat ltac:(cbn; tauto)) (gpA_stack_malloc 1%nat ltac:(cbn; tauto)) (gpA_stack_malloc 4%nat ltac:(cbn; tauto)) (gpA_stack_malloc 6%nat ltac:(cbn; tauto))
           gpA_stack_free_6 gpA_vsnprintf gpA_acc_lits gpA_acc_globals gpA_globals_client gpA_got_lib gpA_ssp_keep gpA_live_hi gpA_acc_rmask).
Qed.

(* [comment removed for export] *)
