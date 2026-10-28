(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_libiface_pem D_agree D_clx PLayout Fz_kit Fz_ckit I_ut Fz_M_malloc Fz_env Fz_M_secure Th_mutex Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_rep Fz_W5_agr Fz_W2_exdc Fz_W2_bnew Fz_W3_iface Fz_W5_env.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

Definition LIB_A (CL : list (Z * Z)) (m : mem) : Prop :=
  Forall (fun p => ro_cells asegs m (fst p) (snd p)) CL_RO /\ rw_cells asegs m G_ALLOW_CUST [C1 (Z_to_bv 8 1)] /\ sec_off m
  /\ exists (E : Z) (LBL : list (Z * Z)), libenv_core m LBL E /\ errst_at_rest E [] m /\ In (E, 904) CL /\ incl_live LBL CL /\ ~ In (E, 904) LBL.
Definition REST_A (m : mem) : Prop := True.
Definition REST_A_fp (a : Z) : Prop := False.
Lemma REST_A_agree : forall m m', REST_A m -> agree_on REST_A_fp m m' -> REST_A m'.
Proof. intros; exact I. Qed.
Lemma REST_A_fp_where : forall a, REST_A_fp a -> client_static a /\ outside LIB_W a /\ ~ cl_cell a.
Proof. intros a []. Qed.

(* [comment removed for export] *)
Lemma ssp_guard_rw : forall (m : mem) g, ro_cells asegs m ssp_guard [C8 g] -> rw_cells asegs m ssp_guard [C8 g].
Proof.
  intros m g RO. split; [exact RO|]. cbn [cells_size csize Nat.add]. apply wr_at_wseg8; [| unfold ssp_guard; lia | unfold ssp_guard; lia].
  intros i Hi. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [vm_compute; discriminate|]). destruct Hi.
Qed.

Theorem W7_OPEN_A : forall CL m (g : word) (v : word), LIB_A CL m -> ro_cells asegs m ssp_guard [C8 g] -> rw_cells asegs m (errno_cell (Z_to_bv 64 TP_A)) [C4 v] ->
  cl_env m (Z_to_bv 8 1) g /\ sec_off m
  /\ exists (E : Z) (LBL : list (Z * Z)), libenv m LBL E /\ errst_at_rest E [] m /\ In (E, 904) CL /\ incl_live LBL CL /\ ~ In (E, 904) LBL /\ REST_A m.
Proof.
  intros CL m g v (RO & LAT & SEC & E & LBL & LE & ERS & INE & INCL & NLE) SSP ERR.
  split; [| split; [exact SEC|]].
  - split; [exact RO|]. split; [exact LAT|]. split; [right; reflexivity|]. exact (ssp_guard_rw m g SSP).
  - exists E, LBL. split; [| exact (conj ERS (conj INE (conj INCL (conj NLE I))))].
    apply (libenv_of_core m LBL E v LE). unfold errno_cell in ERR. rewrite unsigned_lit in ERR by lia. exact ERR.
Qed.

Theorem W7_CLOSE_A : forall CL m (canary : word) E LBL, In (E, 904) CL -> incl_live LBL CL -> ~ In (E, 904) LBL ->
  cl_env m (Z_to_bv 8 1) canary -> sec_off m -> libenv m LBL E -> errst_at_rest E [] m -> REST_A m -> LIB_A CL m.
Proof.
  intros CL m canary E LBL INE INCL NLE (RO & LAT & _ & _) SEC LE ERS _.
  split; [exact RO|]. split; [exact LAT|]. split; [exact SEC|]. exists E, LBL. exact (conj (libenv_core_of m LBL E LE) (conj ERS (conj INE (conj INCL NLE)))).
Qed.

(* [comment removed for export] *)
Theorem lib_local_A : lib_local_d LIB_A.
Proof.
  intros CL m m' (RO & LAT & SEC & E & LBL & LE & ERS & INE & INCL & NLE) AG.
  assert (AGD : forall (lo hi : Z) (a : word), In (lo, hi) LIB_D -> lo <= bv_unsigned a < hi -> m' a = m a) by (intros lo hi a Hin Ha; apply AG; left; exists lo, hi; split; [exact Hin | exact Ha]).
  unfold LIB_D in AGD.
  assert (AGL : forall a : word, in_live CL (bv_unsigned a) -> m' a = m a) by (intros a Ha; apply AG; right; exact Ha).
  (* [comment removed for export] *)
  assert (WIN : forall lo hi a n, In (lo, hi) [(0x5a9f20, 0x5a9f28); (0x5a9f40, 0x5a9f48); (0x5a9f60, 0x5a9f68); (0x5a9f80, 0x5a9f88); (0x5a9fc0, 0x5a9fc8); (0xb9f1c0, 0xb9f1e0);
                                               (0xb9f200, 0xb9f848); (0xb9f860, 0xb9f861); (0xba3e5a, 0xba3e5b); (0xba3e90, 0xba3e98); (0xbc4e58, 0xbc5270); (0xbc52a0, 0xbc5698)] ->
            lo <= a -> a + n <= hi -> agree_on (fun x => a <= x < a + n) m m').
  { intros lo hi a n Hin H1 H2 x Hx. cbv beta in Hx. apply (AGD lo hi x Hin). lia. }
  split; [| split; [| split]].
  - unfold CL_RO, G_MALLOC_IMPL, CL_REALLOC_IMPL, CL_FREE_IMPL, CL_MEMSET_FUNC in RO |- *.
    pose proof (Forall_inv RO) as R1. pose proof (Forall_inv (Forall_inv_tail RO)) as R2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail RO))) as R3.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail RO)))) as R4. cbn [fst snd] in R1, R2, R3, R4.
    apply Forall_cons; [cbn [fst snd]; apply (ro_cells_agree asegs m m' _ _ R1); cbn [cells_size csize Nat.add]; apply (WIN 0x5a9f40 0x5a9f48); [cbn [In]; tauto | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; apply (ro_cells_agree asegs m m' _ _ R2); cbn [cells_size csize Nat.add]; apply (WIN 0x5a9f60 0x5a9f68); [cbn [In]; tauto | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; apply (ro_cells_agree asegs m m' _ _ R3); cbn [cells_size csize Nat.add]; apply (WIN 0x5a9f80 0x5a9f88); [cbn [In]; tauto | lia | lia]|].
    apply Forall_cons; [cbn [fst snd]; apply (ro_cells_agree asegs m m' _ _ R4); cbn [cells_size csize Nat.add]; apply (WIN 0x5a9fc0 0x5a9fc8); [cbn [In]; tauto | lia | lia]|].
    apply Forall_nil.
  - apply (rw_cells_agree_nw asegs m m' _ _ LAT). cbn [cells_size csize Nat.add]. unfold G_ALLOW_CUST. apply (WIN 0xb9f200 0xb9f848); [cbn [In]; tauto | lia | lia].
  - apply (rw_cells_agree_nw asegs m m' _ _ SEC). cbn [cells_size csize Nat.add]. unfold SEC_INIT. apply (WIN 0xb9f860 0xb9f861); [cbn [In]; tauto | lia | lia].
  - exists E, LBL. split; [| split; [| exact (conj INE (conj INCL NLE))]].
    + apply (libenv_core_agree m m' LBL E LE). intros a [Ha|Ha].
      * destruct (libenv_cstat_LIB_D _ Ha) as [Hb|Hb]; [apply (AGD 0xb9f200 0xb9f848); [cbn [In]; tauto | exact Hb] | apply (AGD 0xbc52a0 0xbc5698); [cbn [In]; tauto | exact Hb]].
      * apply AGL. destruct Ha as (p & n & Hin & Hp). exists p, n. split; [exact (INCL _ Hin) | exact Hp].
    + apply (errst_rest_agree m m' E [] ERS). intros a [Ha|Ha]; [| destruct Ha as (p & n & [] & _)].
      apply AGL. exists E, 904. split; [exact INE | exact Ha].
Qed.
