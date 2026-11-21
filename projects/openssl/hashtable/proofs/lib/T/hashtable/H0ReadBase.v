(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (lemmas on the launch's reserved ledger ([res_vm]: the binary's reservations and the vDSO/vvar pair below the mmap base) and on [munmap_model]'s cut of it by [maps_subtract]; the stack window is the launch's 1500 pages, not 8 MiB). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.openssl.hashtable.images Require Import Plain.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib H0TargetPre.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Lim.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition fds_file (path : list byte) (off : word) : list (word * FdEntry) :=
  (Z_to_bv 64 3, FdFile path off) :: fds_std.

Lemma fds_file_insert : forall path off off',
  fd_insert (fds_file path off) (Z_to_bv 64 3) (FdFile path off') = fds_file path off'.
Proof. intros. reflexivity. Qed.

Lemma fds_file_remove : forall path off, fd_remove (fds_file path off) (Z_to_bv 64 3) = fds_std.
Proof. intros. reflexivity. Qed.

Lemma fds_file_lookup3 : forall path off, fd_lookup (fds_file path off) (Z_to_bv 64 3) = Some (FdFile path off).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition mem_eq_outside (M M' : word -> option byte) (rs : list (word * Z)) : Prop :=
  forall a, outside a rs -> M' a = M a.

Lemma mem_eq_outside_refl : forall M rs, mem_eq_outside M M rs.
Proof. intros M rs a _. reflexivity. Qed.

Lemma mem_eq_outside_trans : forall M1 M2 M3 rs,
  mem_eq_outside M1 M2 rs -> mem_eq_outside M2 M3 rs -> mem_eq_outside M1 M3 rs.
Proof. intros M1 M2 M3 rs A B a Ha. rewrite (B a Ha). apply A, Ha. Qed.

Lemma mem_eq_outside_weaken : forall M M' rs rs',
  (forall a, outside a rs' -> outside a rs) -> mem_eq_outside M M' rs -> mem_eq_outside M M' rs'.
Proof. intros M M' rs rs' Hw H a Ha. apply H, Hw, Ha. Qed.

(* [comment removed for export] *)
Lemma mem_eq_outside_rdn : forall M M' rs n (a : word),
  mem_eq_outside M M' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn RSEGS M' a n = rdn RSEGS M a n.
Proof.
  intros M M' rs n a Hf Ho Hb. symmetry. apply rdn_agree. intros j Hj. symmetry. apply Hf. apply Ho. lia.
Qed.

Lemma mem_eq_outside_store_ok : forall M M' rs n (a : word),
  mem_eq_outside M M' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  store_ok RSEGS M a n = true -> store_ok RSEGS M' a n = true.
Proof.
  intros M M' rs n a Hf Ho Hb Hs.
  apply store_ok_of_all; [lia|]. intros x Hx.
  pose proof (store_ok_all RSEGS M n a Hb Hs x Hx) as H1.
  unfold store_ok in *. cbn [store_ok] in *.
  unfold wview in *. pose proof (u64_range a).
  rewrite (Hf x); [exact H1|].
  replace x with (Z_to_bv 64 (bv_unsigned a + (bv_unsigned x - bv_unsigned a))) by (apply bv_eq; rewrite u_small by lia; lia).
  apply Ho. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 6144000)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 6144000 + d)) m = true.

(* [comment removed for export] *)
Definition group_writable (M : word -> option byte) (gm : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 69632)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned gm + d)) m = true.

(* [comment removed for export] *)
Definition meta_writable (M : word -> option byte) (mb : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned mb + 4096 + d)) m = true.

(* [comment removed for export] *)
Definition STAGE : Z := 0x2d9379.

(* [comment removed for export] *)
Definition stage_writable (M : word -> option byte) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 65536)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (STAGE + d)) m = true.

(* [comment removed for export] *)
Definition LA (a : Z) : saddr := SA (ELit 0) a.          (* [comment removed for export] *)
Definition MBA (k : Z) : saddr := SA (EVar 2) k.         (* [comment removed for export] *)
Definition GMA (k : Z) : saddr := SA (EVar 3) k.         (* [comment removed for export] *)
Definition mbx (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).

Definition kn_M1 : list kentry :=
  [ KImg 0x10000 0x2d8000;                       (* [comment removed for export] *)
    KWord (LA 0x30bf98) 8 (EVar 7);              (* [comment removed for export] *)
    KWord (LA 0x30c1eb) 1 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x30c218) 8 (ELit 4096);           (* [comment removed for export] *)
    KWord (LA 0x30c258) 4 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x30d6c0) 4 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x30c260) 8 (EVar 8);              (* [comment removed for export] *)
    KWord (LA 0x30c268) 4 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x30c26c) 4 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x30c270) 8 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x30c278) 8 (mbx 4160);            (* [comment removed for export] *)
    KWord (LA 0x30c280) 8 (ELit 100);            (* [comment removed for export] *)
    KWord (LA 0x30c288) 8 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x30c298) 8 (mbx 4096);            (* [comment removed for export] *)
    KWord (LA 0x30c2a0) 8 (mbx 4096);            (* [comment removed for export] *)
    KWord (LA 0x30c2a8) 8 (mbx 8192);            (* [comment removed for export] *)
    KWord (LA 0x30c410) 8 (mbx 4120);            (* [comment removed for export] *)
    KWord (LA 0x30c590) 8 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x30c5f0) 1 (ELit 1);              (* [comment removed for export] *)
    (* [comment removed for export] *)
    KWord (MBA 4096) 8 (EVar 8);                (* [comment removed for export] *)
    KWord (MBA 4104) 8 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4112) 4 (ELit 101);              (* [comment removed for export] *)
    KWord (MBA 4120) 8 (mbx 4120);              (* [comment removed for export] *)
    KWord (MBA 4128) 8 (mbx 4120);              (* [comment removed for export] *)
    KWord (MBA 4136) 8 (EVar 3);                (* [comment removed for export] *)
    KWord (MBA 4144) 4 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4148) 4 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4152) 8 (ELit 0x11b20);          (* [comment removed for export] *)
    KZero (MBA 4160) (ELit 4032);               (* [comment removed for export] *)
    (* [comment removed for export] *)
    KWord (GMA 0) 8 (mbx 4120);                 (* [comment removed for export] *)
    KWord (GMA 8) 1 (ELit 0);                   (* [comment removed for export] *)
    KZero (GMA 9) (ELit 4);                     (* [comment removed for export] *)
    KWord (GMA 13) 1 (ELit 224);                (* [comment removed for export] *)
    KWord (GMA 14) 2 (ELit 1);                  (* [comment removed for export] *)
    KZero (GMA 16) (ELit 12);
    KWord (GMA 28) 1 (ELit 0);                  (* [comment removed for export] *)
    KWord (GMA 29) 1 (ELit 160);                (* [comment removed for export] *)
    KWord (GMA 30) 2 (ELit 1);                  (* [comment removed for export] *)
    KWord (GMA 0x10020) 1 (ELit 0);             (* [comment removed for export] *)
    KZero (GMA 0x10021) (ELit 4054);            (* [comment removed for export] *)
    KWord (GMA 0x10ff7) 1 (ELit 0);             (* [comment removed for export] *)
    KWord (GMA 0x10ff8) 4 (ELit 4060);          (* [comment removed for export] *)
    KZero (GMA 0x10ffc) (ELit 4) ].             (* [comment removed for export] *)

Record read_pre (sp0 p1 mb bw gm can sec : word) (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_PRE {
  (* [comment removed for export] *)
  rp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rp_gp : getr R 3 = Z_to_bv 64 0x10800;
  rp_tp : getr R 4 = Z_to_bv 64 0x2ebf58;
  rp_s0 : getr R 8 = Z_to_bv 64 2;
  rp_a0 : getr R 10 = Z_to_bv 64 (bv_unsigned gm + 32);        (* [comment removed for export] *)
  rp_s2 : getr R 18 = p1;                                      (* [comment removed for export] *)
  rp_s4 : getr R 20 = Z_to_bv 64 3;                            (* [comment removed for export] *)
  rp_s5 : getr R 21 = Z_to_bv 64 65536;                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  rp_p1  : (0x7fff80000000 <= bv_unsigned p1 <= 0x800000400000)%Z;
  rp_b   : (0x1000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned mb mod 4096 = 0)%Z;
  rp_b_img : (bv_unsigned mb + 8192 <= 0x10000 \/ 0x30e000 <= bv_unsigned mb)%Z;
           (* [comment removed for export] *)
  rp_gm  : (0x30e000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  rp_gm_b : (bv_unsigned mb + 8192 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned mb + 4096)%Z;
           (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_stack : stack_writable M sp0;
  rp_group : group_writable M gm;
  rp_meta  : meta_writable M mb;
  (* [comment removed for export] *)
  rp_errno : exists e : word, rdn RSEGS M (Z_to_bv 64 0x2ebeb4) 4 = Some (word_to_le_bytes 4 e);
  (* [comment removed for export] *)
  rp_stage : stage_writable M;
  (* [comment removed for export] *)
  rp_malloc : forall (x0 x1 x4 x5 x6 x9 : word) (extra : list word) (ebs : list (list byte)),
      know_ok RSEGS (Env (vals_ev ([x0; x1; mb; gm; x4; x5; x6; can; sec; x9] ++ extra)) (blobs_ev ebs)) M kn_M1
}.

(* [comment removed for export] *)
Definition model_pre (path : list byte) (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) : Model :=
  mkModelA (fds_file path (Z_to_bv 64 0)) VM stdin0 fs0 None (Some tid) None.
Definition model_post (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) : Model :=
  mkModelA fds_std VM stdin0 fs0 None (Some tid) None.

(* LPS 727298f3: the reserved ledger is the binary's reservations followed by the launch's
   vDSO/vvar pair ([State.init_reserved]): four vvar pages and the vDSO text's two pages (one
   measured image, so for every kernel build), ending at [vdso_top] of the ledger.  [vdso_top] reads
   only the mmap base and the initial stack pointer, which no call changes; it lies at or above the
   lowest mmap base less a page. *)
Definition vpair (t : Z) : list (word * word) :=
  [(Z_to_bv 64 (t - 24576)%Z, Z_to_bv 64 16384%Z); (Z_to_bv 64 (t - 8192)%Z, Z_to_bv 64 8192%Z)].
Definition res_vm (VM : VmMaps) : Prop :=
  vm_reserved VM = segments_reserved RSEGS ++ vpair (vdso_top VM)
  /\ (mmap_base_min - 4095 <= vdso_top VM <= 2 ^ 47)%Z /\ (vdso_top VM mod 4096 = 0)%Z.

Lemma vpair_vdso : forall kb t, (mmap_base_min - 4095 <= t)%Z -> vdso_reserved kb t = vpair t.
Proof.
  intros kb t Ht. unfold vdso_reserved, vpair. cbv zeta.
  replace (vdso_len kb) with 24576%Z by (vm_compute; reflexivity).
  replace (vdso_vvar_pages * page_size)%Z with 16384%Z by (vm_compute; reflexivity).
  replace (vdso_text_pages kb * page_size)%Z with 8192%Z by (vm_compute; reflexivity).
  replace (t - 24576 <? page_size)%Z with false
    by (symmetry; apply Z.ltb_ge; unfold page_size, mmap_base_min in *; lia).
  replace (t - 24576 + 16384)%Z with (t - 8192)%Z by lia. reflexivity.
Qed.

Lemma res_vm_vdso : forall VM kb, res_vm VM ->
  vm_reserved VM = segments_reserved RSEGS ++ vdso_reserved kb (vdso_top VM).
Proof. intros VM kb (Hr & Ht & _). rewrite vpair_vdso by lia. exact Hr. Qed.

Lemma res_vm_vdso_incl : forall VM kb, res_vm VM -> incl (vdso_reserved kb (vdso_top VM)) (vm_reserved VM).
Proof. intros VM kb H. rewrite (res_vm_vdso VM kb H). apply incl_appr, incl_refl. Qed.

(* the ledger keeps its reserved list, mmap base and initial stack pointer from call to call *)
Lemma res_vm_transport : forall VM VM',
  vm_reserved VM' = vm_reserved VM -> vm_mmap_base VM' = vm_mmap_base VM -> vm_init_sp VM' = vm_init_sp VM ->
  res_vm VM -> res_vm VM'.
Proof.
  intros VM VM' Er Eb Es H.
  assert (Et : vdso_top VM' = vdso_top VM) by (unfold vdso_top, mmap_top, alloc_top; rewrite Eb, Es; reflexivity).
  unfold res_vm in *. rewrite Et, Er. exact H.
Qed.

Lemma region_free_app0 : forall l1 l2 (a n : word),
  region_free (l1 ++ l2) a n = (region_free l1 a n && region_free l2 a n)%bool.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 a n; cbn [app region_free]; [reflexivity|].
  rewrite IH, andb_assoc. reflexivity.
Qed.

(* a range the binary's reservations leave free, and that ends below the pair, is free of the
   whole ledger *)
Lemma res_vm_rf_add : forall VM (a n : word), res_vm VM ->
  region_free (segments_reserved RSEGS) a n = true ->
  (bv_unsigned a + bv_unsigned n <= mmap_base_min - 4095 - 24576)%Z ->
  region_free (vm_reserved VM) a n = true.
Proof.
  intros VM a n (Hr & Ht & _) Hs Hlt. rewrite Hr, region_free_app0, Hs. cbn [vpair region_free andb].
  unfold iv_overlap. rewrite !u_small by (unfold mmap_base_min in *; lia).
  pose proof (u64_range a). pose proof (u64_range n).
  unfold mmap_base_min in *.
  replace (bv_unsigned a <? vdso_top VM - 24576 + 16384)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  replace (vdso_top VM - 24576 <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  replace (bv_unsigned a <? vdso_top VM - 8192 + 8192)%Z with true by (symmetry; apply Z.ltb_lt; lia).
  replace (vdso_top VM - 8192 <? bv_unsigned a + bv_unsigned n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

(* the whole reserved ledger, the binary's four reservations and the pair *)
Lemma res_vm_list : forall VM, res_vm VM -> vm_reserved VM =
  [(Z_to_bv 64 65536%Z, Z_to_bv 64 835584%Z); (Z_to_bv 64 901120%Z, Z_to_bv 64 1699840%Z);
   (Z_to_bv 64 2600960%Z, Z_to_bv 64 380928%Z); (Z_to_bv 64 2981888%Z, Z_to_bv 64 221184%Z);
   (Z_to_bv 64 (vdso_top VM - 24576)%Z, Z_to_bv 64 16384%Z); (Z_to_bv 64 (vdso_top VM - 8192)%Z, Z_to_bv 64 8192%Z)].
Proof.
  intros VM [Hr _].
  assert (E : segments_reserved RSEGS =
    [(Z_to_bv 64 65536%Z, Z_to_bv 64 835584%Z); (Z_to_bv 64 901120%Z, Z_to_bv 64 1699840%Z);
     (Z_to_bv 64 2600960%Z, Z_to_bv 64 380928%Z); (Z_to_bv 64 2981888%Z, Z_to_bv 64 221184%Z)]) by (vm_compute; reflexivity).
  rewrite Hr, E. reflexivity.
Qed.

Lemma res_vm_top : forall VM, res_vm VM -> (0x154555557000 - 4095 <= vdso_top VM <= 2 ^ 47)%Z.
Proof. intros VM (_ & Ht & _). unfold mmap_base_min in Ht. exact Ht. Qed.

(* the launch's ledger: the binary's reservations and the pair [State.init_reserved] places below
   the lower of the mmap base and the stack's lowest page *)
Lemma res_vm_init : forall VM (mbase sp0 : word) kb,
  valid_mmap_base mbase -> valid_sp sp0 ->
  vm_reserved VM = init_reserved (segments_reserved RSEGS) mbase sp0 kb ->
  vm_mmap_base VM = mbase -> vm_init_sp VM = sp0 -> res_vm VM.
Proof.
  intros VM mbase sp0 kb (M1 & M2 & M3) Hsp Er Eb Es.
  assert (Et : vdso_top VM = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size))).
  { unfold vdso_top, mmap_top, alloc_top. rewrite Eb, Es. apply page_round_down_Z_min_r. }
  assert (Ht : (mmap_base_min - 4095 <= vdso_top VM <= 2 ^ 47)%Z /\ (vdso_top VM mod 4096 = 0)%Z).
  { rewrite Et. unfold page_round_down_Z, page_size.
    assert (Hx : (mmap_base_min <= Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size) <= mmap_base_max)%Z).
    { destruct Hsp as (S1 & S2 & _). unfold stack_max_size, sp_window_lo, sp_window_hi, mmap_base_min, mmap_base_max in *. lia. }
    set (x := Z.min (bv_unsigned mbase) (bv_unsigned sp0 - stack_max_size)) in *.
    pose proof (Z.div_mod x 4096 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 4096 ltac:(lia)) as Bx.
    split.
    - unfold mmap_base_max, sp_window_hi in Hx. lia.
    - apply Z_mod_mult. }
  split; [|exact Ht]. rewrite Er. unfold init_reserved. rewrite <- Et. rewrite vpair_vdso by lia. reflexivity.
Qed.

(* what a range the whole ledger and the maps leave free says about the binary's reservations
   and the maps alone *)
Lemma res_vm_rf_drop : forall VM l (a n : word), res_vm VM ->
  region_free (vm_reserved VM ++ l) a n = true -> region_free (segments_reserved RSEGS ++ l) a n = true.
Proof.
  intros VM l a n (Hr & _) H. rewrite Hr, <- app_assoc, !region_free_app0 in H. rewrite region_free_app0.
  apply andb_prop in H as [H1 H2]. apply andb_prop in H2 as [_ H3]. rewrite H1, H3. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vm_exact (VM : VmMaps) (sp0 mb bw B : word) (nb : Z) : Prop :=
  vm_maps VM = [(B, Z_to_bv 64 nb); (mb, Z_to_bv 64 8192)]
  /\ vm_noaccess VM = [(mb, Z_to_bv 64 4096)]
  /\ vm_start_brk VM = mb /\ vm_brk VM = Z_to_bv 64 (bv_unsigned mb + 8192)
  /\ bv_unsigned bw = (bv_unsigned mb + 8192)%Z
  /\ (reserved_top (segments_reserved RSEGS) <= bv_unsigned mb)%Z
  /\ (bv_unsigned B mod 4096 = 0)%Z /\ (0 < bv_unsigned B)%Z /\ (bv_unsigned B + nb <= bv_unsigned sp0 - 8388608)%Z
  /\ region_free (vm_reserved VM) B (Z_to_bv 64 nb) = true
  /\ (bv_unsigned mb + 8192 <= bv_unsigned B \/ bv_unsigned B + nb <= bv_unsigned mb)%Z
  /\ (bv_unsigned mb <= reserved_top (segments_reserved RSEGS) + brk_aslr_max)%Z.   (* [comment removed for export] *)

Definition vm_pre (VM : VmMaps) (sp0 mb bw gm : word) : Prop :=
  res_vm VM
  /\ (LIM <= vm_limit VM)%Z             (* [comment removed for export] *)
  /\ vm_init_sp VM = sp0                (* [comment removed for export] *)
  /\ map_has (vm_maps VM) gm (Z_to_bv 64 69632) = true
  /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 2 ^ 30)%Z
                      /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
  /\ (length (vm_maps VM) <= 8)%nat
  /\ (live_bytes (vm_maps VM) <= 2 ^ 20)%Z
  /\ (exists p, In p (vm_maps VM) /\ fst p <> gm
        /\ (bv_unsigned (fst p) <= bv_unsigned mb + 4096)%Z
        /\ (bv_unsigned mb + 8192 <= bv_unsigned (fst p) + bv_unsigned (snd p))%Z)
  /\ seps (vm_maps VM)    (* [comment removed for export] *)
  /\ vm_ledger mb bw VM    (* [comment removed for export] *)
  /\ vm_exact VM sp0 mb bw gm 69632.   (* [comment removed for export] *)

(* LPS 75d69e00+: [munmap_model] cuts the ledger with [maps_subtract]; on a separated
   ledger where the unmapped entry is exact, the cut is [map_remove]. *)
Lemma vm_seps_pair : forall l, seps l -> forall p q, In p l -> In q l -> p <> q -> iv_disjoint p q.
Proof.
  induction 1 as [|p0 l Hd Hs IH]; intros p q Hp Hq Hne; [destruct Hp|].
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - contradiction.
  - exact (proj1 (Forall_forall _ _) Hd q Hq).
  - pose proof (proj1 (Forall_forall _ _) Hd p Hp) as D. unfold iv_disjoint in *. lia.
  - exact (IH p q Hp Hq Hne).
Qed.

Lemma munmap_stage_ledger1 : forall l (B a n : word) (nb lo hi : Z),
  lo = bv_unsigned a -> hi = (bv_unsigned a + bv_unsigned n)%Z ->
  seps l -> In (a, n) l -> Forall (fun p => 0 < bv_unsigned (snd p))%Z l ->
  (0 < nb < 2 ^ 64)%Z ->
  (bv_unsigned B + nb <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= bv_unsigned B)%Z ->
  maps_subtract ((B, Z_to_bv 64 nb) :: l) lo hi = (B, Z_to_bv 64 nb) :: map_remove l a.
Proof.
  intros l B a n nb lo hi -> -> Hs Hin Hpos Hnb Hd.
  assert (U : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply Z_to_bv_small; unfold bv_modulus; lia).
  pose proof (proj1 (Forall_forall _ _) Hpos (a, n) Hin) as Hn. cbn [snd] in Hn.
  rewrite (OSSVerify.Proofs.openssl.hashtable.lib.Common.MmapSim.maps_subtract_exact _ a n Hn).
  - assert (Hne : B <> a) by (intros ->; lia).
    unfold map_remove. cbn [List.filter fst]. rewrite (bv_eqb_neq B a Hne). cbn [negb]. reflexivity.
  - intros b s [E|Hb]; [injection E as <- <-; rewrite U; lia | exact (proj1 (Forall_forall _ _) Hpos (b, s) Hb)].
  - intros b s [E|Hb] Hba.
    + injection E as <- <-. exfalso. rewrite Hba in Hd. lia.
    + destruct (decide (s = n)) as [E|Ne]; [exact E|exfalso].
      pose proof (vm_seps_pair l Hs (b, s) (a, n) Hb Hin ltac:(intros E; injection E as _ E; exact (Ne E))) as D.
      pose proof (proj1 (Forall_forall _ _) Hpos (b, s) Hb) as P.
      unfold iv_disjoint in D. cbn [fst snd] in D, P. rewrite Hba in D. lia.
  - intros b s [E|Hb] Hba.
    + injection E as <- <-. rewrite U. lia.
    + pose proof (vm_seps_pair l Hs (b, s) (a, n) Hb Hin ltac:(intros E; injection E as E _; exact (Hba E))) as D.
      unfold iv_disjoint in D. cbn [fst snd] in D. exact D.
Qed.

Lemma munmap_stage_ledger2 : forall rest (B' B : word) (nb' nb lo hi : Z),
  lo = bv_unsigned B -> hi = (bv_unsigned B + bv_unsigned (Z_to_bv 64 nb))%Z ->
  (0 < nb' < 2 ^ 64)%Z -> (0 < nb < 2 ^ 64)%Z ->
  (bv_unsigned B' + nb' <= bv_unsigned B \/ bv_unsigned B + nb <= bv_unsigned B')%Z ->
  Forall (fun p => 0 < bv_unsigned (snd p))%Z rest ->
  Forall (fun p => bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned B
                   \/ bv_unsigned B + nb <= bv_unsigned (fst p))%Z rest ->
  maps_subtract ((B', Z_to_bv 64 nb') :: (B, Z_to_bv 64 nb) :: rest) lo hi
  = (B', Z_to_bv 64 nb') :: map_remove rest B.
Proof.
  intros rest B' B nb' nb lo hi -> -> H1 H2 Hd Hpos Hdisj.
  assert (U' : bv_unsigned (Z_to_bv 64 nb') = nb') by (apply Z_to_bv_small; unfold bv_modulus; lia).
  assert (U : bv_unsigned (Z_to_bv 64 nb) = nb) by (apply Z_to_bv_small; unfold bv_modulus; lia).
  rewrite (OSSVerify.Proofs.openssl.hashtable.lib.Common.MmapSim.maps_subtract_exact _ B (Z_to_bv 64 nb)).
  - assert (Hne : B' <> B) by (intros ->; lia).
    unfold map_remove. cbn [List.filter fst].
    rewrite (bv_eqb_neq B' B Hne), bv_eqb_refl. cbn [negb]. reflexivity.
  - rewrite U. lia.
  - intros b s [E|[E|Hin]].
    + injection E as <- <-. rewrite U'. lia.
    + injection E as <- <-. rewrite U. lia.
    + exact (proj1 (Forall_forall _ _) Hpos (b, s) Hin).
  - intros b s [E|[E|Hin]] Hba.
    + injection E as <- <-. exfalso. rewrite Hba in Hd. lia.
    + injection E as <- <-. reflexivity.
    + exfalso. pose proof (proj1 (Forall_forall _ _) Hdisj (b, s) Hin) as D.
      pose proof (proj1 (Forall_forall _ _) Hpos (b, s) Hin) as P. cbn [fst snd] in D, P. rewrite Hba in D. lia.
  - intros b s [E|[E|Hin]] Hba.
    + injection E as <- <-. rewrite U, U'. lia.
    + injection E as <- <-. contradiction.
    + pose proof (proj1 (Forall_forall _ _) Hdisj (b, s) Hin) as D. cbn [fst snd] in D. rewrite U. exact D.
Qed.

(* an entry outside the cut survives it *)
Lemma maps_subtract_keep_in : forall l (p : word * word) (lo hi : Z),
  (lo < hi)%Z -> (0 < bv_unsigned (snd p))%Z -> In p l ->
  (bv_unsigned (fst p) + bv_unsigned (snd p) <= lo \/ hi <= bv_unsigned (fst p))%Z ->
  In p (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] l IH]; intros [b s] lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [fst snd] in *. change (maps_subtract ((a, sz) :: l) lo hi) with (iv_subtract a sz lo hi ++ maps_subtract l lo hi).
  apply in_or_app. destruct Hin as [E|Hin].
  - left. injection E as <- <-.
    rewrite (OSSVerify.Proofs.openssl.hashtable.lib.Common.MmapSim.iv_subtract_outside a sz lo hi Hs Hlh Hd).
    left. reflexivity.
  - right. exact (IH (b, s) lo hi Hlh Hs Hin Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_regions0 (sp0 gm : word) (L : Z) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388480%Z); (Z_to_bv 64 (bv_unsigned gm + 32), L);
   (Z_to_bv 64 STAGE, 65536%Z)].

Record read_post0 (sp0 p1 gm : word) (content : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_POST0 {
  rq_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rq_gp : getr R 3 = Z_to_bv 64 0x10800;
  rq_tp : getr R 4 = Z_to_bv 64 0x2ebf58;
  rq_s0 : getr R 8 = Z_to_bv 64 2;
  rq_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);         (* [comment removed for export] *)
  rq_s2 : getr R 18 = p1;
  rq_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));  (* [comment removed for export] *)
  rq_s4 : getr R 20 = Z_to_bv 64 3;
  rq_s5 : getr R 21 = Z_to_bv 64 65536;                         (* [comment removed for export] *)
  rq_s6 : getr R 22 = Z_to_bv 64 STAGE;                          (* [comment removed for export] *)
  rq_s7 : getr R 23 = Z_to_bv 64 0;                              (* [comment removed for export] *)
  rq_keep : forall r : reg, In r [24; 25; 26; 27]%bv -> getr R r = getr R0 r;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rq_frame : mem_eq_outside M0 M (read_regions0 sp0 gm (Z.of_nat (length content)));
  rq_grows : mem_grows M0 M;
  rq_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  rq_stack : stack_writable M sp0;
  rq_group : group_writable M gm;
  rq_stage : stage_writable M }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valsr (sp0 p1 b gm : word) (L : Z) (can sec : word) (R : bvmap 5 word) : list word :=
  [sp0; p1; b; gm; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0; can; sec; Z_to_bv 64 0] ++ junk_vals R.
Definition ENVr (vals : list word) (content : list byte) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (10 + i).

Definition sr_RE : list expr :=
  [ELit 0; J 1; spx (-128); ELit 0x10800; ELit 0x2ebf58; J 5; J 6; J 7;
   ELit 2; J 9; gmx 32; J 11; J 12; J 13; J 14; J 15;
   J 16; J 17; EVar 1; J 19; ELit 3; ELit 65536; J 22; J 23;
   J 24; J 25; J 26; J 27; J 28; J 29; J 30; J 31].

(* [comment removed for export] *)
Definition kn_RE_base : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144000)) 6144000;
   KAlign (EVar 3) 4096; KRange (EVar 3) 0x30e000 0x7fffff7ef000;
   KWr (SA (EVar 3) 0) 69632;
   KDisj (SA (EVar 0) (-8388608)) 8388608 (SA (EVar 3) 0) 69632;
   KRange (EVar 1) 0x7fff80000000 0x800000400000;
   KWr (LA STAGE) 65536].
Definition kn_RE (Llo Lhi : Z) : list kentry := kn_RE_base ++ [KRange (EVar 4) Llo Lhi].

Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section EntrySym.
  Variables (sp0 p1 b bw gm can sec : word) (L : Z) (R : bvmap 5 word) (M : word -> option byte) (content : list byte).
  Hypothesis RP : read_pre sp0 p1 b bw gm can sec R M.
  Let vals := valsr sp0 p1 b gm L can sec R.
  Let E := ENVr vals content.

  Lemma ev0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = p1. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = b. Proof. reflexivity. Qed.
  Lemma ev3 : ev E 3 = gm. Proof. reflexivity. Qed.
  Lemma ev4 : ev E 4 = Z_to_bv 64 L. Proof. reflexivity. Qed.
  Lemma ev7 : ev E 7 = can. Proof. reflexivity. Qed.
  Lemma ev8 : ev E 8 = sec. Proof. reflexivity. Qed.
  Lemma evJ : forall i, (i < 32)%nat -> ev E (10 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold E, ENVr, vals, valsr. cbn [ev]. unfold vals_ev.
    change (10 + i)%nat with (length [sp0; p1; b; gm; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0; can; sec; Z_to_bv 64 0] + i)%nat.
    rewrite app_nth2_plus. unfold junk_vals. rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi.
    reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. rewrite ev0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.
  Lemma gmx_val : forall k, edenot E (gmx k) = Z_to_bv 64 (bv_unsigned gm + k).
  Proof. intros k. cbn [gmx edenot]. rewrite alu_add. unfold v_add. rewrite ev3.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

  Theorem read_pre_regs : regs_ok E sr_RE R.
  Proof.
    destruct RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hsw Hkm].
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_RE all_regs].
    all: try (rewrite spx_val; rewrite Rsp; f_equal; lia).
    all: try (rewrite gmx_val; assumption).
    all: try (lazymatch goal with |- _ = edenot _ (J ?n) => unfold J; change (edenot E (EVar (10 + n))) with (ev E (10 + n)); rewrite evJ by lia; reflexivity end).
    all: try (change (edenot E (EVar 1)) with (ev E 1); rewrite ev1; assumption).
    all: cbn [edenot]; first [assumption | apply getr_zero | reflexivity].
  Qed.

  Theorem read_pre_know : forall Llo Lhi, (0 <= Llo)%Z -> (Llo <= L <= Lhi)%Z -> (Lhi < 2 ^ 64)%Z ->
    know_ok RSEGS E M (kn_RE Llo Lhi).
  Proof.
    intros Llo Lhi H0 HL Hhi. destruct RP as [Rsp Rgp Rtp Rs0 Ra0 Rs2 Rs4 Rs5 Hsp Hp1 Hb Hbi Hgm Hgb Hst Hgr Hmw Her Hsw Hkm].
    unfold kn_RE, kn_RE_base, know_ok. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      change (ev E 0) with sp0; change (ev E 1) with p1; change (ev E 3) with gm; change (ev E 4) with (Z_to_bv 64 L);
      unfold flat, estart; cbn [a_base a_off edenot]; change (ev E 0) with sp0; change (ev E 3) with gm.
    - split; [lia | exact (proj2 Hsp)].
    - lia.
    - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 0) with sp0.
      replace (bv_unsigned sp0 + -6144000 + d)%Z with (bv_unsigned sp0 - 6144000 + d)%Z by lia. apply Hst; lia.
    - split; [lia | exact (proj2 (proj2 Hgm))].
    - lia.
    - split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot]. change (ev E 3) with gm.
      rewrite Z.add_0_r. apply Hgr; lia.
    - lia.
    - lia.
    - unfold LA, STAGE in *. cbn [a_base a_off edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
      split; [lia|]. intros d m Hd Hm. unfold adenot, v_addi. cbn [a_base a_off edenot].
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite Z.add_0_l. apply Hsw; lia.
    - rewrite u_small by lia. lia.
  Qed.
End EntrySym.
