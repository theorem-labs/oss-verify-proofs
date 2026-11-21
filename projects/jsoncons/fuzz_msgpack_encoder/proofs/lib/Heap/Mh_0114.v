(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed CAPKMAX_le, Forall_app_cons_mid, Forall_filter and 60 more; added vdso_inc, vdso_inc_keep, vdso_init_facts and 2 more; removed kr_t_HnEmbed; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/CJ/Bridge/Embed.v, 427 lines within its lines 9-1036. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap. From LinuxProcessSemantics.LinuxProcessSem Require Vdso. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0108. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge Require BrRes. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require RunP. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module HnEmbed.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0026.Scfg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Exec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.Prelim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.Prog OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KStep.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0108. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge Require BrRes. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083.BrRegs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0083.BrBase OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0108.BrNodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.Mh_0108.KLink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge.BrRes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnTree.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NMAX : Z := 2^30.           (* [comment removed for export] *)
Definition CAPKMAX : Z := 40000.        (* [comment removed for export] *)
Definition CAPBMAX : Z := 2^34.         (* [comment removed for export] *)

Lemma NMAX_facts : 0 < NMAX /\ NMAX mod page_size = 0 /\ 2 * PGSZ <= NMAX.
Proof. unfold NMAX, PGSZ, page_size. split; [lia|]. split; [reflexivity| lia]. Qed.

(* [comment removed for export] *)
Lemma NMAX_le_30 : NMAX <= 2 ^ 30. Proof. unfold NMAX. lia. Qed.
Lemma CAPKMAX_le : CAPKMAX <= 40000. Proof. unfold CAPKMAX. lia. Qed.
Lemma Forall_size_30 : forall l, Forall (fun p : word * word => bv_unsigned (snd p) <= NMAX) l ->
  Forall (fun p : word * word => bv_unsigned (snd p) <= 2 ^ 30) l.
Proof. intros l H. eapply Forall_impl; [|exact H]. intros p Hp. cbn in Hp |- *. pose proof NMAX_le_30. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section IMPL.
Variable segs : list Segment.
Context {St : Type}.

Lemma implM_ret_inv : forall {A} (a : A) (s : St) Q ms,
  implM segs (mret a) s Q ms -> evt segs (Q a s) ms.
Proof. intros A a s Q ms H. exact H. Qed.

Lemma implM_bind_inv : forall {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s Q ms,
  implM segs (mbind m f) s Q ms ->
  implM segs m s (fun a s' ms' => implM segs (f a) s' Q ms') ms.
Proof.
  intros A B m f s Q ms H. unfold implM, mbind in *. apply impl_ebind_inv in H.
  eapply impl_mono; [exact H|]. intros [|[a s']] ms'; cbn; auto.
Qed.

Lemma implM_msys_inv : forall {A} n (dec : resp -> option A) (s : St) Q ms,
  implM segs (msys n dec) s Q ms ->
  evt segs (fun ms1 => at_node segs n ms1 /\ forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms.
Proof.
  intros A n dec s Q ms H. unfold implM, msys in H. apply impl_enode_inv in H.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
  intros rsp a E. apply (Hk rsp (a, s)). rewrite E. reflexivity.
Qed.

Lemma mbind_mget : forall {A} (f : St -> Monad.M St A) s, mbind mget f s = f s s.
Proof. reflexivity. Qed.
Lemma implM_mget_inv : forall {A} (f : St -> Monad.M St A) s Q ms,
  implM segs (mbind mget f) s Q ms -> implM segs (f s) s Q ms.
Proof. intros A f s Q ms H. exact H. Qed.
Lemma implM_mupd_inv : forall {A} g (m : Monad.M St A) s Q ms,
  implM segs (mbind (mupd g) (fun _ => m)) s Q ms -> implM segs m (g s) Q ms.
Proof. intros A g m s Q ms H. exact H. Qed.
Lemma mbind_mupd : forall {A} g (m : Monad.M St A) s, mbind (mupd g) (fun _ => m) s = m (g s).
Proof. reflexivity. Qed.
Lemma mbind_mret_l : forall {A B} (a : A) (f : A -> Monad.M St B) s, mbind (mret a) f s = f a s.
Proof. reflexivity. Qed.

End IMPL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_vmmaps_twice : forall h1 h2 m, with_vmmaps h2 (with_vmmaps h1 m) = with_vmmaps h2 m.
Proof. intros h1 h2 m. reflexivity. Qed.

Lemma with_vmmaps_mat : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.

Lemma live_bytes_cons' : forall e l, live_bytes (e :: l) = bv_unsigned (snd e) + live_bytes l.
Proof. intros [a n] l. reflexivity. Qed.

Lemma Forall_app_cons_mid : forall {A} (P : A -> Prop) l1 x l2,
  Forall P (l1 ++ l2) -> P x -> Forall P (l1 ++ x :: l2).
Proof.
  intros A P l1 x l2 H Hx. apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1|]. constructor; assumption.
Qed.

Lemma length_app_cons_mid : forall {A} (l1 : list A) x l2, length (l1 ++ x :: l2) = S (length (l1 ++ l2)).
Proof. intros. rewrite !length_app. cbn. lia. Qed.

Lemma Forall_filter : forall {A} (P : A -> Prop) f l, Forall P l -> Forall P (List.filter f l).
Proof. intros A P f l H. induction H; cbn; [constructor|]. destruct (f x); [constructor|]; auto. Qed.

Lemma length_filter_le : forall {A} f (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. intros. apply List.filter_length_le. Qed.

Definition vdso_inc (kb : KernelBuild) (h : VmMaps) : Prop :=
  incl (vdso_reserved kb (vdso_top h)) (vm_reserved h).

Lemma vdso_inc_keep : forall kb h h',
  vdso_inc kb h -> vm_reserved h' = vm_reserved h ->
  vm_mmap_base h' = vm_mmap_base h -> vm_init_sp h' = vm_init_sp h -> vdso_inc kb h'.
Proof.
  intros kb h h' H E1 E2 E3. unfold vdso_inc in *. rewrite E1.
  replace (vdso_top h') with (vdso_top h) by (unfold vdso_top, mmap_top, alloc_top; rewrite E2, E3; reflexivity).
  exact H.
Qed.

Ltac vdso_keep_tac :=
  rewrite ?with_vmmaps_vm;
  match goal with H : vdso_inc ?kb _ |- vdso_inc ?kb _ => apply (vdso_inc_keep _ _ _ H); reflexivity end.

Lemma vdso_init_facts : forall kb (x : Z), 0 <= x < 2 ^ 64 ->
  (length (vdso_reserved kb (page_round_down_Z x)) <= 2)%nat
  /\ Forall (fun p => bv_unsigned (snd p) <= 20 * 4096) (vdso_reserved kb (page_round_down_Z x))
  /\ (forall e, In e (vdso_reserved kb (page_round_down_Z x)) -> x - 4095 - 20 * 4096 <= bv_unsigned (fst e)).
Proof.
  intros kb x Hx.
  assert (T1 : page_round_down_Z x <= x) by apply page_round_down_Z_le.
  assert (T0 : x - 4095 <= page_round_down_Z x).
  { unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full x 4096). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)). lia. }
  assert (Ttop : page_round_down_Z x < two_pow_64) by (unfold two_pow_64; lia).
  pose proof (vdso_len_bounds kb) as VL. unfold page_size in VL.
  split; [unfold vdso_reserved; destruct (_ <? _)%Z; cbn [length]; lia|].
  split.
  - apply Forall_forall. intros [a n] Hin. destruct (vdso_reserved_above kb _ a n Ttop Hin) as [A1 A2].
    cbn [snd]. pose proof (bv_unsigned_in_range 64 a). lia.
  - intros [a n] Hin. destruct (vdso_reserved_above kb _ a n Ttop Hin) as [A1 A2]. cbn [fst]. lia.
Qed.

Lemma vdso_reserved_kb_indep : forall kb kb' top,
  vdso_reserved kb top = vdso_reserved kb' top.
Proof.
  intros kb kb' top.
  assert (E : forall k, vdso_text_pages k = vdso_text_pages kb').
  { intros k. unfold vdso_text_pages, vdso_image_of.
    change (length Vdso.vdso_images) with 1%nat. rewrite !Nat.mod_1_r. reflexivity. }
  unfold vdso_reserved, vdso_len. rewrite (E kb). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RI (CAPK CAPB : Z) (ne : nat) (bb : Z) (h : VmMaps) : Prop :=
     Z.of_nat (length (vm_reserved h ++ vm_maps h)) + Z.of_nat ne <= CAPK
  /\ Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_reserved h ++ vm_maps h)
  /\ live_bytes (vm_maps h) + bb <= CAPB
  /\ 0 <= bb
  /\ (bm_on = true \/ CAPBMAX <= vm_limit h)          (* [comment removed for export] *)
  /\ sp_window_lo <= bv_unsigned (vm_init_sp h).      (* [comment removed for export] *)

Lemma RI_weaken : forall CAPK CAPB ne ne' bb bb' h,
  RI CAPK CAPB ne bb h -> (ne' <= ne)%nat -> 0 <= bb' <= bb -> RI CAPK CAPB ne' bb' h.
Proof. intros CAPK CAPB ne ne' bb bb' h (R1 & R2 & R3 & R4 & R5 & R6) Hne Hbb. unfold RI. splits; auto; lia. Qed.

(* [comment removed for export] *)
Lemma RI_add : forall CAPK CAPB ne bb h (a : word) (n : Z) na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= n <= NMAX -> n <= bb -> bv_unsigned (Z_to_bv 64 n) = n ->
  RI CAPK CAPB ne (bb - n)
     (mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb h a n na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hn Hnb Hu. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  rewrite length_app_cons_mid, live_bytes_cons'. cbn [snd]. rewrite Hu. splits; auto; try lia.
  apply Forall_app_cons_mid; [exact R2| cbn [snd]; rewrite Hu; lia].
Qed.

(* [comment removed for export] *)
Lemma RI_tick : forall CAPK CAPB ne bb bb' h na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= bb' <= bb ->
  RI CAPK CAPB ne bb' (mkVmMapsFull (vm_reserved h) (vm_maps h) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb bb' h na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hbb. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp]. splits; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma RI_remove : forall CAPK CAPB ne bb bb' h (aw : word) na sb br,
  RI CAPK CAPB (S ne) bb h -> 0 <= bb' <= bb ->
  RI CAPK CAPB ne bb' (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros CAPK CAPB ne bb bb' h aw na sb br (R1 & R2 & R3 & R4 & R5 & R6) Hbb. unfold RI.
  cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
  unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
  rewrite length_app in R1 |- *. splits; auto; try lia.
  apply Forall_app in R2 as [R2a R2b]. apply Forall_app. split; [exact R2a| apply Forall_filter; exact R2b].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RI_grant_rw : forall CAPK CAPB ne bb (mo : Model) (n : Z),
  RI CAPK CAPB ne bb (m_vmmaps mo) -> CAPK <= CAPKMAX ->
  0 < n <= NMAX -> n mod page_size = 0 ->
  vm_backing_used mo + n <= vm_limit (m_vmmaps mo) ->
  exists a, grant_ok (Z_to_bv 64 0) mo a n = true.
Proof.
  intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R5 & R6) HK Hn Hnal Hfit.
  pose proof (alloc_top_ge_window _ R6) as Htop. pose proof NMAX_facts as (N0 & N1 & _).
  apply (grant_exists_gen (Z_to_bv 64 0) mo NMAX n CAPKMAX task_unmapped_base);
    [exact N0| exact N1| exact Hn| exact Hnal| exact R2| lia| rewrite task_unmapped_base_val; reflexivity| lia
    | rewrite task_unmapped_base_val; unfold NMAX, CAPKMAX; lia| exact Hfit].
Qed.

Lemma RI_grant_na : forall CAPK CAPB ne bb (mo : Model) (n : Z),
  RI CAPK CAPB ne bb (m_vmmaps mo) -> CAPK <= CAPKMAX ->
  0 < n <= NMAX -> n mod page_size = 0 ->
  exists a, grant_ok_na (Z_to_bv 64 0) mo a n = true.
Proof.
  intros CAPK CAPB ne bb mo n (R1 & R2 & R3 & R4 & R5 & R6) HK Hn Hnal.
  pose proof (alloc_top_ge_window _ R6) as Htop. pose proof NMAX_facts as (N0 & N1 & _).
  apply (grant_exists_na_gen (Z_to_bv 64 0) mo NMAX n CAPKMAX task_unmapped_base);
    [exact N0| exact N1| exact Hn| exact Hnal| exact R2| lia| rewrite task_unmapped_base_val; reflexivity| lia
    | rewrite task_unmapped_base_val; unfold NMAX, CAPKMAX; lia].
Qed.

Lemma RI_live_limit : forall CAPK CAPB ne bb h, RI CAPK CAPB ne bb h -> CAPB <= CAPBMAX ->
  bm_on = true \/ live_bytes (vm_maps h) + bb <= vm_limit h.
Proof. intros CAPK CAPB ne bb h (R1 & R2 & R3 & R4 & [R5|R5] & R6) HB; [left; exact R5| right; lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_grow_ok_aligned_elim : forall (m : Model) (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  bv_unsigned b mod page_size = 0 -> d mod page_size = 0 -> 0 < d -> 0 < bv_unsigned b ->
  bv_unsigned b + d < 2 ^ 64 ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  bv_unsigned b + d <= alloc_top h
  /\ region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hnw H.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = bv_unsigned b + d) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. fold b in H. rewrite Hureq in H.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) in H by lia. cbn [andb] in H.
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) in H by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d)) in H
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) in H by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b in H by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b) with (d + page_size) in H by lia.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].

  assert (Hb4 : page_size <= bv_unsigned b) by (clear - Hbal Hb0; unfold page_size in *; Z.div_mod_to_equations; lia).
  eapply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.AllocSim.region_free_prefix; [| exact H2]. rewrite !u64_lit by (unfold page_size in *; lia). unfold page_size; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EVENTS.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.                 (* [comment removed for export] *)
Hypothesis Halloc : sc_alloc scfg = false.   (* [comment removed for export] *)
Variable resv_img : list (word * word).
Variable img_hi : Z.

(* [comment removed for export] *)

Variable CAPK CAPB : Z.
Hypothesis HCAPK : CAPK <= CAPKMAX.
Hypothesis HCAPB : CAPB <= CAPBMAX.

Local Notation KL := (KL2 resv_img img_hi).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma step_brk0 : forall L pbrk ms mo K,
  KL L pbrk (m_vmmaps mo) -> ld_brk L = BPUntried ->
  m_halted mo = None -> m_vm_lazy mo = [] ->
  Nodes.at_node segs (NBrk 0) ms ->
  (let r := bv_unsigned (vm_brk (m_vmmaps mo)) in
   let rsp := mkEffectU (vm_brk (m_vmmaps mo)) [] [] [] [] [] in
   dec_brk0 rsp = Some r ->
   brk0_answer_ok r = true ->
   KL (set_brkph (BPQueried r) L) r (m_vmmaps mo) ->
   srealizes segs scfg (mkCfg (nret ms rsp) mo) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo K HK Hph Hh Hl Hat HC.
  destruct (KL2_brk0 resv_img img_hi L pbrk (m_vmmaps mo) HK Hph) as [Hans HK'].
  eapply (bn_brk_query segs scfg); [exact Hh| exact Hl| exact Hat|].
  apply HC; [reflexivity| exact Hans| exact HK'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_brk_same : forall cur req (b : word), bv_unsigned b = cur ->
  dec_brk cur req (mkEffectU b [] [] [] [] []) = Some BrkSame.
Proof. intros cur req b Hb. unfold dec_brk. rewrite Hb, Z.eqb_refl. reflexivity. Qed.

Lemma dec_brk_grown : forall cur d (b : word), bv_unsigned b = cur ->
  cur mod page_size = 0 -> d mod page_size = 0 -> 0 < d -> 0 <= cur -> cur + d < 2 ^ 64 ->
  dec_brk cur (cur + d) (mkEffectU (Z_to_bv 64 (cur + d)) [] [(b, Z_to_bv 64 d)] [] [] []) = Some BrkGrown.
Proof.
  intros cur d b Hb Hcal Hdal Hd Hc Hnw. unfold dec_brk.
  rewrite u64_lit by lia. replace (cur + d =? cur) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
  rewrite Z.eqb_refl. unfold brk_new_pages.
  rewrite (page_round_up_Z_aligned cur) by (first [lia | exact Hcal]).
  rewrite (page_round_up_Z_aligned (cur + d)) by (first [lia | rewrite Z.add_mod, Hcal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [zeros_of]. replace (cur + d - cur) with d by lia.
  unfold wa. rewrite <- Hb, Z_to_bv_bv_unsigned. cbn [listNN_eqb]. rewrite !bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_brk_grow : forall L pbrk ms mo (d : Z) ne bb K (e := EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + d)),
  let h := m_vmmaps mo in let b := vm_brk h in let req := bv_unsigned b + d in
  KL L pbrk h ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> d <= bb -> 0 < d <= NMAX -> d mod page_size = 0 ->
  pbrk = bv_unsigned b -> bv_unsigned b mod PGSZ = 0 -> 0 < bv_unsigned b -> bv_unsigned b + d < 2 ^ 64 ->
  bv_unsigned (vm_start_brk h) <= bv_unsigned b + d ->
  (answer_ok L e pbrk = true /\ KL (event_post L e pbrk) pbrk h) ->
  (region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 d) = true -> bv_unsigned b + d <= alloc_ceiling ->
   answer_ok L e req = true /\
   KL (event_post L e req) req
      (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                    (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h))) ->
  Nodes.at_node segs (NBrk req) ms ->
  (* [comment removed for export] *)
  (let rsp := mkEffectU b [] [] [] [] [] in
   dec_brk pbrk req rsp = Some BrkSame ->
   answer_ok L e pbrk = true ->
   KL (event_post L e pbrk) pbrk h ->
   RI CAPK CAPB ne bb h ->
   srealizes segs scfg (mkCfg (nret ms rsp) mo) K) ->
  (* [comment removed for export] *)
  (let rsp := mkEffectU (Z_to_bv 64 req) [] [(b, Z_to_bv 64 d)] [] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                          (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_brk pbrk req rsp = Some BrkGrown ->
   answer_ok L e req = true ->
   KL (event_post L e req) req h' ->
   RI CAPK CAPB ne (bb - d) h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo d ne bb K e h b req HK Hh Hl Hm HRI Hdb Hd Hdal Hpb Hbal Hb0 Hnw Hsb [HansR HKR] HG Hat HREF HGRANT.
  pose proof (u64_range b) as Hbr.
  assert (Hbal' : bv_unsigned b mod page_size = 0) by (unfold page_size; unfold PGSZ in Hbal; exact Hbal).
  eapply (bn_brk_grow segs scfg Halloc ms mo d K Hh Hl); [exact Hat| exact Hbal'| exact Hdal| lia| exact Hb0| exact Hnw| exact Hsb| |].
  -
    apply HREF; [apply dec_brk_same; symmetry; exact Hpb| exact HansR| exact HKR|].
    eapply (RI_weaken CAPK CAPB (S ne) ne bb bb); [| lia| pose proof HRI as (_ & _ & _ & R4 & _); lia].
    subst h. rewrite <- (vmmaps_eta (m_vmmaps mo)) in HRI. exact HRI.
  -
    intros Hadm.
    destruct (brk_grow_ok_aligned_elim mo d Hbal' Hdal ltac:(lia) Hb0 Hnw Hadm) as [Hce Hrf].
    change (m_vmmaps mo) with h in Hce. rewrite (KL2_alloc_top _ _ _ _ _ HK) in Hce.
    destruct (HG Hrf Hce) as [HansG HKG].
    apply HGRANT; [| exact HansG| exact HKG|].
    + rewrite Hpb. apply dec_brk_grown; first [reflexivity| assumption| lia].
    + apply RI_add; [exact HRI| lia| exact Hdb| apply u64_lit; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_MAPF : (Z.land MAPF MAP_FIXED =? 0) = true.
Proof. reflexivity. Qed.

Lemma answer_ok_mmap : forall L a len prot z,
  answer_ok L (EMmap a len prot MAPF) z = mmap_answer_ok (lranges L) len z.
Proof. intros. unfold answer_ok. rewrite land_MAPF. reflexivity. Qed.

Lemma event_post_mmap_rw : forall L len z, is_err z = false ->
  event_post L (EMmap 0 len PROT_RW MAPF) z = set_groups ((z, len) :: ld_groups L) L.
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.

Lemma event_post_mmap_none : forall L len z, is_err z = false ->
  event_post L (EMmap 0 len PROT_NONE MAPF) z = set_metas ((z, len, 0) :: ld_metas L) L.
Proof. intros L len z Hz. unfold event_post. rewrite land_MAPF, Hz. reflexivity. Qed.

Lemma mmap_addr_ok_nil : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  mmap_addr_ok len [] (bv_unsigned a) = true.
Proof.
  intros len a H1 H2 H3. unfold mmap_addr_ok. rewrite H1, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _) H2).
  rewrite (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

Lemma dec_mmap_ok : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  dec_mmap len [] (mkEffectU a [] [(a, Z_to_bv 64 (mmap_len len))] [] [] []) = Some (MmOk (bv_unsigned a)).
Proof.
  intros len a H1 H2 H3. unfold dec_mmap. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.

Lemma dec_mmap_none_ok : forall len (a : word),
  bv_unsigned a mod page_size = 0 -> 0 < bv_unsigned a -> bv_unsigned a + mmap_len len <= alloc_ceiling ->
  dec_mmap_none len [] (mkEffectU a [] [] [(a, Z_to_bv 64 (mmap_len len))] [] []) = Some (MmOk (bv_unsigned a)).
Proof.
  intros len a H1 H2 H3. unfold dec_mmap_none. rewrite !bv_eqb_refl, (mmap_addr_ok_nil len a H1 H2 H3). reflexivity.
Qed.


Lemma step_mmap_rw : forall L pbrk ms mo len ne bb K (e := EMmap 0 len PROT_RW MAPF),
  let h := m_vmmaps mo in let n := mmap_len len in
  KL L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> n <= bb -> n <= NMAX ->
  Nodes.at_node segs (NMmap 0 len 3 34) ms ->
  K [] ->
  (forall a : word,
     let z := bv_unsigned a in
     let rsp := mkEffectU a [] [(a, Z_to_bv 64 n)] [] [] [] in
     let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) (vm_noaccess h) (vm_start_brk h)
                            (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
     dec_mmap len [] rsp = Some (MmOk z) ->
     answer_ok L e z = true -> is_err z = false ->
     KL (event_post L e z) pbrk h' ->
     RI CAPK CAPB ne (bb - n) h' ->
     srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HnN Hat HK0 HC. subst e.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
  assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
  assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NMAX in HnN; lia).

  destruct (Z.leb (vm_backing_used mo + n) (vm_limit (m_vmmaps mo))) eqn:Hfit.
  2:{ destruct (RI_live_limit _ _ _ _ _ HRI HCAPB) as [Hon|Hll].
      - apply (bn_mmap_rw_refused segs scfg ms mo len K Hon Hh Hat); [unfold LEN_MAX in Hlen; lia| |].
        + change (page_round_up_Z len) with n. exact Hfit.
        + exact HK0.
      - exfalso. apply Z.leb_gt in Hfit. pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.vm_backing_used_le_live mo Hl Hm). unfold vm_live_bytes in *. fold h in Hll. subst h. lia. }
  apply Z.leb_le in Hfit.
  eapply (bn_mmap_rw segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| |].
  - change (page_round_up_Z len) with n. eapply (RI_grant_rw CAPK CAPB (S ne) bb mo n HRI HCAPK); [lia| exact HnA| exact Hfit].
  - intros a Hg. change (page_round_up_Z len) with n in Hg |- *.
    destruct (grant_ok_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4 & G5).
    fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
    destruct (KL2_mmap_new resv_img img_hi L pbrk h a len false HK Hq Hlen
                ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
    unfold mmap_model. fold h. apply HC.
    + apply dec_mmap_ok; [exact G1| exact G2| exact G3].
    + rewrite answer_ok_mmap. exact Hans.
    + exact Herr.
    + rewrite (event_post_mmap_rw L len _ Herr). exact HK'.
    + apply RI_add; [exact HRI| lia| exact Hnb| exact Hun].
Qed.

Lemma step_mmap_none : forall L pbrk ms mo len ne bb K (e := EMmap 0 len PROT_NONE MAPF),
  let h := m_vmmaps mo in let n := mmap_len len in
  KL L pbrk h -> brk_quiet L -> 0 < len < LEN_MAX ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h -> n <= bb -> n <= NMAX ->
  Nodes.at_node segs (NMmap 0 len 0 34) ms ->
  (forall a : word,
     let z := bv_unsigned a in
     let rsp := mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] [] in
     let h' := mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) ((a, Z_to_bv 64 n) :: vm_noaccess h)
                            (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
     dec_mmap_none len [] rsp = Some (MmOk z) ->
     answer_ok L e z = true -> is_err z = false ->
     KL (event_post L e z) pbrk h' ->
     RI CAPK CAPB ne (bb - n) h' ->
     srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo len ne bb K e h n HK Hq Hlen Hh Hl Hm HRI Hnb HnN Hat HC. subst e.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. fold n in Hn1.
  assert (HnA : n mod page_size = 0) by (unfold n; apply mmap_len_aligned).
  assert (Hun : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; unfold NMAX in HnN; lia).
  eapply (bn_mmap_none segs scfg Halloc ms mo len K Hh Hl Hat); [unfold LEN_MAX in Hlen; lia| |].
  - change (page_round_up_Z len) with n. eapply (RI_grant_na CAPK CAPB (S ne) bb mo n HRI HCAPK); [lia| exact HnA].
  - intros a Hg. change (page_round_up_Z len) with n in Hg |- *.
    destruct (grant_ok_na_unpack _ _ _ _ Hg) as (G1 & G2 & G3 & G4).
    fold h in G3. rewrite (KL2_alloc_top _ _ _ _ _ HK) in G3.
    destruct (KL2_mmap_new resv_img img_hi L pbrk h a len true HK Hq Hlen
                ltac:(unfold PGSZ; unfold page_size in G1; exact G1) G2 G3 G4) as (HK' & Hans & Herr).
    unfold noaccess_model. fold h. apply HC.
    + apply dec_mmap_none_ok; [exact G1| exact G2| exact G3].
    + rewrite answer_ok_mmap. exact Hans.
    + exact Herr.
    + rewrite (event_post_mmap_none L len _ Herr). exact HK'.
    + apply RI_add; [exact HRI| lia| exact Hnb| exact Hun].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_mmap_fixed_ok : forall addr (aw : word), aw = Z_to_bv 64 addr -> 0 <= addr <= 2^64 - 4096 ->
  dec_mmap_fixed addr PGSZ (mkEffectU aw [] [] [(aw, Z_to_bv 64 PGSZ)] [] []) = Some FxDone.
Proof.
  intros addr aw -> Ha. unfold dec_mmap_fixed.
  rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]).
  rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by lia. reflexivity.
Qed.

Lemma step_mmap_fixed : forall L pbrk ms mo cur ne bb K,
  let h := m_vmmaps mo in
  let a := round_up_pg cur in
  let e := EMmap a PGSZ PROT_NONE MAPFX in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  KL L pbrk h -> ld_brk L = BPGuard cur ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  Nodes.at_node segs (NMmap a PGSZ 0 50) ms ->
  (let rsp := mkEffectU aw [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_mmap_fixed a PGSZ rsp = Some FxDone ->
   answer_ok L e a = true ->
   KL (event_post L e a) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo cur ne bb K h a e aw nw HK Hph Hh Hl Hm HRI Hat HC. subst e aw nw. subst a.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_mmap_fixed resv_img img_hi L pbrk h cur HK Hph) as (Ea & Hcal & Hc0 & Hce & Hrf & Hmc & Hans & HK').
  rewrite !Ea in Hrf. rewrite !Ea in Hmc. rewrite !Ea in Hans. rewrite !Ea in HK'. rewrite !Ea in Hat. rewrite !Ea in HC. rewrite ?Ea.
  set (aw := Z_to_bv 64 cur) in *. set (nw := Z_to_bv 64 PGSZ) in *.
  assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.
  eapply (bn_mmap_fixed segs scfg Halloc ms mo cur PGSZ K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hcal. exact Hcal.
  - lia.
  - unfold PGSZ; lia.
  - rewrite HprP. fold h. rewrite (KL2_alloc_top _ _ _ _ _ HK). lia.
  - rewrite HprP. exact Hrf.
  - rewrite HprP. exact Hmc.
  - rewrite HprP. fold nw. fold aw.
    rewrite (fixed_noaccess_model_simple aw nw mo Hl Hm). fold h.
    assert (Ua : bv_unsigned aw = cur) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_mmap_fixed_ok; [reflexivity| unfold PGSZ in *; lia].
    + unfold answer_ok. change (Z.land MAPFX MAP_FIXED =? 0) with false. exact Hans.
    + exact HK'.
    + eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_munmap_ok : forall a len (aw nw : word), aw = Z_to_bv 64 a -> nw = Z_to_bv 64 (mmap_len len) ->
  dec_munmap a len (mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] []) = Some (RgDone true).
Proof. intros a len aw nw -> ->. unfold dec_munmap. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma step_munmap : forall L pbrk ms mo a l0 len ne bb K (e := EMunmap a len),
  let h := m_vmmaps mo in
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  KL L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  Nodes.at_node segs (NMunmap a len) ms ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_munmap a len rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo a l0 len ne bb K e h n aw nw HK Hq Hin Hlen Hh Hl Hm HRI Hat HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
    as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
  fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
  assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
  eapply (bn_munmap segs scfg Halloc ms mo a len K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - lia.
  - lia.
  - rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
  - rewrite Hpr. exact Hhas.
  - rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
    unfold mmap_fixed_destroyed_next.
    rewrite (maps_subtract_has (vm_maps h) aw nw (k2_wf _ _ _ _ _ HK) Hhas).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
    + exact Hans.
    + exact HK'.
    + eapply RI_remove; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dec_mprotect_rw_ok : forall a (aw nw : word), aw = Z_to_bv 64 a -> nw = Z_to_bv 64 (mmap_len PGSZ) ->
  dec_mprotect_rw a PGSZ (mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] []) = Some (RgDone true).
Proof. intros a aw nw -> ->. unfold dec_mprotect_rw, dec_mprotect. rewrite !bv_eqb_refl. reflexivity. Qed.

Lemma step_mprotect : forall L pbrk ms mo b l k ne bb K,
  let h := m_vmmaps mo in
  let a := b + (1 + k) * PGSZ in
  let e := EMprotect a PGSZ PROT_RW in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 PGSZ in
  KL L pbrk h -> brk_quiet L -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  RI CAPK CAPB (S ne) bb h ->
  vdso_inc (m_kernel mo) h ->
  Nodes.at_node segs (NMprotect a PGSZ 3) ms ->
  K [] ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [(aw, nw)] [] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) a (a + PGSZ))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_mprotect_rw a PGSZ rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   RI CAPK CAPB ne bb h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo b l k ne bb K h a e aw nw HK Hq Hin Hk Hh Hl Hm HRI Hvd Hat HK0 HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_mprotect resv_img img_hi L pbrk h b l k HK Hq Hin Hk) as (Hal & Ha0 & Hce & Hcn & Hcm & Hans & HK').
  fold a in Hal, Ha0, Hce, Hcn, Hcm, HK', Hans |- *. fold aw nw in Hcn, Hcm, HK'.
  assert (HprP : page_round_up_Z PGSZ = PGSZ) by reflexivity.

  destruct (mprotect_budget_ok mo aw nw) eqn:Hfit.
  2:{ destruct (RI_live_limit _ _ _ _ _ HRI HCAPB) as [Hon|Hll].
      - apply (bn_mprotect_refused segs scfg ms mo a PGSZ K Hon Hh Hat); rewrite ?HprP.
        + unfold page_size. unfold PGSZ in Hal. exact Hal.
        + unfold PGSZ; lia.
        + lia.
        + unfold two_pow_64. lia.
        + exact (KL2_meta_page_free resv_img img_hi L pbrk h b l k _ HK Hin Hk Hvd).
        + exact Hcn.
        + exact Hcm.
        + fold nw. exact Hfit.
        + exact HK0.
      - exfalso. pose proof HRI as (_ & _ & _ & R4 & _).
        assert (Hok : mprotect_budget_ok mo aw nw = true); [| congruence].
        apply OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.mprotect_budget_ok_intro; [exact Hl| exact Hm|]. unfold vm_live_bytes. fold h. lia. }
  eapply (bn_mprotect segs scfg Halloc ms mo a PGSZ K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - unfold PGSZ; lia.
  - lia.
  - rewrite HprP. unfold two_pow_64. lia.
  - rewrite HprP. exact (KL2_meta_page_free resv_img img_hi L pbrk h b l k _ HK Hin Hk Hvd).
  - rewrite HprP. exact Hcn.
  - rewrite HprP. exact Hcm.
  - rewrite HprP. fold nw. exact Hfit.
  - rewrite HprP. fold aw nw. unfold mprotect_model. fold h.
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply u64_lit; unfold PGSZ; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_mprotect_rw_ok; [reflexivity|]. rewrite (mmap_len_of_aligned PGSZ) by (unfold PGSZ; first [lia| reflexivity]). reflexivity.
    + exact Hans.
    + exact HK'.
    + eapply RI_tick; [exact HRI| pose proof HRI as (_ & _ & _ & R4 & _); lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ev_step_brk0 : ev_step (EBrk 0) = (mbind (msys (NBrk 0) dec_brk0) (fun r => mbind (mupd (set_brk_ps r)) (fun _ => mret r))).
Proof. reflexivity. Qed.

Lemma ev_step_brk : forall req, req <> 0 ->
  ev_step (EBrk req) =
  mbind mget (fun s => mbind (msys (NBrk req) (dec_brk (ps_brk s) req))
     (fun a => match a with BrkGrown => mbind (mupd (set_brk_ps req)) (fun _ => mret req) | BrkSame => mret (ps_brk s) end)).
Proof. intros req H. unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) H). reflexivity. Qed.

Lemma ev_step_mmap_rw : forall len,
  ev_step (EMmap 0 len PROT_RW MAPF) =
  mbind (msys (NMmap 0 len PROT_RW MAPF) (dec_mmap len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.

Lemma ev_step_mmap_none : forall len,
  ev_step (EMmap 0 len PROT_NONE MAPF) =
  mbind (msys (NMmap 0 len PROT_NONE MAPF) (dec_mmap_none len [])) (fun a => mret match a with MmErr e => neg_errno e | MmOk x => x end).
Proof. reflexivity. Qed.

Lemma ev_step_mmap_fixed : forall a len,
  ev_step (EMmap a len PROT_NONE MAPFX) =
  mbind (msys (NMmap a len PROT_NONE MAPFX) (dec_mmap_fixed a len))
        (fun x => mret match x with FxKept e => neg_errno e | FxDone => a | FxLost e => neg_errno e end).
Proof. reflexivity. Qed.

Lemma ev_step_munmap : forall a len,
  ev_step (EMunmap a len) =
  mbind (msys (NMunmap a len) (dec_munmap a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.

Lemma ev_step_mprotect : forall a len prot,
  ev_step (EMprotect a len prot) =
  mbind (msys (NMprotect a len prot) (dec_mprotect_rw a len)) (fun x => mret match x with RgErr e => neg_errno e | RgDone _ => 0 end).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma machine_event : forall {A B} n (dec : resp -> option A) (f : A -> Monad.M PState B) (s : PState) Qm ms,
  implM segs (mbind (msys n dec) f) s Qm ms ->
  exists ms1, Exec.msteps segs ms ms1 /\ Nodes.at_node segs n ms1 /\
    forall rsp a, dec rsp = Some a -> exists ms2, Exec.msteps segs (nret ms1 rsp) ms2 /\ implM segs (f a) s Qm ms2.
Proof.
  intros A B n dec f s Qm ms H. apply implM_bind_inv, implM_msys_inv in H.
  destruct H as (ms1 & Hms & Hat & Hk). exists ms1. split; [exact Hms|]. split; [exact Hat|].
  intros rsp a E. destruct (Hk rsp a E) as (ms2 & Hms2 & H2). exists ms2. auto.
Qed.

Lemma srz_cj_msteps : forall ms ms' mo mo0 K,
  mo = with_vmmaps (m_vmmaps mo) mo0 -> m_halted mo0 = None -> m_vm_lazy mo0 = [] ->
  Exec.msteps segs ms ms' -> srealizes segs scfg (mkCfg ms' mo) K -> srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros ms ms' mo mo0 K Emo Hh Hl Hms Hc.
  eapply srz_msteps; [rewrite Emo, with_vmmaps_halted; exact Hh| rewrite Emo, with_vmmaps_lazy'; exact Hl| apply cj_msteps_cat; exact Hms| exact Hc].
Qed.

Theorem embed : forall {R} (t : M R) L Post (E : ev -> Prop) (ne : nat) (bb : Z) (Q : R -> Prop)
    (s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) K,
  ctree_ok L t Post ->
  gtree E ne bb t Q ->
  (forall a len prot flags, E (EMmap a len prot flags) -> is_fixed flags = false -> mmap_len len <= NMAX) ->
  implM segs (membed t) s Qm ms ->
  KL L (ps_brk s) (m_vmmaps mo) ->
  mo = with_vmmaps (m_vmmaps mo) mo0 ->
  m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
  RI CAPK CAPB ne bb (m_vmmaps mo) ->
  vdso_inc (m_kernel mo0) (m_vmmaps mo) ->
  (forall r s' ms' mo' L' c n,
     Qm r s' ms' -> cpathw ecost L t L' r c n -> Post L' r -> Q r ->
     KL L' (ps_brk s') (m_vmmaps mo') ->
     mo' = with_vmmaps (m_vmmaps mo') mo0 ->
     RI CAPK CAPB (ne - n)%nat (bb - c) (m_vmmaps mo') ->
     vdso_inc (m_kernel mo0) (m_vmmaps mo') ->
     ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
     srealizes segs scfg (mkCfg ms' mo') K) ->
  K [] ->                                             (* [comment removed for export] *)
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros R t. induction t as [r|e k IH]; intros L Post E ne bb Q s Qm ms mo mo0 K Hct Hgt HE Himpl HK Emo Hh Hl Hm HRI Hvd CONT HK0.
  -
    cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
    eapply (CONT r s ms' mo L 0 0%nat HQ (cpw_ret ecost L r) Hct Hgt HK Emo); try reflexivity.
    eapply RI_weaken; [exact HRI| lia| pose proof HRI as (_ & _ & _ & R4 & _); lia].
    exact Hvd.
  -
    cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
    assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    destruct (gtree_vis_inv E ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
    cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
    assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
    assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
    pose proof HRI as (_ & _ & _ & Hbb0 & _).
    assert (Hvdm : vdso_inc (m_kernel mo) (m_vmmaps mo)) by (rewrite Emo at 1; exact Hvd).
    assert (KONT : forall z (s1 : PState) ms2 (mo1 : Model) (bb1 : Z),
              answer_ok L e z = true -> good e z ->
              implM segs (membed (k z)) s1 Qm ms2 ->
              KL (event_post L e z) (ps_brk s1) (m_vmmaps mo1) ->
              mo1 = with_vmmaps (m_vmmaps mo1) mo0 ->
              RI CAPK CAPB ne' bb1 (m_vmmaps mo1) -> 0 <= bb - ecost e <= bb1 ->
              ps_m s1 = ps_m s -> ps_fa s1 = ps_fa s -> ps_so s1 = ps_so s ->
              vdso_inc (m_kernel mo0) (m_vmmaps mo1) ->
              srealizes segs scfg (mkCfg ms2 mo1) K).
    { intros z s1 ms2 mo1 bb1 Hans Hgood Hi1 HK1 Emo1 HRI1 Hbb1 E1 E2 E3 Hvd1.
      eapply (IH z (event_post L e z) Post E ne' (bb - ecost e) Q s1 Qm ms2 mo1 mo0 K (Hk z Hans) (Hg z Hgood) HE Hi1 HK1 Emo1 Hh Hl Hm).
      - eapply RI_weaken; [exact HRI1| lia| lia].
      - exact Hvd1.
      - intros r s' ms' mo' L' c n HQ' Hcp HP HQr HK' Emo' HRI' Hvd' E1' E2' E3'.
        eapply (CONT r s' ms' mo' L' (ecost e + c) (S n) HQ'); [eapply cpw_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK'| exact Emo'
          | replace (bb - (ecost e + c)) with (bb - ecost e - c) by lia; exact HRI'| exact Hvd'| congruence| congruence| congruence].
      - exact HK0. }
    clear IH CONT Hk Hg.
    destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [event_pre] in Hpre; try contradiction.
    +
      destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
      *
        rewrite ev_step_brk0 in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        eapply step_brk0; [exact HK| exact Hph| exact Hh'| exact Hl'| exact Hat|].
        intros r0 rsp Hdec Hans HK'.
        destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
        destruct Hi2 as (ms3 & Hms3 & Hi3).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
        eapply (KONT r0 (set_brk_ps r0 s) ms3 mo bb);
          [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| eapply RI_weaken; [exact HRI| lia| lia]| cbn [ecost Z.eqb]; lia
          | reflexivity| reflexivity| reflexivity| exact Hvd].
      *
        destruct (KL2_brk_grow1 resv_img img_hi L (ps_brk s) (m_vmmaps mo) cur HK Hph)
          as (Ecur & Epbrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
        rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
        rewrite Ereq in *. rewrite <- Epbrk in HREF.
        destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + 2 * PGSZ)) = 2 * PGSZ).
        { cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
        rewrite Hc2 in *.
        eapply (step_brk_grow L (ps_brk s) ms1 mo (2 * PGSZ) ne' bb K HK Hh' Hl' Hm' HRI);
          [lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| lia| exact Hbal| exact Hb0| exact Hnw| exact Hsb
          | exact HREF| exact HGR| exact Hat| |].
        --
           intros rsp Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT (ps_brk s) s ms3 mo bb);
             [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| unfold PGSZ in *; lia
             | reflexivity| reflexivity| reflexivity| exact Hvd].
        --
           intros rsp h' Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
           destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - 2 * PGSZ));
             [exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
      *
        destruct (KL2_brk_grow2 resv_img img_hi L (ps_brk s) (m_vmmaps mo) b l HK Hph Hreg)
          as (Epbrk & Ebrk & Ereq & Hbal & Hb0 & Hnw & Hsb & Hne0 & HREF & HGR).
        rewrite (ev_step_brk _ Hne0) in Himpl. apply implM_mget_inv in Himpl.
        rewrite Ereq in *. rewrite <- Epbrk in HREF.
        assert (Epbrk' : ps_brk s = bv_unsigned (vm_brk (m_vmmaps mo))) by lia.
        destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        assert (Hc2 : ecost (EBrk (bv_unsigned (vm_brk (m_vmmaps mo)) + PGSZ)) = 2 * PGSZ).
        { cbn [ecost]. rewrite (proj2 (Z.eqb_neq _ _) Hne0). reflexivity. }
        rewrite Hc2 in *.
        eapply (step_brk_grow L (ps_brk s) ms1 mo PGSZ ne' bb K HK Hh' Hl' Hm' HRI);
          [unfold PGSZ in *; lia| pose proof NMAX_facts; unfold PGSZ in *; lia| unfold PGSZ, page_size; reflexivity| exact Epbrk'| exact Hbal| exact Hb0| exact Hnw| exact Hsb
          | exact HREF| exact HGR| exact Hat| |].
        --
           intros rsp Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT (ps_brk s) s ms3 mo bb);
             [exact Hans| exact I| exact Hi3| exact HK'| exact Emo| exact HRI'| unfold PGSZ in *; lia
             | reflexivity| reflexivity| reflexivity| exact Hvd].
        --
           intros rsp h' Hdec Hans HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_mupd_inv, implM_ret_inv in Hi2.
           destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT _ (set_brk_ps _ s) ms3 _ (bb - PGSZ));
             [exact Hans| exact I| exact Hi3| cbn [ps_brk set_brk_ps]; rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| unfold PGSZ in *; lia
             | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
    +
      destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
      *
        assert (Hc2 : ecost (EMmap 0 len prot MAPF) = mmap_len len) by reflexivity. rewrite Hc2 in *.
        pose proof (HE 0 len prot MAPF HEe eq_refl) as HnN.
        destruct Hprot as [-> | ->].
        --
           rewrite ev_step_mmap_none in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
           eapply (step_mmap_none L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HnN Hat).
           intros aw z rsp h' Hdec Hans Herr HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT z s ms3 _ (bb - mmap_len len));
             [exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
        --
           rewrite ev_step_mmap_rw in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
           eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
           eapply (step_mmap_rw L (ps_brk s) ms1 mo len ne' bb K HK Hq Hlen Hh' Hl' Hm' HRI Hcost HnN Hat HK0).
           intros aw z rsp h' Hdec Hans Herr HK' HRI'.
           destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
           eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
           eapply (KONT z s ms3 _ (bb - mmap_len len));
             [exact Hans| cbn [good]; right; exact Herr| exact Hi3| rewrite with_vmmaps_vm; exact HK'
             | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
             | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
      *
        assert (Hc2 : ecost (EMmap (round_up_pg cur) PGSZ PROT_NONE MAPFX) = 0) by reflexivity. rewrite Hc2 in *.
        rewrite ev_step_mmap_fixed in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
        eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
        eapply (step_mmap_fixed L (ps_brk s) ms1 mo cur ne' bb K HK Hph Hh' Hl' Hm' HRI Hat).
        intros rsp h' Hdec Hans HK' HRI'.
        destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
        eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
        eapply (KONT (round_up_pg cur) s ms3 _ bb);
          [exact Hans| cbn [good]; left; reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
          | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
          | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
    +
      destruct Hpre as (Hq & l0 & Hin & Hlen).
      assert (Hc2 : ecost (EMunmap a len) = 0) by reflexivity. rewrite Hc2 in *.
      rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
      eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
      eapply (step_munmap L (ps_brk s) ms1 mo a l0 len ne' bb K HK Hq Hin Hlen Hh' Hl' Hm' HRI Hat).
      intros rsp h' Hdec Hans HK' HRI'.
      destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
      eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
      eapply (KONT 0 s ms3 _ bb);
        [exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
        | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
        | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
    +
      destruct Hpre as (Hq & -> & -> & b & l & kk & Hin & -> & Hk2).
      assert (Hc2 : ecost (EMprotect (b + (1 + kk) * PGSZ) PGSZ PROT_RW) = 0) by reflexivity. rewrite Hc2 in *.
      rewrite ev_step_mprotect in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
      eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
      eapply (step_mprotect L (ps_brk s) ms1 mo b l kk ne' bb K HK Hq Hin Hk2 Hh' Hl' Hm' HRI Hvdm Hat HK0).
      intros rsp h' Hdec Hans HK' HRI'.
      destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
      eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
      eapply (KONT 0 s ms3 _ bb);
        [exact Hans| reflexivity| exact Hi3| rewrite with_vmmaps_vm; exact HK'
        | rewrite Emo, with_vmmaps_twice, with_vmmaps_vm; reflexivity| rewrite with_vmmaps_vm; exact HRI'| lia
        | reflexivity| reflexivity| reflexivity| vdso_keep_tac].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_shrunk (h0 h : VmMaps) : Prop :=
     vm_reserved h = vm_reserved h0
  /\ (length (vm_maps h) <= length (vm_maps h0))%nat
  /\ live_bytes (vm_maps h) <= live_bytes (vm_maps h0)
  /\ (Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h0) -> Forall (fun p => bv_unsigned (snd p) <= NMAX) (vm_maps h))
  /\ vm_limit h = vm_limit h0 /\ vm_mmap_base h = vm_mmap_base h0.

Lemma vm_shrunk_refl : forall h, vm_shrunk h h.
Proof. intros h. unfold vm_shrunk. repeat split; auto; lia. Qed.

Lemma vm_shrunk_remove : forall h0 h aw na sb br,
  vm_shrunk h0 h ->
  vm_shrunk h0 (mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) na sb br (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
Proof.
  intros h0 h aw na sb br (S1 & S2 & S3 & S4 & S5 & S6). unfold vm_shrunk. cbn [vm_reserved vm_maps vm_limit vm_mmap_base vm_init_sp].
  pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.live_bytes_map_remove_le (vm_maps h) aw) as Hlb.
  unfold map_remove in *. pose proof (length_filter_le (fun p : word * word => negb (bv_eqb (fst p) aw)) (vm_maps h)) as Hlen.
  splits; auto; try lia. intros HF. apply Forall_filter. apply S4. exact HF.
Qed.

Lemma step_munmap_free : forall L pbrk ms mo a l0 len K (e := EMunmap a len),
  let h := m_vmmaps mo in
  let n := mmap_len l0 in
  let aw := Z_to_bv 64 a in let nw := Z_to_bv 64 n in
  KL L pbrk h -> brk_quiet L -> In (a, l0) (ld_groups L) -> (len = l0 \/ len = round_up_pg l0) ->
  m_halted mo = None -> m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  Nodes.at_node segs (NMunmap a len) ms ->
  (let rsp := mkEffectU (Z_to_bv 64 0) [] [] [(aw, nw)] [] [] in
   let h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))
                          (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) in
   dec_munmap a len rsp = Some (RgDone true) ->
   answer_ok L e 0 = true ->
   KL (event_post L e 0) pbrk h' ->
   srealizes segs scfg (mkCfg (nret ms rsp) (with_vmmaps h' mo)) K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros L pbrk ms mo a l0 len K e h n aw nw HK Hq Hin Hlen Hh Hl Hm Hat HC. subst e.
  pose proof alloc_ceiling_lt as Hcl.
  destruct (KL2_munmap resv_img img_hi L pbrk h a l0 len HK Hq Hin Hlen)
    as (Hlen1 & Hlen2 & Hal & Ha0 & Hn0 & Hce & Hhas & Hans & HK' & Hcnt & Hlb).
  fold n aw nw in Hhas, HK', Hcnt, Hlb, Hlen2, Hn0, Hce.
  assert (Hpr : page_round_up_Z len = n) by (rewrite <- Hlen2; reflexivity).
  eapply (bn_munmap segs scfg Halloc ms mo a len K Hh Hl Hat).
  - unfold page_size. unfold PGSZ in Hal. exact Hal.
  - lia.
  - lia.
  - rewrite Hpr. unfold TASK_SIZE. pose_ceil. lia.
  - rewrite Hpr. exact Hhas.
  - rewrite Hpr. fold aw nw. rewrite (munmap_model_simple aw nw mo Hl Hm). fold h.
    unfold mmap_fixed_destroyed_next.
    rewrite (maps_subtract_has (vm_maps h) aw nw (k2_wf _ _ _ _ _ HK) Hhas).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply u64_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply u64_lit; lia).
    rewrite Ua, Un. apply HC.
    + apply dec_munmap_ok; [reflexivity| rewrite Hlen2; reflexivity].
    + exact Hans.
    + exact HK'.
Qed.

Theorem embed_free : forall {R} (t : M R) L Post (ne : nat) (bb : Z) (Q : R -> Prop)
    (s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) (h0 : VmMaps) K,
  ctree_ok L t Post ->
  gtree efree_ok ne bb t Q ->
  implM segs (membed t) s Qm ms ->
  KL L (ps_brk s) (m_vmmaps mo) ->
  mo = with_vmmaps (m_vmmaps mo) mo0 ->
  m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
  vm_shrunk h0 (m_vmmaps mo) ->
  (forall r s' ms' mo' L',
     Qm r s' ms' -> cpath L t L' r -> Post L' r -> Q r ->
     KL L' (ps_brk s') (m_vmmaps mo') ->
     mo' = with_vmmaps (m_vmmaps mo') mo0 ->
     vm_shrunk h0 (m_vmmaps mo') ->
     ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
     srealizes segs scfg (mkCfg ms' mo') K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros R t. induction t as [r|e k IH]; intros L Post ne bb Q s Qm ms mo mo0 h0 K Hct Hgt Himpl HK Emo Hh Hl Hm HS CONT.
  - cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
    eapply (CONT r s ms' mo L HQ (cpath_ret L r) Hct Hgt HK Emo HS); reflexivity.
  - cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
    assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    destruct (gtree_vis_inv efree_ok ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
    cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
    assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
    assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
    destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [efree_ok] in HEe; try contradiction.
    cbn [event_pre] in Hpre. destruct Hpre as (Hq & l0 & Hin & Hlen).
    rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    eapply (step_munmap_free L (ps_brk s) ms1 mo a l0 len K HK Hq Hin Hlen Hh' Hl' Hm' Hat).
    intros rsp h' Hdec Hans HK'.
    destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
    eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
    eapply (IH 0 (event_post L (EMunmap a len) 0) Post ne' (bb - ecost (EMunmap a len)) Q s Qm ms3 _ mo0 h0 K
              (Hk 0 Hans) (Hg 0 eq_refl) Hi3).
    + rewrite with_vmmaps_vm. exact HK'.
    + rewrite Emo, with_vmmaps_twice, with_vmmaps_vm. reflexivity.
    + exact Hh. + exact Hl. + exact Hm.
    + rewrite with_vmmaps_vm. apply vm_shrunk_remove. exact HS.
    + intros r s' ms' mo' L' HQ' Hcp HP HQr HK'' Emo' HS' E1 E2 E3.
      eapply (CONT r s' ms' mo' L' HQ'); [eapply cpath_vis; [exact Hans| exact Hcp]| exact HP| exact HQr| exact HK''| exact Emo'| exact HS'| exact E1| exact E2| exact E3].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma live_bytes_map_remove_has : forall l (a n : word), map_has l a n = true ->
  live_bytes (map_remove l a) + bv_unsigned n <= live_bytes l.
Proof.
  induction l as [|[b s] l IH]; intros a n H; [cbn in H; discriminate|].
  unfold map_has in H. cbn [existsb fst snd] in H. fold (map_has l a n) in H.
  unfold map_remove. cbn [List.filter fst]. fold (map_remove l a).
  destruct (bv_eqb b a) eqn:Eb; cbn [negb andb] in H |- *.
  - destruct (bv_eqb s n) eqn:Es.
    + apply bv_eqb_eq in Es. subst s. pose proof (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0094.RefNodes.live_bytes_map_remove_le l a). cbn [live_bytes]. lia.
    + pose proof (IH a n H). cbn [live_bytes]. pose proof (u64_range s). lia.
  - cbn [live_bytes]. pose proof (IH a n H). lia.
Qed.

Theorem embed_freew : forall {R} (t : M R) L Post (ne : nat) (bb : Z) (Q : R -> Prop)
    (s : PState) (Qm : R -> PState -> machine_state -> Prop) ms (mo mo0 : Model) (h0 : VmMaps) (u0 k0 : Z) K,
  ctree_ok L t Post ->
  gtree efree_ok ne bb t Q ->
  implM segs (membed t) s Qm ms ->
  KL L (ps_brk s) (m_vmmaps mo) ->
  mo = with_vmmaps (m_vmmaps mo) mo0 ->
  m_halted mo0 = None -> m_vm_lazy mo0 = [] -> m_vm_materialized mo0 = [] ->
  vm_shrunk h0 (m_vmmaps mo) ->
  live_bytes (vm_maps (m_vmmaps mo)) + u0 <= live_bytes (vm_maps h0) ->
  Z.of_nat (length (vm_maps (m_vmmaps mo))) + k0 <= Z.of_nat (length (vm_maps h0)) ->
  (forall r s' ms' mo' L' u n,
     Qm r s' ms' -> cpathw unmap_len L t L' r u n -> Post L' r -> Q r ->
     KL L' (ps_brk s') (m_vmmaps mo') ->
     mo' = with_vmmaps (m_vmmaps mo') mo0 ->
     vm_shrunk h0 (m_vmmaps mo') ->
     live_bytes (vm_maps (m_vmmaps mo')) + (u0 + u) <= live_bytes (vm_maps h0) ->
     Z.of_nat (length (vm_maps (m_vmmaps mo'))) + (k0 + Z.of_nat n) <= Z.of_nat (length (vm_maps h0)) ->
     ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
     srealizes segs scfg (mkCfg ms' mo') K) ->
  srealizes segs scfg (mkCfg ms mo) K.
Proof.
  intros R t. induction t as [r|e k IH]; intros L Post ne bb Q s Qm ms mo mo0 h0 u0 k0 K Hct Hgt Himpl HK Emo Hh Hl Hm HS HU HN CONT.
  - cbn [membed] in Himpl. apply implM_ret_inv in Himpl. destruct Himpl as (ms' & Hms & HQ).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    cbn [ctree_ok] in Hct. cbn [gtree] in Hgt.
    eapply (CONT r s ms' mo L 0 0%nat HQ (cpw_ret unmap_len L r) Hct Hgt HK Emo HS); [rewrite Z.add_0_r; exact HU| cbn [Z.of_nat]; rewrite Z.add_0_r; exact HN| reflexivity| reflexivity| reflexivity].
  - cbn [ctree_ok] in Hct. destruct Hct as [Hpre Hk].
    assert (Hne : match e with EUndef _ => False | _ => True end) by (destruct e; cbn in Hpre; auto).
    destruct (gtree_vis_inv efree_ok ne bb e k Q Hgt Hne) as (ne' & -> & HEe & Hcost & Hg). clear Hgt Hne.
    cbn [membed] in Himpl. apply implM_bind_inv in Himpl.
    assert (Hh' : m_halted mo = None) by (rewrite Emo, with_vmmaps_halted; exact Hh).
    assert (Hl' : m_vm_lazy mo = []) by (rewrite Emo, with_vmmaps_lazy'; exact Hl).
    assert (Hm' : m_vm_materialized mo = []) by (rewrite Emo, with_vmmaps_mat; exact Hm).
    destruct e as [req|a len prot flags|a len|a len prot|p c hh|u]; cbn [efree_ok] in HEe; try contradiction.
    cbn [event_pre] in Hpre. destruct Hpre as (Hq & l0 & Hin & Hlen).
    destruct (KL2_munmap resv_img img_hi L (ps_brk s) (m_vmmaps mo) a l0 len HK Hq Hin Hlen) as (Hlen1 & Hlen2 & _ & _ & Hn0 & _ & Hhas & _ & _ & Hcnt & _).
    pose proof (mmap_len_ge len ltac:(lia)) as [LG _]. rewrite Hlen2 in LG.
    pose proof (live_bytes_map_remove_has _ _ _ Hhas) as HLB.
    rewrite (u64_lit (mmap_len l0)) in HLB by (pose proof alloc_ceiling_lt; destruct (KL2_munmap resv_img img_hi L (ps_brk s) (m_vmmaps mo) a l0 len HK Hq Hin Hlen) as (_ & _ & _ & A0 & _ & CE & _); lia).
    rewrite ev_step_munmap in Himpl. destruct (machine_event _ _ _ _ _ _ Himpl) as (ms1 & Hms & Hat & Hk1).
    eapply srz_cj_msteps; [exact Emo| exact Hh| exact Hl| exact Hms|].
    eapply (step_munmap_free L (ps_brk s) ms1 mo a l0 len K HK Hq Hin Hlen Hh' Hl' Hm' Hat).
    intros rsp h' Hdec Hans HK'.
    destruct (Hk1 _ _ Hdec) as (ms2 & Hms2 & Hi2). apply implM_ret_inv in Hi2. destruct Hi2 as (ms3 & Hms3 & Hi3).
    eapply (srz_cj_msteps _ ms3 _ mo0); [rewrite Emo, with_vmmaps_twice; reflexivity| exact Hh| exact Hl| eapply Exec.msteps_trans; [exact Hms2| exact Hms3]|].
    eapply (IH 0 (event_post L (EMunmap a len) 0) Post ne' (bb - ecost (EMunmap a len)) Q s Qm ms3 _ mo0 h0 (u0 + len) (k0 + 1) K
              (Hk 0 Hans) (Hg 0 eq_refl) Hi3).
    + rewrite with_vmmaps_vm. exact HK'.
    + rewrite Emo, with_vmmaps_twice, with_vmmaps_vm. reflexivity.
    + exact Hh. + exact Hl. + exact Hm.
    + rewrite with_vmmaps_vm. apply vm_shrunk_remove. exact HS.
    + rewrite with_vmmaps_vm. subst h'. cbn [vm_maps]. clear - HLB HU LG. lia.
    + rewrite with_vmmaps_vm. subst h'. cbn [vm_maps]. clear - Hcnt HN. lia.
    + intros r s' ms' mo' L' u n HQ' Hcp HP HQr HK'' Emo' HS' HU' HN' E1 E2 E3.
      eapply (CONT r s' ms' mo' L' (len + u) (S n) HQ'); [| exact HP| exact HQr| exact HK''| exact Emo'| exact HS'| replace (u0 + (len + u)) with (u0 + len + u) by lia; exact HU'
        | replace (k0 + Z.of_nat (S n)) with (k0 + 1 + Z.of_nat n) by lia; exact HN'| exact E1| exact E2| exact E3].
      change len with (unmap_len (EMunmap a len)) at 1. eapply cpw_vis; [exact Hans| exact Hcp].
Qed.

End EVENTS.
End CEIL_WRAP_1.


End HnEmbed.
From Stdlib Require ZArith NArith List Lia Bool Permutation. From stdpp Require gmap. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0032. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require RunP Decode. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface.
Module HnStep.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0032. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.MallocCtrl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Inv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0032.MI_Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.MI_Arith OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_List OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Ext OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Ext2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Geom OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Pres4 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.MI_Bits.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP Decode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge Require Import BrRes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap Require HnIface. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnTree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnAbs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnEmpty OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWNtf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnMeta OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWSlot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWGrp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWMalloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnRes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.HnIface.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_HnStep () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI79OSSVerify5KrLib2CJ4Spec7Mh_00045STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C79OSSVerify5KrLib2CJ4Spec7Mh_00045STree9stree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad1MC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=implM_ret_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00506HnTree:apw_cpathwC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib4Heap7Mh_00506HnTree@cpathw_cpath_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8ctree_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Sim:cpath_liveC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4optrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_ebind_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_enode_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC69OSSVerify5KrLib2CJ4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad5implMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_bind_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv3blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fsc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_msys_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad4msysC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:mbind_mgetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_mget_invC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6lookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5Mergec69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_mupd_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:mbind_mupdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed<mbind_mret_lC1?~~~~~~~~~~~~~~~K35stdpp8fin_maps6FinMap01c69OSSVerify5KrLib4Heap7Mh_01147HnEmbedCForall_app_cons_midC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00c69OSSVerify5KrLib4Heap7Mh_01147HnEmbedClength_app_cons_midC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consI35stdpp4gmap4gmap00C35stdpp4base4fmapc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=Forall_filterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC35stdpp8fin_maps:map_eq_iffc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed@length_filter_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;filter_trueC46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula08I69OSSVerify5KrLib4Heap7Mh_00506HnTree6cpathw00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=machine_eventC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed5embedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes5gtreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes=gtree_vis_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464Prog6membedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:embed_freeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed;embed_freewC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4cptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC35stdpp8fin_mapsAmap_to_list_emptyC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib4Heap7Mh_00505HnAbs4INVCC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib4Heap7Mh_00505HnRes3RES00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib4Heap7Mh_00509HnWMalloc3MQCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3PhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3PsiC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5hostsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib4Heap7Mh_00505HnAbs4EINV00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3NLKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3L63C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib4Heap7Mh_00506HnMeta6MARITH00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs5nmetaC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C46Stdlib7Sorting;Permutation>Permutation_inC69OSSVerify5KrLib4Heap7Mh_00509HnWMalloc:malloc_endC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3subI79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_R00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_A00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_L00C1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7s_metasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv2MRC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6m_nextC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv7in_listC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6m_prevC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv7il_linkC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5lhead01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv9il_activeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv:live_groupC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5m_memC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00497MI_Geom9hosts_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes=nmeta_le_ngrpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs4ngrpC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib4Heap7Mh_00505HnRes:ngrp_boundC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK69OSSVerify5KrLib4Heap7Mh_00505HnRes3RES01C1?~~~~~~~~~~~~~~~K46Stdlib7Sorting;Permutation;Permutation02C69OSSVerify5KrLib4Heap7Mh_00507HnEmpty4GEOMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes2CMC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_M00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_G00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5inv_S00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5bslotC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv2x0C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6mstate00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4mled00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5lhead00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5lhead02C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableK47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C35stdpp4base6LookupI46Stdlib9micromega5Tauto8GFormula00I69OSSVerify5KrLib4Heap7Mh_00507HnWFree4FREL00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00507HnWFree8free_endC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps<lookup_emptyC35stdpp4base5emptyC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc8s_groupsC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4ghdr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs6gemptyC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC69OSSVerify5KrLib4Heap7Mh_00505HnAbs5fmaskC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc8m_maplenC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib4Heap7Mh_00505HnAbs4EINV01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7s_slotsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc9s_regionsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6r_kindC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5r_lenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5s_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296MallocBc_meta_alloc_shiftC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps8map_sizeC35stdpp4base4sizeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7s_areasC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs6nareasC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib4Heap7Mh_00506HnMeta7metalenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs4zsumC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listC69OSSVerify5KrLib4Heap7Mh_00506HnMeta6regsumC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp8fin_maps>map_size_emptyC79OSSVerify5KrLib2CJ4Spec7Mh_00296MallocBc_avail_meta_countC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib4Heap7Mh_00506HnMeta6MARITH01C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof03C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5minitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5stripC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4ghdr00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00326MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6region00C1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst7Inj_Z_ZC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5rkind00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5rkind03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2IBC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4UNITC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K47Corelib7Numbers7BinNums1N01C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4PGSZC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5rkind01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes:comparison03C46Stdlib5Lists4List2hdC69OSSVerify5KrLib4Heap7Mh_00505HnRes9rs_marithC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes<nareas_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes8rs_nmetaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1ZBdiv_le_lower_boundc69OSSVerify5KrLib4Heap7Mh_01146HnStep5NAMAXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3maxC59OSSVerify5KrLib4Heap7HnIface4cszRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes3cszC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeC79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep<page_size_eqC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMSTEP.
Context {RUNp : RunP}.

Theorem RES_malloc cs L BL LS nreq c n cs' p L' BL' LS' SZ K :
  INVC x0 cs L BL LS -> RES cs SZ K -> Permutation (map fst SZ) (map bslot BL) ->
  MQC cs LS nreq c n (cs', Some p) -> INVC x0 cs' L' BL' LS' -> map bslot BL' = p :: map bslot BL -> Z.of_nat (length BL') <= K ->
  RES cs' ((p, nreq) :: SZ) K /\ c <= Phi cs' - Phi cs /\ Z.of_nat n <= Psi cs' - Psi cs
  /\ Permutation (map fst ((p, nreq) :: SZ)) (map bslot BL')
  /\ (forall b m, hosts cs b m -> hosts cs' b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
ltac2:(KReplay.run1 (kr_t_HnStep ()) ["HMSTEP"] "p'0h01bh11mh21Hh32Hhh41li001lh51hh61xi011xh71Ah81Bh92BLh:3BL'h;2H0h<1Kh=1Lh>2L'h?2LSh@3LS'hA2SZhB4__x1hC4__x2hD4__x3hE4__x4hF1ahG1chH2cshI3cs'hJ1fhK1khL1nhM4nreqhN1oi021ohO1phP1qhQ1yhR3ALLhS5CARVEhT2E0hU2E1hV3EBLhW3EMPhX2EQhY2HChZ2HKh[2HNh\2Hbh]3Hinh^3IA'h_3IG'h`3IL'ha3IM'hb3INVhc4INV'hd3IR'he3IS'hf4L630hg4L631hh3MA0hi3MA1hj2MQhk3NL0hl3NL1hm3NM0hn2Nxho3OLDhp2Pmhq3SZBhr3SZPhs2_Hht3_H0hu7__arithhv4__ffhw8__varmaphx5__withy4cstrhz5cstr0h{1eh|1ih}2sci032sch~1zi047rs_einvi056rs_l63i069rs_marithi076rs_nlki088rs_nmetap%0p&0p;1p;2p;6p;3p;4p;5p;Fp;7p;8p-1R0p10000p4p710R1p8P0g000QR2p4p710R3p8P0P2p4p7210R0p8p1000nR4p4p710R5g0020R6p4p710R7p8P5p1002Lp4p710R8p8P5p1002jp4p7210R9p8P5g003GR:p4p710R;p8P4p4p7210R4P7p8P4P8p8P4P9p8P4P;p8p1003ep4p70P;p8g004UR4p4p70R<g005UR=p4p710R>p8P<g005lR?p4p710R@p8P<P5p8P<g006HR5p4p710RAp8P<P?p4p7210RBp8P<P7p8P<p10073p4p73110RCp8P<p10087RDp4p710REp8P<P8p8P<P9p8P<p1008kRFp60621002RGp8P<p100:2RHp4p7210RIp8P<p100:jp4p710RJp8P<P;p8P<P3p8P<p100;gp4p7210RKp8P<g00<jRLp4p710RMp8P<p100=Jp4p7210RNp8P<p100>Sp4p7210ROp8P<p100?Up4p7210R<p8PDp4p7211P7p8g00@[RPp4p70RQP7p8PQPCp8PQPEp8PQP8p8PQP9p8PQPGp8PQPIp8PQPJp8PQP;p8PQP3p8PQPKp8PQPNp8PQPOp8PQP<p8PGPEp8PGPIp8PGP0p8PGp100A[p4p741110REp8PGp100BQp4p741110RQp8PGp100CLRRp4p7210RSp8PGPRp4p73110RRp8PGp100DXp4p7210RTp8PGp100Edp4p710RGp8p100F[p4p710RUp100G9RVp4p710RWp8PUPVp4p7210RVp8PFp606311001RFp100GRp4p7210RXp8PFp100HIp4p73110RYp8p100IARZp606311002R[PDp4p7210RDp8P[PIp8P[P3p8P[PYp8P[PEp8P[PQp8P[PSp8P[PGp8g00JIRSp4p70RQP@p8PQPMp8PQg00KHRQp4p710R\p8PZp6064111001RZPDp8PZPHp4p73110RHp8PZP3p8PZPYp8PZPEp8PZPRp8PZPGp8PHPDp8p100Kep4p70P;p8p100LSp606311001RGP;p8PGp100M[p4p7210RRp8PGP3p8PGPYp8PGPTp8p100NRp60621000RTPDp8PTPHp8p100OVp606311001RTPDp8PTPHp8PTPYp8p100P^RTp4p73101REp100Q8R]p4p73110p8PEp100QQR^p4p73110p8PEp100Qmp4p710p8PEp100R@R_p4p7201p8PEp100RRp4p7201p8PEg00RdR`p4p73110p8PEp100S8Rap4p73110p8PEp100SLRbp4p73110p8PEp100Sfp4p7201p8PTp4p710RcP]p4p710p8PcP^p4p710p8PcPWp8PcPVp8PcP`p4p710p8PcPap4p710p8PcPbp4p710p8p100T9p606311001RbPDp8PbPHp8PbPYp8p100UAp60621000RbPDp8PbPHp8p100VERbp60621001RcPXp8PcPIp8Pbp606311000RbPDp8PbPHp8p100WKp4p7=1111111111100P7p8p100Wep6061001RbP1p8Pbp100Y2p4p710Rcp8Pbp100YOp4p710p8p100Ylp6061000Rbp100[9p4p710p8PbPMp8PbPcp8g00[VRcp4p710RbPUp8PbPWp8PbPVp8Pbp100[jp4p73110p8p100\<p6061001RbP1p8Pbp100]Cp4p710Rbp8Pcp4p741110R1PEp8P1p100]_REp4p73101p8p100^;p6061000RVPMp8PVPbp8PVp100_Ep4p710p8g00_eRVp4p711g00`DRbp4p73101p8p100`hp4p7210PJp8p100aiRWp60621002RUP[p8PUPIp8PUPGp8PUPRp8PUPYp8PWp606311001RWPDp8PWPZp8PWPHp8PWPYp8p100c0p606<11111111111004RWPCp8PWPFp8PWp100cop4p710RHp8PWPZp8PWPJp8PWp100dip4p710RDp8PWp100ekp4p7210RUp8PWPYp8PWPOp8p100fkp6067111111003RWPCp8PWPFp8PWPHp8PWPZp8PWPJp8PWPDp8PWPUp8PWPYp8PWPOp8PEp4p710P;p8p100gop6067111111003REPCp8PEPFp8PEPHp8PEPZp8PEPJp8PEPDp8PEPUp8PEPYp8PEPOp8g00i4REp4p70RYP>p8PYP@p8PYPAp8PYPBp8PYP7p8PYPCp8PYP8p8PYP9p8PYPJp8PYP;p8PYP3p8PYP0p8PYPKp8PYPMp8PYPNp8PYPOp8PYPQp4p7210RQp8PYP<p8p100j4p4p70P;p8p100jjp4p7<111111111110P;p8g00kMR;p4p741110R<PTp4p7511100RYp8PYP<p8p100kfp4p741110R<PTp4p76111100RYp8PYP<p8p100l>p4p741110R<PTp4p771111100RYp8PYP<p8p100l^p4p741110R<PTp4p7:1111111100RTp8PTP<p8P_p4p7200R_P1p8P1P_p8g00m5j1STg00mUj2TTg00n5j6jTg00o1R_k301TP2k20Dk305TP?j4?TP5j3]Tg00onS00k10>Tg010Pj2fTg0112j4bTg011Rk607Tg012Qj3YTg0131j31TPLj2ZTg013Kj14Tg014Fj18Tg015Aj30Tg016Bj1hTg017@j1WTg018;j2JTg0196j1@Tg01:7j12TP=j3FTg01;4R=j23Tg01;ORLk203Tg01;ik50MTg01<Hk209Tg01<bj4[Tg01==k40HTg01=Wk60pTg01>CmF0oTg01?Ik10BTg01?ij1=Tg01@Ij2>TP:j6}Tg01@fk40?Tg01Aij1lTg01Blj2KTg01Cok40`Tg01DMk60_TPck40^TP;k40]Tg01Dnk10\TP`k60[Tg01F1j1zTg01FSj1\Tg01Flj25Tg01Gjj1_Tg01HlR`j2qTg01IFk20=Tg01JIk20ZTg01Jbk10YTg01Kdk40XTg01Lgk30WTg01MBk40VTg01M]k10UTg01N`k60RTg01Oek10;Tg01PJj1BTg01Poj1wTg01QMk202Tg01Qij2^Tg01Roj1XTP6k60:Tg01T6k20PTg01TUk108Tg01UVk70OTg01V\k70NTg01Waj1vTg01X]j27Tg01Y9k70LTg01Z;j2uTg01ZXj2dTg01[5k106Tg01[Zj1tTg01\9j2cTg01\bk20KTg01]Kk30JTg01^4j3xTg01^]k20ITg01_Ik10QTg01_gk20<Tg01`Ej4eTg01`ck10STg01aAk10TTg01alj2sTg01bOk20GTg01c2k30FTg01cUk304Tg01d8k20nTg01dZk20mTg01eFk30kTg01eek40jTg01fWk80iTg01gTk50gTg01h?k100Tg01i=k10eTg01j7k30fTg01k:k30ATg01l=k30dTg01m@k40cTg01mkk70bTPbk80lTPSPEg01nOf0RbC?p=;f1R6#=/7bp=`f3R;PEg01oPRcf2R:P6Cb;Ybp=9%46/>bp=P%86/>bp=N156b$00p=:f6R5f5R?f4R23015:6$00=1;b'3p=<P2PEP;P:C?=]E6/3bp=If7R1@015?172;%=:/76/3b'3'3p=L&0eb,76p=CAF46bp=D%2b91c6p=rA1;:6,q2/3bp=G%=;%8:/>6'7/3bp=m%4:/>6,7;/3bp>0E136b,3:p=61>6b,7:p=R%26=1cbp=O%4b,>6p=p%8b,>6p=QA05?2156b$0091;:'3p=M172;17:6/3b'3p=~A0;:6/3bp=o%=5/7?A1;:6,q2/3b'3p=nA1c6bp=EA1c:6/qbp>0@P;PEP:P6C?=]Ebp>0ag01onR<@0f6bp=VB0A<6bp=UB0d<6bp=AB0A<:6/3bp=k&086=1Pb#\p=HA1P6b#\p=aA1P6bp=y17:6/3bp=|PcP6g020lPbH0cp=iP6PVg021SRTPTg0223RYPbg022SK0bp=gP;PVPTPTPYP:P6PbL0lp={P:PEP6PbC?p>0CA]E6bp>0hg0233RVg0247RO%SSRNg0257RM%S4RK[R0g026:R31T4cRJ#SR9p,4RUNpR8P<f=RCf<R7f;RBf:RAEjf>R@@01:6P_f?R_P;P:PJP420D4cR>P2C?%;@5]4fARUP@PCP7PBPV&0>ERDPAf9RZ,fECbJ07P8P<PBPZf8RHP1Ej%SERF%;Z%;U9YEB311ZSA/`1P@1TEcRWPCPUPZC9RRPHf@RGfERI#4,P@P_%8I,N@PW20DEcR_PR%;BfGRR?06bPUP:P61TPc/Tc/Tc/TcR[PUP6fHRX/:6F<[^14^04DIGL[[[[[PbfDRa#h%WIfFR^/JA%@R%2XR]/CBPJP4P>PCC?%;RRd5]4fJRePRP^PIPaPVPDfCRDfBRf,fECbJ07P8P<PaPfPUPGEj%;f%;e9YEa51F1ZSD/`GP4PcP6PbCb=FJaRgP4PJP4P>PIC?fORh#;RiP:P1P6\6Rj%S:RkP=P2P;P:P6C?9F;bP2PbO1=1?:AF5b;'3X6?-03?Rl[P;PbO1=126AF?b:'3X62-032P?P2P;P:C?9F26[RmP5P?P2P;C?9F?:\lP2P;P:P6PbI0MPbn2001000000120000000XQ:W4WJX8QX7\Pm^Q:^4k^Jj^8Q^7\PbPJP4P>P^P;PJB054cb=142AFJbR'3X6JP4PcP;P:CbR>B054c>=14;AFJ>^2094;P6C[H0HO6b2J0pW]XKcXP41D:i\g^Kc^P4P8PhfNRgfMR>fLRJfKR\PefIRQPXPRP^PIPaPDPUPAPZPHPbP2P;P:NF0o%hX%WXPWPRP\PDC9,JX%@XPePX%4hPQPX%8h1r]hPKPag026YR]O1&0B4RjfQRk?06bP\P:P6P[P\P6fRRm/:6F<[^14^04DGCmH0E3636P=%hQ%WQPWPXPJPaC9,JQ%@Q%4QfPRl#4Rn5R\PePQ%8lRo%2lRp,OQPKPIP]O1PjA0m6bPJP:P6P[PJP6fSRq/:6RrF<[^14^04DGCm3636PePWPQP>PIC9RsPaPJ%4kRa,PeP\%8kRt,NePWP_PsPdA0q6bP>P:P6P[P>P6fTRd/:6RsF<[^14^04DIGLPb%h\%WJPWP\PhPRC9,JJ%@J%4J%4q5RgP>PJ%8q%2q,OJPKPXP]O1PjfURe?06bPhP:P6P[PhP6fVRu/:6F<[^14^04DGCm3636P=%W>PWPJPlPXC9,J>%@>PhP>%4dRvPgP>%8dRw%2dRx,O>PKPQP]O1PjA0u6bPlP:P6P[PlP6fWRy/:6RzF<[^14^04DGCmH0E36PgPWP>PkPQC9R{PXPl%4eR|,PgPh%8eR},NgPWP_P{%;\A0y6bPkP:P6P[PkP6fXR{/:6R~F<[^14^04DIGLPb%WhPWPhPqP\C9,Jl%@lPm1pny%=k1Qoy1rpyPKPJP]O1PjfYRp?06bPqP:P6P[PrfZRrP6FM[^14^04DGD~36P=PWPlPdPJC9,Jk%@k%4{Ro9RqaPm%8{Ra,>t%2{Rt,OkPKP>P]O1PjA0r6bPdP:P6f[Rn/:6R\91[sCo[^14^04Fn36PmPWPkPeP>C9R>PJPd%4pRJ,PmPq%8pRs,NmPWP_P>PiA0n6bPeP:P6P[PeP6f\Ri/:6R>F<[^14^04DIGLPbPWPmPuPgC9,Jq%@d%4nRg9RuvPe1Qwn1rxnPKPlP]O1Pjf]Rx?06bPyP:P6P[Pzf^RzP6FM[^14^04Fn36P=%@ePy1p|i%=u%8iR|,>}%2iR},OePKPkP]O1PjA0z6bP{P:P6f_Rw/:6Rv91[~Co[^14^04DGD~PuPWPePpPkC9RkPlP{%4x,PuPy%8xR~,NuPWP_Pk%;qA0w6bPpP:P6P[PpP6f`Rk/:6RuF<[^14^04DIGLPb%@yPr1pow%=p%8wRo,>a1rtwPKPdP]O1PjfaRt?06bPnP:P6P[P\fbR\P6FM[^14^04DGD~P=%4k9RnJPr1Qsk%2kRs,OpPKPeP]O1PjA0\6bPiP:P6fcRJ/:6Ra91[>Co[^14^04FnPrPWPpPxPeC9R>PdPi%4t,PrPn%8t,NrPWP_P>%;yA0J6bPxP:P6P[PxP6fdRy/:6R>F<[^14^04DIGLPb%4\Rr9RxgPx1Q|J%2JR|,E}PKP{P]O1PjfeR}?06bPwP:P6P[PvffRvP6FM[^14^04FnP=1Q~y,`z%2y,OxPKPpP]O1PjA0v6bPkP:P6fgR~/:6Rg91[uCo[^14^04DGPzPWPxPtPpC9RpP{Pk%4}R{,PzPw%8}Ru,NzPWP_Pp%;nA0~6bPtP:P6P[PtP6fhRn/:6RpF<[^14^04DIGLPb1Qov,`k%2~Ro,EsPKPiP]O1PjfiRs?06bPJP:P6P[PafjRaP6FM[^14^04DGP=%2t%2nPxP]O1=1Kj40@A0a6bPyP:P6P[P>fkR>P6FM[^14^04P\PWPtP}PxC9RxPiPy1prsPJ%8s,N\PWP_Px%;wA0>6bP}P:P6P[P}P6flRx/:6F<[^14^04DIGLPb%2aPwP]O1=1Kj60@|fmR|?06bP~P:P6P[PgfnRgP6FM[^14^04PWPyPnPkC9Rr>01}w%4x9R~{S011Qux,`vS02PWP_Pr%;\S03H0aRuA0g6bPnP:P6P[PpfoRpP6FM[^14^04S04'3S05'3S06'3P}PrPwPQPIPUPCP`%2x,O}PtP]O1=1Kj%2vRw/CkP6%2|Rr,EwPc%2g1Cb\X~cPePoPbE}WXPbO1P\P]O1=1KjPmP8P<P~P}PyPJEjP=P8P<PnPvH0?%ln1Vny1Kny1Uny1An}3636%2s/CJPbP8P<PaPnH0?%l>1V>~1K>~1U>~1A>n3636P=%lx1Vxn1Kxn1Axs9kxn361Cr~Pb%lg1Vp>1Kp>1Apx9kp>36P=fpRr/Vx1Krx1Urx1Ar|36fqR|#2/C>PbfrRx/VgfsRg/Kp1Ugp1Agr36P=ftR~/Kr1A~|9k~rfuRr#2/CpPbfvRp/KxfwRx1Ax~7kgP=fxRx/U~1AxrfyRr#2/CgPbfzRg/Upf{Rp/Axg027\Rx$0>P4PxP4g028^R~g029<R|Pcg029URJH0`RvP~P|g029nPcPJg02:LJ0_RJPxH0^P4PvPJPxH0]Pbf}RJ$0\J0[%zx31#\RxPzP6PbO2f~Rz/56Rv%z4R|'HS07%_v/a|'qP`p+01@R`/5:Rv/H|%_v/a|p+01A/5;Rv/H|R~PbPbX2~PbO1%_v/a|20=J2Rvp+01CR~/5?Ro#_/a|[p+01BRe/52#_/y|Rw#\R[20=z?[20Zv[&0Yo/y|\wPePJPAP2H0X40WPbH0VPzPbO1,D?X5M-03MPLPMP`PbO1,D5X5Mp+01DRw/55/H|PbPePbO1,DHPMPwPbO1,DAp+01I/5B/H|]3P6p+01E&0UbO1,DBp+01JRop+01FPfP6P7PbJ0Rg02:jR[g02;HRv$0;#B#BR{#B#B#wRi-0267|61^o715o7Ro#X/E636P=202:i9|[:p+01KRd/^C15dC#X/E:'3p+01L/5@/H|Pb2022i9|[2p+01NRi/^G15iG#X/E?'3P=p+01OR=/^U15=U#X/E5p+01P/5f/H|Pbp+01Q/^DPLP4p+01SRL?0bIX0415LI#X/EAp+01T/5^/H|[Pbp+01U?0bRp+01V/5X#X/ECPP1f4:RX1ab|XNP1yX|RXPP1f4;Q00P4p-0Pbg02;mg02<IRRn10110200021000000X{Pg02<fP|PbJ0:PR20PRbb;W2%\Xep+01WRX/5Q$08P<PXPLPqP:PQP6K0OE}WtW\X04P6PbO2n2001000000120101000W2P6PbO2n2001000000120000000W2WsP6PbO2n2001000000120000000bFW3X}cPbO1P~P]O1,DZPKPwP]O11DBbX4KPbPjPlJ0:1DAjPR1Ho|Pbn010000000b3W3n0110000021110300PbO1W3X5MP6PbO2n2001000000121101000b|WnPbO1n200100000021000011000bNWpX14Q07\x^14P8PJPpPgPrPnPbK0N%2J%vJ'7P8Pzf|R8PpPgPsP\K0L%vz%BvRz#B#B#B#BR\#B#wRs1ZSp#='u%w\R\'d'71ZS8Rp$06%=p,7[&06e%=e,7[g02=BReg02=nRp#tRg#tRJ#t,cc1ccJ20Kcs1ccg60Jc1ccp5xc5xc5xcg02>M+0I&0Be3Y%SePcPcPc&0QcReP220<c2CeP:PeCeP6Pc20<c;P2PeCeCe&0Sc&0TcRe1sc{R{20GcsRp&0;z,scRg60Fc20Gc\RJ604c'i,ge%zTRTPe1scvRv/i{,gePTPe1sczRz,ig,gePTB04czJ:0Fcp>04cJ,iv,geC{C{C{20neYPbP:g02?9Reg02?YRY+0920mb:=1eYdB0kc[6H0jbvbwbxXBcXCcXDcXEc1us:/d\,7;1762172;1d2\,us/d\,7;[[[^Bc^Cc^Dc^EcPb%v~1ZS`#=P8%2~P;P2P>O7bubzby%2`/Creb;b2bRWeW_P6PbO2n2001000000121000000W2W`P6PbO2n2001000000121000000W2WaP6PbO2n2001000000121000000W2W^P6PbO2n2001000000121000000W2WdP6PbO2n2001000000121000000b2WWPbO1n200100000021000011000L0iQ01Q06PZQ02Q05P?PuQ04PF%;aRa9YEyB0CW_t9YE}00hbX4FPEPyB0CW_kPaPmI0gQ03PhE}PuePbC[C[C[C[WoWSP6PbO2n2001000000121000000W2W[P6PbO2n2001000000121000000W2WYP6PbO2n2001000000121000000W2WiP6PbO2n2001000000121000000W2WgP6PbO2n2001000000121000000W2WlP6PbO2n2001000000121000000W2WUP6PbO2n2001000000121000000bFbqWZWVWcWjWrWmWhWfWkWTP2P;P:P6PbO5n30001000000151104107105106108W2WbX<cXA9X@0X:NX>OXOEXIVXL3XGcXMcX?0X9NX=OXHVPCP7PBPAPZPHP1P5P?P2P;P:P6PbO>X<cWAX@0X:NX>OXOEXIVWLXGcXMcW?W9W=WHo"). Qed.

Theorem RES_free cs L BL LS cs' u nu L' BL' LS' SZ SZ' K :
  INVC x0 cs L BL LS -> RES cs SZ K -> FREL cs LS cs' u nu -> INVC x0 cs' L' BL' LS' ->
  (forall e, In e SZ' -> In e SZ) ->
  RES cs' SZ' K /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat nu
  /\ (forall b m, hosts cs' b m -> hosts cs b m /\ GEOM (MR cs' m) = GEOM (MR cs m)).
Proof.
ltac2:(KReplay.run1 (kr_t_HnStep ()) ["HMSTEP"] "p'0h01bh11mh23SZ'h31eh41Hh52BLh63BL'h71Kh81Lh92L'h:2LSh;3LS'h<2SZh=2csh>3cs'h?2nuh@1uhA2E0hB2E1hC2FRhD3INVhE4INV'hF4L630hG4L631hH3MA0hI3MA1hJ3NL0hK3NL1hL2NMhM3NM0hN3OLDhO2PHhP2PShQ3SUBhR1ahS1zi007rs_einvi016rs_l63i029rs_marithi036rs_nlki048rs_nmetap;1p;2p;6p;3p;5p;Bp;8p;4p-1R0p10000p4p710R1p8P0p1000QR2p4p710R3p8P0P2p4p7210R2p8p1000nR0p4p710R4p10020p4p710R5p8P4p1002Lp4p710R6p8P4p1002jp4p7210R7p8P4g003GR8p4p710R9p8P0p4p7210R0P5p8P0P6p8P0P7p8P0P9p8p1003ep4p70P9p8g004UR0p4p70R:g005UR;p4p710R<p8P:p1005lR=p4p710R>p8P:P4p8P:p1006Hp4p710R4p8P:P=p4p7210R=p8P:P5p8P:p10073p4p73110R?p8P:p10087R@p4p710RAp8P:P6p8P:P7p8P:p1008kRBp60621002RCp8P:p100:2RDp4p7210REp8P:p100:jp4p710RFp8P:P9p8P:P3p8P:p100;gp4p7210RGp8P:p100<jp4p710RHp8P:p100=Jp4p7210RIp8P:p100>Sp4p7210RJp8P:p100?Up4p7210R:p8P@p4p7211P5p8g00@[RKp4p70RLP5p8PLP?p8PLPAp8PLP6p8PLP7p8PLPCp8PLPEp8PLPFp8PLP9p8PLP3p8PLPGp8PLPIp8PLPJp8PLP:p8PCPAp8PCPEp8PCP2p8PCp100A[p4p741110RAp8PCp100BQp4p741110RLp8PCp100CLRMp4p7210RNp8PCPMp4p73110RMp8PCp100DXp4p7210ROp8PCp100Edp4p710RCp8p100F[p4p710RPp100G9RQp4p710RRp8PPPQp4p7210RQp8PBp606311001RBp100GRp4p7210RSp8PBp100HIp4p73110RTp8p100IARUp606311002RVP@p4p7210R@p8PVPEp8PVP3p8PVPTp8PVPAp8PVPLp8PVPNp8PVPCp8g00JIRNp4p70RLP>p8PLPHp8PLp100KHRLp4p710p8PUp6064111001RUP@p8PUPDp4p73110RDp8PUP3p8PUPTp8PUPAp8PUPMp8PUPCp8PDP@p8p100Kep4p70P9p8p100LSp606311001RCP9p8PCp100M[p4p7210RMp8PCP3p8PCPTp8PCPOp8p100NRp60621000ROP@p8POPDp8p100OVp606311001ROP@p8POPDp8POPTp8p100P^ROp4p73101RAp100Q8RWp4p73110p8PAp100QQRXp4p73110p8PAp100Qmp4p710p8PAp100R@RYp4p7201p8PAp100RRp4p7201p8PAp102@9RZp4p73110p8PAp100S8R[p4p73110p8PAp100SLR\p4p73110p8PAp100Sfp4p7201p8POp4p710R]PWp4p710p8P]PXp4p710p8P]PRp8P]PQp8P]PZp4p710p8P]P[p4p710p8P]P\p4p710p8p100T9p606311001R\P@p8P\PDp8P\PTp8p100UAp60621000R\P@p8P\PDp8p100VER\p60621001R]PSp8P]PEp8P\p606311000R\P@p8P\PDp8p100WKp4p7=1111111111100P5p8p100Wep6061001R\P1p8P\p100Y2p4p710R]p8P\p100YOp4p710p8p100Ylp6061000R\p100[9p4p710p8P\PHp8P\P]p8p100[VR]p4p710R\PPp8P\PRp8P\PQp8P\p100[jp4p73110p8p100\<p6061001R\P1p8P\p100]Cp4p710R\p8P]p4p741110R]PAp8P]p100]_RAp4p73101p8p100^;p6061000R1PHp8P1P\p8P1p100_Ep4p710p8p100_ep4p711p102@Mp4p73101p8p100`hp4p7210PFp8p100aiR1p60621002R\PVp8P\PEp8P\PCp8P\PMp8P\PTp8P1p606311001R1P@p8P1PUp8P1PDp8P1PTp8p100c0p606<11111111111004R1P?p8P1PBp8P1p100cop4p710RDp8P1PUp8P1PFp8P1p100dip4p710R@p8P1p100ekp4p7210R\p8P1PTp8P1PJp8p100fkp6067111111003R1P?p8P1PBp8P1PDp8P1PUp8P1PFp8P1P@p8P1P\p8P1PTp8P1PJp8PAp4p710P9p8p100gop6067111111003RAP?p8PAPBp8PAPDp8PAPUp8PAPFp8PAP@p8PAP\p8PAPTp8PAPJp8p100i4p4p70RAP<p8PAP>p8PAP4p8PAP=p8PAP5p8PAP?p8PAP6p8PAP7p8PAPFp8PAP9p8PAP3p8PAP2p8PAPGp8PAPHp8PAPIp8PAPJp8PAPLp4p7210p8PAP:p8p100j4p4p70P9p8p100jjp4p7<111111111110P9p8p100kMp4p741110R9POp4p7511100R:p8P:P9p8p100kfp4p741110R9POp4p76111100R:p8P:P9p8p100l>p4p741110R9POp4p771111100R:p8P:P9p8p100l^p4p741110R9POp4p7:1111111100ROp8POP9p8PYp4p7200RYP]p8P]PYp8g00m5j1ITg00mUj2DTg00n5j6HTg00o1RYj3FTg02A1j5NTP;j37Tg013Kj12Tg014Fj11Tg015Aj33Tg016Bj1ETg017@j1@Tg018;j2?Tg0196j1;Tg01:7j15Tg01i=j1MTg01X]j2LTg02B1lBSTg01?ij1BTg01;4R;j26TP8j6RTg01fWj8QTg01<bj4GTg01Flj2PTg01h?j1OTg0131j3<Tg01@Ij2ATf1R8f0R]'P#Op=0f5R9f4ROf3R:33f2RA?<8]'6p=4g01oPRL%B8,AA7<:/6]p=>f6RJ?F9O1AA89<L:/6]'6p==%B:,AO9<L9A<LA8/6]'6p=81AA89<L:/6]p=C168],6Ap=:1A8]9<LAp=9A<LA8/6]p=KA<L8]p=Jg0233RIg0247RH%INRNg0257%I0[RGg026:R21D0LR3#IRFp,4RUNpR7g01onR6f<R?f;R5f:R=f9R4EHf=R>?F:8PYf>RYPOPAf?P?P5P=P4DNP7P6P?P4f8R<f7RTEHA73]TA7384[^33PYPTPJ%2YfBR\#2P>%1Y%1\P?f@R@?38]fERUPAP81DKL/DL/DL/DLRKfARD/0810U8E4[^10^00C>F=[[[P]fCRB#EfDR1#@1?U5fFRM#;fGRC#5RE%M5'LfHRVPUP1PBP\DNP7P6PUP\PDP@EHA73]@A738\[^33P7fKR7fJR@fIR6PVPCPMPUP1PBP\PDPYPJP9POPAP8MBS%EC%@CA73]8RYA7381[^331?68[^2F%;C%2C%27R1PM%1C%17RBPUPE%57REA368]fNRQPAP8PK10@810Q8RRE4[^10^00E8CC3:3:P;%EV%@VA738U\Y^331?@8[^2F%;V%2VfLRP#2RS;9C%1V%1PR[PM%5V%5PRZA3@8]fORXPAP8PK107810X8RWE4[^10^00E83:3:P6P\PD%26fMR\#2R^PV%16%1\R_PCA378]fPRCPAP8PK10P810C8R`E4[^10^00C>F=P]%E@%@7A738V\Y^331?\8[^2F%;7%2XRV=91@PB%1XRBP6PE%5XREA3\8]fRR1PAP8PKPR1018RRE4[^10^00E83:3:P;%@PA7386\Y^331?Q8[^2F%;PPS%2CRSP7P[%1CR[P@PZ%5CRZA3Q8]fSRaPAP8PKPW10a8RWE4[^10^00E8CC3:P\PMPUP^fQR^#2RMPPP_%1^R_P7A3X8]fTR7PAP8PKP`1078R`E4[^10^00C>F=P]%@QA738P\Y^331?^8[^2F%;XPV%2aRVPQPB%1aRBP\PE%5aREA3^8]fVRPPAP8PKPR10P8RRE4[^10^00E8CC3:P;A738\\Y^331?18[^2F%;C%27Rb=9SXP[%17R[PQPZ%57RZA318]fWRSPAP8PKPW10S8RWE4[^10^00E83:P^P@P6PMfURM#2R@PCP_%1MR_PXA3a8]fXRcPAP8PKP`10c8R`E4[^10^00C>F=P]A738X\Y^331?78[^2F%;a%2SR3=9V1PB%1SRBP^PE%5SREA3M8]fZRVPAP8PKPR10V8RRE4[^10^00E83:P;%;7Pb%2cRbPaP[%1cR[P1PZ%5cRZA3P8]f[RYPAP8PKPW10Y8RWE4[^10^00E8CCPMPQP\P@fYR@#2RQP7P_%1@R_PaA3S8]f\RaPAP8PKP`10a8R`E4[^10^00C>F=P]%;PP3%2YPPPB%1YRBPMPE%5YREA3@8]f^R3PAP8PKPR1038RRE4[^10^00E8CCP;%2a=9bSP[%1aR[PPPZ%5aRZA3V8]f_RbPAP8PKPW10b8RWE4[^10^00E8P@P1P^PQf]RQ#2R^PcP_%1QR_PSA3Y8]f`RSPAP8PKP`10S8R`E4[^10^00C>F=P]%2V%23;9@PB%1bP@PE%5bREA3Q8]fbRBPAP8PKPR10B8RRE4[^10^00E8P;%1S%BV59[%5SR[A338]fcRcPAP8PKPW10c8RWE4[^10^005KZPQPPPMP^faR^#2RMPaP_%1^R_PYA3b8]fdRYPAP8PKP`10Y8R`E4[^10^00C>F=P]%13%1B%Ba39%5cA3^8]ffR3PAP8PKPR1038RRE4[^10^005KEP;%5YR;,J[A3B8]fgR[PAP8PKPW10[8R[E4[^10^00P^PVP@PMfeRM#2PSP_%1MPbA3c8]fhRbPAP8PKP`10b8E4[^10^00C>F=P]%5B%53'JA3M8]fjRMPAP8PKPR10M8E4[^10^00AFYQa%2Y%2b;9cRc%1Y%1b%BB39RBA338]fkR3PAP8PKP[1038E4[^10^00R0'6R3'6PYPQPaP6PUPDPQP\O2P>PL%5b%MQ,L]XSLPCP;P8ERGQPcP3P4PBP0P9P]CGCGCGWNWLP8P]O2n2001000000121000000W4WPP8P]O2n2001000000121000000W4WOP8P]O2n2001000000121000000W4WIP8P]O2n2001000000121000000W4WGP8P]O2n2001000000121000000W4WKP8P]O2n2001000000121000000W4WBP8P]O2n2001000000121000000bRWQWEWCWMWHWFWJWAPOP:PAP8P]O5n30001000000151100103101102104W4WDX7LX2FX<FX;GX6NX9HX?2X@LX>IX:GX5NX8HX=IP?P5P=P4P<PTPJP9POP:PAP8P]O=X7LX2FW<X;GX6NX9HW?X@LX>IW:W5W8W=o"). Qed.

Theorem RES_init secret resv K : 0 <= K -> RES (strip (minit secret resv)) [] K.
Proof.
ltac2:(KReplay.run1 (kr_t_HnStep ()) ["HMSTEP"] "p'0h01Hh14__x1h27__arithh34__ffh46__sat1h58__varmaph65__with71nh81mh92aih:2H0h;2H1h<6__sat0h=1oi001oh>1rh?1xi011xh@2H2hA2HahB1KhC4cstrhD1ehE4resvhF3ridhG6secrethH2H3hI2H4hJ2HKhK1bhL2b1hM2b2hN1chO1ihP2krhQ1lhR2m1hS2m2hT1yi021zp%0p&0p;2p;1p;3p;4p;6p;=p;5p;<p;7p;8p;Bp-1R0p10000p4p710R1p8P0g000QR2p4p710R3p8P0P2p4p7210R0p8p1000nR4p4p710R5g0020R6p4p710R7p8P5p1002Lp4p710R8p8P5p1002jp4p7210R9p8P5g003GR:p4p710R;p8P4p4p7210R4P7p8P4P8p8P4P9p8P4P;p8p1003ep4p70P;p8g004UR4p4p70R<g005UR=p4p710R>p8P<g005lR?p4p710R@p8P<P5p8P<p1006Hp4p710R5p8P<P?p4p7210RAp8P<P7p8P<p10073p4p73110RBp8P<p10087RCp4p710RDp8P<P8p8P<P9p8P<p1008kREp60621002RFp8P<p100:2RGp4p7210RHp8P<p100:jp4p710RIp8P<P;p8P<P3p8P<p100;gp4p7210RJp8P<p100<jp4p710RKp8P<p100=Jp4p7210RLp8P<p100>Sp4p7210RMp8P<p100?Up4p7210R<p8PCp4p7211P7p8g00@[RNp4p70ROP7p8POPBp8POPDp8POP8p8POP9p8POPFp8POPHp8POPIp8POP;p8POP3p8POPJp8POPLp8POPMp8POP<p8PFPDp8PFPHp8PFP0p8PFp100A[p4p741110RDp8PFp100BQp4p741110ROp8PFp100CLRPp4p7210RQp8PFPPp4p73110RPp8PFp100DXp4p7210RRp8PFp100Edp4p710RFp8p100F[p4p710RSp100G9RTp4p710RUp8PSPTp4p7210RTp8PEp606311001REp100GRp4p7210RVp8PEp100HIp4p73110RWp8p100IARXp606311002RYPCp4p7210RCp8PYPHp8PYP3p8PYPWp8PYPDp8PYPOp8PYPQp8PYPFp8p100JIp4p70RQP@p8PQPKp8PQp100KHRQp4p710p8PXp6064111001RXPCp8PXPGp4p73110RGp8PXP3p8PXPWp8PXPDp8PXPPp8PXPFp8PGPCp8p100Kep4p70P;p8p100LSp606311001RFP;p8PFp100M[p4p7210RPp8PFP3p8PFPWp8PFPRp8p100NRp60621000RRPCp8PRPGp8p100OVp606311001RRPCp8PRPGp8PRPWp8g02C3RRp4p73101RDp100Q8ROp4p73110p8PDp100QQRZp4p73110p8PDg02CQR[p4p710p8PDp100R@p4p7201p8PDp100RRp4p7201p8PDg00RdR\p4p73110p8PDp100S8R]p4p73110p8PDp100SLR^p4p73110p8PDp100Sfp4p7201p8PRp4p710R_POp4p710p8P_PZp4p710p8P_PUp8P_PTp8P_P\p4p710p8P_P]p4p710p8P_P^p4p710p8p100T9p606311001R^PCp8P^PGp8P^PWp8p100UAp60621000R^PCp8P^PGp8p100VER^p60621001R_PVp8P_PHp8P^p606311000R^PCp8P^PGp8PRp4p7<111111111110P7p8p100Wep6061001R^P1p8P^p100Y2p4p710R_p8P^p100YOp4p710p8p100Ylp6061000R^p100[9p4p710p8P^PKp8P^P_p8g00[VR_p4p710R^PSp8P^PUp8P^PTp8P^p100[jp4p73110p8p100\<p6061001R^P1p8P^p100]Cp4p710R^p8P_p4p741110R1PDp8P1g00jjRDp4p73101p8p100^;p6061000RTPKp8PTP^p8PTp100_Ep4p710p8g00_eRTp4p711g01mkR^p4p73101p8p100`hp4p7210PIp8p100aiRUp60621002RSPYp8PSPHp8PSPFp8PSPPp8PSPWp8PUp606311001RUPCp8PUPXp8PUPGp8PUPWp8p100c0p606<11111111111004RUPBp8PUPEp8PUp100cop4p710RGp8PUPXp8PUPIp8PUp100dip4p710RCp8PUp100ekp4p7210RSp8PUPWp8PUPMp8p100fkp6067111111003RUPBp8PUPEp8PUPGp8PUPXp8PUPIp8PUPCp8PUPSp8PUPWp8PUPMp8PDp4p710P;p8p100gop6067111111003RUPBp8PUPEp8PUPGp8PUPXp8PUPIp8PUPCp8PUPSp8PUPWp8PUPMp8p100i4p4p70RUP>p8PUP@p8PUP5p8PUPAp8PUP7p8PUPBp8PUP8p8PUP9p8PUPIp8PUP;p8PUP3p8PUP0p8PUPJp8PUPKp8PUPLp8PUPMp8PUPQp4p7210p8PUP<p8p100j4p4p70P;p8PDp4p7<111111111110P;p8g00kMR;p4p741110R<PRp4p7511100RUp8PUP<p8g00kfR<p4p741110RUPRp4p76111100RQp8PQPUp8g00l>RUp4p741110RQPRp4p771111100RMp8PMPQp8g00l^RQp4p741110RMPRp4p7:1111111100RLp8PLPMp8PRp4p73100RMP1p8P1PMp8g00mUj2fTg00m5j1gTg01?Ij1cTg015Aj3UTg00onS00j1PTg01Cok40OTg01DMk60ITP_j4Nj3|TP;j4Rj3vTg02Cdj1[Tg02Dhj2<Tg0131j31Tg02Ejj2CTg01Flj26Tg01Roj1@TP<j4Qj3~TP[j2STg01F1j1JTg02Fhj3zTPUj3sTg02G?j3qTg02GVj3pTPQj3oj4eTg02Gnj3nTP6j6GTg02HGj1kTg02IDj1uTg02JJj1yTg01T6j2VTg02KOk100Tg01FSj1KTg01Oej1>Tg01Poj18Tg01X]R6j20Tg01PJj15Tg01;4j2DTg02LSk30]Tg01Dnj1dTP\j6LTg01TUk10\Tg01Gjk10[Tg01Hlk20ZTPRl=bTg017@k10YTg0112k40XTP=k30WTg02MQk10VTg010Pj2=TP2k30UTg02NTj1`Tg02OYj1_Tg02P[j1^Tg01ZXj23Tg01;OR2k20STg018;k20RTg01_Ik10QTg01`ck10PTg01aAk10NTg01bOj2ETg01d8k20MTg01<Hj27Tg01dZk20LTg01eFk30KTg01eek40JTg02Q\k10HTg02R]k10GTg02Skj4tTg02TEj3TTg01[5k10FTg01?iR=j1BTg02TWk20ETg01QMk202Tg02U?j2rTg02U\k30DTg02V@j2iTg01_gk20CTg01alk20BTg02Vak30ATg01cUj3HTg02WDk10@Tg02XGj1YTg02YEk10?Tg01\bk20>Tg01[Zj1lTg01\9j2XTg01]Kk30=Tg01^4j3mTg01^]j2jTg012Qj3xTg01c2j3MTg01Z;RRj22Tg02ZXk30<Tg02[5S01k10;TP?j4\Tg02\5j1ZTg02]1j5wTPDm<0:TP:j6{Tg02]Nk209Tg02^Mk108Tg01@IR:j2]Tg02^km<01Tg02_Pk30kTg02`3k405Tg02`^m<04Tg01:7k10jTg02a>k10iTg02bLk70hTg02cMk20gTg01i=k10fTg01fWk80`Tg02d9k20_Tg02e:k10aTg01m@k40^TP^k70bTg00`Dk80cTg02f;k40dTg02f^m<0eTg02gCmB03Tg02:jR^f0RD'0p=9f1R?00_D$0ap=4P4g02giR\f3RQf2RUP?PDELp=I1=4Dp=A1=\Dp=?P4PDP?PUPQf4R[f5R<f6R;f7R_g02hkRMf8R1P\f9RLM=bp=hg028^RKg02j2RJPQPUP?PDELp=Og01oPR0P?g020lPDH0^p=;P?PTg021SR3P3g0223RIPDg022SK0bp=:PQPTP3P3PIPUP?PDL0cp=W1]D^p=FP0P0g02k6PDH0dp=}g026:RTP0P0P0P=P=PQPUP?g02=nR=P^PDN<0ep>07P0P0P0P0P0P0PRP;P<P[PRPQg02kZRRPRPUP?P^PDNB03p>06P0P0P0P0P0P0P:P_P;P<P:P[PQPUP?P^P^PDNB03p>0TPTP=PQPUP?PDE{p=a1f00#gS02Q02%9DR:14QUR91f40R8#cRBP?14_;R7?UQUP2P0%P\RAP4PKg029<R5P0g029UR@H0OR>PKP5g029nRWP0P@g02:LJ0IR@P\CNRSP4P>P@P\CRRCP<14L1RX#[CI%A[/<D#?31RGX90AUXQUf:RE/4LRP/C<f;RF/4ERH/C[f<RY/4FRV/6_R]#@16V<#@510A14L_[[[[PDPSPCP_%[HCI%A;RZ/<D#?51APAPSPCP1P4P>P@P\CQ,SSROCI%A1/<U#?91ADX=APD%J\R\A|4>@R`Az4>@RaAv4>@RbA~4>@RcAs4>@RdAq4>@ReAp4>@RfAo4>@RgAn4M@RhP1M:hEG%A_/<?#?91A\f=Ri/4YRj?U_;f>Rk/4i/CLf?Ri/4k/C1f@Rl/4iRi/6F#@16iL#@510P0fA/4l/6ERE#kP0p-0S03PDg02;mRlg02<IRiPin011020003001000010000XD0RLg02<fS04%uE#yP?EGPiA14kY/VDbIWHW@W;W:b0W0X90P?PDO2n2001000000121101000W0XS4XM4XR4XL414<[Rk?U?DP2P0PSPCPQ%[7CI%AU/<D#?51AX901C7U141_S05/6QR2$00=10^#Kg02;HRY#>#>RE#8RF%@2R2'0%5YRm#5Rn#>#>#5#8Ro,02'D'D[PDPAPSPCP;POCI1<ZU#?91ADX=APDP\P`PaPbPcPdPePfPgPhP;M:hEG%A</<?#?91A\1CH;P0%k]PLQ04%u]#yPDEGPi16j1Rj$00=10^#K%@jRj,0F10jo'D'D/VDb;W:b0X0GX90P?PDO2n2001000000121101000W0X84XK460]9g027\RG#PRjP4PGP4P>P@PGCNRoP4P>P@PGCRRFPD14[Q#dEL%JGR]31#K16k?RL$0\%J4RH51N#K&0[L=1NH#K+0ZPDP4P`PaPbPcPdPePfPgPMPhPGP?M=bP4PGPoPFP?%dkEL=1j]eO1'VW0X84&0Y9eP4P0PQPUH0XR]>0W8BPi%P8P4P8P4P>P@P8CNP4P>P@P8CRP<&0VXEL1=8]3116P[#@%>E#>#>#8510%PJREPKP5PWPJCNRPPKP5PWPJCRR]B0UK01%`VCO1=JDRV31g02l\R1%_Dg02m_31%^Dg02nb,3_g02o`'3510'D'DX>J-0SJ[[PDn010000000W0XO0X84X70XN420R9BeP9g02=BRB#cR_%gBR8&0Q0S06&0P0RX&0N0R<1E0^Rj/;j':20M<IRIPDPUg02?9RFg02?YRH'720LDU=1FHdB0K0^?H0JRHb3b5b610^^RFPDb2&0H9RN$0GRL#9eP4P>P@g030`R;CNR\P4P;P\P4P>P@P;CeCtRAP4P>P@P;CQ,S\3TRZ$0FRO%BZRC#9RS%8mRm00E^R2202^mRp1rm^Rq-02^\FRF[Rr%9mRsB0Dm^?VlWARt%9q\l^AsRsP?g031bRu1i^m'7PpeO1RpPFP_P820C0?RvPXP<20B0YRw,;j,:<S07%J3S081E0mR3g032H60A0Rx%8YRY,E0=H0j=H0w';,:<CWPIPHb3b5b6X1013Y^Ry/3?,0q\:^10PDPCP[O2RCb2b4b<b4bC&0@99T\A#BRA,3y,0qe%Y9R\,3y,0qe1rmLRL&0?N,3Y/3\'0ePOPSP2PrPtPsPpPF20>0m%l=RS,X060=01X0=RO5m0g02>MRy'j=xB_P8PvPXP<Q07Q08AM03w9H03,;x,:<CWPIPHb3b5b6X1012m?,3m,0q\:^10PCb2b4b<b4bC12mA,3m,0qe12m\,3mRC,0qe10LCe1fKJRC#gRz%cCS09PCP0B0<KJD$0;XPCR{PDC\#Zg032fR|,2mR}/2qR~'0XQzP2PrPtPsPpPFP_P8Q06PX%5n#5#5Rn#5RF#5#5#5#5#5#5#8Rp,E09M03=M0x,;j,:<PIPHb3b5b612mp/2q#9PDb2b4b<b4%9~ePCP0P{Q09C\#Z/0~ePKPJPPPKP5PWPJCeRqPKP5PWPJCQ,SPRpDwPKA|K5WRmAzK5WRxAvK5WR3A~K5WRsAsK5WRtAqK5WRrApK5WR2AoK5WRzP5AnK5WRWPJN<0:E{PCP0P{PKPJPPPq%`9DwC\#Z/0~eQ010099Rq/0~e12}L,0qePPP]P?PpCO=1EVPEPPP]PUPpCO1=JU91EDX=EPD%JJRpPKPmPxP3PsPtPrP2PzP5PWPJPUM=bEG1=J?91Ep%_Ug033fRW511%^QRQQ05#Y,3Y,2|R5'ig034i51uPEPpQ00PJQ03PDPiPln10110000021000000XDEQ041=J[PUEGPi1ViDb@W;10Q5eW:b0W0X>JXFKPPP]P?%`kCO=1EV%_?=11W%^U%Y7,3Y,2|'0[[^>J^FKe%BDRK,2R#FP4PGPoP4P>P@PGCeCtRJP4P>P@PGCQ,So5ToR@#B'0X7T%B=R=,2RR>#FR|/0KX7T10|=RY12R^R7#FRW/0^P0P0P6PDX?0R1P610?D$08XT0X?0RVP|PWP1P1P11]?D#},70X80X70P>P7P1P1P112?D#},70X80X70170RP=P1P1170KX?T170^R7H07R>K06P7L0TP=P^P>N<01P_P8PvPXAM0wj>0k0j/;j,:<PIPHb3b5b6X1012D^#F/0^^10PDPRO1b2H05PYeP@P4P`PaPbPcPdPePfPgPMPhPGN<04RGCaPZP4P`PaPbPcPdPePfPgPMPhP;N<04Ca12RA#F%d99ToJ#BRJ'0e12R\R\#F&0j9R9'0e&0iN,]\/09eK0h%8FRF%8nRn,3U'2/3n,0KX7T13?n,2F/3nRT,0=RK%9TR\P0P0P6P1P6PVP=P^P>PTPT170TN<01%lS,X09m0O/jy-0gO=xB_P8PvPXP<Q07Q081E0F1E0nRn9H0w5M0=H0n,;j,:<CWPIPHb3b5b6X10P\\:^10PDPUP?O2b2H05PKeP@PGCa10JTe&0f?,09eL0`WJXB0WEXG0PUP?PDO3XB0WEXG0o"). Qed.

(* [comment removed for export] *)
Definition NAMAX (K : Z) : Z := (CM K + NSLOTS) / NSLOTS.

Lemma nareas_K cs L BL LS SZ K : INVC x0 cs L BL LS -> RES cs SZ K -> nareas cs <= NAMAX K.
Proof.
ltac2:(KReplay.run1 (kr_t_HnStep ()) ["HMSTEP"] "h02BLh11Kh21Lh32LSh42SZh57__arithh64__ffh78__varmaph85__with94__x1h:4__x2h;4__x3h<4__x4h=2csh>1Hh?2H0h@3INVhA1Rp;1p;2p;6p;3p;4p;7p;5p;8p-1R0p10000p4p710R1p8P0p1000QR2p4p710R3p8P0P2p4p7210R2p8p1000nR0p4p710R4p10020p4p710R5p8P4p1002Lp4p710R6p8P4p1002jp4p7210R7p8P4p1003Gp4p710R8p8P0p4p7210R0P5p8P0P6p8P0P7p8P0P8p8p1003ep4p70P8p8g004UR0p4p70R9p1035Op4p710R:p8P9p1005lR;p4p710R<p8P9P4p8P9p1006Hp4p710R4p8P9P;p4p7210R;p8P9P5p8P9p10073p4p73110R=p8P9p10087R>p4p710R?p8P9P6p8P9P7p8P9p1008kR@p60621002RAp8P9p100:2RBp4p7210RCp8P9p100:jp4p710RDp8P9P8p8P9P3p8P9p100;gp4p7210REp8P9p100<jp4p710RFp8P9p100=Jp4p7210RGp8P9p100>Sp4p7210RHp8P9p100?Up4p7210R9p8P>p4p7211P5p8p100@[p4p70RIP5p8PIP=p8PIP?p8PIP6p8PIP7p8PIPAp8PIPCp8PIPDp8PIP8p8PIP3p8PIPEp8PIPGp8PIPHp8PIP9p8PAP?p8PAPCp8PAP2p8PAp100A[p4p741110R?p8PAp100BQp4p741110RIp8PAp100CLRJp4p7210RKp8PAPJp4p73110RJp8PAp100DXp4p7210RLp8PAp100Edp4p710RAp8p100F[p4p710RMp100G9RNp4p710ROp8PMPNp4p7210RNp8P@p606311001R@p100GRp4p7210RPp8P@p100HIp4p73110RQp8p100IARRp606311002RSP>p4p7210R>p8PSPCp8PSP3p8PSPQp8PSP?p8PSPIp8PSPKp8PSPAp8g00JIRKp4p70RIP<p8PIPFp8PIp100KHRIp4p710p8PRp6064111001RRP>p8PRPBp4p73110RBp8PRP3p8PRPQp8PRP?p8PRPJp8PRPAp8PBP>p8p100Kep4p70P8p8p100LSp606311001RAP8p8PAp100M[p4p7210RJp8PAP3p8PAPQp8PAPLp8p100NRp60621000RLP>p8PLPBp8p100OVp606311001RLP>p8PLPBp8PLPQp8p100P^RLp4p73101R?p100Q8RTp4p73110p8P?p100QQRUp4p73110p8P?p100Qmp4p710p8P?p100R@RVp4p7201p8P?p100RRp4p7201p8P?p102@9RWp4p73110p8P?p100S8RXp4p73110p8P?p100SLRYp4p73110p8P?p100Sfp4p7201p8PLp4p710RZPTp4p710p8PZPUp4p710p8PZPOp8PZPNp8PZPWp4p710p8PZPXp4p710p8PZPYp4p710p8p100T9p606311001RYP>p8PYPBp8PYPQp8p100UAp60621000RYP>p8PYPBp8p100VERYp60621001RZPPp8PZPCp8PYp606311000RYP>p8PYPBp8p100WKp4p7=1111111111100P5p8p100Wep6061001RYP1p8PYp100Y2p4p710RZp8PYp100YOp4p710p8p100Ylp6061000RYp100[9p4p710p8PYPFp8PYPZp8p100[VRZp4p710RYPMp8PYPOp8PYPNp8PYp100[jp4p73110p8p100\<p6061001RYP1p8PYp100]Cp4p710RYp8PZp4p741110RZP?p8PZp100]_R?p4p73101p8p100^;p6061000R1PFp8P1PYp8P1p100_Ep4p710p8g00_eR1p4p711g01mkRYp4p73101p8p100`hp4p7210PDp8p100aiRNp60621002ROPSp8POPCp8POPAp8POPJp8POPQp8PNp606311001RNP>p8PNPRp8PNPBp8PNPQp8p100c0p606<11111111111004RNP=p8PNP@p8PNp100cop4p710RBp8PNPRp8PNPDp8PNp100dip4p710R>p8PNp100ekp4p7210ROp8PNPQp8PNPHp8p100fkp6067111111003RNP=p8PNP@p8PNPBp8PNPRp8PNPDp8PNP>p8PNPOp8PNPQp8PNPHp8P?p4p710P8p8p100gop6067111111003R?P=p8P?P@p8P?PBp8P?PRp8P?PDp8P?P>p8P?POp8P?PQp8P?PHp8p100i4p4p70R?P:p8P?P<p8P?P4p8P?P;p8P?P5p8P?P=p8P?P6p8P?P7p8P?PDp8P?P8p8P?P3p8P?P2p8P?PEp8P?PFp8P?PGp8P?PHp8P?PIp4p7210p8P?P9p8p100j4p4p70P8p8p100jjp4p7<111111111110P8p8p100kMp4p741110R8PLp4p7511100R9p8P9P8p8p100kfp4p741110R8PLp4p76111100R9p8P9P8p8p100l>p4p741110R8PLp4p771111100R9p8P9P8p8p100l^p4p741110R8PLp4p7:1111111100RLp8PLP8p8PVp4p7200RVPZp8PZPVp8g00m5j12Tg00mUj2^Tg00n5j6QTg00o1j3ITg035fj4]Tg036gj7TTg02XGj1;Tg01Z;j27Tg01:7j18Tg01ZXj23Tg01X]j20Tg037kj4GTg01i=j1<Tg01?Ij1\Tg01_Ij1VTg01`cj1UTg01aAj1STg01bOj2ATg01Oej19Tg01PJj11Tg01Poj1RTg01m@j4@Tg01d8j2PTg01<Hj2OTg01dZj2MTg0131j3LTg01eFj3KTg01eej4JTg01QMj2>Tg01[Zj1=Tg01\9j26Tg01^4j3?Tg01^]j2HTg012Qj3NTg01_gj2CTg01`Ej4BTg01alj25Tg01F1j1FTg01c2j3[Tg01cUj3ETg038kj5WTg039Wj1XTPYj7YTg00`Dj8ZTf1RYP1g021SRVPVg0223RZf0R8g022SFYp=4g01oPRLPYg020lP8C@p=:f3R9P1PVPVPZf2R1PYP8GZp=Dg0233R?g0247RI%2KRKg0257%20[RH1^0L#2R0p,4RUNpRGg01onf5RFf4REP9P1EQf6R2?I1YPGf7RGP2PFPEPYPGP9P1P8C]FTg02kZR2%;GR3'7%8G/32'0f8RGPEP9PYCG%8G%<9'0%<E/32P2f9#;g02=BRG#\RD%2GR7%VLR6%ULR=%SLR5PLg02:jR;,ALg03:Ug02;HR4#9R<#1#1#9#1#9#RR:,ALC@'41P5ZRZP8P1g02?9RQg02?YRO'O1M81=LQOdAKL;YCJROb6b7b81>;:P8b51>;2eg02=nR;#=R:#=,6L16L:16L;5?L5?Lg02>M'H=NGDP7PLPL1CLEP1P6CBPY1CL9CBP=P5%14R=#1,5LR615L<R<':,45%FVRVP515L4R415L=5[LR=AEL64':,45PVAEL<4,:=,45CDCDPZPOb6b7b8X9LX:LX;LX<L109117Y113EY'0171913E1'0[[^9L^:L^;L^<LP8f:RO#8%<F%;OP2PYP1O6b5DWb?b>%X1,03eWAW@X1LX40X3HX0KX2IX=?PFPEP9P1PYP8O6X1LW4W3W0W2W=o"). Qed.

(* [comment removed for export] *)
Lemma cszR_csz n : cszR n = csz n.
Proof.
ltac2:(KReplay.run1 (kr_t_HnStep ()) ["HMSTEP"] "h04__x1h11zh21Hh37__arithh44__ffh58__varmaph65__with71np;1p;2p;3p;4p;6p;7p-1R0p10000p4p710R1p8P0p1000QR2p4p710R3p8P0P2p4p7210R2p8p1000nR0p4p710R4g0020R5p4p710R6p8P4p1002Lp4p710R7p8P4p1002jp4p7210R8p8P4g003GR9p4p710R:p8P0p4p7210R0P6p8P0P7p8P0P8p8P0P:p8p1003ep4p70P:p8p1004Up4p70R0p1035Op4p710R;p8P0p1005lR<p4p710R=p8P0P4p8P0p1006Hp4p710R4p8P0P<p4p7210R<p8P0P6p8P0p10073p4p73110R>p8P0p10087R?p4p710R@p8P0P7p8P0P8p8P0p1008kRAp60621002RBp8P0p100:2RCp4p7210RDp8P0p100:jp4p710REp8P0P:p8P0P3p8P0p100;gp4p7210RFp8P0p100<jp4p710RGp8P0p100=Jp4p7210RHp8P0p100>Sp4p7210RIp8P0p100?Up4p7210R0p8P?p4p7211P6p8p100@[p4p70RJP6p8PJP>p8PJP@p8PJP7p8PJP8p8PJPBp8PJPDp8PJPEp8PJP:p8PJP3p8PJPFp8PJPHp8PJPIp8PJP0p8PBP@p8PBPDp8PBP2p8PBp100A[p4p741110R@p8PBp100BQp4p741110RJp8PBp100CLRKp4p7210RLp8PBPKp4p73110RKp8PBp100DXp4p7210RMp8PBp100Edp4p710RBp8p100F[p4p710RNp100G9ROp4p710RPp8PNPOp4p7210ROp8PAp606311001RAp100GRp4p7210RQp8PAp100HIp4p73110RRp8p100IARSp606311002RTP?p4p7210R?p8PTPDp8PTP3p8PTPRp8PTP@p8PTPJp8PTPLp8PTPBp8p100JIp4p70RLP=p8PLPGp8PLp100KHRLp4p710p8PSp6064111001RSP?p8PSPCp4p73110RCp8PSP3p8PSPRp8PSP@p8PSPKp8PSPBp8PCP?p8p100Kep4p70P:p8p100LSp606311001RBP:p8PBp100M[p4p7210RKp8PBP3p8PBPRp8PBPMp8p100NRp60621000RMP?p8PMPCp8p100OVp606311001RMP?p8PMPCp8PMPRp8p100P^RMp4p73101R@p100Q8RJp4p73110p8P@p100QQRUp4p73110p8P@p100Qmp4p710p8P@p100R@RVp4p7201p8P@p100RRp4p7201p8P@p102@9RWp4p73110p8P@p100S8RXp4p73110p8P@p100SLRYp4p73110p8P@p100Sfp4p7201p8PMp4p710RZPJp4p710p8PZPUp4p710p8PZPPp8PZPOp8PZPWp4p710p8PZPXp4p710p8PZPYp4p710p8p100T9p606311001RYP?p8PYPCp8PYPRp8p100UAp60621000RYP?p8PYPCp8p100VERYp60621001RZPQp8PZPDp8PYp606311000RYP?p8PYPCp8p100WKp4p7=1111111111100P6p8p100Wep6061001RYP1p8PYp100Y2p4p710RZp8PYp100YOp4p710p8p100Ylp6061000RYp100[9p4p710p8PYPGp8PYPZp8p100[VRZp4p710RYPNp8PYPPp8PYPOp8PYp100[jp4p73110p8p100\<p6061001RYP1p8PYp100]Cp4p710RYp8PZp4p741110RZP@p8PZp100]_R@p4p73101p8p100^;p6061000R1PGp8P1PYp8P1p100_Ep4p710p8g00_eR1p4p711g01mkRYp4p73101p8p100`hp4p7210PEp8p100aiROp60621002RPPTp8PPPDp8PPPBp8PPPKp8PPPRp8POp606311001ROP?p8POPSp8POPCp8POPRp8p100c0p606<11111111111004ROP>p8POPAp8POp100cop4p710RCp8POPSp8POPEp8POp100dip4p710R?p8POp100ekp4p7210RPp8POPRp8POPIp8p100fkp6067111111003ROP>p8POPAp8POPCp8POPSp8POPEp8POP?p8POPPp8POPRp8POPIp8P@p4p710P:p8p100gop6067111111003R@P>p8P@PAp8P@PCp8P@PSp8P@PEp8P@P?p8P@PPp8P@PRp8P@PIp8p100i4p4p70R@P;p8P@P=p8P@P4p8P@P<p8P@P6p8P@P>p8P@P7p8P@P8p8P@PEp8P@P:p8P@P3p8P@P2p8P@PFp8P@PGp8P@PHp8P@PIp8P@PLp4p7210p8P@P0p8p100j4p4p70P:p8p100jjp4p7<111111111110P:p8p100kMp4p741110R:PMp4p7511100R0p8P0P:p8p100kfp4p741110R:PMp4p76111100R0p8P0P:p8p100l>p4p741110R:PMp4p771111100R0p8P0P:p8p100l^p4p741110R:PMp4p7:1111111100RMp8PMP:p8PVp4p7200RVPZp8PZPVp8g01PJj1<Tg01Poj11Tg01Oej1;Tg02U?j2RTg01ZXj20Tg03;<j23Tg01Z;j26Tg03;Yj25Tg01@Ij2:Tg01?Ij1BTg00m5j1QTg01_gj2PTg01`cj1OTg01aAj1MTg01alj2LTg01cUj38Tg01m@j4@Tg01d8j2JTg01<Hj2?Tg01dZj2ITg0131j3>Tg01eFj3GTg01eej4HTg02_Pj3FTP5j6ATP9j6KTg03<6j1ETg03<lj1DTg01bOj2NTPYj7CTf0RY#<#<p=7%;Y#;p=9g01oPR9f1R5;>Yp=21N9Yp=4P5P1g021SR1P1g0223R1PYg022SFCp==P9g02;HRV#<RZ#<R:#7RM#7#7#7#7#1R0%1Z%;Z#7#1RZ'RR@105ZRL%;V#9#9#9#9#9#1RI'0RH/30/60'5%1:R:,05%1MRM'0RG/0Y%1VRF':/3Y/6Y,5@'2X19g02=BR2#BR3%Q2R21P95RE%O9R8%M9R7P91L9VRV%4Z589R>g03=gR6%4:989V%4M589C@'=1J71R1PYf2RVg02?9R<g02?YR4'?1IYV=><4dg02:j=G95CHR4b4b5b6X0910YZR<10Y:/0M'2RM^09PYP5O1b3PMP9PL10VZRM/0IR5/30/60,5@R:10Y0/:F/30/60,5@'2X19P3P2PEP8P9%4I989>P6%40989>%4F5F9C@,=7P1P4b4b5b6X0910<I10<0/:F'2^09PYPVO1b310L0/:F,2HP9P5f3/0Z/0I/30/60,5@13Y0/60,5@'2X191?9:10M0/:FPYEAb2PGPYEAb2g03>Ng03?FEK%EY%DY'2eX79PYO1X79o"). Qed.

End HMSTEP.

End HnStep.
Module HnReach.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0032. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.MallocCtrl OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Inv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0032.MI_Kit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_List OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Ext OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Sim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0049.MI_Contracts.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP Decode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Bridge Require Import BrRes.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnTree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnAbs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnEmpty OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWNtf OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnMeta OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWFree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWSlot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWGrp OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnWMalloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0050.HnRes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Heap.Mh_0114.HnStep.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_HnReach () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3sndI79OSSVerify5KrLib2CJ4Spec7Mh_00045STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI46Stdlib7Sorting;Permutation;Permutation00C79OSSVerify5KrLib2CJ4Spec7Mh_00045STree9stree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad1MC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=implM_ret_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad5mbindC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00506HnTree:apw_cpathwC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC69OSSVerify5KrLib4Heap7Mh_00506HnTree@cpathw_cpath_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8ctree_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Sim:cpath_liveC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4optrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree4implC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree9impl_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_ebind_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ6Bridge7Mh_00836BrBase>impl_enode_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5ITree5epostC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC69OSSVerify5KrLib2CJ4Spec5Monad4mretC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad5implMC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_bind_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv3blkC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fsc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_msys_invC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec5Monad4msysC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:mbind_mgetC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_mget_invC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5emptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6LookupC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5Mergec69OSSVerify5KrLib4Heap7Mh_01147HnEmbed>implM_mupd_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:mbind_mupdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed<mbind_mret_lC1?~~~~~~~~~~~~~~~K35stdpp8fin_maps6FinMap01c69OSSVerify5KrLib4Heap7Mh_01147HnEmbedCForall_app_cons_midC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appI46Stdlib5Lists4List6Exists00c69OSSVerify5KrLib4Heap7Mh_01147HnEmbedClength_app_cons_midC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8nil_consI35stdpp4gmap4gmap00C35stdpp4base4fmapc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=Forall_filterC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC35stdpp8fin_maps>map_size_emptyc69OSSVerify5KrLib4Heap7Mh_01147HnEmbed@length_filter_leC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List;filter_trueC46Stdlib9micromega5Tauto5eKindK46Stdlib9micromega5Tauto8GFormula05I69OSSVerify5KrLib4Heap7Mh_00506HnTree6cpathw00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed=machine_eventC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed5embedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes5gtreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes=gtree_vis_invC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464Prog6membedC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed:embed_freeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01147HnEmbed;embed_freewC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4cptrC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC35stdpp8fin_mapsAmap_to_list_emptyC35stdpp4gmap;gmap_lookupC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2CJ3Lib4RunP:secret_valC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5minitC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5stripC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib4Heap7Mh_00505HnRes3RES00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3PhiC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs3PsiC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00c69OSSVerify5KrLib4Heap7Mh_01146HnStep8RES_initC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs4wregC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs4zsumC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC35stdpp8fin_maps8map_sizeC35stdpp4base4sizeC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_maps;map_to_listC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc9s_regionsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5s_ctxC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5c_brkC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7s_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1N00I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6region00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs7is_gregC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableI79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4area00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify5KrLib2CJ4Spec7Mh_00326MI_Kit;aptr_eq_decC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc8brkstate00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4PGSZC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List2InC46Stdlib5Lists4List:length_mapC35stdpp4base5EmptyC46Stdlib5Lists4List7existsbC35stdpp8fin_maps:map_eq_iffK46Stdlib9micromega5Tauto8GFormula08I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6creach00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv7ld_liveC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc7cmallocC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv5cpath00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6creach02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_0049<MI_Contracts:creach_simC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib4Heap7Mh_00505HnAbs:INVC_stripC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00509HnWMalloc3MQCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes9rs_marithC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00509HnWMalloc<cmalloc_walkC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z7add_0_lC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_lK47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02c69OSSVerify5KrLib4Heap7Mh_01146HnStep:RES_mallocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5hostsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_0049<MI_ContractsFcmalloc_contract_proofC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv:event_postC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9event_preC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv8set_liveC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv4INVLC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC69OSSVerify5KrLib4Heap7Mh_00505HnAbs4INVCC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv2MRC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00507HnEmpty4GEOMC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00045STree5stree01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9answer_okC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2CJ4Spec7Mh_00045STree5stree02C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6mstate00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv5bslotC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00496MI_Inv2x0C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z8inj_succI79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc2ev00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4mled00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes5ecostC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5lhead00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I46Stdlib9micromega5Tauto8GFormula00C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc5cfreeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:in_map_iffK47Corelib4Init5Logic2ex01C46Stdlib7Sorting;Permutation>Permutation_inK79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv6creach03C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_0049<MI_Contracts8In_bslotC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib4Heap7Mh_00507HnWFree4FREL00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes7rs_einvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00507HnWFree:cfree_walkC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01146HnStep8RES_freeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv9ap_removeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00506HnTree9unmap_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes3cszC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powc69OSSVerify5KrLib4Heap7Mh_01146HnStep5NAMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ6Bridge5BrRes3potC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnAbs6nareasC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib4Heap7Mh_01146HnStep8nareas_KC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes6rs_l63C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes9Phi_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes9Psi_boundC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4Heap7Mh_00505HnRes9pot_boundC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationBPermutation_lengthC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega:ZMicromega;ZArithProof03C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc6NSLOTSC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00".
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HMREACH.
Context {RUNp : RunP}.

Theorem reach_init resv K : 0 <= K ->
  RES (strip (minit secret_val resv)) [] K /\ Phi (strip (minit secret_val resv)) = 0 /\ Psi (strip (minit secret_val resv)) = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_HnReach ()) ["HMREACH"] "p'0h01nh11xi001xh21Kh31mh44resvh52HKh67__arithh74__ffh88__varmaph95__with:2krh;1lh<1yi013offi023ridp&0p;2p;1p;3p;4p;6p;<p;7p;5p;Bp-1R0p10000p4p710R1p8P0g000QR2p4p710R3p8P0P2p4p7210R0p8p1000nR4p4p710R5p10020p4p710R6p8P5p1002Lp4p710R7p8P5p1002jp4p7210R8p8P5g003GR9p4p710R:p8P4p4p7210R4P6p8P4P7p8P4P8p8P4P:p8p1003ep4p70P:p8g004UR4p4p70R;p1005Up4p710R<p8P;g005lR=p4p710R>p8P;P5p8P;p1006Hp4p710R5p8P;P=p4p7210R?p8P;P6p8P;p10073p4p73110R@p8P;p10087RAp4p710RBp8P;P7p8P;P8p8P;p1008kRCp60621002RDp8P;p100:2REp4p7210RFp8P;p100:jp4p710RGp8P;P:p8P;P3p8P;p100;gp4p7210RHp8P;g00<jRIp4p710RJp8P;p100=Jp4p7210RKp8P;p100>Sp4p7210RLp8P;p100?Up4p7210R;p8PAp4p7211P6p8p100@[p4p70RMP6p8PMP@p8PMPBp8PMP7p8PMP8p8PMPDp8PMPFp8PMPGp8PMP:p8PMP3p8PMPHp8PMPKp8PMPLp8PMP;p8PDPBp8PDPFp8PDP0p8PDp100A[p4p741110RBp8PDp100BQp4p741110RMp8PDp100CLRNp4p7210ROp8PDPNp4p73110RNp8PDp100DXp4p7210RPp8PDp100Edp4p710RDp8p100F[p4p710RQp100G9RRp4p710RSp8PQPRp4p7210RRp8PCp606311001RCp100GRp4p7210RTp8PCp100HIp4p73110RUp8p100IARVp606311002RWPAp4p7210RAp8PWPFp8PWP3p8PWPUp8PWPBp8PWPMp8PWPOp8PWPDp8p100JIp4p70ROP>p8POPJp8POp100KHROp4p710p8PVp6064111001RVPAp8PVPEp4p73110REp8PVP3p8PVPUp8PVPBp8PVPNp8PVPDp8PEPAp8p100Kep4p70P:p8p100LSp606311001RDP:p8PDp100M[p4p7210RNp8PDP3p8PDPUp8PDPPp8p100NRp60621000RPPAp8PPPEp8p100OVp606311001RPPAp8PPPEp8PPPUp8p100P^RPp4p73101RBp100Q8RMp4p73110p8PBp100QQRXp4p73110p8PBg00QmRYp4p710p8PBp100R@p4p7201p8PBp100RRp4p7201p8PBp100RdRZp4p73110p8PBp100S8R[p4p73110p8PBp100SLR\p4p73110p8PBp100Sfp4p7201p8PPp4p710RPPMp4p710p8PPPXp4p710p8PPPSp8PPPRp8PPPZp4p710p8PPP[p4p710p8PPP\p4p710p8p100T9p606311001R\PAp8P\PEp8P\PUp8p100UAp60621000R\PAp8P\PEp8p100VER\p60621001RPPTp8PPPFp8P\p606311000R\PAp8P\PEp8p100WKp4p7=1111111111100P6p8p100Wep6061001R\P1p8P\p100Y2p4p710RPp8P\p100YOp4p710p8p100Ylp6061000R\p100[9p4p710p8P\PJp8P\PPp8g00[VRPp4p710R\PQp8P\PSp8P\PRp8P\p100[jp4p73110p8p100\<p6061001R\P1p8P\g00]CR\p4p710R1p8PPp4p741110RRPBp8PRg00]^RBp4p73101p8p100^>p6061000RSPJp8PSP1p8PSp100_Hp4p710p8g00_hRSp4p711g00`GR1p4p73101p8p100`kp4p7210PGp8p100alRQp60621002RTPWp8PTPFp8PTPDp8PTPNp8PTPUp8PQp606311001RQPAp8PQPVp8PQPEp8PQPUp8p100c3p606<11111111111004RQP@p8PQPCp8PQp100d2p4p710REp8PQPVp8PQPGp8PQp100dlp4p710RAp8PQp100enp4p7210RTp8PQPUp8PQPLp8p100fnp6067111111003RQP@p8PQPCp8PQPEp8PQPVp8PQPGp8PQPAp8PQPTp8PQPUp8PQPLp8PBp4p710P:p8p100h2p6067111111003RQP@p8PQPCp8PQPEp8PQPVp8PQPGp8PQPAp8PQPTp8PQPUp8PQPLp8p100i7p4p70RQP<p8PQP>p8PQP5p8PQP?p8PQP6p8PQP@p8PQP7p8PQP8p8PQPGp8PQP:p8PQP3p8PQP0p8PQPHp8PQPJp8PQPKp8PQPLp8PQPOp4p7210p8PQP;p8p100j7p4p70P:p8g00jmR;p4p7<111111111110P:p8g00kPR:p4p741110RQPBp4p7511100ROp8POPQp8g00kiRQp4p741110ROPBp4p76111100RLp8PLPOp8g00lAROp4p741110RLPBp4p771111100RKp8PKPLp8g00laRLp4p741110RKPBp4p7:1111111100RJp8PJPKp8PBp4p73100RKPRp8PRPKp8g00m8j2<Tg00mXj1=Tg00n8j2fTg00nTj1]Tg00oOk200Tg010Pj1nTg011Qj1;Tg0121j3eTg012nj1aTg013ij1\Tg014dj23Tg015?j4YTP2j3~Tg016@j1zTP=j48Tg017<j19TP\j3:TPIj2>Tg0188RIj11Tg018Xj1GTg019=j1?Tg019[j4cTg01:9j6bTPPj4Sj3LTPLj4Vj3TTg01:Zj4^TPQj4Bj3HTPYj2ITg01;4j3JTg01;FRYj22Tg01;cRQj26Tg01<@j24Tg01<Zj3[Tg01=@j1Zj37Tg01=Zj1XTg01>8l<{Tg01>]j6yTg01?Fj1wTg01?dj1pTg01@Bj1oTg01@mj2QTg01APj3FTg01B3j4PTg01B^j3mTP1j7lTg01CAj2kTg01Ccj2jTg01DOj3iTg01Dnj4hTg01E`j4gTg01FKj3KTP:j3MTPOj3ETg01Fbj3NTg01G9j3OTg01GQj3DTPBl<dTP9j6ATg01Gjj5@TP;l<qTg01HGj1rTg01ILj1sTg01JMj1tTg01KNj1uTg01LQj4vTg01Llj4`Tg01MOl<xTg01N4lBUTg01NZj7_Tg01O>R;f0R9g01O\RB37p=5f1RO/69=7;Bp=0P;P;g01P:P9C`p=Rg01P^R:P;P;P;PIPIf3RIf2R1POg01Q=RLPBP9M<xp=WP;P;P;P;P;P;PYP9POP1PYPIf4RYf5RPf6R\f7R=PBf8R2MBUp=}P;P;P;P;P;P;PQP9POP1PQPIPYPBPPP\P=P2MBUp=|POPSg01Q\R2P2g01R<R=P9g01R\F_p=C1<;;#=R\1fB9p,4RUNp#]RP0001#nRY1<4;#;;eO%aY#5%\Y#5'3RIPPP1POP9CYg01S<RPg01SZRQ'<RK#=RR%;KRJPKP;A~PQ9#zX:KRHP9C8#9/0Bg01T^R0=:K9,>K#1g01U]#GR3#G#?RGP4PPg01VBR8P;g01V[R7CcR@PPP8g01W4R6P;P7g01WREbR7g01X0R?CSR5P4P?P5P4P@P7P?CVC^R>P4P@P7P?CB,I53JR<#1'2'0'3X;RP:PLPKP;PHPJC8#9/0BRRA:K0J,>K#1RJ%19RU,2G'0'3X0:10BBRT%1LRL12GLRA'6RV#5RE'312GBRC,6BRN#5RD,3TRFPTPEPTPDp-0/4T9[TTP;P;%Z;RTP9X1;RDPTA7;O9#XX<;X1;PVPNPDPDPD16O9#R,4;X3;X0;PLPDPD14;UX1:14;BR:CWRUPAPCPDPDPD12O9#R,4;X3;X0;PGPG14;GPLPUM9}M9|PBPBP:M<{Eyg01Y2R:#;%=:%w;%p;%o;R:PSP2P2P=P;1Q;BR2=F;2g01Y^RSP2CP,C:P;1Q;G=m;29F;2PSP2CP,C:Fl1k:=P9P1g01ZER:g01ZeR='41j91=7:=dAi;BOChb7b8b9PFP9b6Cg10JA,3ReP<P4AL4@7AK4@7AM4@7AH4@7AE4@7AN4@7AO4@7AT4@7g01[ER@AD4@7P?M<dEAPPPQPPP8P6PQCSR?PPP8P6PQCVR@PPP8P6PQCB,I?D@PPALP86AKP86AMP86AHP86AEP86ANP86AOP86ATP86P8ADP86PQM<qEAPKP;PHPPPQP?P@%rYD@R@C8#9g01\LP;%sY#tPB%?3g01]R'2PBn011000003000020102101'0A:K0@,>K#1%uY9J5>#1,2G'0'3ePIeCvW5X2;X4\POP9O2X2;W4o"). Qed.

Theorem reach_malloc cs L n L' cs' p c k SZ K :
  creach cs L -> 0 <= n -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  cpathw ecost L (cmalloc cs n) L' (cs', Some p) c k -> Z.of_nat (length (ld_live L)) + 1 <= K ->
  creach cs' (set_live (p :: ld_live L') L') /\ ld_live L' = ld_live L
  /\ RES cs' ((p, n) :: SZ) K /\ c <= Phi cs' - Phi cs /\ Z.of_nat k <= Psi cs' - Psi cs /\ ~ In p (ld_live L).
Proof.
ltac2:(KReplay.run1_chk (kr_t_HnReach ()) ["HMREACH"] "p'0h01Hh11mi001mh22H0h32H2h42LSh52H1h62BLh72H3h81bh92H4h:1pi011ph;3CPkh<3CTkh=1Li021Lh>1nh?2L'i032L'h@2LxhA1lhB1ri041rhC1si051shD2sthE1zi061zhF2LyhG1PhH1ei071ehI1ki081khJ2r0hK2HKhL3LENhM2MQhN2e0hO1thP1xi091xhQ5INVC0hR5INVC1hS1KhT2SZhU2_HhV4__x1hW4__x2hX4__x3hY1ci0:1chZ2csh[3cs'h\2e1h]2r1h^3BL'h_2CPh`3CPWha2CRhb3CR'hc2CThd3EBLhe2ELhf3Esthg4Est'hh2FRhi2H5hj2HChk3HK'hl2HNhm2Hkhn2Hnho2IHhp3INVhq4INV'hr4LEN0hs4LIVEht5LIVE'hu3LS'hv2NIhw1Rhx2R'hy3SZPhz4SZP'h{3_H0h|7__arithh}4__ffh~8__varmapi0;5__witi0<1ai0=4cstri0>5cstr0i0?2kki0@3st'i0A1yi0B2m0p%0p&0p;2p;1p;3p;4p;9p;:p;6p;7p;>p;<p;Fp;5p;8p-1R0p10000p4p710R1p8P0g01^RR2p4p710R3p8P0P2p4p7210R0p8g000nS00p4p710R4g0020R5p4p710R6p8P4g002jR7p4p710R8p8P4P7p4p7210R9p8P4g003GR:p4p710R;p8Q00p4p7210R<P6p8P<P8p8P<P9p8P<P;p8p1003ep4p70P;p8g004UR<p4p70R=g01^oR>p4p710R?p8P=g005lR@p4p710RAp8P=P4p8P=g006HR4p4p710RBp8P=P@p4p7210RCp8P=P6p8P=g0073RDp4p73110REp8P=p10087RFp4p710RGp8P=P8p8P=P9p8P=p1008kRHp60621002RIp8P=p100:2RJp4p7210RKp8P=p100:jp4p710RLp8P=P;p8P=P3p8P=g00;gRMp4p7210RNp8P=g00<jROp4p710RPp8P=g00=JRQp4p7210RRp8P=g00>SRSp4p7210RTp8P=g00?UR=p4p7210RUp8PFp4p7211P6p8g00@[S01p4p70RVP6p8PVPEp8PVPGp8PVP8p8PVP9p8PVPIp8PVPKp8PVPLp8PVP;p8PVP3p8PVPNp8PVPRp8PVPTp8PVPUp8PIPGp8PIPKp8PIP0p8PIp100A[p4p741110RGp8PIp100BQp4p741110RVp8PIp100CLRWp4p7210RXp8PIPWp4p73110RWp8PIp100DXp4p7210RYp8PIp100Edp4p710RIp8p100F[p4p710RZp100G9R[p4p710R\p8PZP[p4p7210R[p8PHp606311001RHp100GRp4p7210R]p8PHp100HIp4p73110R^p8p100IAR_p606311002R`PFp4p7210RFp8P`PKp8P`P3p8P`P^p8P`PGp8P`PVp8P`PXp8P`PIp8g00JIRXp4p70RVPAp8PVPPp8PVg01_FRVp4p710p8P_p6064111001R_PFp8P_PJp4p73110RJp8P_P3p8P_P^p8P_PGp8P_PWp8P_PIp8PJPFp8p100Kep4p70P;p8p100LSp606311001RIP;p8PIp100M[p4p7210RWp8PIP3p8PIP^p8PIPYp8p100NRp60621000RYPFp8PYPJp8p100OVp606311001RYPFp8PYPJp8PYP^p8p100P^RYp4p73101RGp100Q8Rap4p73110p8PGp100QQRbp4p73110p8PGp101_ep4p710p8PGp100R@Rcp4p7201p8PGp100RRp4p7201p8PGp100RdRdp4p73110p8PGp100S8Rep4p73110p8PGp100SLRfp4p73110p8PGp100Sfp4p7201p8PYp4p710RgPap4p710p8PgPbp4p710p8PgP\p8PgP[p8PgPdp4p710p8PgPep4p710p8PgPfp4p710p8p100T9p606311001RfPFp8PfPJp8PfP^p8p100UAp60621000RfPFp8PfPJp8p100VERfp60621001RgP]p8PgPKp8Pfp606311000RfPFp8PfPJp8p100WKp4p7=1111111111100P6p8p100Wep6061001RfP1p8Pfp100Y2p4p710Rgp8Pfp100YOp4p710p8p100Ylp6061000Rfp100[9p4p710p8PfPPp8PfPgp8p100[VRgp4p710RfPZp8PfP\p8PfP[p8Pfp100[jp4p73110p8p100\<p6061001RfP1p8Pfp101`8p4p710Rfp8Pgp4p741110RgPGp8Pgp101`TRGp4p73101p8p100^>p6061000R1PPp8P1Pfp8P1p100_Hp4p710p8g00_hR1p4p711g01a0Rfp4p73101p8g00`kR[p4p7210PLp8p100alR\p60621002RZP`p8PZPKp8PZPIp8PZPWp8PZP^p8P\p606311001R\PFp8P\P_p8P\PJp8P\P^p8p100c3p606<11111111111004R\PEp8P\PHp8P\p100d2p4p710RJp8P\P_p8P\PLp8P\p100dlp4p710RFp8P\p100enp4p7210RZp8P\P^p8P\PTp8p100fnp6067111111003R\PEp8P\PHp8P\PJp8P\P_p8P\PLp8P\PFp8P\PZp8P\P^p8P\PTp8PGp4p710P;p8p100h2p6067111111003RGPEp8PGPHp8PGPJp8PGP_p8PGPLp8PGPFp8PGPZp8PGP^p8PGPTp8g00i7RGp4p70R^P?p8P^PAp8P^PBp8P^PCp8P^P6p8P^PEp8P^P8p8P^P9p8P^PLp8P^P;p8P^P3p8P^P0p8P^PNp8P^PPp8P^PRp8P^PTp8P^PVp4p7210p8P^PUp8p100j7p4p70P;p8p100jmp4p7<111111111110P;p8p100kPp4p741110R;PYp4p7511100RUp8PUP;p8p100kip4p741110R;PYp4p76111100RUp8PUP;p8p100lAp4p741110R;PYp4p771111100RUp8PUP;p8p100lap4p741110R;PYp4p7:1111111100RYp8PYP;p8Pcp4p7200RcPgp8PgPcp8g00m8j2XTg00mXj1bTg01aTj3eTg00n8j27Tg0121j3]TP2k203TP@j4WTg01bVj11TP4j3^Tg01cWS02k10JTg01d9j3\TP[m90>Tg0188S03j1;Tg019=k10fTg01;cj2GTPQm:0_Tg01e<S04j68Tg01f=m:0YTP=k70TTg01g?j4|Tg010Pj1NTg01hKR=j26Tg01=@j30k101Tg012nj14Tg013ij12Tg01hek708TP5j6ATg01igk30cj6`Tg01jfk40bTg01kgm90aTPMm>0`Tg01loj2sTg01mFk10^Tg01mgk20]Tg01nGk10\Tg01<@j2PTP:j6Tj8uTPOk10Zk207TP7j6gTg01nkR7j1_Tg01oJk20XTg01omk30WTg01>8m<0UTg020Jk40STg0211j1~Tg021Vj2nTg022?j3}Tg022hk20RTg011Qk10QTg023Tj3RTg0244k20OTg01?Fk10NTg024Rj4zTg01?dk10MTg01@Bk10LTg0250j2pTg018Xj1yTg01@mk20KTg01APk30ITg01B3j4lTg025Sk10HTg01CAk20GTg01Cck20FTg01DOk30DTg01Dnk40CTg0265mF0BTg0278j2JTg027Uj3HTg014dROj23Tg028Vk60?Tg000Qk30=TPSj5FTQ00k30PTg029nj3LTg02;2k20;Tg02;Qk20:TPDk70oTg01LQj4aTg02<Tk202Tg02=6j4hTg02=Vj2iTg02>Xj6jTP>k306Tg02?Xk105Tg02@1k60nTPVk40mTg01MOm<0lTg01NZk70kTPfk80jTg02@mk20iTg02Akk10eTg02Bik40gTg02Ckk40hTg02Dnk50dTg02F0Rff2RVf1R>f0RD-02GChp=Q207GDp=I202GDp>0[ARG>Dp=Sf3RS1i>D7eVp>00%1>=0VDp==PXPGg02G4R:PDCWp=9f7RMf6R550ff5RQg02H5R[f4R4PSPVP>Ej/3D'3p=>PGg01O>R@PVP>Ch=RSDp=51J5Q,7M%;41JSV'7B06G>D$05'3'3p=?A05Q4A]SV>/3D'3p=DARGSV/i>9eQ4/3Dp=CA0f>Dp=dPMP[P5PQP4PSEj%1>=0VD'3p=oPQP[P4PSPVP>Ej/3Dp>0<P4P[PSPVP>PDEjp=fP4P[PSPVP>PDJ0np=[%1>9RGV/iDp=KARGV>/iDp=YPGP@P4PSCh=RQV=]5>/3Dp>09Ae5Q4A0SV>/3D'3p>04g01P^R2?0>Dp=V207XDp=BPXPGP:PDH0mp=qP2P2P@P@P7Q03Q03PSg02I3PVP>PDN<0lp>0VP>P1g01Q\S05Q05g01R<S06PDg01R\K0kp=tPSP1Q05Q05Q06PVP>PDL0jp=wg01ZES07g01ZeS0870Dp>0E%;>/7Dp=cPSPGPVP>CW=^GDp>0A20i>D$0ep=EAHQ4SA0V>D'3p=M%;S1JV>'7/3Dp=kA]Q4S17V>/3D'3p>0@PSPGPVP>CWPXPGP:PDCW5^Gp=U1JQ4,75%;S1JV>'7/3D'3p=vPGP@P>PDChp=xARSV>=]4Dp={1J>D,7Vp=rB06G>D$05p=mg02IWR:P@P>PDH0gp=:g02JWR1?0>Dp=<P1P4PSPVP>PDETp=ZQ07PSPVP>PDH0hQ0830p=OP:P@PVP>PDI0dp=@1X<@S09#bS0:Q0:p,4RUNpR7f9Rcf8Rg3eg01O\R;/7gf;RY?]SVQ09P<203<@S0;P4CW%1Y5^<P7&0JGRU,XfR^g02KWRTf<RRf=RP=\7Yf:RNAQUcgPMP5N90>%1PR0#I#;g01U]S0<$0fR3'G/7QP7P^PTf?RL=\7PR9f>R8PRAQUYNREPcPgP>N:0_P7P^P8P9PRPEE8P7f@REPLP8PPPR&0[YP5PQPDN:0YP7PR1SY0PPH00P7P^PEfAR0=\7LP8AQUPRP>K0T%bGR9%1E7=8P7fBR6P0PgC|%bXRXg02LQ%b<[RC%NVRBfERAP7PVfDR?P>PD%9>RZ9=9?G>X4C'6X6X'6XDf,6fP=PfPBfFRFP7PVPAP>PD%1AR_=09ZG>X4C,6CX6X,6XXDfP7PEPL%10RJP0P9PJfCRJ#1RHPE1XG@R\PLP6PRC5PYP8%4E%4?RWPP%2E%2?RIPLPHG?FDECPDPBfHRHP7PVfGRKP>PD%1KR`=09ZG>X4C,6CX6X,6XP=PX%NSR]fIReP7PSPHP>PDA=9HZG>X4C,6CX6XP7P?PJP_PAP9P_P`P?P\PJPFPEC5PLP6PW%4HRWP0PI%2HRIPJP`G?FDECPD%NQS0=fKR`P7PQfJR_P>PDA=9_ZG>X4C,6CP=PC%N5RdfLRbP7P5P`PVPD%1`Ra%9VRh509G>X4CP7PHPK%1eRiPeP9PiPaPHP\PKP_P?C5PJPFPW%4bRWPAPI%2bRIPKPaG?FDECPD%NgS0>fNRaP7PgfMRiP4PD%1iRj%94Rk509G>PO%NcRlfORm'dP7PcPaPQP>P9Pa%9QRnGoP7PbP`PjPiP9Pj%1mRjPbP\P`PaPHC5PKP_PWfPRW#4RoPePI%2WRIP`PjG?FDECPD%NYRjfQRp'dP7PRPpPgP4%1pRq%9gS0?509J0<POP7PPfRRrPcPQDf%9cRs9=9rP7PWPmPqPpP9PqfSS0@#1RqPWP\PmPrPbC5P`PaPofTRo#4PiPI%2oPmPqG?FDECPDP7PLPoPYPMDffURq%9RRI5=9P7P[P0fVRtPPPcP>K08P7%N0S0APtPPPcD[Pf%N6S0BP7PDfXRuPLPYD[X1fPDPuP5EAP7PufWRvP8PND[P7PqAKottPHC|PBPuP7PVfYRw=KvwRxP>PDA=9xZG>X4C,6CX6X,6XXDf,6fP=PfPBPwP7PVfZRx#1Ry=YuxRzP>PDA=9zZG>X4C,6CX6X,6XXDfP7PvPt%1uRzPuP9PzPyPvP\PtPwQ0@C5PrPq%4vf[Rz#4R{Po%2v%2zR|PtPyG?FDECPDPBPzP7PVf\RB#1Ry=YxBR}P>PDA=9}ZG>X4C,6CX6X,6XP=PXP]PBP7PSf]R]=Kz]R~P>PDA=9~ZG>X4C,6CX6XP7PzP}P9Pyf^Ry#1R}PzP\PxP]PvPtPwP{f_R{#4R~PuP|%2{R|PxP}G?K09K04PDQ0=PyP7PQAK]{{R}P>PDA=9}ZG>X4C,6CP=PCPdP{P7P5f`Rd#1R==YydR}PVPDA=9}hG>X4CP7P{P}P9P=fbR=#1R}P{P\PyfaRhPzPxP]P~fcR~#4RZPBP|%2~R|PyP}G?K09K04PDQ0>PhP7PgAYd}=R}P4PDA=9}kG>PO1dl=P7PcAKh~~RlPQP>P9PlPnGoP7P~P=fdRn#1RlPnP9PlffS0>#1RlP~P\P=feR}P{C5PyPhPZfgRZ#4RhPdP|%2ZR|P=PlG?FDECPD1djnP7PRQ0>9YnlRlPgP4P9PlQ0?GoPOP7PPAK}ZZRlPcPQDfA=9lsP7PZQ0>fhRl#1RsPlP9PsfjRs#1RjPZP\Q0>fiRkP~C5P=P}PhfkRh#4PnP|%2hQ0>PjG?FDECPDP7PLAKZkkPYPMDfAYljs==9IP7P[P0AKkhhR[PPPcP>K08P7Q0AP[PPPcD[PfQ0BP7PDfmR[=Kh[PLPYD[X1fPDPhP5EAP7PhflRI=KsIP8PND[P7P^PTfpRTfnRj5\7foR|P[AQUIhS0BPsPkP=P;g01Q=R~B0cTrjP7PTP|PtPrPjPKPTPlPZPnH0bP}N90aN>0`PTPrPj1G;s1s~kQ0BE`P@1G;hfrR}PoPTPD1s~hAQUj[S0BE`XE@PDPh&0^hEAfqRZQ0@P|Ph1s~sAQU[IE`P220]~hfsRlPqPZP[PDAQU|jE`X>2PDPh&0\hEAP}PoPTPIPhQ0BE`P9%1}Q09P<Q0;PICW=^<DXA9Q0>%9wS0>PbEAQ09P<Q0;PhCWQ0>5^<P9%1ZS0>,S|%9z,STRh909DXA9P9%1lS0;1STD=09hXA9S09P9%9xS0BQ09Q0B,S|S0B,P9Q0;PiETQ0>P=ET%9JS0>P5EAQ0>Q0B509P9P2&0ZG%9?S0>PhPDEgQ0>#I%Ih'VP2%9AS0>#I%9]S0B,S}#I,VDX>2PD%BARh%qAEA%9B,SZ#I,VhP2Q0B#I%BK%_D'VX>2PD%B]Rh%q]EA%BF%_h'VP9fwRh#1S0B%ID#;/G3/7TXA9Pk%9yRyPpEA%Iy#;/G3/7|P2%9{#I%;DS09/G3/7ZX>2PD%B{Ry%q{EA%;y/G3/7T%BeS0A%BdS0?#_S0='VQ0A#;RyQ0?#;Rk/G350@S0CP2P@&012Q03&01@%;>Q0950@1V>D20X>D40WZ0A2XP2Q0APy1P@yQ0=1GD3XP@RyPkO1PyQ0?Pk1P@kH0VN<0UPVH0SQ0C%B_Rk#~%;k,7;%B=R=#~%;=,7;g01Y2R=%_~Rk#_,n@1n@k1n@~5}@5}@g02MT+0R&0Q=3R%b=P@P@20O@SPV&0N@R=CzP>P=Cz&0M@&0L@R=P@Q0<,p@S0Cg01Y^Q0<#yR~#y,p@20K@360I@RkCl,t=Q05$0HRyP=P@Pkg02N@Rk1p@~R~Cl,t=PyP@Q0CPkP~Cl,t=CwCwQ06-0G=PDPVQ07Q08'P20FDV$0EdB0D@;>H0Cb}b~c0;XV@XW@XX@1GV390@D1GS3/7V17VS[[^V@^W@^X@PD%Bn#;fuRn%Bi#;PSP4O5b|c0>c0=brbKbKbLbLbL%B?/cIP7fvRIPnPBPuftR3PTP|P}PZQ0;=YZlPAP0PjP[PiPsPVPSP5P>PDNF0BP}P\PZP3PjC5RsP[PT%4}%4IS0;'JP|%2}%2IS08P\203G@R[PsQ0>H0AfxRs?H>DPnPVP>Q01/X@/X@/X@/X@R;1En>fyR=/E>S01EM[^1<^8<'3CkJ0@POP\P}PnP|C5R~=]ljPZ%4l%4hRjPT%2l%2hS0>P\P[P~PFCUAH=>DPIPVP>P;1EI>fzR~/E>RkEM[^1<^8<'3FvP7P3Pl%1nRyPnP9PyQ0BP3P\PlPIPTC5P|P}%43%4sS07PZ%23%2sS06PlQ0BG?FDECPDPnP\1x3hPZPTD{P3Q0;%4~PlQ08%2~S08P\P[P\PnPsP}C5PeCUf|R}?H>DP=PVP>P;Q01f}RT/E>S01EM[^1<^8<'3FvPOf{RZ#49rnjP3Q0>%2ZRjP\P[P\PIP=PlC5P_CUAHT>DP~PVP>P;Pkf~Rk/E>R|EM[^1<^8<'3CkP7PsPh%1=RyP=P9Py%1ZRyPsP\PhP~P3C5PlPIQ07%4}S07PnQ06%2}S06PhPyG?FDECPD%4=%4T5rhPhQ08%2kP\P[P\P=P}PIC5PiCUp+01ARy?H>DPTPVP>P;Q01p+01BRl/E>S01EM[^1<^8<'3CkPOp+01@S08#2,Jj,csP\P[P\P~PTPhC5PaCUAHl>DPkPVP>P;P|p+01CR|/E>RjEM[^1<^8<'3P7P}PZ%1TR3PTP9P3Q08#1R3P}P\PZPkPsC5PhP~Q07%4yS07P=Q06%2yS06PZP3G?FDECPD%2T%2l'J,c~P\P[P\PTPyP~C5PpCUp+01ER~?H>DPlPVP>P;Q01p+01FR3/E>S01EM[^1<^8<'3POP\P[P\PkPlPZC5PrCUAH3>DP|PVP>P;Pjp+01GRj/E>EM[^1<^8<P7PyQ08%1lRhPlP9Php+01DRh#1S0>PyP\Q08P|P}C5PZPkQ07%4~PTQ06%2~Q08Q0>G?FDECPDP\P[P\PyPhPTC5PoCUp+01IS0>?H>DP3PVP>P;Q01p+01JR;/E>EM[^1<^8<P7Ph%1~R<,S|P~H00%1jR[909<R<PhP\1x|3Q08PkD{Rk%4hp+01HR\#45rlRl%2h%2\'J,cyRy1m|[R['3R|'3Rh'3RZ'3PIP<PZPnPkPhPPPlP|PcPyP[PQP7P\PjP3PTP}J0?P7P^PjA\7\3Q02PGp-0R}B0=fUD%1V,mDg02NgS02n10110900021010:00XB^X?1S08DFB0P:@^RTP:P@P^P}\^\1R[P7P^PSP4PVDFP7P^P4PQPVP>E8P4PSPVO2S01[[^B^^F1]G^@1S06XOTP7P^PS1:^4PVDFP7P^P41:^QPVP>E8Q04P7P^1<4NRy1:^R90T4A0^4NPPPRPYO2[\yS07[[PD1<>cS0;1:^>R|1:^YS0B50T1<ScRlA0^ScRh1<QPS0CPD1<58S05PL1:^MRk1:^0Rn50T1<>LA0^cLP6P0PEO2]3S0<]5S0?]2X111:^5RZ1:^E50TPTP^Q00P:P@P^P^PDPDPNn3000110500021010420107108XHTPkPnPDEgA0^M0A0^g6PDA0^cJP^P?1<?6RnA0^>6PAP?PJO2]3]5X:^1<J0PDPnPJA0^KJRnPFPAP?O2]3X11A0^F6PDPnP^P?PKPFPAO2X:^P1PAP7P^PD1:^eRnPKDFP7P^P>1:^_PKPFE8PePHPKO2];]<X@1P7P^PA1:^HPFDFP7P^PFPnPFPAE8P^PFP7P^PH1:^DPHPKE8P7P^PeP|P_DFP`P_PeO2]<];XJ^P7P^PK1:^FPKPFE8P7P^PH1:^KRnPeDFPDW<W;P_PSPDP>GuW;W<PKPSPJP6GuPHPDETb7W3PAPDDZb3W2PNPDETb3W5PDO1b5W2PMPDDZb2W0PSPVP>PDO4W3W5W2W0X]^X=1P>PDO2PT^P@R<P7PQP4PVCOS0=P7P^AL5QSP4PSO1PVP>E8S0A1<MAS09A@^M5RI=0Tn1<QAS03A0^QAS0D1<YeS0EPD1<R_S0FP`A@^PRR_1:^iS0G50T1<Y`S0HA0^Y`RnP7PSPEP8COP7P^AL40LPEPLO1S0IP8PPE8PWPmPaO2S0J]2]0]9]7S0K]3X11A@^RYS0L1:^b50TPTP_Q00P:P@P^P}PDg02OCRbQ02n3000110500021010420107108XNTg02O`S0MQ0GPDEAPbQ0HP7PmPEP8COP7P^ALW0LQ0IP8PPE8Q0J]2]0^9n]700;Db0W3PPPDDZb0W5PSPVP>PDPQP4O6W9W7W3W5W2W0X]^X?1XE@WIXH:X=1PMP5PQP4PSPVP>PDO8n200510010510B10100000022110210481102107108106103104000000Q0B90TSPRPYPNO2\h\lS0B[\lX:^X11XCTX11PQPZPSPVO4PD1P15S0H1PTk1P14S0J1P^SRNO4b0W;W<XB^XF1XG[X@1XJ^PT\@RYP7P^PSPQP4O1PVDFP7P^P4P5PQO1PVP>E8Q01[[^B^^F1^G[^@1\@P7P^PSA@^5QPVDFP7P^P4PIPVP>E8Q04P7P^A@^8PRn90T4Q07[\yPDQ0;A0T|_Q0CPDQ05PLA@^J6R|90TkQ0?]2X11A@^6090TZPTPkQ00P:P@P^P}PDQ02Pbn3000110500021010420107108XNTQ0MP|PDEAPb1<0LQ0<]500;Db5W2PMPDDZb2W0PSPVP>PDO4X3hX5lW2W0XJ^X=1P>PDO2Q0=Q0AQ09A@^eH90TIQ03Q0DQ0EPDQ0FP`A@^maRI90T_Q0K]3X11Q0LA@^ai50TPTPYQ00P:P@P^PYPDP8PDn3000110500021010420107108X\TP_PIPDEgA0YRaPTP:Q00P:P@P^P:PDPEP>n3000110500021010420107108X\TPnA@^WmP>EgA0:8WA0:LpPDA0:ErP:Q0@Q0@90Y0RL1<EWR8A0^EWP7PoPSPJCOP7P^ALq4?PAP?O1PJP6E8PqPoQ0@O2]2]0]9]7[XH:A0YErPDPLPYPo1<0pRYA0^0pRpP7PqPuP?COP7P^ALtwAPSPAO1P?PJE8PtPqPoO2]2]0]9]7XC<PDPYPrA0^6rRrP7PtPwPACORAP7P^ALvxFRYPwPFO1RLPVP?E8PvPtPqO2]2]0]9X11PDPrP^Q0@P7PvPxPFCOP7P^ALuzKPxPKO1PtP>E8PuPvPtO2Rt]2]0X:^P7P^PYPLPqPoE8PO20:uzP7PwPBPDCOP7P^ALx]>PBP>O1PwDF[^E@PtPo20:x]P7PBP{PDCOP7P^AL]d>P{P>O1PBDF[^E@P]P`ALB{`PzPxPwPDP`PQO2P4O7WmWUP>PDO2n2001000000120000000WiX3APJPDETb3X9pP6PDDZb3X78P6PDETb7W2P0PDETb2W0PDO1b0PDO1b0W3PPPDDZb0W5PSPVP>PDPQP4O6W9W7W3W5W2W0XJ^X?1XE@XI<XN:X=1PMP5PQP4PSPVP>PDO8n200510010510B10100000022010210481102107108106103104000000A0TS_Q0B[\lX:^X11XCTX11PQA@^gMPSPVO4PDQ0HA@^cg,PTQ0JPNO4b0W;W<XB^XF1XG[X@1WoY0?XH:PDK0oWOQ06^OTPDA\7;\Q0>Q08PjAQU3~R3P>P=O7Q08PjP3O2P9%1\1mjDXA9PD%1;PsEAbvbhbcCaCaCaCaCaW{WUP>PDO2n2001000000121000000W0WlP>PDO2n2001000000121000000W0WjP>PDO2n2001000000121000000W0WxP>PDO2n2001000000121000000c0<bkbdbzbMbMbMbRbRWtWqP>PDO2n2001000000121000000W0WgP>PDO2n2001000000121000000W0XuCP>PDO2n2001000000121109000W0X^XP>PDO2n2001000000121109000W0Z0@fP>PDO2n2001000000121109000bCbQbQWsWpP>PDO2n2001000000121000000W0WfP>PDO2n2001000000121000000W0X4CP>PDO2n2001000000121109000W0X6XP>PDO2n2001000000121109000W0XDfP>PDO2n2001000000121109000bCbebbb_WKW`WyWwWnWaXS@WTXI2XY@X:GX[fX?1X>@X=1XZfPcPgPMP5PQP4PSPVP>PDO:XS@WTXI2XY@X:GX[fX?1X>@X=1XZfo"). Qed.

Theorem reach_free cs L c0 L' cs' u k SZ SZ' K n0 :
  creach cs L -> In (c0, n0) SZ -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  cpathw unmap_len L (cfree cs (Some c0)) L' cs' u k -> (forall e, In e SZ' -> In e SZ) ->
  creach cs' (set_live (ap_remove c0 (ld_live L')) L') /\ ld_live L' = ld_live L
  /\ RES cs' SZ' K /\ Phi cs' = Phi cs - u /\ Psi cs' = Psi cs - Z.of_nat k.
Proof.
ltac2:(KReplay.run1 (kr_t_HnReach ()) ["HMREACH"] "p'0h02LSh11Hh22BLh31mh41bh51nh62sth72FRh83cs'h91lh:3offh;1uh<1xi001xh=1Ah>1Bh?2Hch@5INVC0hA5INVC1hB1KhC1LhD2L'hE2SZhF3SZ'hG2c0hH2cshI1ehJ1fhK1khL2n0hM1shN1yhO3BL'hP2CPhQ3CPWhR2CRhS3CR'hT2ELhU3EsthV4Est'hW3HinhX2HkhY3INVhZ4INV'h[4LIVEh\5LIVE'h]3LS'h^2PHh_2PSh`1Rha2R'hb3SUBhc3SZPhd2_Hhe1ahf2n1hg2nuhh3st'hi1zp&0p;2p;1p;3p;4p;9p;:p;6p;5p;7p;;p;>p;Cp-1R0p10000p4p710R1p8P0g01^RR2p4p710R3p8P0P2p4p7210R0p8p1000nR4p4p710R5g0020R6p4p710R7p8P5p1002Lp4p710R8p8P5p1002jp4p7210R9p8P5p1003Gp4p710R:p8P4p4p7210R4P7p8P4P8p8P4P9p8P4P:p8p1003ep4p70P:p8g004UR4p4p70R;g01^oR<p4p710R=p8P;g005lR>p4p710R?p8P;P5p8P;g006HR5p4p710R@p8P;P>p4p7210RAp8P;P7p8P;p10073p4p73110RBp8P;p10087RCp4p710RDp8P;P8p8P;P9p8P;p1008kREp60621002RFp8P;p100:2RGp4p7210RHp8P;p100:jp4p710RIp8P;P:p8P;P3p8P;g00;gRJp4p7210RKp8P;p100<jp4p710RLp8P;g00=JRMp4p7210RNp8P;p100>Sp4p7210ROp8P;g00?UR;p4p7210RPp8PCp4p7211P7p8g00@[RQp4p70RRP7p8PRPBp8PRPDp8PRP8p8PRP9p8PRPFp8PRPHp8PRPIp8PRP:p8PRP3p8PRPKp8PRPNp8PRPOp8PRPPp8PFPDp8PFPHp8PFP0p8PFp100A[p4p741110RDp8PFp100BQp4p741110RRp8PFp100CLRSp4p7210RTp8PFPSp4p73110RSp8PFp100DXp4p7210RUp8PFp100Edp4p710RFp8p100F[p4p710RVp100G9RWp4p710RXp8PVPWp4p7210RWp8PEp606311001REp100GRp4p7210RYp8PEp100HIp4p73110RZp8p100IAR[p606311002R\PCp4p7210RCp8P\PHp8P\P3p8P\PZp8P\PDp8P\PRp8P\PTp8P\PFp8g00JIRTp4p70RRP?p8PRPLp8PRg00KHRRp4p710R]p8P[p6064111001R[PCp8P[PGp4p73110RGp8P[P3p8P[PZp8P[PDp8P[PSp8P[PFp8PGPCp8p100Kep4p70P:p8p100LSp606311001RFP:p8PFp100M[p4p7210RSp8PFP3p8PFPZp8PFPUp8p100NRp60621000RUPCp8PUPGp8p100OVp606311001RUPCp8PUPGp8PUPZp8p100P^RUp4p73101RDp100Q8R^p4p73110p8PDp100QQR_p4p73110p8PDp101_ep4p710p8PDp100R@R`p4p7201p8PDp100RRp4p7201p8PDp100RdRap4p73110p8PDp100S8Rbp4p73110p8PDp100SLRcp4p73110p8PDp100Sfp4p7201p8PUp4p710RdP^p4p710p8PdP_p4p710p8PdPXp8PdPWp8PdPap4p710p8PdPbp4p710p8PdPcp4p710p8p100T9p606311001RcPCp8PcPGp8PcPZp8p100UAp60621000RcPCp8PcPGp8p100VERcp60621001RdPYp8PdPHp8Pcp606311000RcPCp8PcPGp8p100WKp4p7=1111111111100P7p8p100Wep6061001RcP1p8Pcp100Y2p4p710Rdp8Pcp100YOp4p710p8p100Ylp6061000Rcp100[9p4p710p8PcPLp8PcPdp8p100[VRdp4p710RcPVp8PcPXp8PcPWp8Pcp100[jp4p73110p8p100\<p6061001RcP1p8Pcp101`8p4p710Rcp8Pdp4p741110RdPDp8Pdp101`TRDp4p73101p8p100^>p6061000R1PLp8P1Pcp8P1p100_Hp4p710p8p100_hp4p711p102P<p4p73101p8g00`kR1p4p7210PIp8p100alRcp60621002RWP\p8PWPHp8PWPFp8PWPSp8PWPZp8Pcp606311001RcPCp8PcP[p8PcPGp8PcPZp8p100c3p606<11111111111004RcPBp8PcPEp8Pcp100d2p4p710RGp8PcP[p8PcPIp8Pcp100dlp4p710RCp8Pcp100enp4p7210RWp8PcPZp8PcPOp8p100fnp6067111111003RcPBp8PcPEp8PcPGp8PcP[p8PcPIp8PcPCp8PcPWp8PcPZp8PcPOp8PDp4p710P:p8p100h2p6067111111003RDPBp8PDPEp8PDPGp8PDP[p8PDPIp8PDPCp8PDPWp8PDPZp8PDPOp8g00i7RDp4p70RZP=p8PZP?p8PZP@p8PZPAp8PZP7p8PZPBp8PZP8p8PZP9p8PZPIp8PZP:p8PZP3p8PZP0p8PZPKp8PZPLp8PZPNp8PZPOp8PZPRp4p7210RRp8PZPPp8p100j7p4p70P:p8p100jmp4p7<111111111110P:p8p100kPp4p741110R:PUp4p7511100RPp8PPP:p8p100kip4p741110R:PUp4p76111100RPp8PPP:p8p100lAp4p741110R:PUp4p771111100RPp8PPP:p8p100lap4p741110R:PUp4p7:1111111100RUp8PUP:p8P`p4p7200R`Pdp8PdP`p8g00m8j2GTg00mXj1QTg01aTj3XTg02=6j4?TP<j36Tg0121j3FTP2j2zj3eTP>j4KTg01bVj10TP5j3jTg02<Tj2VTg02P`j2UTP1l9iTPMm:03Tg01e<k602Tg01hKRMj23Tg02Qaj5}Tg01=@j32Tg01<@j2wTg01LQj4NTg02R@j4qTg02RZj6oTg02SFl9nTP;j7kTg01g?j4aTg010Pj1=Tg012nj15Tg013ij11Tg01hej7hTP6j6PTg0188j1ZTg02THj3{Tg02URj5OTg02VRj4yTg02WQl;xTPJl>vTg01;cj2cTg01loj2]Tg01mFj1tTg01mgj2sTg01nGj1rTg02XUlCpTg027Uj38Tg02YVj2LTg014dRJj24Tg02=Vj2WTg02>Xj6YTg0278j2ATg02@1j6lTg02@mj2~Tg02Akk100Tf3R6f2R;f1R132f0R5'4p=^%05,L1p=m1W159X6;p=g%0592;1p=bPTPDg02G4P5CKp=@%01=2;5p=9g02F0R>f7R2f6R<32f5R`g02H5Rdf4R:P6P;P1EY/45'4p=7g01O>RU%Z5,A172;p=:AF<`:1A;192U6/45'4p=C%01926;/45p=B1L6;/W19X`:/45p=;1A;192U6/45p=TA2<`:AF6;1/45'4p=SA2>15p=\P2PdP<P`P:P6EY%01=2;5'4p=`P`PdP:P6P;P1EY/45p>01P:PdP6P;P1P5EYp=[%51/A5p=DAF2<`A2U:6%Z5,A192U;'4'4p=_P:PdP6P;P1P5Elp=I%01,L;/W5p=<1L;1/W5p=JAX<`:A26;1/45'4p=fA2U:61A1592U;'4p=|PDPUP1P5C?p=R%Z5,A1p=M1~15$00p=>A2;15,46p=EA2U;1/45p=H1A1592U;p=u%51=2U5p=dg02JWRPg01P^RZ1G4URO#QRNp,4RUNpRLf:RKf9R03XP4PUP0P1C?=6O:f<R3?F`6POP41z4URIP<CK%035j4PLP>g02ZYR9f=R8f>RB1V43'Uf;R7PKP0f8RAM9iA6O5AA6O1K[^IOPLP>P9f@R@1V4B'UR?f?R=P8P3P7PKP1N:03PLP>P=P?P8P3J02P4POP4PIPKCK%0@R?P=P6P1\1RW%Q;RCPJP:P6P;P1CK9665P`P:P5O1P;A6<56C^X<`,3`R[[P:P6P5O1P1A6`5;C^X<:,3:P`P:P6P;CK96:1[RGP<P`P:P6CK96`;\[P:P6P;P1P5D}P5n2001000000120000000XN;W9WJX>RX=]PG^N;^9C^JW^>R^=]P5POP4PIP7P@POP4Ae4U5fARIA6O53C^X<OP4PUP@PAC?R]Ae4U]=24@A6O]71w4@P<CNCqO6b1EoA64=?PLfBR]PIP@P=PBP2P5P1M9nPLPB1m@=P=CgPLP>P]fCRO1V4I'UP@P=P;Fk%QDRR?b?]PLfDR?POP0Ca%QTRTg02LQ%Q4[RW%=;RCfGRGPLP;fFR[P1P5%@1RE99R[G7X0W'3X2T'3X6>,3>PMP>PCfHRcPLP;PGP1P5%0GRS=2REG7X0W,3WX2T,3TX6>PLP]P?%0ORFPOPRPFfERFP]PBP8%5]%5[ROPI%1]%1[RH;:@FCCBE;P5PCfJR@PLP;fIR\P1P5%0\RX=2REG7X0W,3WX2T,3TPMPT%=6RVfKRYPLP6P@P1P5A9R@EG7X0W,3WX2TPLP[PcPSPGPRPSPXP[P]PIPO%5@ROPF%1@RX=:H?CTFSE;P5%=`RHfMR?PLP`fLRSP1P5A9RSEG7X0W,3WPMPW%=<RGfNRbPLP<P?P;P5%0?Ra%@;R_52RG7X0WPLP@PS%0YR^PYPRP^PaP@P[PFPO%5bROP\%1bRF=:XcCTFSE;P5%=ARXfPR[PLPAfORaP:P5%0aR^%@:RY52RG7PJ%=0RefQRf'\PLP0P[P`P1PRP[%@`RgG`PLPbP[P^PaPRP^PfPbP@P\POfRRO#5R@P?%1OR^=:FSFCCBE;P5%=7RFfSRa'\PLP3PaPAP:%0aRh%@ARi52RJ01PJPLP8fTRjP0P`D[%@0Rk99RjPLPOPjPhPaPRPhfURhPOPbP?P@fVR@/DfP^%1@P[G_CBE;P5PLP=P@P7P2D[fWR[%@3R^59RPLPdPIfXR?P8P0P1FhPL%=IRbP?P8P0DIP>%=]R]PLP5fZROP=P7DIX3>P5POP<EPPLPOfYRaPBPKDIPLP[A<a??PcCaPCPOPLP;f\Rlf[Rm;<mRnP1P5A9RnEG7X0W,3WX2T,3TX6>,3>PMP>PCPmPLP;f]Rn%0lRo;JlRpP1P5A9RpEG7X0W,3WX2T,3TX6>PLPaPm%0ORpPOPRPpPoPaPhPj%5a%5nRhP?%1a%1nRo;:[CTFSE;P5PCPnPLP;f_RCf^Rp#0Rq;JpRrP1P5A9RrEG7X0W,3WX2T,3TPMPTPVPpPLP6f`RV?<CCRsP1P5A9RsEG7X0W,3WX2TPLPnPrPRPq%0VPnPaP?PhfaRh#5R?Pl%1hRq=:omFCFfP5PHPVPLP`fbRH?<hhRoP1P5A9RoEG7X0W,3WPMPWPGPhPLP<fcRG%0HRo;JHRHP;P5A9RH_G7X0WPLPhPHPRPofdRo#0RHPhPnPlP?feR?#5R_PV%1?RE=:qCFCFfP5PXPGPLPAAJ?HoRHP:P5A9RHYG7PJ1\eoPLP0ffRe?<??RHP`P1PRPHPgG`PLP?fgRg%0eRHPePRPHfhRH#0RYP?PhPVP_fiR_#5RhPo%1_RX=:EGCTFSE;P51\FePLP3AJ_YHRYPAP:PRPYPiG`PJPLP8fjRi?<__RYP0P`D[A9RYkPLP_fkRY%0iRkPiPRPkflRk#0RiP_P?PoPhfmRh/DHPX%1h%ZgD|FSE;P5PLP=A<kYYP7P2D[AJhik=9R^PLPdPIfnRI?<hhRdP8P0P1FhPLPbPdP8P0DIP>P]PLP5fpR]foRd;<dP=P7DIX3>P5PhP<EPPLPhA<dIIPBPKDIPRfqRB#0A64B5X9RPV%@@R@P\EPA64]@A{B[51GDURD/GUR[PDPUfsR@/R1P5C?;6aX5U,3UX:U,3UPMPUPDPUftRa/R1P5C?=6[OX5U,3UX:UPLPBP@frRO#0R\POPRP\PaPBPhPk%5BfuRk#5R\P]%1B%1kRI;:dFCCBE;P5PDPUfvR7/R1P5C?=6[lX5U,3UPMPUPDPUfwRM/R;P5C?=6[nX5UPLPkPM%07R=P7PRP=fxR=PkPBP]P\fyR\/DaPI%1\P@G_CBE;P5PDPU1R\:P5C?=6[CPLP>P9f|R9fzR[,V4'Uf{RDP\P=PMP7Phg01O\Rhg01Q=RIp+01@RaPCP5P;P1DOX8>XgZX;UR]PLP9PDPVPlP[P`P1PfP9PkP@PdCyP5M;xM>vP]1chM1]I7P=O3PU1ch=f~RhPpP[P51]I=DOXiUP5P=%t=EPf}R]PnP\P=1]IMDOPZ1sI=PaPCPDP[P5DOX5ZP5P=%r=EPPhPpP[P\P=DOPLPaPhPGPCPDP[P\A<]99PSPcP=PMP7PjPOP5P8PdMCpPDPMP7%5D%5aR7P[%1D%1aRd/M\A8]15p+01CR8?8;11GQU/GU/GU/GURQ1>h11>81ROCE[^34^443HFCPJAF9=M%59p+01ARM#5RjPD%19%1MRc/M[A8h15p+01DRS?8;1PQ1>a11>S1RCCE[^34^443HCTPLP]Pa%0hRGPhPRPGPMP]P\P=%5]p+01BRG#5RpP9%1]%1GRI;:DFCCBE;P5AFh[\1DSh%1SR[/M]A8G15p+01GRD?8;1PQPO1>D1ROCE[^34^445Hd5H7PJp+01ER7#5=uja%17Rj/MhA8815p+01HRh?8;1PQPC1>h1RCCE[^34^445HcPLPGPS%08RcP8PRPcP7PGP]P9Ppp+01FRp#5R9PM%1pR]=:IaFCCBE;P51DDG,d8%1h/MGA8p15p+01KRI?8;1PQPO1>I1ROCE[^34^445H[PJp+01IRJ#1R[=:j8A8D15p+01LRj?8;1PQPC1>j1CE[^34^44PLPpPh%0DRCPDPRPCPJPpPGPMP9p+01JR9/D7P]%19PSG_CBE;P5%1D%1I;:7A8915p+01OR]?8;1PQPO1>]1CE[^34^44PLPJ%09RL,LIP9CgAbRLjRLAFJ7SR7p+01MRS/Dh,dJRJ%1S=:[DR['4RD'4RS'4P\PLPSP=P7PDP0PJP[P`P1CNCNCNCNWdW_P1P5O2n2001000000120000000W1W^P1P5O2n2001000000121000000W1WaP1P5O2n2001000000121000000beb7b7b7WXXfUP1P5O2n2001000000121100000W1X:UP1P5O2n2001000000121100000bIb?bAbAW\WZP1P5O2n2001000000121000000W1WVP1P5O2n2001000000121000000W1X]WP1P5O2n2001000000121100000W1XOTP1P5O2n2001000000121100000W1Xh>P1P5O2n2001000000121100000bMb@b@W[WYP1P5O2n2001000000121000000W1WUP1P5O2n2001000000121000000W1X0WP1P5O2n2001000000121100000W1X2TP1P5O2n2001000000121100000W1X6>P1P5O2n2001000000121100000bMbTbSb?bPWbWQWcW`WWWRXLUXBUXFNXENXKZX;UX8>XDPXG4XCPXH>PKP0PAP2P<P`P:P6P;P1P5O;XLUXBUXFNWEWKX;UX8>XDPXG4WCXH>o"). Qed.

(* [comment removed for export] *)
Theorem reach_bounds cs L SZ K :
  creach cs L -> RES cs SZ K -> Permutation (map fst SZ) (ld_live L) ->
  Phi cs <= zsum (map (fun e => csz (snd e)) SZ) + 32 * 2 ^ 20 + PGSZ * (6 * NAMAX K + 8)
  /\ Psi cs <= Z.of_nat (length SZ) + 32 + 4 * NAMAX K
  /\ pot cs <= NSLOTS * (2 + 2 * NAMAX K)
  /\ 0 <= nareas cs <= NAMAX K.
Proof.
ltac2:(KReplay.run1 (kr_t_HnReach ()) ["HMREACH"] "p'0h04__x1h16__sat2h24__x2h32LSh47__arithh54__ffh68__varmaph75__with84__x3h94cstrh:5cstr0h;2BLh<4LEN0h=6__sat1h>1Hh?4__x4h@1EhA1nhB2sthC2HahD5INVC0hE1KhF1LhG2PShH2SZhI6__sat3hJ2cshK2CRhL2E0hM3EsthN3INVhO3LENhP4LIVEhQ2NAhR3NA0hS2PHhT2PThU1RhV3SZPhW4SZP'hX5cstr1hY1ehZ1lh[1mh\1sh]1xi001xh^1yp%0p&0p;2p;1p;3p;4p;7p;6p;9p;;p;:p;<p;8p-1R0p10000p4p710R1p8P0g01^RR2p4p710R3p8P0P2p4p7210R0p8p1000nR4p4p710R5g0020R6p4p710R7p8P5p1002Lp4p710R8p8P5p1002jp4p7210R9p8P5p1003Gp4p710R:p8P4p4p7210R4P7p8P4P8p8P4P9p8P4P:p8p1003ep4p70P:p8g004UR4p4p70R;p1005Up4p710R<p8P;g005lR=p4p710R>p8P;P5p8P;g006HR5p4p710R?p8P;P=p4p7210R@p8P;P7p8P;p10073p4p73110RAp8P;p10087RBp4p710RCp8P;P8p8P;P9p8P;p1008kRDp60621002REp8P;p100:2RFp4p7210RGp8P;p100:jp4p710RHp8P;P:p8P;P3p8P;p100;gp4p7210RIp8P;g00<jRJp4p710RKp8P;p100=Jp4p7210RLp8P;p100>Sp4p7210RMp8P;p100?Up4p7210R;p8PBp4p7211P7p8p100@[p4p70RNP7p8PNPAp8PNPCp8PNP8p8PNP9p8PNPEp8PNPGp8PNPHp8PNP:p8PNP3p8PNPIp8PNPLp8PNPMp8PNP;p8PEPCp8PEPGp8PEP0p8PEp100A[p4p741110RCp8PEp100BQp4p741110RNp8PEp100CLROp4p7210RPp8PEPOp4p73110ROp8PEp100DXp4p7210RQp8PEp100Edp4p710REp8p100F[p4p710RRp100G9RSp4p710RTp8PRPSp4p7210RSp8PDp606311001RDp100GRp4p7210RUp8PDp100HIp4p73110RVp8p100IARWp606311002RXPBp4p7210RBp8PXPGp8PXP3p8PXPVp8PXPCp8PXPNp8PXPPp8PXPEp8g00JIRPp4p70RNP>p8PNPKp8PNg01_FRNp4p710p8PWp6064111001RWPBp8PWPFp4p73110RFp8PWP3p8PWPVp8PWPCp8PWPOp8PWPEp8PFPBp8p100Kep4p70P:p8p100LSp606311001REP:p8PEp100M[p4p7210ROp8PEP3p8PEPVp8PEPQp8p100NRp60621000RQPBp8PQPFp8p100OVp606311001RQPBp8PQPFp8PQPVp8p100P^RQp4p73101RCp100Q8RYp4p73110p8PCp100QQRZp4p73110p8PCp101_ep4p710p8PCp100R@R[p4p7201p8PCp100RRp4p7201p8PCp100RdR\p4p73110p8PCp100S8R]p4p73110p8PCp100SLR^p4p73110p8PCp100Sfp4p7201p8PQp4p710R_PYp4p710p8P_PZp4p710p8P_PTp8P_PSp8P_P\p4p710p8P_P]p4p710p8P_P^p4p710p8p100T9p606311001R^PBp8P^PFp8P^PVp8p100UAp60621000R^PBp8P^PFp8p100VER^p60621001R_PUp8P_PGp8P^p606311000R^PBp8P^PFp8p100WKp4p7=1111111111100P7p8p100Wep6061001R^P1p8P^p100Y2p4p710R_p8P^p100YOp4p710p8p100Ylp6061000R^p100[9p4p710p8P^PKp8P^P_p8g00[VR_p4p710R^PRp8P^PTp8P^PSp8P^p100[jp4p73110p8p100\<p6061001R^P1p8P^p101`8p4p710R^p8P_p4p741110R1PCp8P1p101`TRCp4p73101p8p100^>p6061000RSPKp8PSP^p8PSp100_Hp4p710p8g00_hRSp4p711g01a0R^p4p73101p8p100`kp4p7210PHp8p100alRTp60621002RRPXp8PRPGp8PRPEp8PRPOp8PRPVp8PTp606311001RTPBp8PTPWp8PTPFp8PTPVp8p100c3p606<11111111111004RTPAp8PTPDp8PTp100d2p4p710RFp8PTPWp8PTPHp8PTp100dlp4p710RBp8PTp100enp4p7210RRp8PTPVp8PTPMp8p100fnp6067111111003RTPAp8PTPDp8PTPFp8PTPWp8PTPHp8PTPBp8PTPRp8PTPVp8PTPMp8PCp4p710P:p8p100h2p6067111111003RCPAp8PCPDp8PCPFp8PCPWp8PCPHp8PCPBp8PCPRp8PCPVp8PCPMp8g00i7RCp4p70RVP<p8PVP>p8PVP?p8PVP@p8PVP7p8PVPAp8PVP8p8PVP9p8PVPHp8PVP:p8PVP3p8PVP0p8PVPIp8PVPKp8PVPLp8PVPMp8PVPNp4p7210p8PVP;p8p100j7p4p70P:p8p100jmp4p7<111111111110P:p8p100kPp4p741110R:PQp4p7511100R;p8P;P:p8p100kip4p741110R:PQp4p76111100R;p8P;P:p8p100lAp4p741110R:PQp4p771111100R;p8P;P:p8g00laR:p4p741110R;PQp4p7:1111111100RQp8PQP;p8P[p4p7200R[P1p8P1P[p8g00m8k20_Tg00mXj1]Tg01aTk30MTg0121k309TP2k20^TP=j4OTg01bVj1iTP5j3gTg01g?k40FTg010Pj1ETg01hKR5j2HTg012nj1MTg000Qk30TTg02[[k10STg018Xj1:Tg019=j1ATg02\Vj1cTg02];k20ITg01;Fj24Tg02]Xj1ITg013ij1FTPJj21Tg0188RJj10Tg02^Vj1KTg02_Nj15Tg01hek70]Tg02@1j6kTP6j6\Tg02`Lm90WTg00n8j22Tg02VRj4}Tg02aMj4|Tg01jfj4zTg02bKm;0VTg02cLm:0UTg01;cj23Tg02dMk70RTg02eNk40QTPNj4tTg01=@j1sj3ZTg01oJk20OTg01omk30NTg01<@j2WTg020Jj4fTg0211j1[Tg02f>k20LTg02ffj2rTg02gBk30KTg02gfk20JTg02hGk10HTg02hek20GTg01nkj1pTg021Vj2eTg02iFk30ETg022hj2bTg011Qk10DTg023Tj3_Tg0244j2aTg01?Fk10ATg024Rj4^Tg01?dk10>Tg01@Bk10=Tg0250j2`Tg01B3j4dTg025Sk10<Tg01CAk20;Tg01Cck20:Tg01DOk308Tg01Dnk407Tg01E`k406Tg019[k40?Tg01:9k60@TP_k405TP:k40BTg01:Zk40CTg01KNj1nTg01;4j3qTg01@mj2wTg014dR:j2>Tg02ioj2mTg02jXj3lTg02kAk104Tg02k_k303Tg02lBk202Tg00`Gk70PTg01LQj4jTg02>Xj6~Tg017<j1{Tg01>8m<0\Tg022?k30[Tg01NZk700TP^k80XTg01B^k30YTg01APk30ZTg02F0R^f1R_f0RN3Zp=Jf4R6g02H5R=f3R2f2R[P_PNE~p=GPPPCg02G4R1PNCOp=9%i_=Z[Np=;1>_N,>[p=UP[g01O>R;P_PNCO#{p=R%:N#:p==14[_/3Np=Dg01]R/4Np=P14_N,3[p=8g02ln/4Np=Qg01O\RQ/2[12_N'>p=L12[_/>Np=Y132[/3_,26/>Np=<f5RVP=P6P2P[P_E~/>Np=vP6P;P2P[CO#{/3_/3Np=y%M_/2Np=x11PNp=S14_N,3[,22p=N%K_/2Np=ug01P^RM?Z_Np=BAZ;_Np=XPMP;PNPJP_P[P2P6PVf6RJf7RLf8RKN<0\p=h12QNp=7B0[;_Np=TP_PSg01Q\RIPIg01R<R0PNg01R\R3K00p=oP2PSPIPIP0P[P_PNL0Xp=CP[PSPIPIP0P;P_g02N@PNCdP3K00p=@1w;Np=VB0Y;_Np=6B0Z;_Np=?126212[_/>N'>p>01g02JWS0020_4;R3#]RHQ00p,4RUNpR9@0M2[B096[_P3P420^4;R8P2CO%i65g4P9PJPVP[H0F%]PRAg02LQ%]4[R7%E[R@f9R?'JP9P[PKP_PNDG%]CR>%9_R<7;K3UX37'HX;A'HXB^,H^P5P^f:RR,J@P9P[P?P_PNDGA;>?<3UX37,H7X;A,HAXB^%MKB0T4;N$0SXY3RB=R3Jg01U]RW#:RF#:RD#:RT#=RO#ARE%AFRG%cF#=RX#ARU+0IR]'4R\%cWRZ#:RY#AR`%IVRa%ATRT3D#P%FK113J#0PE%ADRb/4a%KKA8GGa#Q%5KRc?Lca3YD<D<PNf<Rc,J@P9P[f;R@P_PNDGA;>@<3UX37,H7X;A,HAP5PA%E2f=Ra'JP9P2PcP_PNDGA;>c<3UX37,H7X;A%McAR3BRP\%I?Rd=D`T#P%Fc113R#0PE14bd%KcA8GGd#Q%5cRe?Led3YD<D<PN%EVf?Re'JP9PVf>RdP_PNDGA;>d<3UX37,H7P5P7%EJf@R5'JP9PJPeP[PNDG%9[9;>e3UX37%M5AR3BdP\%IaR<=D`T#P%F5113d#0PE14b<%K5A8GG<#Q%55Rf?Lf<3YD<D<PN%EKfBRf'JP9PKfAR<P6PNDG%969;><3UP:%E?fCRg'JP9P?PfPVP_%9V9;>fEvfDRh#MAR3BfP\%I<Ri=D`T#P%Fh113f#0PE14bi%KhA8GGi#Q%5hRj?Lji3YD<D<PN%E@fERj'JP9PcPjPKP6%9K9;>jEvP:P9PafFR:P?PVDG%9?9;>:fHRV#MAR3B:P\%IjRi=D`T#P%FV113:#0PE14bi%KVA8GGi#Q%5VRk?Lki3YD<D<PNP9PePVP@PLDGfIRV%9c5;>P9P=P<fJRkPaP?P_K0]P9P=%E<PkPaP?EkP^%EfP9P=PNfLR?PeP@EkX[^PNP?PJE\P9P=P?fKR=PdPREkP>%i?P3P4P8P?CO=g4NXZ>fGR>%9eR@P[E\P3P4P8P=CO=g4@P9fNR@fMRiP5PcP?P=P_PVN90W%5@%I='2P9fOR5P@P<PaPiP[P5PiP?PkC}P5PiP?PkC|P_P5PiP?PkCzN;0VP3PBPiP\%55=D`T#PDy,x5P9fPRkP5PfPdP@P2PkP@PiP=C}PkP@PiP=C|P[N:0U%Fk%Sf#0/3EPb%5kCNP9fQR9PkPgPeP6P9P5P@P?CzK0R%5998GG#Q,u9P4P3P4P8PkCOR?%9hR5P6H0Q114?1145'BPMP3P4P8P9CO,14%9:R5,14,BNXAMPN1139R?P3P4P8P9CtE\%9j,14,B?PM11C5fSR5,13R8/BNXAMPN%S:RePPPCP1P:CtE\fRR:,13R1/Be%S>R>/B8S01%0>RC%08RP'XRg%sMRf%s;R=%0_%0NRi'X1B_N20O_N40NX^MX]MRdP>PC1W;CR<P8PP1W;PRlM9hS021B8>1XPCRmPfP=PdP8PPPlP>PCP<M9hPNCfPmfTRm,13R<#[Rl%0<#7R<%SVRV#[R8%0V#7RV20LGURn1rQGRo%7U1rQ][Rp[Rq%7GRrg02NgRsB0KGU_UWCRU%7]\s^CrRrP_g02n020JQG'WPoeO1RoPpg01Y2Rs&0HW-0G;g01Q=R]#pRt,e;Ru60E;1e;]R]'Tg02MTRv'b&0DsRw3_%]sRxP;1a;[S03P_&0A;S04C^S05&0>;Ry&0=;RzP;1`;FRFg01Y^R{1`;WRWCd,oz&0<IR|P;PWP{PFCd,ozCC20;z0R{PNP[g01ZER}g01ZeR~'W20:N[=Z}~dB08;Q_H07R~b5b6b7X0;X2;1X_N1X_[[^0;^2;PNfZR},13#0S06%S@#0PJO3b4b1b=b1b:b9bLH06b@b@b@%Sh113k'B%SjRj/B?%0jRk%0?Rh'XRJPfP=PdPjPk1W;kP?Ph1W;hM9hPNCfPJ%[1%01RJ#7%[>%7CP4g01S<RCg01VBR>P;g01V[RhH0?R?PCP>g01W4P;Phg01WRJ0@Rhg01X0R>H05RCP4P>PCP4P?PhP>H0BH0CR>fV#n3qRh#[%0h#7PnPqPUPrPoPpPwPx1a;_PyPz1w;Q=@zWRQP|PQCCP{P~b5b6b7X0;%7NRh%7_[^0;PNf[#n9qC>#0P6O2b4bIb1bIbXb:b9b<%55#7R>eP>PMPefURe#FR>13iEPb%5eRiCNXAMP2P1P_E\%FmR113JERJPb%5mRMCNP3PBP5P\%:O#=#=#=#ARO%I:R5=D`T'4Dy,xeP>13PEPbP5CNRP%:YRY#c#:#cR>#ARCA8GG5'4,ueReALii5R5'>Ri'>Q01PgQ02P[CfR?PgPlP<P8PVPnPqPUPrPoPp%pt,e;Rt%:Y#=#=#=#=#=#A,m;=l;u/T]'T/bv=_swPxP;P;1a;6P[Q04C^P_1a;2RYC^R4PyPz%VERk%VGRj&04X603;'6,?FRX%VORd%V`R=1`;DRD'6%VTRf'?'6'?9@zWP|Pz1`;ZRZ9@zDR@P|16=Z/?f,6d,?X9@zWCCCCP{P~b5b6b7X0;X2;X8;X?;PN13_\POAD`2TCN1262RXP[132\POAD`6TCN[[^0;^2;^8;^?;PNf\RO#5RdfY#IRfAR3B}%MOPcPaO6b4b1b=b1b:b9b<PPPiP?PgPlP<P8PVPnPqPUPrPoPp1Tt]1T]t/bv+02=_swPxP4PyPz1?FkRk%VbR4/6D'?9@zWP|PzP@P|164Z,?k9@zWCCCCP{P~b5b6b7X0;X2;X8;X?;PN13_EPbP2CNP[132EPbP6CN\X[^0;^2;^8;^?;PNPdPfQ06%FOPLPaO6b4b1b=b1b:b9b<PeP5P?PgPlP<P8PVPnPqPUPrPoPp%:>#A,m;=l;u/T],Tt/bv=_swPxP;Q03P_PYC^PyPz%VCRY16jZ,?j'69@zWP|PzA@zZFP|16jF,?j,6Y9@zWCCCCP{P~b5b6b7X0;X2;X8;A8GG[,4C,2N122[A8GG2,4C,2[[[^0;^2;^8;PNPdPf%KOPRPaO5b4b1b=b1b:b9b<P?PgPlP<P8PVPnPqPUPrPoPpPwPxQ05PyPzPQP|PzA@zWFRWP|PzPSPIPIP0PQPWK0PCCCCP{P~b5b6b7X0;X2;12_[AL[[2[\h^0;^2;PNPfPdPKPaO4b4b1b=b1b:b9b<CjCjCjbG%MmAR3B:P\%I9R9=D`T#PP1A8Jb9%KmA8GG9#QALMM9I01D<ebRbObTbGbSbQbWbDbDWPWNP_PNO2n2001000000121000000W>WMP_PNO2n2001000000121000000W>X37P_PNO2n2001000000121100000W>X;AP_PNO2n2001000000121100000W>XB^P_PNO2n2001000000121100000b\WVWUWKXE;XHHWFXJ^P2P[P_PNO4XE;WHWFXJ^o"). Qed.

End HMREACH.

End HnReach.
