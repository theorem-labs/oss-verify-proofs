(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape AsanCeil BackingAlgebra.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS Nodes NodesA NodesA_mm NodesA_madv.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import FrmExec FrmRun RT_iface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma frmW_intro : forall (Pm : machine_state -> Prop) ms, Pm ms -> FP.frm0 (ms_fcsr ms) -> frmW Pm ms.
Proof. intros Pm ms H1 H2. exact (conj H1 H2). Qed.

(* [comment removed for export] *)
Lemma nretA_fcsr : forall ms eff, ms_fcsr (nretA ms eff) = ms_fcsr ms.
Proof. intros ms eff. reflexivity. Qed.
Lemma set_mem_fcsr : forall ms m, ms_fcsr (set_mem ms m) = ms_fcsr ms.
Proof. intros ms m. reflexivity. Qed.
Lemma restrict_fcsr : forall H ms, ms_fcsr (restrict H ms) = ms_fcsr ms.
Proof. intros H ms. reflexivity. Qed.

Section Kit.
Variable segs : list Segment.
Variable segtop : Z.

Lemma ASTF_conseq : forall A Pm Pm' PM PM' c,
  AST segtop A (frmW Pm) PM c -> (forall ms, Pm ms -> Pm' ms) -> (forall mo, PM mo -> PM' mo) -> AST segtop A (frmW Pm') PM' c.
Proof.
  intros A Pm Pm' PM PM' c H HP HQ. eapply AST_conseq; [exact H | | exact HQ]. intros ms [H1 H2]. split; [exact (HP ms H1) | exact H2].
Qed.

Lemma ASTF_exI : forall {X} A (Pm : X -> machine_state -> Prop) PM c,
  AST segtop A (frmW (fun ms => exists x, Pm x ms)) PM c -> exists x, AST segtop A (frmW (Pm x)) PM c.
Proof.
  intros X A Pm PM c (H1 & ([x H2] & H2') & H3 & H4). exists x. split; [exact H1|]. split; [split; [exact H2 | exact H2']|].
  split; [exact H3 | exact H4].
Qed.

Lemma ASTF_frm : forall A Pm PM c, AST segtop A (frmW Pm) PM c -> FP.frm0 (ms_fcsr (cfg_ms c)).
Proof. intros A Pm PM [ms mo] (_ & (_ & H) & _ & _). cbn [cfg_ms] in *. rewrite restrict_fcsr in H. exact H. Qed.

Lemma cps_ASTF_ex : forall {X} A (Pm : X -> machine_state -> Prop) PM Q,
  (forall x, cps segs (AST segtop A (frmW (Pm x)) PM) Q) -> cps segs (AST segtop A (frmW (fun ms => exists x, Pm x ms)) PM) Q.
Proof. intros X A Pm PM Q H T c Hc Hk. destruct (ASTF_exI A Pm PM c Hc) as [x Hx]. exact (H x T c Hx Hk). Qed.

Lemma cps_ASTF_pure : forall A Pm PM (phi : Prop) Q,
  (phi -> cps segs (AST segtop A (frmW Pm) PM) Q) -> cps segs (AST segtop A (frmW (fun ms => Pm ms /\ phi)) PM) Q.
Proof.
  intros A Pm PM phi Q H T c (H1 & ([H2 Hphi] & H2') & H3 & H4) Hk. apply (H Hphi T c); [|exact Hk].
  split; [exact H1|]. split; [split; [exact H2 | exact H2']|]. split; [exact H3 | exact H4].
Qed.

Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Hypothesis Hrom : rom_frm_ok segs = true.

(* [comment removed for export] *)
Lemma astf_evt : forall A Pm PM Q, mat_stable PM ->
  (forall ms, Pm ms -> evt segs Q ms) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW Q) PM).
Proof using Hwx Hsegs Hrom.
  intros A Pm PM Q HPM W. apply (ast_evt segs segtop Hwx Hsegs A (frmW Pm) PM (frmW Q) HPM).
  intros ms [HP HF]. exact (evt_frm0 segs Hrom Q ms (W ms HP) HF).
Qed.

(* [comment removed for export] *)
Lemma astf_evt0 : forall A Pm PM Q, mat_stable PM ->
  (forall ms, Pm ms -> FP.frm0 (ms_fcsr ms) -> evt segs Q ms) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW Q) PM).
Proof using Hwx Hsegs Hrom.
  intros A Pm PM Q HPM W. apply (ast_evt segs segtop Hwx Hsegs A (frmW Pm) PM (frmW Q) HPM).
  intros ms [HP HF]. exact (evt_frm0 segs Hrom Q ms (W ms HP HF) HF).
Qed.

(* [comment removed for export] *)
Lemma ast_read_file_f : forall A Pm PM K KM fd buf count p off data,
  3 <= fd < 2^32 -> 0 < count <= 0x7ffff000 -> buf + count <= 0x800000000000 -> mat_stable KM ->
  let bs := file_read data off (Z_to_bv 64 count) in
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 63) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ areg ms 11 = Z_to_bv 64 buf /\ areg ms 12 = Z_to_bv 64 count /\ wr_at segs (ms_mem ms) buf count
                       /\ K (nretA ms (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\ fs_lookup (m_fs mo) p = Some data
                       /\ KM (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo)) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd buf count p off data H1 H2 H3 H4 bs Hm HM.
  apply (ast_read_file segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM fd buf count p off data H1 H2 H3 H4); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4 & X5 & X6).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_read_dir_f : forall A Pm PM K KM fd buf count,
  3 <= fd < 2^32 -> 0 < count <= 0x7ffff000 -> 0 <= buf -> buf + count <= 0x800000000000 -> mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 63) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ areg ms 11 = Z_to_bv 64 buf /\ areg ms 12 = Z_to_bv 64 count
                       /\ K (nretA ms (efferr EISDIR))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir /\ KM mo) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd buf count H1 H2 H3 H4 H5 Hm HM.
  apply (ast_read_dir segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM fd buf count H1 H2 H3 H4 H5); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4 & X5).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_close_f : forall A Pm PM K KM fd,
  3 <= fd < 2^32 -> mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 57) /\ areg ms 10 = Z_to_bv 64 fd
                       /\ K (nretA ms (eff0 (Z_to_bv 64 0)))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) <> None
                       /\ KM (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo)) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd H1 H2 Hm HM.
  apply (ast_close segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM fd H1 H2); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_open_fail_f : forall A Pm PM (Ke : Z -> machine_state -> Prop) KMe path fs,
  mat_stable KMe -> open_ent path fs = None ->
  (forall ms, Pm ms -> open_at segs path ms /\ forall e, 1 <= e <= 4095 -> Ke e (nretA ms (efferr e))) ->
  (forall mo, PM mo -> m_fs mo = fs /\ KMe mo) ->
  cps segs (AST segtop A (frmW Pm) PM) (fun c => exists e, 1 <= e <= 4095 /\ AST segtop A (frmW (Ke e)) KMe c).
Proof using Hwx Hsegs.
  intros A Pm PM Ke KMe path fs H1 H2 Hm HM.
  apply (ast_open_fail segs segtop Hwx Hsegs A (frmW Pm) PM (fun e => frmW (Ke e)) KMe path fs H1 H2); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2). split; [exact X1|].
  intros e He. split; [exact (X2 e He) | rewrite nretA_fcsr; exact HF].
Qed.

Lemma ast_open_br_f : forall A Pm PM (Ke : Z -> machine_state -> Prop) KMe (Ko : word -> machine_state -> Prop)
    (KMo : word -> Model -> Prop) path fs ent,
  mat_stable KMe -> (forall fdw, mat_stable (KMo fdw)) -> open_ent path fs = Some ent ->
  (forall ms, Pm ms -> open_at segs path ms /\ (forall e, 1 <= e <= 4095 -> Ke e (nretA ms (efferr e)))
                       /\ (forall fdw, Ko fdw (nretA ms (eff0 fdw)))) ->
  (forall mo, PM mo -> m_fs mo = fs /\ KMe mo /\ fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None
                       /\ KMo (alloc_fd (m_fds mo)) (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo)) ->
  cps2 segs (AST segtop A (frmW Pm) PM) (fun c => exists e, In e openat_errnos /\ AST segtop A (frmW (Ke e)) KMe c)
                                        (fun c => exists fdw, AST segtop A (frmW (Ko fdw)) (KMo fdw) c).
Proof using Hwx Hsegs.
  intros A Pm PM Ke KMe Ko KMo path fs ent H1 H2 H3 Hm HM.
  apply (ast_open_br segs segtop Hwx Hsegs A (frmW Pm) PM (fun e => frmW (Ke e)) KMe (fun fdw => frmW (Ko fdw)) KMo path fs ent H1 H2 H3);
    [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3). split; [exact X1|]. split.
  - intros e He. split; [exact (X2 e He) | rewrite nretA_fcsr; exact HF].
  - intros fdw. split; [exact (X3 fdw) | rewrite nretA_fcsr; exact HF].
Qed.

Lemma ast_mmap_fixed_commit_f : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 < addr -> addr mod page_size = 0 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0
       /\ K (nretA ms (mkEffect (Z_to_bv 64 addr) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo -> model_ivs_wf mo
       /\ addr + page_round_up_Z len <= alloc_top (m_vmmaps mo)
       /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + overlap_sum (vm_maps (m_vmmaps mo)) addr (addr + page_round_up_Z len) + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_fixed flags50 mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  (forall mo, PM mo -> alloc_top (m_vmmaps mo) <= 2^47) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len H1 H2 H3 Hm HM HT.
  apply (ast_mmap_fixed_commit segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM addr len H1 H2 H3); [|exact HM | exact HT].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_munmap_f : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= TASK_SIZE ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 215) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ K (nretA ms (mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))] [] []))) ->
  (forall mo, PM mo -> model_ivs_wf mo
       /\ map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true
       /\ eager_used mo + overlap_sum (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr)) addr (addr + page_round_up_Z len)
            + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ KM (mdl_munmap mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)))) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len H1 H2 H3 H4 Hm HM.
  apply (ast_munmap segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM addr len H1 H2 H3 H4); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_madvise_dontneed_ms_f : forall A Pm PM K KM addr len,
  0 < len < 2^64 -> 0 <= addr -> addr mod page_size = 0 -> addr + page_round_up_Z len <= 2^47 ->
  (forall p : word, addr <= bv_unsigned p -> bv_unsigned p + 4096 <= addr + page_round_up_Z len -> page_allowedb A p = true) ->
  mat_stable KM ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 233) /\ areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 4
       /\ K (nretA ms (mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo ->
       madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z len)) = true /\ KM mo) ->
  cps segs (AST segtop A (frmW Pm) PM) (AST segtop A (frmW K) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM addr len H1 H2 H3 H4 H5 H6 Hm HM.
  apply (ast_madvise_dontneed_ms segs segtop Hwx Hsegs A (frmW Pm) PM (frmW K) KM addr len H1 H2 H3 H4 H5 H6); [|exact HM].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4 & X5).
  repeat (split; [assumption|]). rewrite nretA_fcsr. exact HF.
Qed.

Lemma ast_mmap_anon_rw_f : forall A Pm PM (G : word -> Prop) (K : word -> machine_state -> Prop) (KM : word -> Model -> Prop) len,
  0 < len < 2^64 ->
  (forall ms, Pm ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 11 = Z_to_bv 64 len
       /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 34 /\ areg ms 15 = Z_to_bv 64 0
       /\ forall a, G a -> K a (nretA ms (mkEffect a [] [(a, Z_to_bv 64 (page_round_up_Z len))]))) ->
  (forall mo, PM mo -> model_ivs_wf mo /\ lazy_in_maps mo
       /\ (exists a : word, (bv_unsigned a mod page_size = 0)%Z /\ (0 < bv_unsigned a)%Z
             /\ (bv_unsigned a + page_round_up_Z len <= alloc_top (m_vmmaps mo))%Z
             /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 (page_round_up_Z len)) = true)
       /\ eager_used mo + page_round_up_Z len + A_bytes A <= vm_limit (m_vmmaps mo)
       /\ forall a, grant_ok34 mo (page_round_up_Z len) a -> G a /\ KM a (mdl_mmap_rw mo a (Z_to_bv 64 (page_round_up_Z len)))) ->
  (forall mo, PM mo -> alloc_top (m_vmmaps mo) <= 2^47) ->
  cps segs (AST segtop A (frmW Pm) PM) (fun c => exists a, G a /\ AST segtop A (frmW (K a)) (KM a) c).
Proof using Hwx Hsegs.
  intros A Pm PM G K KM len H1 Hm HM HT.
  apply (ast_mmap_anon_rw segs segtop Hwx Hsegs A (frmW Pm) PM G (fun a => frmW (K a)) KM len H1); [|exact HM | exact HT].
  intros ms [HP HF]. destruct (Hm ms HP) as (X1 & X2 & X3 & X4 & X5 & X6).
  repeat (split; [assumption|]). intros a Ga. split; [exact (X6 a Ga) | rewrite nretA_fcsr; exact HF].
Qed.

End Kit.
