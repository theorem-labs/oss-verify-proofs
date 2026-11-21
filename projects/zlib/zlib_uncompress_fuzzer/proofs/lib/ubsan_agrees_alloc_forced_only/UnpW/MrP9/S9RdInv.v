(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require ModelAmb PropExec. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require S9ReadBase S9ReadStage.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image InitMem Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require SM09. Import SM09. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import PState. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import KEv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module RB := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S9ReadBase.
Module RS := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S9ReadStage.

(* [comment removed for export] *)
Section SHAPE.
Variables (fd : FdState) (io : IoState) (fsys : FsState) (proc : ProcState) (lim : LimState) (time : TimeState).
(* a worker port727 (): VmState's two new fields, the kernel build and the vDSO run; vm_only keeps both
   (Lib/Nodes ), so the shape keeps them. *)
Variables (kb : KernelBuild) (vd : Vdso.VdsoRun).

Definition mo_shape (V : VmMaps) : Model := mkModelOf fd (mkVmState V [] [] kb vd) io fsys proc lim time.
Definition G_shape : PState -> Model -> Prop := fun _ mo => mo = mo_shape (m_vmmaps mo).

Lemma frame_ok_G_shape : frame_ok G_shape.
Proof.
  intros s s' mo mo' _ _ (E1 & E2 & E3 & E4 & E5 & E6 & _ & E8 & EK & _ & EV) HG. unfold G_shape in *.
  assert (L0 : m_vm_lazy mo = [] /\ m_vm_materialized mo = []) by (rewrite HG; split; reflexivity).
  destruct (E8 (proj1 L0) (proj2 L0)) as [L1 L2].
  destruct mo' as [fd' [maps' lazy' mat' kb' vd'] io' fsys' proc' lim' time'].
  unfold m_vm_lazy, m_vm_materialized in L1, L2. cbn in L1, L2, E1, E2, E3, E4, E5, E6, EK, EV. subst lazy' mat'.
  rewrite HG in E1, E2, E3, E4, E5, E6, EK, EV. cbn in E1, E2, E3, E4, E5, E6, EK, EV. subst. reflexivity.
Qed.
End SHAPE.

Section RD.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word).

Definition G_rd (off : Z) : PState -> Model -> Prop := fun _ mo => mo = RS.modelG path stdin0 fs0 tid off (m_vmmaps mo).
Definition G_post : PState -> Model -> Prop := fun _ mo => mo = RB.model_post (m_vmmaps mo) stdin0 fs0 tid.

Lemma frame_ok_G_rd : forall off, frame_ok (G_rd off).
Proof. intros off. unfold G_rd, RS.modelG, ModelAmb.mkModelA. apply frame_ok_G_shape. Qed.
Lemma frame_ok_G_post : frame_ok G_post.
Proof. unfold G_post, RB.model_post, ModelAmb.mkModelA. apply frame_ok_G_shape. Qed.

(* [comment removed for export] *)
(* a worker port727 (): a G_rd model's far-end reader is its AmbIn's; minv (Lib/Nodes) reads it. *)
Lemma rdr_of_OWN_rd : forall X off s mo, OWN X (G_rd off) s mo -> ModelAmb.ia_channel_reader stdin0 = true.
Proof.
  intros X off s mo [(L & _ & HKL & _) [_ HG]]. pose proof (minv_reader _ (kl_minv _ _ _ HKL)) as R.
  unfold G_rd in HG. rewrite HG in R. exact R.
Qed.

Hypothesis Hfile : fs_lookup fs0 path <> None.
Hypothesis Htid : 0 < bv_unsigned tid < 2 ^ 22.
Hypothesis Hrdr : ModelAmb.ia_channel_reader stdin0 = true.   (* a worker port727: minv's reader conjunct *)

Lemma minv_modelG : forall off V, sp_window_lo <= bv_unsigned (vm_init_sp V) <= sp_window_hi ->
  minv (RS.modelG path stdin0 fs0 tid off V).
Proof.
  intros off V Hsp. unfold minv.
  change (m_fds (RS.modelG path stdin0 fs0 tid off V)) with
    [(Z_to_bv 64 3, FdFile path (Z_to_bv 64 off)); (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
     (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  change (m_tid (RS.modelG path stdin0 fs0 tid off V)) with (Some tid).
  change (m_fs (RS.modelG path stdin0 fs0 tid off V)) with fs0.
  change (m_vm_lazy (RS.modelG path stdin0 fs0 tid off V)) with (@nil (word * word)).
  change (m_vm_materialized (RS.modelG path stdin0 fs0 tid off V)) with (@nil word).
  change (m_vmmaps (RS.modelG path stdin0 fs0 tid off V)) with V.
  cbn [fd_lookup].
  repeat split; try reflexivity; try lia; try exact Hrdr.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 3) k) eqn:E3; [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off' H.
    destruct (bv_eqb (Z_to_bv 64 3) k); [injection H as <- _; exact Hfile|].
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 3) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. lia.
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. unfold Fork.PID_MAX_ENVELOPE. lia.
Qed.

Lemma minv_model_post : forall V, sp_window_lo <= bv_unsigned (vm_init_sp V) <= sp_window_hi ->
  minv (RB.model_post V stdin0 fs0 tid).
Proof.
  intros V Hsp. unfold minv.
  change (m_fds (RB.model_post V stdin0 fs0 tid)) with
    [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  change (m_tid (RB.model_post V stdin0 fs0 tid)) with (Some tid).
  change (m_vm_lazy (RB.model_post V stdin0 fs0 tid)) with (@nil (word * word)).
  change (m_vm_materialized (RB.model_post V stdin0 fs0 tid)) with (@nil word).
  change (m_vmmaps (RB.model_post V stdin0 fs0 tid)) with V.
  cbn [fd_lookup].
  repeat split; try reflexivity; try (intros; discriminate); try lia; try exact Hrdr.
  - intros k c H.
    destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0. { apply bv_eqb_eq in E0. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1. { apply bv_eqb_eq in E1. subst k. vm_compute. reflexivity. }
    destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2. { apply bv_eqb_eq in E2. subst k. vm_compute. reflexivity. }
    discriminate.
  - intros k p off H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|].
    destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
  - intros k e H.
    destruct (bv_eqb (Z_to_bv 64 0) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 1) k); [inversion H; exact I|].
    destruct (bv_eqb (Z_to_bv 64 2) k); [inversion H; exact I|discriminate].
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. lia.
  - match goal with H : Some _ = Some _ |- _ => injection H as <- end. unfold Fork.PID_MAX_ENVELOPE. lia.
Qed.
End RD.

(* [comment removed for export] *)
Lemma KL_same_vm : forall L b mo mo', KL L b mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> KL L b mo'.
Proof.
  intros L b mo mo' [K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12] E MI Hh.
  constructor; rewrite ?E; assumption.
Qed.

Lemma OWN_same_vm : forall X (G G' : PState -> Model -> Prop) s mo mo',
  OWN X G s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> G' s mo' -> OWN X G' s mo'.
Proof.
  intros X G G' s mo mo' [(L & Hc & HK & Hi) [Hnd _]] E MI Hh HG'.
  split; [|split; [exact Hnd | exact HG']]. exists L. split; [exact Hc|]. split; [|exact Hi].
  eapply KL_same_vm; eassumption.
Qed.

Lemma OWN_weaken : forall X (G G' : PState -> Model -> Prop) s mo, OWN X G s mo -> G' s mo -> OWN X G' s mo.
Proof. intros X G G' s mo [H1 [H2 _]] HG'. split; [exact H1|]. split; [exact H2 | exact HG']. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.PlainS9 Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM15. Import MM15. Import MM15.ProgDeps. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require MM13. Import MM13. Import MM13.MallocBlocks.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MrP9 Require Import S9HBase S9HConv.

(* [comment removed for export] *)
Definition rd_ivs : list (Z * Z) :=
  [(0x21000, 0x21c30); (0x21c38, 0x22e60); (0x22e61, 0x22ea9); (0x32ea9, 0x72ee0); (0x72f14, 0x72f60); (0x72f68, 0x72f80);
   (0x72f88, 0x72fa0); (0x72fb0, 0x72fc0); (0x72fc8, 0x92fd8); (0x92ff0, 0x93218); (0x93220, 0x93228); (0x93658, 0x94000)].

Section INV.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.
Hypothesis ATOPE : ATOP = sp0 - 8388608.
Variables (path : list byte) (stdin0 : ModelAmb.AmbIn) (fs0 : Fs) (tid : word) (content : list byte).

(* [comment removed for export] *)
Definition main_cells (junk : list byte) : list cell :=
  [CB 8 junk; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (sp0 + 32));
   C8 (Z_to_bv 64 0x148cc); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (sp0 + 8)); C8 (Z_to_bv 64 0x18c50)].

(* [comment removed for export] *)
Record rd_base (M : word -> option byte) : Prop := RD_BASE {
  rb_stk  : stk (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 6144513) (sp0 - 128);
  rb_up   : wr_at (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 48) 48;
  rb_frm  : exists junk, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M (sp0 - 128) (main_cells junk);
  rb_err  : exists errv : word, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M RERRNO [C4 errv];
  rb_mi   : mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M;
  rb_aux  : rauxv_ok M sp0;
  rb_img  : pristine_in rd_ivs M;
  rb_tid  : OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72f08) 4 = Some (word_to_le_bytes 4 tid)
}.

(* [comment removed for export] *)
Record rd_inv (G : PState -> Model -> Prop) (pb : bptr) (buf cap len : Z) (M : word -> option byte) (s : PState) (mo : Model) : Prop := RD_INV {
  ri_heap : RHEAP s [(pb, buf, cap)] M;
  ri_own  : OWN [pb] G s mo;
  ri_blk  : exists bs, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M buf [CB (Z.to_nat cap) bs] /\ firstn (Z.to_nat len) bs = firstn (Z.to_nat len) content;
  ri_len  : 0 <= len <= cap /\ len <= Z.of_nat (length content);
  ri_base : rd_base M
}.

(* [comment removed for export] *)
Lemma rd_blk_range : forall G pb buf cap len M s mo, rd_inv G pb buf cap len M s mo ->
  0 < buf /\ buf mod 16 = 0 /\ buf + cap <= ATOP /\ (buf + cap <= 0x10000 \/ 0x94000 <= buf).
Proof.
  intros G pb buf cap len M s mo RI.
  pose proof (RHEAP_block_range_proof _ _ _ (pb, buf, cap) (ri_heap _ _ _ _ _ _ _ _ RI) ltac:(left; reflexivity)) as (H1 & H2 & H3 & H4 & H5).
  cbn in *. auto.
Qed.

(* [comment removed for export] *)
Definition fp_rd (iv : Z * Z) : Prop :=
     (sp0 - 6144513 <= fst iv /\ snd iv <= sp0 - 128)   (* a worker (A1) route (A): rd_base's stk window *)
  \/ (snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x94000 <= fst iv))
  \/ (0x22ea9 <= fst iv /\ snd iv <= 0x32ea9).

Lemma fp_rd_disjoint : forall W A n,
  Forall fp_rd W -> 0 <= n ->
  (sp0 - 128 <= A \/ (0x10000 <= A /\ A + n <= 0x94000 /\ (A + n <= 0x22ea9 \/ 0x32ea9 <= A))) ->
  disjoint_from W A n.
Proof.
  intros W A n HW Hn HZ. induction HW as [|[lo hi] W H _ IH]; cbn; [exact I|]. split; [|exact IH].
  unfold fp_rd in H. cbn [fst snd] in H. lia.
Qed.

Lemma rd_base_munch : forall W M M', rd_base M -> munch W M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> Forall fp_rd W ->
  Forall (fun iv => snd iv <= ATOP -> (snd iv <= 0x10000 \/ 0x94000 <= fst iv) -> wv_out M iv) W ->  (* a worker (A1) route (A) *)
  rd_base M'.
Proof.
  intros W M M' [ST UP (junk & FRM) (errv & ERR) MI AUX IMG TIDC] MU WM FW FV.
  pose proof (same_on_munch _ _ _ MU WM) as SO.
  assert (DJ : forall A n, 0 <= n ->
             (sp0 - 128 <= A \/ (0x10000 <= A /\ A + n <= 0x94000 /\ (A + n <= 0x22ea9 \/ 0x32ea9 <= A))) ->
             disjoint_from W A n) by (intros A n Hn HZ; apply fp_rd_disjoint; assumption).
  constructor.
  - apply (stk_wmono M M'); [exact ST | lia | exact WM].
  - destruct UP as (U0 & U1 & UW). split; [exact U0|]. split; [exact U1|]. intros i Hi. apply WM. apply UW. exact Hi.
  - exists junk. eapply rw_cells_transport; [exact FRM | exact MU | exact WM |]. apply DJ; [cbn; lia | left; lia].
  - exists errv. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. apply DJ; [cbn; lia |]. right. unfold RERRNO. cbn. lia.
  - eapply mem_inv_munch; [exact MI | exact MU | |].
    + intros a Ha. apply (disjoint_outside W a 1); [|lia]. apply DJ; [lia | right; lia].
    + (* a worker (A1) route (A): the stack class is in rd_base's window, the heap class is FV's *)
      rewrite Forall_forall in FW, FV |- *. intros [l0 h0] IN a Ha Hout. cbn [fst snd] in Ha.
      pose proof (FW _ IN) as H. unfold fp_rd in H. cbn [fst snd] in H. destruct H as [H|[H|H]].
      * pose proof ST as (_ & _ & STK). exact (proj1 (STK a ltac:(lia))).
      * exact (FV (l0, h0) IN ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia) a ltac:(cbn [fst snd]; lia) Hout).
      * lia.
  - (* a worker port727: through rauxv_ok_frame, so this text does not open rauxv_ok (either auxv form). *)
    eapply rauxv_ok_frame; [exact AUX | exact MU | exact WM |].
    eapply Forall_impl; [|exact FW]. intros [lo hi] H. unfold fp_rd in H. cbn [fst snd] in H |- *.
    unfold RAUXV_CELL. lia.
  - eapply pristine_in_same_on; [exact IMG | exact SO |]. intros lo hi a IN Ha. split.
    + unfold rd_ivs in IN. cbn [In] in IN. repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
    + apply (disjoint_outside W a 1); [|lia]. apply DJ; [lia|]. right.
      unfold rd_ivs in IN. cbn [In] in IN. repeat (destruct IN as [IN|IN]; [injection IN as <- <-; lia|]). destruct IN.
  - rewrite <- TIDC. apply (rdn_same_on (outside W)); [exact SO | | lia | lia].
    intros x Hx. apply (disjoint_outside W x 1); [|lia]. apply DJ; [lia | right; lia].
Qed.

(* [comment removed for export] *)
Lemma fp_rd_write_ok : forall LB W, Forall fp_rd W ->
  Forall (fun iv => snd iv <= ATOP -> (snd iv <= 0x10000 \/ 0x94000 <= fst iv) ->
                    exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) W ->
  Forall (rclient_write_ok LB) W.
Proof.
  intros LB W FW FB. induction FW as [|[a b] W H _ IH]; [constructor|].
  inversion FB as [|? ? HB FB']; subst. constructor; [|apply IH; exact FB'].
  unfold rclient_write_ok, fp_rd in *. cbn [fst snd] in *. destruct H as [H|[H|H]].
  - left. lia.
  - right; right. apply HB; lia.
  - right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_ivs_client : forall LB SP lo hi a, In (lo, hi) rd_ivs -> lo <= a < hi -> 0 <= a < 2^64 /\ rclient_addr LB SP a.
Proof.
  intros LB SP lo hi a IN Ha. unfold rd_ivs in IN. cbn [In] in IN.
  unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP.
  repeat (destruct IN as [IN|IN]; [injection IN as <- <-; split; [lia | right; left; lia]|]). destruct IN.
Qed.

Lemma rd_base_heap : forall LB SP M M' (errv' : word),
  rd_base M -> rheap_pres LB SP M M' -> SP <= sp0 - 128 ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' (sp0 - 6144513) (sp0 - 128) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  rd_base M'.
Proof.
  intros LB SP M M' errv' [_ UP (junk & FRM) _ _ _ IMG TIDC] HP HS MI' ST' ERR' AUX'.
  assert (HP0 : rheap_pres [] (sp0 - 128) M M') by (eapply rheap_pres_weaken; [exact HP | lia | intros b []]).
  constructor; try assumption.
  - eapply rheap_pres_wr_at; [exact HP0 | exact UP |]. left. lia.
  - exists junk. exact (rheap_pres_rw_cells _ _ _ _ _ _ HP0 FRM ltac:(left; lia)).
  - exists errv'. exact ERR'.
  - eapply pristine_in_same_on; [exact IMG | apply same_on_rheap_pres; exact HP0 |]. apply rd_ivs_client.
  - rewrite <- TIDC. apply (rdn_same_on (rclient_addr [] (sp0 - 128))); [apply same_on_rheap_pres; exact HP0 | | lia | lia].
    intros x Hx. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. right; left. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_inv_heap_same : forall G G' pb buf cap len M M' s s' mo mo' (errv' : word),
  rd_inv G pb buf cap len M s mo ->
  rheap_pres [(pb, buf, cap)] (sp0 - 128) M M' ->
  RHEAP s' [(pb, buf, cap)] M' -> OWN [pb] G' s' mo' ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M' -> stk (run_segments psegs rc_inp rc_sp rc_mb) M' (sp0 - 6144513) (sp0 - 128) -> rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' RERRNO [C4 errv'] -> rauxv_ok M' sp0 ->
  rd_inv G' pb buf cap len M' s' mo'.
Proof.
  intros G G' pb buf cap len M M' s s' mo mo' errv' RI HP HH' HOWN' MI' ST' ERR' AUX'.
  destruct RI as [_ _ (bs & BLK & PRE) LEN BASE].
  pose proof (rw_cells_bound _ _ _ _ BLK) as BB. cbn [cells_size csize] in BB.
  constructor; try assumption.
  - exists bs. split; [|exact PRE]. eapply rheap_pres_rw_cells; [exact HP | exact BLK |].
    right; right. exists (pb, buf, cap). split; [left; reflexivity|]. cbn [cells_size csize blk_addr blk_size fst snd]. lia.
  - eapply rd_base_heap; [exact BASE | exact HP | lia | exact MI' | exact ST' | exact ERR' | exact AUX'].
Qed.

(* [comment removed for export] *)
Lemma rd_inv_munch : forall G G' pb buf cap len len' W M M' s mo mo',
  rd_inv G pb buf cap len M s mo -> munch W M M' -> wmono (run_segments psegs rc_inp rc_sp rc_mb) M M' -> Forall fp_rd W ->
  Forall (fun iv => snd iv <= ATOP -> (snd iv <= 0x10000 \/ 0x94000 <= fst iv) -> buf <= fst iv /\ snd iv <= buf + cap) W ->
  (exists bs, rw_cells (run_segments psegs rc_inp rc_sp rc_mb) M' buf [CB (Z.to_nat cap) bs] /\ firstn (Z.to_nat len') bs = firstn (Z.to_nat len') content) ->
  0 <= len' <= cap -> len' <= Z.of_nat (length content) ->
  OWN [pb] G' s mo' ->
  rd_inv G' pb buf cap len' M' s mo'.
Proof.
  intros G G' pb buf cap len len' W M M' s mo mo' RI MU WM FW FB BLK L1 L2 HOWN'.
  destruct RI as [HH _ RBLK _ BASE].
  constructor.
  - eapply RHEAP_frame_proof; [exact HH | exact MU | exact WM |]. apply fp_rd_write_ok; [exact FW|].
    eapply Forall_impl; [|exact FB]. intros [a b] H H1 H2. exists (pb, buf, cap). split; [left; reflexivity|]. cbn in *. apply H; assumption.
  - exact HOWN'.
  - exact BLK.
  - lia.
  - eapply rd_base_munch; try eassumption.
    (* a worker (A1) route (A): W's heap class lies in the buffer (FB), which was writable (ri_blk) *)
    destruct RBLK as (bs0 & (_ & (_ & _ & WA)) & _). cbn [cells_size csize] in WA.
    rewrite Nat.add_0_r, Z2Nat.id in WA by lia.
    eapply Forall_impl; [|exact FB]. intros [l0 h0] H H1 H2 a Ha _. cbn [fst snd] in *.
    destruct (H H1 H2) as [B1 B2]. replace a with (buf + (a - buf)) by lia. apply WA. lia.
Qed.
End INV.
