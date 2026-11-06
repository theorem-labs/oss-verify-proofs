From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U.Reusable Require Import
  YK11 YM05 YM06 YP09 YO0i YO0f YO0d YH00 YH02 YN03 YN2b YN0e YN06 YN09 YN0i YN10 YN0x YN23 YN0w.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.U Require Import Img0 KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require PropExec Mem Cells Frame Step.
Import ListNotations.
Open Scope Z_scope.
Definition B0 : malloc_syms :=
  MSyms (ms_segs src0_msyms) (ms_pcs src0_msyms) (ms_malloc src0_msyms) (ms_free src0_msyms) None
    (ms_ctx src0_msyms) (ms_lock src0_msyms) (ms_libc src0_msyms) (ms_got_guard src0_msyms) (ms_guard src0_msyms)
    (ms_replaced src0_msyms) (ms_size_classes src0_msyms) (ms_small_cnt src0_msyms) (ms_med_cnt src0_msyms)
    (ms_debruijn src0_msyms) (ms_tp src0_msyms) (ms_errno_off src0_msyms) (ms_realloc src0_msyms) (ms_vmlock src0_msyms) (ms_debruijn_len src0_msyms).
Lemma mreal_post {R} : forall segs (t : itree astate R) c (Q Q' : R -> config -> Prop),
  mreal segs c t Q -> (forall r c', Q r c' -> SR segs c' (Q' r)) -> mreal segs c t Q'.
Proof.
  intros segs t. induction t as [r | q s k IH | f]; intros c Q Q' H HK; cbn in *.
  - eapply SR_bind; [exact H | exact (HK r)].
  - eapply SR_mono; [exact H |]. intros c1 Hk. destruct q;
    try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
         split; [exact Hn|]; split; [intros i; eapply IH; [apply Hc | exact HK] | exact Hcl]).
    destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact HK].
  - exact I.
Qed.
Lemma errno_low : errno_addr src0_msyms + 4 <= CEIL_MIN.
Proof. vm_compute. intros H. discriminate H. Qed.
Lemma rw_cells_ext : forall (m m' : word -> option byte) A cs,
  Step.rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (Cells.cells_size cs) ->
     mbyte src0segs m' a = mbyte src0segs m a /\ (writable_at src0segs m a -> writable_at src0segs m' a)) ->
  Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wl & Hw)] H.
  assert (HL : length (Cells.cells_bytes cs) = Cells.cells_size cs) by (apply Cells.cells_bytes_length; exact Hwf).
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi).
    destruct (H (A + Z.of_nat i)) as [E _]; [rewrite <- HL; lia|]. exact E.
  - split; [exact Wa|]. split; [exact Wl|]. intros i Hi. destruct (H (A + i)) as [_ W]; [lia|].
    apply W. exact (Hw i Hi).
Qed.
Lemma replaced_cells : forall m : word -> option byte, exists rb, Step.ro_cells rsegs m 0x964f0 [Cells.CB 4 rb].
Proof.
  intros m.
  assert (HB : forall i, 0 <= i < 4 -> exists b, Mem.mrd rsegs m (Mem.wa (0x964f0 + i)) = Some b).
  { intros i Hi. unfold Mem.mrd. destruct (m (Mem.wa (0x964f0 + i))) as [b|]; [exists b; reflexivity|].
    assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct Hc as [-> | [-> | [-> | ->]]]; vm_compute; eexists; reflexivity. }
  destruct (HB 0 ltac:(lia)) as [b0 E0]. destruct (HB 1 ltac:(lia)) as [b1 E1].
  destruct (HB 2 ltac:(lia)) as [b2 E2]. destruct (HB 3 ltac:(lia)) as [b3 E3].
  exists [b0; b1; b2; b3]. split; [cbn; auto|].
  split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. destruct i as [|[|[|[|i]]]]; [exact E0 | exact E1 | exact E2 | exact E3 | lia].
Qed.
Section a. Context {rc : RunCeil}.
Let LL := MRx_laws src0_msyms.
Definition L0 : MR_laws B0 (MRx src0_msyms) :=
  Build_MR_laws B0 (MRx src0_msyms) (mr_wf _ _ LL) (mr_blocks _ _ LL) (mr_blocks_aligned _ _ LL) (mr_blocks_range _ _ LL)
    (mr_blocks_disjoint _ _ LL) (mr_frame _ _ LL) (mr_owned_low _ _ LL) (mr_model _ _ LL) (mr_ceil _ _ LL).
Definition API0 : AllocAPI B0.
Proof using.
  refine {| aa_MR := MRx src0_msyms; aa_laws := L0 |}.
  - intros mem md sec H Hs. apply (MRx_init src0_msyms mem md sec src0_syms_ok); [|exact Hs].
    destruct H. constructor; assumption.
  - exact (fun fx => @src0_malloc_realizes fx rc (@src0_alloc_meta fx rc) (@src0_malloc_small fx rc (@src0_alloc_slot fx rc))).
  - exact (fun fx => @src0_free_realizes fx rc (@src0_ntfree_of_A fx rc (@src0_ntA fx rc))).
  - exact (fun fx => @src0_free_null fx).
  - intros fx pc L A regs mem md m n H. discriminate H.
Defined.
Lemma img_low0 : img_low B0.
Proof using. apply (img_low_of_check B0 CEIL_MIN); [vm_compute; reflexivity | apply alloc_ceiling_value]. Qed.
Lemma kb_mid_noE : forall K sp L A mem md (E : Z -> Prop) L' A' mem' md',
  kb_mid B0 API0 K sp L A mem md E L' A' mem' md' ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img src0_msyms a) ->
  kb_mid B0 API0 K sp L A mem md (fun _ => False) L' A' mem' md'.
Proof using.
  intros K sp L A mem md E L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs _. apply H8; [exact Ha | exact Ho | exact Ho' | exact Hs |].
  intros He. destruct (HE a He) as [Hlt Hni]. destruct Ha as [Ha|Ha]; [lia | exact (Hni Ha)].
Qed.
End a.
