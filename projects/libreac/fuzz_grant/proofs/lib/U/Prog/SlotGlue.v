From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem Cells Frame Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require PropExec Exec Regs6ss MState.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotBridge SlotGlueStep SlotImg.
Import ListNotations.
Open Scope Z_scope.

Lemma mbyte_mrd : forall segs m a, YP09.mbyte segs m a = mrd segs m (wa a).
Proof. reflexivity. Qed.

Lemma writable_wview : forall segs m a, YP09.writable_at segs m a <-> wview segs m (wa a) <> None.
Proof. reflexivity. Qed.

Lemma bytes_through : forall mem m0 mem' a bs,
  mem_rel rsegs mem m0 -> ro_agree rsegs mem' -> bytes_at rsegs m0 a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> YP09.mbyte rsegs mem' (a + i) = YP09.mbyte rsegs mem (a + i)) ->
  bytes_at rsegs (normalize rsegs mem') a bs.
Proof.
  intros mem m0 mem' a bs HR Hro HB Hm.
  apply bytes_at_normalize; [exact Hro|].
  apply (proj2 (bytes_at_rel rsegs mem m0 a bs HR)) in HB.
  destruct HB as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). specialize (Hm (Z.of_nat i) ltac:(lia)). rewrite !mbyte_mrd in Hm. exact Hm.
Qed.

Lemma wr_through : forall mem m0 mem' a n,
  mem_rel rsegs mem m0 -> ro_agree rsegs mem' -> wr_at rsegs m0 a n ->
  (forall i, 0 <= i < n -> YP09.writable_at rsegs mem' (a + i)) ->
  wr_at rsegs (normalize rsegs mem') a n.
Proof.
  intros mem m0 mem' a n HR Hro HW Hw.
  apply (wr_at_norm rsegs mem' (normalize rsegs mem') a n (mem_rel_normalize rsegs mem' Hro)).
  - destruct HW as (H1 & H2 & _). split; [exact H1|]. split; [exact H2|]. intros i Hi.
    apply writable_wview. exact (Hw i Hi).
  - intros i Hi. destruct HW as (_ & _ & H3). exact (ro_false_of_wview rsegs mem m0 _ HR (H3 i Hi)).
Qed.

Lemma rw_cells_through : forall mem m0 mem' A cs,
  mem_rel rsegs mem m0 -> ro_agree rsegs mem' -> rw_cells rsegs m0 A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     YP09.mbyte rsegs mem' (A + i) = YP09.mbyte rsegs mem (A + i) /\ YP09.writable_at rsegs mem' (A + i)) ->
  rw_cells rsegs (normalize rsegs mem') A cs.
Proof.
  intros mem m0 mem' A cs HR Hro [[Hwf HB] HW] Hm. split; [split; [exact Hwf|] |].
  - apply (bytes_through mem m0); [exact HR | exact Hro | exact HB |].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. exact (proj1 (Hm i Hi)).
  - apply (wr_through mem m0); [exact HR | exact Hro | exact HW |].
    intros i Hi. exact (proj2 (Hm i Hi)).
Qed.

Lemma high_present : forall m a, 0x51000 <= a < 2 ^ 64 -> wview rsegs m (wa a) <> None ->
  exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha H. unfold wview, mrd in *. destruct (m (wa a)) as [b|]; [exists b; reflexivity|].
  exfalso. apply H. rewrite wa_unsigned by lia. rewrite find_segment_rsegs_high by lia. reflexivity.
Qed.


Lemma stk_through : forall mem m0 mem' lo hi,
  mem_rel rsegs mem m0 -> ro_agree rsegs mem' -> stk rsegs m0 lo hi -> 0x51000 <= lo ->
  (forall a, lo <= a < hi -> YP09.writable_at rsegs mem' a) -> stk rsegs (normalize rsegs mem') lo hi.
Proof.
  intros mem m0 mem' lo hi HR Hro (H1 & H2 & H3) Hlo Hw. split; [exact H1|]. split; [exact H2|].
  intros a Ha. pose proof (mem_rel_normalize rsegs mem' Hro) as HR'.
  assert (Ero : ro_addr rsegs (wa a) = false) by exact (ro_false_of_wview rsegs mem m0 _ HR (proj1 (H3 a Ha))).
  split.
  - rewrite (wview_rel_rw rsegs mem' _ _ HR' Ero). apply writable_wview. exact (Hw a Ha).
  - rewrite <- (mrd_rel rsegs mem' _ _ HR'). apply high_present; [lia|]. apply writable_wview. exact (Hw a Ha).
Qed.



Lemma stk_noseg : forall mem' lo hi, ro_agree rsegs mem' -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> find_segment rsegs a 1 = None /\ YO0d.present mem' a) ->
  stk rsegs (normalize rsegs mem') lo hi.
Proof.
  intros mem' lo hi Hro Hlo Hhi H. split; [exact Hlo|]. split; [exact Hhi|]. intros a Ha.
  destruct (H a Ha) as [Hf [b Hb]].
  assert (Ero : ro_addr rsegs (wa a) = false) by (unfold ro_addr; rewrite wa_unsigned by lia; rewrite Hf; reflexivity).
  assert (En : normalize rsegs mem' (wa a) = Some b) by (unfold normalize; rewrite Ero; exact Hb).
  split; [unfold wview; rewrite En; discriminate | exists b; unfold mrd; rewrite En; reflexivity].
Qed.

Lemma pairwise_mid : forall (l1 l2 : list (Z * Z)) x y,
  pairwise ranges_disjoint (l1 ++ x :: l2) -> In y (l1 ++ l2) -> ranges_disjoint x y.
Proof.
  induction l1 as [|z l1 IH]; intros l2 x y H Hy; cbn [app] in *.
  - destruct H as [H _]. apply H. exact Hy.
  - destruct H as [Hz Hr]. destruct Hy as [<-|Hy].
    + assert (Hx : In x (l1 ++ x :: l2)) by (apply in_or_app; right; left; reflexivity).
      specialize (Hz x Hx). unfold ranges_disjoint in *. lia.
    + exact (IH l2 x y Hr Hy).
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma ms_eta : forall s, ms_fregs s = fp_regs -> ms_fcsr s = fp_csr -> ms_svc_pending s = None -> ms_resv s = None ->
  s = YK11.mkst (ms_regs s) (ms_pc_val s) (ms_mem s) (ms_rom s).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma kept_high : forall L A regs mem md E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  errno_addr B + 4 <= alloc_ceiling ->
  forall a, spZ regs <= a < 2 ^ 64 -> alloc_ceiling <= a -> ~ E a ->
  YP09.mbyte (ms_segs B) mem' a = YP09.mbyte (ms_segs B) mem a /\
  (YP09.writable_at (ms_segs B) mem a <-> YP09.writable_at (ms_segs B) mem' a).
Proof.
  intros L A regs mem md E L' A' regs' mem' md' HMR HCP Herr a Ha Hac HE.
  destruct HCP as (HMR' & _ & _ & _ & _ & _ & _ & Hfr & _).
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HMR Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HMR' Ho). lia.
  - unfold scratch_k. intros [H|H]; lia.
  - exact HE.
Qed.

Lemma kept_img : forall L A regs mem md E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  AllocExtra B (aa_MR API) ->
  forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
  ~ (errno_addr B <= a < errno_addr B + 4) -> a < spZ regs - ALLOC_STACK -> ~ E a ->
  YP09.mbyte (ms_segs B) mem' a = YP09.mbyte (ms_segs B) mem a /\
  (YP09.writable_at (ms_segs B) mem a <-> YP09.writable_at (ms_segs B) mem' a).
Proof.
  intros L A regs mem md E L' A' regs' mem' md' HMR HCP HAX a Himg Hst Hctx Herr Hlo HE.
  destruct HCP as (HMR' & _ & _ & _ & _ & _ & _ & Hfr & _).
  apply Hfr.
  - right. exact Himg.
  - intros [Ho|Ho]; [apply Hctx; exact (ax_img HAX L A mem md a HMR Himg Ho) | exact (Hst Ho)].
  - intros [Ho|Ho]; [apply Hctx; exact (ax_img HAX L' A' mem' md' a HMR' Himg Ho) | exact (Hst Ho)].
  - unfold scratch_k. intros [H|H]; [lia | exact (Herr H)].
  - exact HE.
Qed.

Lemma call_post_k_regs : forall stk L A regs1 regs2 mem md E L' A' regs' mem' md',
  (forall r, callee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs1 (Z_to_bv 5 r)) ->
  call_post_k B (aa_MR API) stk L A regs1 mem md E L' A' regs' mem' md' ->
  call_post_k B (aa_MR API) stk L A regs2 mem md E L' A' regs' mem' md'.
Proof.
  intros stk L A regs1 regs2 mem md E L' A' regs' mem' md' Hcs
    (H1 & H2 & H3 & H4 & H5 & Hpres & H7 & Hfr & H9 & Hscr).
  assert (Esp : spZ regs2 = spZ regs1).
  { assert (E2 : YK11.getr regs2 2%bv = YK11.getr regs1 2%bv) by exact (Hcs 2 ltac:(unfold callee_saved; lia)).
    unfold spZ. rewrite E2. reflexivity. }
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj _ (conj H7 (conj _ (conj H9 _))))))))).
  - intros r Hr. rewrite (Hpres r Hr). symmetry. exact (Hcs r Hr).
  - intros a Ha Ho Ho' Hs HE. apply Hfr; try assumption. unfold scratch_k in *. rewrite <- Esp. exact Hs.
  - intros a Hs. apply Hscr. unfold scratch_k in *. rewrite <- Esp. exact Hs.
Qed.

Lemma cs_after : forall stk L A s s0 mem md E L' A' regs' mem' md',
  ms_rel rsegs s s0 ->
  call_post_k B (aa_MR API) stk L A (ms_regs s) mem md E L' A' regs' mem' md' ->
  forall k, callee_saved k -> YK11.getr regs' (Z_to_bv 5 k) = rg s0 k.
Proof.
  intros stk L A s s0 mem md E L' A' regs' mem' md' (HRr & _) (_ & _ & _ & _ & _ & Hpres & _) k Hk.
  rewrite (Hpres k Hk), HRr. reflexivity.
Qed.

(* the jal, the transport to the real memory, and call_pre; the continuation receives the contract's post *)
Ltac jal_prelude s s0 HR HJ0 Hseg Hh Hl :=
  rewrite Hseg;
  eapply (evt_SR rsegs s _ _ _ (evt_rel rsegs _ s s0 wx_apart_rsegs HR HJ0) Hh Hl);
  let s1 := fresh "s1" in let s1' := fresh "s1'" in
  intros s1 (s1' & HJ & HR1 & Hrs);
  pose proof HR as (HRr & HRf & HRp & HRs & HRv & HRc & HRo & HRm);
  pose proof HR1 as (HR1r & HR1f & HR1p & HR1s & HR1v & HR1c & HR1o & HR1m);
  destruct HJ as (Jpc & J1 & J2 & J3 & J4 & J8 & J9 & J10 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27 &
                  Jf & Jc & Jv & Js & Jo & Jm).

Lemma regs_after_jal : forall s s0 s1 s1' tgt ret a0,
  ms_rel rsegs s s0 -> ms_rel rsegs s1 s1' -> jal_post s0 tgt ret a0 s1' ->
  (forall k, YK11.getr (ms_regs s1) (Z_to_bv 5 k) = rg s1' k) /\
  (forall r, callee_saved r -> YK11.getr (ms_regs s) (Z_to_bv 5 r) = YK11.getr (ms_regs s1) (Z_to_bv 5 r)).
Proof.
  intros s s0 s1 s1' tgt ret a0 (HRr & _) (HR1r & _)
    (_ & _ & J2 & J3 & J4 & J8 & J9 & _ & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27 & _).
  assert (G : forall k, YK11.getr (ms_regs s1) (Z_to_bv 5 k) = rg s1' k) by (intros k; rewrite HR1r; reflexivity).
  split; [exact G|].
  intros r Hr. rewrite G. rewrite HRr. change (YK11.getr (ms_regs s0) (Z_to_bv 5 r)) with (rg s0 r).
  unfold callee_saved in Hr.
  destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [exact (eq_sym J2)|exact (eq_sym J3)|exact (eq_sym J4)|
                                              exact (eq_sym J8)|exact (eq_sym J9)|].
  assert (r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
    as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]] by lia; symmetry; assumption.
Qed.

Lemma state_after_jal : forall s s0 s1 s1' tgt ret a0,
  ms_rel rsegs s s0 -> ms_rel rsegs s1 s1' -> jal_post s0 tgt ret a0 s1' -> ro_same rsegs (ms_mem s) (ms_mem s1) ->
  ms_fregs s = fp_regs -> ms_fcsr s = fp_csr -> ms_rom s0 = seg_rom rsegs ->
  s1 = YK11.mkst (ms_regs s1) (Z_to_bv 64 tgt) (ms_mem s) (seg_rom rsegs).
Proof.
  intros s s0 s1 s1' tgt ret a0 HR HR1 HJ Hrs Hfr Hfc Hrom0.
  pose proof HR as (HRr & HRf & HRp & HRs & HRv & HRc & HRo & HRm).
  pose proof HR1 as (HR1r & HR1f & HR1p & HR1s & HR1v & HR1c & HR1o & HR1m).
  destruct HJ as (Jpc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Jf & Jc & Jv & Js & Jo & Jm).
  assert (Em : ms_mem s1 = ms_mem s).
  { apply functional_extensionality. intros a.
    apply (mem_unchanged_rel rsegs (ms_mem s) (ms_mem s0) (ms_mem s1) (ms_mem s1') HRm HR1m Hrs).
    intros y. rewrite Jm. reflexivity. }
  rewrite (ms_eta s1) at 1.
  - rewrite Em, HR1p, Jpc, HR1o, Jo, Hrom0. reflexivity.
  - rewrite HR1f, Jf, <- HRf. exact Hfr.
  - rewrite HR1c, Jc, <- HRc. exact Hfc.
  - rewrite HR1s. exact Js.
  - rewrite HR1v. exact Jv.
Qed.

Definition sp_ok (s0 : machine_state) : Prop :=
  spZ (ms_regs s0) mod 16 = 0 /\ alloc_ceiling + ALLOC_STACK <= spZ (ms_regs s0) /\ spZ (ms_regs s0) < 2 ^ 63 /\
  (forall a, spZ (ms_regs s0) - ALLOC_STACK <= a < spZ (ms_regs s0) -> YP09.writable_at rsegs (ms_mem s0) a).

Lemma call_pre_after_jal : forall s s0 s1 s1' tgt ret a0 L A md,
  unit_binding B -> ms_rel rsegs s s0 -> ms_rel rsegs s1 s1' -> jal_post s0 tgt ret a0 s1' ->
  ms_mem s1 = ms_mem s ->
  aa_MR API L A (ms_mem s) md -> WF A -> bounded A -> st_init_done A = true -> errno_wr B (ms_mem s) ->
  YK0s.ret_ok (Z_to_bv 64 ret) -> rg s0 4 = w64 (ms_tp B) -> sp_ok s0 ->
  call_pre B (aa_MR API) L A (ms_regs s1) (ms_mem s) md.
Proof.
  intros s s0 s1 s1' tgt ret a0 L A md (Hseg & _) HR HR1 HJ Em HMR HWF Hbd Hinit Herr Hret Htp
    (Hsp16 & Hsplo & Hsphi & Hspw).
  destruct (regs_after_jal s s0 s1 s1' tgt ret a0 HR HR1 HJ) as [G _].
  pose proof HR as (HRr & _ & _ & _ & _ & _ & _ & HRm).
  destruct HJ as (_ & J1 & J2 & _ & J4 & _).
  assert (Hsp1 : spZ (ms_regs s1) = spZ (ms_regs s0)).
  { unfold spZ. change (YK11.getr (ms_regs s1) 2%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 2)). rewrite G, J2.
    reflexivity. }
  unfold call_pre.
  refine (conj HMR (conj HWF (conj Hbd (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - change (YK11.getr (ms_regs s1) 1%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 1)). rewrite G, J1. exact Hret.
  - rewrite Hsp1. exact Hsp16.
  - rewrite Hsp1. exact Hsplo.
  - rewrite Hsp1. exact Hsphi.
  - intros a Ha. rewrite Hsp1 in Ha. rewrite Hseg.
    apply (writable_at_rel rsegs (ms_mem s) (ms_mem s0) a HRm). apply Hspw. exact Ha.
  - change (YK11.getr (ms_regs s1) 4%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 4)). rewrite G, J4. exact Htp.
  - exact Herr.
  - intros H. rewrite Hinit in H. discriminate.
Qed.

Lemma malloc_core : forall s s0 md L A b n ret (P : config -> Prop),
  frame_allocator B API -> unit_binding B -> ms_rel rsegs s s0 ->
  MemNorm.ro_agree (ms_segs B) (ms_mem s) -> ms_fregs s = fp_regs -> ms_fcsr s = fp_csr ->
  alloc_state B API L A (ms_mem s) md b -> errno_wr B (ms_mem s) -> room_slots b n ->
  Exec.evt rsegs (jal_post s0 MALLOC_PC ret (w64 n)) s0 -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  ms_rom s0 = seg_rom rsegs -> rg s0 4 = w64 (ms_tp B) -> sp_ok s0 ->
  (forall L' A' regs' mem' md' res,
     call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md (fun _ => False) L' A' regs' mem' md' ->
     YK11.getr regs' (Z_to_bv 5 10) = Z_to_bv 64 res -> res mod 16 = 0 -> fresh_block B res n ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     blocks_kept B L A (ms_mem s) mem' (fun _ => False) -> ro_agree rsegs mem' -> guard_kept B (ms_mem s) mem' ->
     (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) -> st_init_done A' = true ->
     res_ok_slots A' (sb_malloc b n) ->
     P (mkCfg (YK11.mkst regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md')) ->
  SR (ms_segs B) (mkCfg s md) P.
Proof.
  intros s s0 md L A b n ret P HFA HUB HR Hro Hfr Hfc (HMR & HWF & Hbd & Hinit & Hres) Herr Hroom
    HJ0 Hret Hrom0 Htp Hsp K.
  pose proof HUB as (Hseg & Hmal & Hfre).
  pose proof HFA as (Hmc & _).
  destruct (mr_model B _ (aa_laws API) L A (ms_mem s) md HMR) as (Hh & Hl & _).
  rewrite Hseg.
  eapply (evt_SR rsegs s _ md _ (evt_rel rsegs _ s s0 wx_apart_rsegs HR HJ0) Hh Hl).
  intros s1 (s1' & HJ & HR1 & Hrs).
  pose proof (state_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ Hrs Hfr Hfc Hrom0) as Es1.
  assert (Em : ms_mem s1 = ms_mem s) by (rewrite Es1; reflexivity).
  destruct (regs_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ) as [G Hcs].
  pose proof (call_pre_after_jal s s0 s1 s1' _ _ _ L A md HUB HR HR1 HJ Em HMR HWF Hbd Hinit Herr Hret Htp Hsp) as Hpre.
  rewrite Es1.
  pose proof (Hmc L A (ms_regs s1) (ms_mem s) md n b) as HM.
  rewrite Hseg, Hmal in HM.
  eapply SR_mono; [apply HM | ].
  - exact Hpre.
  - rewrite <- Hseg. exact Hro.
  - change (YK11.getr (ms_regs s1) 10%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 10)). rewrite G.
    destruct HJ as (_ & _ & _ & _ & _ & _ & _ & J10 & _). exact J10.
  - exact Hres.
  - exact Hroom.
  - intros c' (L' & A' & regs' & mem' & md' & res & Ec' & HCP & Hr10 & _ & H16 & Hfresh & Hsplit & Hkept &
                 Hro' & Hguard & Hub & Hinit' & _ & Hslots).
    assert (Hra : YK11.getr (ms_regs s1) 1%bv = Z_to_bv 64 ret).
    { change (YK11.getr (ms_regs s1) 1%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 1)). rewrite G.
      destruct HJ as (_ & J1 & _). exact J1. }
    rewrite Ec', Hra. rewrite ?Hseg. rewrite ?Hseg in Hro'.
    apply (K L' A' regs' mem' md' res); try assumption.
    apply (call_post_k_regs ALLOC_STACK L A (ms_regs s1) (ms_regs s)); [exact Hcs | exact HCP].
Qed.

Lemma free_core : forall s s0 md L A b q n ret (P : config -> Prop),
  frame_allocator B API -> unit_binding B -> ms_rel rsegs s s0 ->
  MemNorm.ro_agree (ms_segs B) (ms_mem s) -> ms_fregs s = fp_regs -> ms_fcsr s = fp_csr ->
  alloc_state B API L A (ms_mem s) md b -> errno_wr B (ms_mem s) -> In (q, n) (user_blocks A) ->
  Exec.evt rsegs (jal_post s0 FREE_PC ret (w64 (ptr_addr L q))) s0 -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  ms_rom s0 = seg_rom rsegs -> rg s0 4 = w64 (ms_tp B) -> sp_ok s0 ->
  (forall L' A' regs' mem' md',
     call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md
       (fun a => ptr_addr L q <= a < ptr_addr L q + n) L' A' regs' mem' md' ->
     (exists b1 b2, blocks L A = b1 ++ (ptr_addr L q, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     blocks_kept B L A (ms_mem s) mem' (fun a => a = ptr_addr L q) -> ro_agree rsegs mem' -> guard_kept B (ms_mem s) mem' ->
     (forall q' k, In (q', k) (user_blocks A) -> q' <> q -> In (q', k) (user_blocks A')) ->
     st_init_done A' = true -> res_ok_slots A' (sb_free b n) ->
     P (mkCfg (YK11.mkst regs' (Z_to_bv 64 ret) mem' (seg_rom rsegs)) md')) ->
  SR (ms_segs B) (mkCfg s md) P.
Proof.
  intros s s0 md L A b q n ret P HFA HUB HR Hro Hfr Hfc (HMR & HWF & Hbd & Hinit & Hres) Herr Hq
    HJ0 Hret Hrom0 Htp Hsp K.
  pose proof HUB as (Hseg & Hmal & Hfre).
  pose proof HFA as (_ & Hfc' & _).
  destruct (mr_model B _ (aa_laws API) L A (ms_mem s) md HMR) as (Hh & Hl & _).
  rewrite Hseg.
  eapply (evt_SR rsegs s _ md _ (evt_rel rsegs _ s s0 wx_apart_rsegs HR HJ0) Hh Hl).
  intros s1 (s1' & HJ & HR1 & Hrs).
  pose proof (state_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ Hrs Hfr Hfc Hrom0) as Es1.
  assert (Em : ms_mem s1 = ms_mem s) by (rewrite Es1; reflexivity).
  destruct (regs_after_jal s s0 s1 s1' _ _ _ HR HR1 HJ) as [G Hcs].
  pose proof (call_pre_after_jal s s0 s1 s1' _ _ _ L A md HUB HR HR1 HJ Em HMR HWF Hbd Hinit Herr Hret Htp Hsp) as Hpre.
  rewrite Es1.
  pose proof (Hfc' L A (ms_regs s1) (ms_mem s) md q n b) as HM.
  rewrite Hseg, Hfre in HM.
  eapply SR_mono; [apply HM | ].
  - exact Hpre.
  - rewrite <- Hseg. exact Hro.
  - exact Hq.
  - change (YK11.getr (ms_regs s1) 10%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 10)). rewrite G.
    destruct HJ as (_ & _ & _ & _ & _ & _ & _ & J10 & _). exact J10.
  - exact Hres.
  - intros c' (L' & A' & regs' & mem' & md' & Ec' & HCP & Hsplit & Hkept & Hro' & Hguard & Hub & Hinit' & _ & Hslots).
    assert (Hra : YK11.getr (ms_regs s1) 1%bv = Z_to_bv 64 ret).
    { change (YK11.getr (ms_regs s1) 1%bv) with (YK11.getr (ms_regs s1) (Z_to_bv 5 1)). rewrite G.
      destruct HJ as (_ & J1 & _). exact J1. }
    rewrite Ec', Hra. rewrite ?Hseg. rewrite ?Hseg in Hro'.
    apply (K L' A' regs' mem' md'); try assumption.
    + apply (call_post_k_regs ALLOC_STACK L A (ms_regs s1) (ms_regs s)); [exact Hcs|].
      apply call_post_k_alloc. exact HCP.
    + exact (Hinit' Hinit).
Qed.

Section Kept.
Variables (x : slot_ctx) (s s0 : machine_state) (md : Model) (L : layout) (A : astate) (E : Z -> Prop)
  (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model).
Hypothesis Hseg : ms_segs B = rsegs.
Hypothesis HR : ms_rel rsegs s s0.
Hypothesis HMR : aa_MR API L A (ms_mem s) md.
Hypothesis HCP : call_post_k B (aa_MR API) ALLOC_STACK L A (ms_regs s) (ms_mem s) md E L' A' regs' mem' md'.
Hypothesis Hsp : rg s0 2 = w64 (SPL x).
Hypothesis Hro' : ro_agree rsegs mem'.
Hypothesis Herrlo : errno_addr B + 4 <= alloc_ceiling.
Hypothesis HS : alloc_ceiling + LLVM_STACK <= x_S x.
Hypothesis HS63 : x_S x < 2 ^ 63.
Hypothesis HST0 : stk rsegs (ms_mem s0) (x_S x - LLVM_STACK) (x_S x).
Hypothesis HElow : forall a, E a -> a < alloc_ceiling.
Hypothesis HEimg : forall a, E a -> ~ in_img B a.
Hypothesis HAX : AllocExtra B (aa_MR API).
Hypothesis Hbw : blocks_writable B API.

Lemma ELS' : LLVM_STACK = 8800. Proof. reflexivity. Qed.

Lemma spZ_s : spZ (ms_regs s) = x_S x - 608.
Proof.
  pose proof alloc_ceiling_val as Hacv. pose proof HS as HS8. rewrite ELS' in HS8.
  destruct HR as (HRr & _). unfold spZ. rewrite HRr. change (YK11.getr (ms_regs s0) 2%bv) with (rg s0 2).
  rewrite Hsp. unfold w64. change (SPL x) with (x_S x - 608). apply MState.unsigned_lit. lia.
Qed.

Lemma wr0 : forall a, x_S x - 8800 <= a < x_S x -> YP09.writable_at rsegs (ms_mem s) a.
Proof.
  intros a Ha. destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
  apply (writable_at_rel rsegs (ms_mem s) (ms_mem s0) a HRm). apply writable_wview.
  destruct HST0 as (_ & _ & H3). rewrite ELS' in H3. exact (proj1 (H3 a Ha)).
Qed.

Lemma KH : forall a, x_S x - 608 <= a < x_S x ->
  YP09.mbyte rsegs mem' a = YP09.mbyte rsegs (ms_mem s) a /\ YP09.writable_at rsegs mem' a.
Proof.
  intros a Ha. pose proof HS as HS8. rewrite ELS' in HS8.
  destruct (kept_high L A (ms_regs s) (ms_mem s) md E L' A' regs' mem' md' HMR HCP Herrlo a) as [E1 E2];
    [rewrite spZ_s; lia | lia | intros He; pose proof (HElow a He); lia |].
  rewrite Hseg in E1, E2. split; [exact E1|]. apply E2. apply wr0. lia.
Qed.

Lemma KS : forall a, x_S x - 8800 <= a < x_S x - 608 -> YP09.writable_at rsegs mem' a.
Proof.
  intros a Ha. rewrite <- Hseg. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr).
  apply Hscr. unfold scratch_k. left. rewrite spZ_s. unfold ALLOC_STACK. lia.
Qed.

Lemma frame_kept : forall a0 cs, x_S x - 608 <= a0 -> a0 + Z.of_nat (cells_size cs) <= x_S x ->
  rw_cells rsegs (ms_mem s0) a0 cs -> rw_cells rsegs (normalize rsegs mem') a0 cs.
Proof.
  intros a0 cs H1 H2 H. destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
  apply (rw_cells_through (ms_mem s) (ms_mem s0)); [exact HRm | exact Hro' | exact H |].
  intros i Hi. apply KH. lia.
Qed.

Lemma stack_kept : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x).
Proof.
  pose proof alloc_ceiling_val as Hacv. pose proof HS as HS8. rewrite ELS' in HS8. destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
  rewrite ELS'. apply (stk_through (ms_mem s) (ms_mem s0)); [exact HRm | exact Hro' | rewrite <- ELS'; exact HST0 | lia |].
  intros a Ha. destruct (Z_lt_le_dec a (x_S x - 608)); [apply KS; lia | apply (KH a); lia].
Qed.

Lemma row_img : forall i, 0 <= i < 24 -> in_img B (CTRL_HEADAMP_ROW + i).
Proof. intros i Hi. apply (in_img_rsegs B _ Hseg). unfold CTRL_HEADAMP_ROW. lia. Qed.

Lemma row_kept :
  (forall i, 0 <= i < 24 -> ~ static_owned B (CTRL_HEADAMP_ROW + i) /\
     ~ (ms_ctx B <= CTRL_HEADAMP_ROW + i < ms_ctx B + CTX_SIZE) /\
     ~ (errno_addr B <= CTRL_HEADAMP_ROW + i < errno_addr B + 4)) ->
  CTRL_HEADAMP_ROW + 24 <= x_S x - LLVM_STACK ->
  bytes_at rsegs (ms_mem s0) CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES ->
  bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES.
Proof.
  intros Hrow HRS HRW. destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
  apply (bytes_through (ms_mem s) (ms_mem s0)); [exact HRm | exact Hro' | exact HRW |].
  intros i Hi. change (length CTRL_HEADAMP_BYTES) with 24%nat in Hi.
  destruct (Hrow i ltac:(lia)) as (Hst & Hctx & Her).
  destruct (kept_img L A (ms_regs s) (ms_mem s) md E L' A' regs' mem' md' HMR HCP HAX
              (CTRL_HEADAMP_ROW + i) (row_img i ltac:(lia)) Hst Hctx Her) as [E1 _].
  - rewrite spZ_s. unfold ALLOC_STACK. rewrite ELS' in HRS. lia.
  - intros He. exact (HEimg _ He (row_img i ltac:(lia))).
  - rewrite Hseg in E1. exact E1.
Qed.

Lemma block_kept : forall q n cs, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A') ->
  Z.of_nat (cells_size cs) <= n ->
  rw_cells rsegs (ms_mem s0) (ptr_addr L q) cs -> rw_cells rsegs (normalize rsegs mem') (ptr_addr L q) cs.
Proof.
  intros q n cs Hq Hq' Hn H. destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
  destruct HCP as (HMR' & _ & _ & _ & Hstab & _ & _ & _ & Hbk & _).
  apply (rw_cells_through (ms_mem s) (ms_mem s0)); [exact HRm | exact Hro' | exact H |].
  intros i Hi. split.
  - rewrite <- Hseg. apply (Hbk q n i Hq Hq'). lia.
  - rewrite <- Hseg. apply (Hbw L' A' mem' md' (ptr_addr L q) n i HMR'); [|lia].
    unfold blocks. apply in_map_iff. exists (q, n). split; [|exact Hq'].
    cbn [fst snd]. rewrite (Hstab q n Hq Hq'). reflexivity.
Qed.

Lemma payload_kept :
  (x_n x = 0 \/ exists q, In (q, x_n x) (user_blocks A) /\ In (q, x_n x) (user_blocks A') /\ ptr_addr L q = x_p x) ->
  rw_cells rsegs (ms_mem s0) (x_p x) [CB (length (x_pl x)) (x_pl x)] ->
  rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)].
Proof.
  intros [H0|(q & Hq & Hq' & Hpq)] H.
  - destruct HR as (_ & _ & _ & _ & _ & _ & _ & HRm).
    apply (rw_cells_through (ms_mem s) (ms_mem s0)); [exact HRm | exact Hro' | exact H |].
    cbn [cells_size csize]. intros i Hi. exfalso. unfold x_n in H0. lia.
  - rewrite <- Hpq. apply (block_kept q (x_n x)); [exact Hq | exact Hq' | | rewrite Hpq; exact H].
    cbn [cells_size csize]. unfold x_n. lia.
Qed.

End Kept.

Lemma new_block_cells : forall L' A' mem' md' q res n,
  ms_segs B = rsegs -> aa_MR API L' A' mem' md' -> ro_agree rsegs mem' -> In (q, n) (user_blocks A') ->
  ptr_addr L' q = res -> fresh_block B res n -> 0 <= n ->
  exists junk, rw_cells rsegs (normalize rsegs mem') res [CB (Z.to_nat n) junk].
Proof.
  intros L' A' mem' md' q res n Hseg HMR' Hro' Hq Hpq (Hr4096 & Hrceil & Hrimg) Hn.
  pose proof alloc_ceiling_lt as Hac.
  assert (HS1 : stk rsegs (normalize rsegs mem') res (res + Z.of_nat (Z.to_nat n))).
  { apply stk_noseg; [exact Hro' | lia | lia |]. intros a Ha. split.
    - apply (noimg_noseg B a Hseg). replace a with (res + (a - res)) by lia. apply Hrimg. lia.
    - replace a with (ptr_addr L' q + (a - res)) by lia.
      exact (proj1 (mr_blocks B _ (aa_laws API) L' A' mem' md' q n (a - res) HMR' Hq ltac:(lia))). }
  exact (SegSetModel.stk_cell (normalize rsegs mem') res (res + Z.of_nat (Z.to_nat n)) res (Z.to_nat n) HS1
           ltac:(lia) ltac:(lia)).
Qed.

Lemma live_after_malloc : forall L A L' A' res n,
  (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) -> live_blk L' A' res n.
Proof.
  intros L A L' A' res n (b1 & b2 & Eb' & _).
  assert (Hin : In (res, n) (blocks L' A')) by (rewrite Eb'; apply in_or_app; right; left; reflexivity).
  unfold blocks in Hin. apply in_map_iff in Hin as ([q k] & Eq & Hq). cbn [fst snd] in Eq.
  injection Eq as E1 E2. subst k. exists q. split; [exact Hq | exact E1].
Qed.

Lemma new_block_apart : forall L A L' A' mem' md' res n a k,
  aa_MR API L' A' mem' md' ->
  (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
  In (a, k) (blocks L A) -> res + n <= a \/ a + k <= res.
Proof.
  intros L A L' A' mem' md' res n a k HMR' (b1 & b2 & Eb' & Eb) Hin.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L' A' mem' md' HMR') as Hdis. rewrite Eb' in Hdis.
  rewrite Eb in Hin. pose proof (pairwise_mid b1 b2 (res, n) _ Hdis Hin) as Hd.
  unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma in_blocks : forall L A q n, In (q, n) (user_blocks A) -> In (ptr_addr L q, n) (blocks L A).
Proof. intros L A q n Hq. unfold blocks. apply in_map_iff. exists (q, n). split; [reflexivity | exact Hq]. Qed.

Lemma fresh_apart_img : forall res n a k, fresh_block B res n -> 0 < n -> 0 < k ->
  (forall i, 0 <= i < k -> in_img B (a + i)) -> res + n <= a \/ a + k <= res.
Proof.
  intros res n a k (_ & _ & Hrimg) Hn Hk Himg.
  destruct (Z_le_gt_dec (res + n) a) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (a + k) res) as [H2|H2]; [right; exact H2|].
  exfalso. apply (Hrimg (Z.max res a - res)); [lia|].
  replace (res + (Z.max res a - res)) with (a + (Z.max res a - a)) by lia. apply Himg. lia.
Qed.

Lemma sp_ok_of_body : forall x s0, rg s0 2 = w64 (SPL x) ->
  stk rsegs (ms_mem s0) (x_S x - LLVM_STACK) (x_S x) -> x_S x mod 16 = 0 -> x_S x < 2 ^ 63 ->
  alloc_ceiling + LLVM_STACK <= x_S x -> sp_ok s0.
Proof.
  intros x s0 Hsp HST H16 H63 HS. pose proof alloc_ceiling_val as Hacv.
  assert (ELS : LLVM_STACK = 8800) by reflexivity. rewrite ELS in HST, HS.
  assert (Esp : spZ (ms_regs s0) = x_S x - 608).
  { unfold spZ. change (YK11.getr (ms_regs s0) 2%bv) with (rg s0 2). rewrite Hsp. unfold w64.
    change (SPL x) with (x_S x - 608). apply MState.unsigned_lit. lia. }
  unfold sp_ok. rewrite Esp. unfold ALLOC_STACK.
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  intros a Ha. apply writable_wview. destruct HST as (_ & _ & H3). exact (proj1 (H3 a ltac:(lia))).
Qed.

Lemma payload_after_malloc : forall x L A L' A' mem md E regs regs' mem' md',
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) ->
  payload_blk B x L A ->
  payload_blk B x L' A' /\
  (x_n x = 0 \/ exists q, In (q, x_n x) (user_blocks A) /\ In (q, x_n x) (user_blocks A') /\ ptr_addr L q = x_p x).
Proof.
  intros x L A L' A' mem md E regs regs' mem' md' (_ & _ & _ & _ & Hstab & _) Hub [(H0 & Himg)|(Hpos & q & Hq & Hpq)].
  - split; [left; split; assumption | left; exact H0].
  - split; [right; split; [exact Hpos|]; exists q; split; [apply Hub; exact Hq | rewrite (Hstab q _ Hq (Hub _ _ Hq)); exact Hpq]|].
    right. exists q. split; [exact Hq|]. split; [apply Hub; exact Hq | exact Hpq].
Qed.

Lemma blk_after_malloc : forall x L A L' A' mem' md' res n,
  ms_segs B = rsegs -> aa_MR API L' A' mem' md' -> fresh_block B res n -> 0 < n ->
  (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
  payload_blk B x L A -> alloc_ceiling + LLVM_STACK <= x_S x -> blk x res n.
Proof.
  intros x L A L' A' mem' md' res n Hseg HMR' Hfresh Hn Hsplit Hpay HS.
  pose proof Hfresh as (Hr4096 & Hrceil & Hrimg). pose proof alloc_ceiling_lt as Hac.
  assert (ELS : LLVM_STACK = 8800) by reflexivity.
  unfold blk. split; [lia|]. split; [lia|]. split; [left; rewrite ELS in *; lia|]. split.
  - destruct Hpay as [(H0 & Himg)|(_ & q & Hq & Hpq)].
    + rewrite H0. destruct (Z_lt_le_dec (x_p x) res) as [Hlt|Hge]; [right; lia|].
      destruct (Z_lt_le_dec (x_p x) (res + n)) as [Hlt2|Hge2]; [|left; lia].
      exfalso. apply (Hrimg (x_p x - res)); [lia|]. replace (res + (x_p x - res)) with (x_p x) by lia. exact Himg.
    + rewrite <- Hpq. exact (new_block_apart L A L' A' mem' md' res n _ _ HMR' Hsplit (in_blocks L A q _ Hq)).
  - apply (fresh_apart_img res n CTRL_HEADAMP_ROW 24 Hfresh Hn ltac:(lia)).
    intros i Hi. apply (in_img_rsegs B _ Hseg). unfold CTRL_HEADAMP_ROW. lia.
Qed.

Theorem seg_mallocT_holds : seg_mallocT B API.
Proof.
  unfold seg_mallocT, malloc_glue. intros x HS s md L A b Hpre _ Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & Ha00 & (Hs10 & Hs90) & Hs200 & Hs190 & Hs180 & Hs210).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (malloc_core s s0 md L A b 460 PC_MALLOC_T_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocT; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res 460 Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact I]].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_T_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    destruct (live_after_malloc L A L' A' res 460 Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res 460 Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res 460 Hseg HMR' Hfresh ltac:(lia) Hsplit Hpay HS) as Hblk.
    unfold At_mallocT_ret, body, common, cur.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 27), (CS 25), (CS 9), (CS 19), (CS 18), (CS 20)
      by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Lemma live_after : forall L A L' A' mem md E regs regs' mem' md' t n,
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  live_blk L A t n -> (forall q, In (q, n) (user_blocks A) -> ptr_addr L q = t -> In (q, n) (user_blocks A')) ->
  live_blk L' A' t n /\ exists q, In (q, n) (user_blocks A) /\ In (q, n) (user_blocks A') /\ ptr_addr L q = t.
Proof.
  intros L A L' A' mem md E regs regs' mem' md' t n (_ & _ & _ & _ & Hstab & _) (q & Hq & Hpq) Hk.
  pose proof (Hk q Hq Hpq) as Hq'.
  split; [exists q; split; [exact Hq' | rewrite (Hstab q n Hq Hq'); exact Hpq]|].
  exists q. split; [exact Hq|]. split; [exact Hq' | exact Hpq].
Qed.

Theorem seg_mallocSW1_holds : seg_mallocSW1 B API.
Proof.
  unfold seg_mallocSW1, malloc_glue. intros x t HS s md L A b Hpre Hlive Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as ((((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                      HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                    Hn0 & H80 & Hs90 & HSL0 & HCS0 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                    HHr0 & HI10) & Hok0 & Ha00 & (H210 & H250) & H180 & H190 & HC1980).
  unfold slots, cslot in HSL0, HCS0.
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  assert (Hn1 : 0 < sw1_size x) by (unfold sw1_size; lia).
  apply (malloc_core s s0 md L A b (sw1_size x) PC_MALLOC_SW1_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocSW1; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    destruct (live_after L A L' A' _ _ _ _ _ _ _ t 460 HCP Hlive (fun q Hq _ => Hub q 460 Hq)) as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res (sw1_size x) Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HSLk := HSL0). assert (HCSk := HCS0). assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    assert (HC198k := HC1980).
    eapply frame_kept in HSLk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HCSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HC198k; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    destruct (live_after_malloc L A L' A' res _ Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res (sw1_size x) Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res (sw1_size x) Hseg HMR' Hfresh Hn1 Hsplit Hpay HS) as Hblk.
    assert (Htap : res + sw1_size x <= t \/ t + 460 <= res).
    { rewrite <- Hpqt. exact (new_block_apart L A L' A' mem' md' res _ _ _ HMR' Hsplit (in_blocks L A qt _ Hqt)). }
    unfold At_mallocSW1_ret, at_after_admit, body, common, cur5, slots, cslot, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 25), (CS 21), (CS 19), (CS 18)
      by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Theorem seg_mallocSW2_holds : seg_mallocSW2 B API.
Proof.
  unfold seg_mallocSW2, malloc_glue. intros x t HS s md L A b Hpre Hlive Hroom.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  unfold At_mallocSW2 in HP. unfold At_mallocSW2_ret. destruct (raw_rd (x_pl x)) as [[rb rw] prw].
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & (Hs10 & Hs90) & Ha00 & HC500 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                   HHr0 & HI10).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (malloc_core s s0 md L A b 4352 PC_MALLOC_SW2_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hroom).
  - rewrite <- Ha00. apply jal_at_mallocSW2; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' res HCP Hr10 H16 Hfresh Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, False -> a < alloc_ceiling) by tauto.
    assert (HEi : forall a, False -> ~ in_img B a) by tauto.
    destruct (payload_after_malloc x L A L' A' _ _ _ _ _ _ _ HCP Hub Hpay) as [Hpay' Hpayk].
    destruct (live_after L A L' A' _ _ _ _ _ _ _ t 460 HCP Hlive (fun q Hq _ => Hub q 460 Hq)) as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) mem' (seg_rom rsegs)), md', L', A', res.
    split; [reflexivity|].
    split.
    2:{ split; [exact (live_after_malloc L A L' A' res 4352 Hsplit)|].
        split; [exact HCP|]. split; [exact Hfresh|]. split; [exact H16|]. split; [exact Hsplit|].
        split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_MALLOC_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HWSk := HWS0). assert (HSTAk := HSTA0). assert (HC50k := HC500).
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HC50k; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    destruct (live_after_malloc L A L' A' res _ Hsplit) as (qn & Hqn & Hpqn).
    destruct (new_block_cells L' A' mem' md' qn res 4352 Hseg HMR' Hro' Hqn Hpqn Hfresh ltac:(lia)) as (junk & Hjunk).
    pose proof (blk_after_malloc x L A L' A' mem' md' res 4352 Hseg HMR' Hfresh ltac:(lia) Hsplit Hpay HS) as Hblk.
    assert (Htap : res + 4352 <= t \/ t + 460 <= res).
    { rewrite <- Hpqt. exact (new_block_apart L A L' A' mem' md' res _ _ _ HMR' Hsplit (in_blocks L A qt _ Hqt)). }
    unfold body, common, cur5, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 21), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | exact Hr10 | apply mem_inv_normalize | lia | exists junk; exact Hjunk ].
Qed.

Lemma pairwise_in2 : forall l x y, pairwise ranges_disjoint l -> In x l -> In y l -> x <> y -> ranges_disjoint x y.
Proof.
  induction l as [|a l IH]; intros x y H Hx Hy Hne; [destruct Hx|].
  destruct H as [Ha Hl]. destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - contradiction.
  - apply Ha. exact Hy.
  - pose proof (Ha x Hx) as D. unfold ranges_disjoint in *. lia.
  - exact (IH x y Hl Hx Hy Hne).
Qed.

Lemma same_ptr_sizes : forall L A mem md q k n, aa_MR API L A mem md ->
  In (q, k) (user_blocks A) -> In (q, n) (user_blocks A) -> 0 < k -> 0 < n -> k = n.
Proof.
  intros L A mem md q k n HMR Hk Hn Hk0 Hn0. destruct (Z.eq_dec k n) as [E|Ne]; [exact E|]. exfalso.
  pose proof (mr_blocks_disjoint B _ (aa_laws API) L A mem md HMR) as Hdis.
  pose proof (pairwise_in2 _ _ _ Hdis (in_blocks L A q k Hk) (in_blocks L A q n Hn)) as D.
  assert (Hne : (ptr_addr L q, k) <> (ptr_addr L q, n)) by (intros E; injection E; lia).
  specialize (D Hne). unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma live_after_free : forall L A L' A' mem md E regs regs' mem' md' t k q n,
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  (forall q' k', In (q', k') (user_blocks A) -> q' <> q -> In (q', k') (user_blocks A')) ->
  In (q, n) (user_blocks A) -> 0 < k -> 0 < n -> k <> n -> live_blk L A t k ->
  live_blk L' A' t k /\ exists qt, In (qt, k) (user_blocks A) /\ In (qt, k) (user_blocks A') /\ ptr_addr L qt = t.
Proof.
  intros L A L' A' mem md E regs regs' mem' md' t k q n HMR HCP Hub Hq Hk Hn Hkn (qt & Hqt & Hpqt).
  assert (Hne : qt <> q) by (intros ->; exact (Hkn (same_ptr_sizes L A mem md q k n HMR Hqt Hq Hk Hn))).
  pose proof (Hub qt k Hqt Hne) as Hqt'.
  destruct HCP as (_ & _ & _ & _ & Hstab & _).
  split; [exists qt; split; [exact Hqt' | rewrite (Hstab qt k Hqt Hqt'); exact Hpqt]|].
  exists qt. split; [exact Hqt|]. split; [exact Hqt' | exact Hpqt].
Qed.

Lemma payload_after_free : forall x L A L' A' mem md E regs regs' mem' md' q n,
  call_post_k B (aa_MR API) ALLOC_STACK L A regs mem md E L' A' regs' mem' md' ->
  (forall q' k', In (q', k') (user_blocks A) -> q' <> q -> In (q', k') (user_blocks A')) ->
  0 < n -> (ptr_addr L q + n <= x_p x \/ x_p x + x_n x <= ptr_addr L q) ->
  ((x_n x = 0 /\ in_img B (x_p x)) \/ (0 < x_n x /\ exists q', In (q', x_n x) (user_blocks A) /\ ptr_addr L q' = x_p x)) ->
  ((x_n x = 0 /\ in_img B (x_p x)) \/ (0 < x_n x /\ exists q', In (q', x_n x) (user_blocks A') /\ ptr_addr L' q' = x_p x)) /\
  (x_n x = 0 \/ exists q', In (q', x_n x) (user_blocks A) /\ In (q', x_n x) (user_blocks A') /\ ptr_addr L q' = x_p x).
Proof.
  intros x L A L' A' mem md E regs regs' mem' md' q n (_ & _ & _ & _ & Hstab & _) Hub Hn Hap
    [(H0 & Himg)|(Hpos & qp & Hqp & Hpqp)].
  - split; [left; split; assumption | left; exact H0].
  - assert (Hne : qp <> q) by (intros ->; rewrite Hpqp in Hap; lia).
    pose proof (Hub qp _ Hqp Hne) as Hqp'.
    split; [right; split; [exact Hpos|]; exists qp; split; [exact Hqp' | rewrite (Hstab qp _ Hqp Hqp'); exact Hpqp]|].
    right. exists qp. split; [exact Hqp|]. split; [exact Hqp' | exact Hpqp].
Qed.

Lemma freed_low : forall L A mem md q n a, aa_MR API L A mem md -> In (q, n) (user_blocks A) ->
  ptr_addr L q <= a < ptr_addr L q + n -> a < alloc_ceiling.
Proof.
  intros L A mem md q n a HMR Hq Ha.
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HMR Hq). lia.
Qed.

Lemma freed_noimg : forall L A mem md q n a, AllocExtra B (aa_MR API) -> aa_MR API L A mem md ->
  In (q, n) (user_blocks A) -> ptr_addr L q <= a < ptr_addr L q + n -> ~ in_img B a.
Proof.
  intros L A mem md q n a HAX HMR Hq Ha. replace a with (ptr_addr L q + (a - ptr_addr L q)) by lia.
  apply (ax_blocks_img HAX L A mem md q n _ HMR Hq). lia.
Qed.

Theorem seg_freeT_holds : seg_freeT B API.
Proof.
  unfold seg_freeT, free_glue. intros x t HS s md L A b q Hpre _ Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & Hblkt & Ht16).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (free_core s s0 md L A b q 460 PC_FREE_T_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- H80. apply jal_at_freeT; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + 460 -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q 460 a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + 460 -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q 460 a HAX HMR Hq Ha)).
    pose proof Hblkt as (_ & _ & _ & Htpay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q 460 HCP Hub ltac:(lia) ltac:(rewrite Hpq; exact Htpay) Hpay)
      as [Hpay' Hpayk].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact I]].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_T_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    unfold At_ret0. right. unfold body, common.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia ].
Qed.

Theorem seg_freeSW1_holds : seg_freeSW1 B API.
Proof.
  unfold seg_freeSW1, free_glue. intros x t sw HS s md L A b q Hpre Hlive Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as ((((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                      HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                    Hn0 & H80 & Hs90 & HSL0 & HCS0 & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                    HHr0 & HI10) & Hok0 & Ha00 & H190 & Hblks).
  unfold slots, cslot in HSL0, HCS0.
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  assert (Hn1 : 0 < sw1_size x) by (unfold sw1_size; lia).
  assert (Hn460 : sw1_size x <> 460) by (unfold sw1_size; lia).
  apply (free_core s s0 md L A b q (sw1_size x) PC_FREE_SW1_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- Ha00. apply jal_at_freeSW1; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + sw1_size x -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q _ a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + sw1_size x -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q _ a HAX HMR Hq Ha)).
    pose proof Hblks as (_ & _ & _ & Hspay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q _ HCP Hub Hn1 ltac:(rewrite Hpq; exact Hspay) Hpay)
      as [Hpay' Hpayk].
    destruct (live_after_free L A L' A' _ _ _ _ _ _ _ t 460 q _ HMR HCP Hub Hq ltac:(lia) Hn1 ltac:(lia) Hlive)
      as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW1_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HSLk := HSL0). assert (HCSk := HCS0). assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    eapply frame_kept in HSLk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HCSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    unfold At_raw, at_after_admit, body, common, slots, cslot, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia | (right; split; [reflexivity | exact Hok0]) ].
Qed.

Theorem seg_freeSW2_holds : seg_freeSW2 B API.
Proof.
  unfold seg_freeSW2, free_glue. intros x t sw HS s md L A b q Hpre Hlive Hq Hpq.
  destruct Hpre as (HFA & HUB & Htp & (s0 & HP & HR) & Hro & Hfr & Hfc & Hal & Herr & Hpay & Herrlo & Hrow).
  pose proof HUB as (Hseg & _ & _).
  pose proof HFA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbw & _ & _ & _ & HAX & _).
  pose proof Hal as (HMR & _).
  pose proof HP as HP0.
  destruct HP0 as (((Hpc0 & HF0 & Hfc0 & Hrv0 & Hsvc0 & Hro0 & Hgp0 & Htp0 & HPL0 & HST0 & HMI0 & Hp00 & Hpn0 & Hpd0 &
                     HRW0 & HRS0 & HRP0) & Hsp0 & HSV0 & HS160 & Hsv120 & HS630) &
                   Hn0 & H80 & Ha00 & H90 & (H210 & H250) & (HTb0 & HT160 & HTl0 & HT0) & (Hwl0 & Hstl0 & HWS0 & HSTA0) &
                   HHr0 & HI10 & Hblks).
  pose proof HR as (HRr & HRf & _ & _ & _ & HRc & _ & HRm).
  apply (free_core s s0 md L A b q 4352 PC_FREE_SW2_RET _ HFA HUB HR Hro Hfr Hfc Hal Herr Hq).
  - rewrite Hpq, <- Ha00. apply jal_at_freeSW2; assumption.
  - vm_compute. reflexivity.
  - exact Hro0.
  - rewrite Htp0, Htp. reflexivity.
  - exact (sp_ok_of_body x s0 Hsp0 HST0 HS160 HS630 HS).
  - intros L' A' regs' mem' md' HCP Hsplit Hkept Hro' Hguard Hub Hinit' Hslots.
    pose proof HCP as (HMR' & HWF' & Hbd' & _).
    assert (HEl : forall a, ptr_addr L q <= a < ptr_addr L q + 4352 -> a < alloc_ceiling)
      by (intros a Ha; exact (freed_low L A _ md q _ a HMR Hq Ha)).
    assert (HEi : forall a, ptr_addr L q <= a < ptr_addr L q + 4352 -> ~ in_img B a)
      by (intros a Ha; exact (freed_noimg L A _ md q _ a HAX HMR Hq Ha)).
    pose proof Hblks as (_ & _ & _ & Hspay & _).
    destruct (payload_after_free x L A L' A' _ _ _ _ _ _ _ q 4352 HCP Hub ltac:(lia) ltac:(rewrite Hpq; exact Hspay) Hpay)
      as [Hpay' Hpayk].
    destruct (live_after_free L A L' A' _ _ _ _ _ _ _ t 460 q 4352 HMR HCP Hub Hq ltac:(lia) ltac:(lia) ltac:(lia) Hlive)
      as [Hlive' (qt & Hqt & Hqt' & Hpqt)].
    assert (CS := cs_after _ _ _ _ _ _ _ _ _ _ _ _ _ HR HCP).
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) mem' (seg_rom rsegs)), md', L', A'.
    split; [reflexivity|].
    split.
    2:{ rewrite <- Hpq. split; [apply call_post_k_alloc; exact HCP|].
        split; [exact Hsplit|]. split; [exact Hkept|]. split; [exact Hguard|]. exact Hub. }
    unfold glue_post. cbn [ms_mem ms_fregs ms_fcsr YK11.mkst].
    split; [|split; [rewrite Hseg; exact Hro'|]].
    2:{ split; [reflexivity|]. split; [reflexivity|].
        split; [exact (conj HMR' (conj HWF' (conj Hbd' (conj Hinit' Hslots))))|].
        split; [|split; [exact Hpay' | exact Hlive']].
        intros a Ha. destruct HCP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hscr). apply Hscr. unfold scratch_k. right. exact Ha. }
    exists (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)).
    split.
    2:{ unfold ms_rel. cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem YK11.mkst].
        repeat split; apply mem_rel_normalize; exact Hro'. }
    assert (HFx : fp_regs = x_F x) by (rewrite <- HF0, <- HRf, Hfr; reflexivity).
    assert (HCx : fp_csr = x_fc x) by (rewrite <- Hfc0, <- HRc, Hfc; reflexivity).
    assert (RG : forall k, rg (YK11.mkst regs' (Z_to_bv 64 PC_FREE_SW2_RET) (normalize rsegs mem') (seg_rom rsegs)) k =
                           YK11.getr regs' (Z_to_bv 5 k)) by (intros; reflexivity).
    assert (HSTk : stk rsegs (normalize rsegs mem') (x_S x - LLVM_STACK) (x_S x)) by (eapply stack_kept; eassumption).
    assert (HSVk : rw_cells rsegs (normalize rsegs mem') (x_S x - 104) (map C8 (rev (x_sv x) ++ [x_ra x]))).
    { eapply frame_kept; try eassumption; [lia | rewrite (SegSetModel.saved_size _ _ Hsv120); lia]. }
    assert (HRWk : bytes_at rsegs (normalize rsegs mem') CTRL_HEADAMP_ROW CTRL_HEADAMP_BYTES)
      by (eapply row_kept; eassumption).
    assert (HPLk : rw_cells rsegs (normalize rsegs mem') (x_p x) [CB (length (x_pl x)) (x_pl x)])
      by (eapply payload_kept; eassumption).
    assert (HWSk := HWS0). assert (HSTAk := HSTA0).
    eapply frame_kept in HWSk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    eapply frame_kept in HSTAk; try eassumption; [| change (SPL x) with (x_S x - 608); lia | change (SPL x) with (x_S x - 608); cbn; lia].
    assert (HTk : rw_cells rsegs (normalize rsegs mem') t [CB 460 (T_end (x_pl x))]).
    { rewrite <- Hpqt. eapply block_kept; try eassumption; [cbn; lia | rewrite Hpqt; exact HT0]. }
    unfold At_freeSW2_ret, body, common, cur5, table, arrays.
    cbn [ms_pc_val ms_fregs ms_fcsr ms_resv ms_svc_pending ms_rom ms_mem YK11.mkst].
    rewrite !RG. rewrite (CS 2), (CS 3), (CS 4), (CS 8), (CS 21), (CS 25) by (unfold callee_saved; lia).
    repeat match goal with |- _ /\ _ => split end.
    all: first [ reflexivity | assumption | apply mem_inv_normalize | lia ].
Qed.

End G.
