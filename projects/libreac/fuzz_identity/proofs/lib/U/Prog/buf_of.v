From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import buf_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac ZBridge
Regs6ss RegisterBridge.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma bo_pre_k : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (S c : Z),
  x2 = Z_to_bv 64 S -> x10 = Z_to_bv 64 c -> 0 <= c < 2 ^ 28 -> 16 <= S < 2 ^ 64 ->
  store_ok rsegs m (wa (S - 8)) 8 = true ->
  Exec.evt rsegs
    (fun ms' => exists y10 y11 : word,
       ms' = MS (mkR (Z_to_bv 64 0x14104) (Z_to_bv 64 (S - 16)) x3 x4 x5 x6 x7 x8 x9 y10 y11 x12 x13 x14 x15 x16 x17
                     x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                F (Z_to_bv 64 0x15ab4) fc None (write_to_mem m (wa (S - 8)) (le8 x1)) ro /\
       y10 = Z_to_bv 64 (Z.max c 1))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x140f0) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro S c E2 E10 Hc HS HST.
  subst x2 x10.
  step. step. step. step. step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  unfold PropExec.v_sltiu, YK11.v_sltiu. rewrite (unsigned_lit c) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec c 1) as [H1|H1].
  - rewrite (unsigned_lit 1) by lia. f_equal. lia.
  - rewrite (unsigned_lit 0) by lia. f_equal. lia.
Qed.

Lemma bo_post_k : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (S q : Z) (ra : word),
  x2 = Z_to_bv 64 (S - 16) -> x10 = Z_to_bv 64 q -> 0 < q < 2 ^ 64 -> 16 <= S < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (S - 8)) 8 = Some (le8 ra) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 S) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17
                              x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                         F (ret_pc ra) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x14104) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro S q ra E2 E10 Hq HS HR.
  subst x2 x10.
  step. if_cases HC.
  { exfalso. unfold bv_eqb in HC. apply Z.eqb_eq in HC.
    rewrite (unsigned_lit q) in HC by lia. rewrite ?(unsigned_lit 0) in HC by lia. lia. }
  step. step. step.
  apply evt_done. replace (S - 16 + 16) with S by lia. reflexivity.
Qed.

Lemma canon_mkst : forall {fx : YK11.FPState} (regs : bvmap 5 word) (pc : word) (mem ro : word -> option byte),
  canonical_register_state (YK11.mkst regs pc mem ro) = MS (mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma bo_pre_c : forall {fx : YK11.FPState} (regs : bvmap 5 word) (mem ro : word -> option byte) (S c : Z),
  YK11.getr regs 2 = Z_to_bv 64 S -> YK11.getr regs 10 = Z_to_bv 64 c -> 0 <= c < 2 ^ 28 -> 16 <= S < 2 ^ 64 ->
  store_ok rsegs mem (wa (S - 8)) 8 = true ->
  Exec.evt rsegs
    (fun ms' => exists y10 y11 : word,
       ms' = MS (mkR (Z_to_bv 64 0x14104) (Z_to_bv 64 (S - 16)) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
                     (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) y10 y11 (reg_get regs 12)
                     (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16) (reg_get regs 17)
                     (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22)
                     (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
                     (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31))
                fp_regs (Z_to_bv 64 0x15ab4) fp_csr None (write_to_mem mem (wa (S - 8)) (le8 (reg_get regs 1))) ro /\
       y10 = Z_to_bv 64 (Z.max c 1))
    (canonical_register_state (YK11.mkst regs (Z_to_bv 64 0x140f0) mem ro)).
Proof.
  intros fx regs mem ro S c E2 E10 Hc HS HST.
  rewrite canon_mkst. unfold mkR_of.
  apply bo_pre_k; [exact E2 | exact E10 | exact Hc | exact HS | exact HST].
Qed.

Lemma bo_post_c : forall {fx : YK11.FPState} (regs : bvmap 5 word) (mem ro : word -> option byte) (S q : Z) (ra : word),
  YK11.getr regs 2 = Z_to_bv 64 (S - 16) -> YK11.getr regs 10 = Z_to_bv 64 q -> 0 < q < 2 ^ 64 -> 16 <= S < 2 ^ 64 ->
  ov_read_bytes rsegs mem (wa (S - 8)) 8 = Some (le8 ra) ->
  Exec.evt rsegs
    (fun ms' => ms' = MS (mkR ra (Z_to_bv 64 S) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5) (reg_get regs 6)
                              (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (Z_to_bv 64 q) (reg_get regs 11)
                              (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15) (reg_get regs 16)
                              (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21)
                              (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
                              (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31))
                         fp_regs (ret_pc ra) fp_csr None mem ro)
    (canonical_register_state (YK11.mkst regs (Z_to_bv 64 0x14104) mem ro)).
Proof.
  intros fx regs mem ro S q ra E2 E10 Hq HS HR.
  rewrite canon_mkst. unfold mkR_of.
  apply bo_post_k; [exact E2 | exact E10 | exact Hq | exact HS | exact HR].
Qed.

Lemma eqv_mkst : forall {fx : YK11.FPState} (R : bvmap 5 word) (pc : word) (m ro : word -> option byte) ms',
  ms_eqv (MS R fp_regs pc fp_csr None m ro) ms' -> exists R', ms' = YK11.mkst R' pc m ro /\ xregs_eqv R R'.
Proof.
  intros fx R pc m ro [R' F' pc' svc' rv' fc' m' ro'] (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro).
  cbn in HF, Hpc, Hsvc, Hrv, Hfc, Hm, Hro. subst. exists R'. split; [reflexivity | exact HR].
Qed.

Lemma getr_x : forall (R R' : bvmap 5 word) (r : bv 5),
  xregs_eqv R R' -> is_x0 r = false -> YK11.getr R' r = reg_get R r.
Proof.
  intros R R' r H H0. unfold YK11.getr.
  match goal with |- (if ?b then _ else _) = _ => replace b with false by (symmetry; exact H0) end.
  symmetry. apply H. exact H0.
Qed.

Lemma ret_pc_ok : forall (k : word), YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H.
  assert (E : bv_unsigned k mod 2 = 0).
  { unfold YK0s.ret_ok, YK14.v_jalr, YK11.jalr_tgtZ in H. rewrite Z.add_0_r in H.
    apply (f_equal bv_unsigned) in H. rewrite Z_to_bv_unsigned in H.
    pose proof (Z.bit0_mod (Z.land (bv_unsigned k) (-2))) as B0.
    rewrite Z.land_spec in B0. change (Z.testbit (-2) 0) with false in B0. rewrite andb_false_r in B0.
    cbn [Z.b2z] in B0. change (bv_wrap 64 ?a) with (a mod 2 ^ 64) in H.
    rewrite <- H. Z.div_mod_to_equations. lia. }
  rewrite <- (Z_to_bv_bv_unsigned k). apply ret_pc_even; [apply bv_unsigned_in_range | exact E].
Qed.

Lemma wr_pt : forall (m : word -> option byte) (w : Z) (bs : list byte) (x : Z),
  0 <= w -> w + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x < w \/ w + Z.of_nat (length bs) <= x ->
  write_to_mem m (wa w) bs (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
  intros m w bs x H1 H2 H3 H4. rewrite write_to_mem_spec by lia. rewrite (unsigned_lit x) by lia.
  destruct (Z.leb_spec w x); destruct (Z.ltb_spec x (w + Z.of_nat (length bs))); cbn [andb];
    try reflexivity; exfalso; lia.
Qed.

Lemma mbyte_wr : forall segs (m : word -> option byte) (w : Z) (bs : list byte) (x : Z),
  0 <= w -> w + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x < w \/ w + Z.of_nat (length bs) <= x ->
  mbyte segs (write_to_mem m (wa w) bs) x = mbyte segs m x.
Proof. intros segs m w bs x H1 H2 H3 H4. unfold mbyte. rewrite wr_pt by assumption. reflexivity. Qed.

Lemma wv_wr : forall segs (m : word -> option byte) (w : Z) (bs : list byte) (x : Z),
  0 <= w -> w + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x < w \/ w + Z.of_nat (length bs) <= x ->
  (writable_at segs (write_to_mem m (wa w) bs) x <-> writable_at segs m x).
Proof.
  intros segs m w bs x H1 H2 H3 H4. unfold writable_at, RiscvSemantics.wview.
  rewrite wr_pt by assumption. tauto.
Qed.

Lemma present_wr : forall (m : word -> option byte) (w : Z) (bs : list byte) (a : Z),
  0 <= w -> w + Z.of_nat (length bs) <= 2 ^ 64 -> present m a -> present (write_to_mem m (wa w) bs) a.
Proof.
  intros m w bs a H1 H2 [v Hv]. unfold present. rewrite write_to_mem_spec by lia.
  match goal with |- exists _, (if ?c then _ else _) = _ => destruct c eqn:E end.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    match goal with |- exists _, ?t = _ => destruct t eqn:N end; [eexists; reflexivity|].
    apply nth_error_None in N. lia.
  - exists v. exact Hv.
Qed.

Lemma fs_bound : forall (l : list Segment) (x n : Z) s, find_segment l x n = Some s ->
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 2 ^ 40) l = true -> x + n <= 2 ^ 40.
Proof.
  induction l as [|s0 l IH]; intros x n s E F; cbn [find_segment] in E; [discriminate|].
  cbv zeta in E. cbn [forallb] in F. apply andb_prop in F as [F1 F2]. apply Z.leb_le in F1.
  revert E. match goal with |- (if ?k then _ else _) = _ -> _ => destruct k eqn:C end; intros E.
  - apply andb_prop in C as [_ C2]. apply Z.leb_le in C2. lia.
  - exact (IH x n s E F2).
Qed.

Lemma ro_hi : forall a : word, 2 ^ 40 <= bv_unsigned a -> Mem.ro_addr rsegs a = false.
Proof.
  intros a H. unfold Mem.ro_addr.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (fs_bound rsegs (bv_unsigned a) 1 s E ltac:(vm_compute; reflexivity)). lia.
Qed.

Lemma mrd_wr : forall segs (m : word -> option byte) (w : Z) (bs : list byte) (x : word),
  0 <= w -> w + Z.of_nat (length bs) <= 2 ^ 64 -> bv_unsigned x < w \/ w + Z.of_nat (length bs) <= bv_unsigned x ->
  Mem.mrd segs (write_to_mem m (wa w) bs) x = Mem.mrd segs m x.
Proof.
  intros segs m w bs x H1 H2 H3. unfold Mem.mrd. rewrite write_to_mem_spec by lia.
  destruct (Z.leb_spec w (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (w + Z.of_nat (length bs)));
    cbn [andb]; try reflexivity; exfalso; lia.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RzCi : RzC}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {RzAi : RzA B API}.

Lemma img_lt : ms_segs B = rsegs -> forall a, in_img B a -> 0 <= a < 2 ^ 40.
Proof.
  intros SEG a Ha. unfold in_img in Ha. destruct Ha as [_ (s & Hin & Ha)]. rewrite SEG in Hin.
  assert (H : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 2 ^ 40) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H s Hin). apply Z.leb_le in H.
  pose proof (bv_unsigned_in_range 64 (fst s)). lia.
Qed.

Lemma evt_seg : forall (Q : machine_state -> Prop) ms, ms_segs B = rsegs -> Exec.evt rsegs Q ms -> Exec.evt (ms_segs B) Q ms.
Proof. intros Q ms E H. rewrite E. exact H. Qed.

Theorem buf_of_holds : buf_of_contract B API.
Proof.
  unfold buf_of_contract, BUF_OF, MALLOC, BUF_OF_FRAME.
  intros L A regs mem md c b SEG MAL ERR PRE HRO Ha0 Hc RES ROOM.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCE & H63 & HSTK & HTP & HERR & HAUX).
  pose proof alloc_ceiling_value as HAC.
  pose proof (mr_model B (aa_MR API) (aa_laws API) L A mem md HMR) as (Hh & Hlz & Hmat).
  unfold ALLOC_STACK in *.
  set (S := spZ regs) in *.
  assert (E2 : YK11.getr regs 2 = Z_to_bv 64 S) by (unfold S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
  assert (HST : store_ok rsegs mem (wa (S - 8)) 8 = true).
  { replace (S - 8) with (S - 16 + 8) by lia.
    apply (wr_at_store_ok rsegs mem (S - 16) 16 8 8%nat); [ | lia | lia].
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (HSTK (S - 16 + i) ltac:(lia)) as W. unfold writable_at in W. rewrite SEG in W. exact W. }
  eapply rz_evt_canon;
    [ apply evt_seg; [exact SEG | eapply bo_pre_c; [exact E2 | exact Ha0 | lia | lia | exact HST]]
    | exact Hh | exact Hlz | ].
  intros ms1 (can & (y10 & y11 & -> & Ey10) & EQ1).
  destruct (eqv_mkst _ _ _ _ _ EQ1) as (R1 & -> & XR1).
  set (mem1 := write_to_mem mem (wa (S - 8)) (le8 (reg_get regs 1))) in *.
  assert (G1 : YK11.getr R1 1 = Z_to_bv 64 0x14104) by (rewrite (getr_x _ _ 1 XR1) by reflexivity; reflexivity).
  assert (G2 : YK11.getr R1 2 = Z_to_bv 64 (S - 16)) by (rewrite (getr_x _ _ 2 XR1) by reflexivity; reflexivity).
  assert (G4 : YK11.getr R1 4 = YK11.getr regs 4) by (rewrite (getr_x _ _ 4 XR1) by reflexivity; reflexivity).
  assert (G10 : YK11.getr R1 10 = Z_to_bv 64 (Z.max c 1))
    by (rewrite (getr_x _ _ 10 XR1) by reflexivity; exact Ey10).
  assert (MB1 : forall x, 0 <= x < 2 ^ 64 -> x < S - 8 \/ S <= x -> mbyte (ms_segs B) mem1 x = mbyte (ms_segs B) mem x).
  { intros x Hx Ho. unfold mem1. apply mbyte_wr; rewrite ?length_le8; lia. }
  assert (WV1 : forall x, 0 <= x < 2 ^ 64 -> x < S - 8 \/ S <= x ->
     (writable_at (ms_segs B) mem1 x <-> writable_at (ms_segs B) mem x)).
  { intros x Hx Ho. unfold mem1. apply wv_wr; rewrite ?length_le8; lia. }
  assert (WM1 : forall x, writable_at (ms_segs B) mem x -> writable_at (ms_segs B) mem1 x).
  { intros x W. unfold mem1, writable_at in *. apply wview_write_mono. exact W. }
  assert (PR1 : forall a, present mem a -> present mem1 a).
  { intros a Hp. unfold mem1. apply present_wr; [lia | rewrite length_le8; lia | exact Hp]. }
  assert (MR1 : aa_MR API L A mem1 md).
  { apply (mr_frame B (aa_MR API) (aa_laws API) L A mem mem1 md md HMR).
    - intros a Ho. pose proof (mr_owned_low B _ (aa_laws API) L A mem md a HMR Ho). apply MB1; lia.
    - intros a _ Hp. apply PR1. exact Hp.
    - intros p n i Hin Hi. apply PR1. apply (proj1 (mr_blocks B _ (aa_laws API) L A mem md p n i HMR Hin Hi)).
    - reflexivity.
    - exact Hh.
    - exact Hlz.
    - exact Hmat. }
  assert (CP : call_pre B (aa_MR API) L A R1 mem1 md).
  { unfold call_pre, spZ. rewrite G2. rewrite (unsigned_lit (S - 16)) by lia. unfold ALLOC_STACK.
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite G1; apply ret_ok_even; reflexivity|].
    split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; apply WM1; apply HSTK; lia|].
    split; [rewrite G4; exact HTP|].
    split; [intros a Ha; apply WM1; apply HERR; exact Ha|].
    intros Hi. destruct (HAUX Hi) as (av & ar & W1 & W2 & W3 & W4 & Hv1 & Hv2 & Hr1 & Hr2 & Hl1 & Hl2).
    assert (HL8 : 0 <= ms_libc B + 8 /\ ms_libc B + 15 < YM05.alloc_ceiling).
    { assert (O1 : owned B L A (ms_libc B + 8)) by (unfold owned, static_owned; right; right; right; left; lia).
      assert (O2 : owned B L A (ms_libc B + 15)) by (unfold owned, static_owned; right; right; right; left; lia).
      pose proof (mr_owned_low B _ (aa_laws API) L A mem md _ HMR O1).
      pose proof (mr_owned_low B _ (aa_laws API) L A mem md _ HMR O2). lia. }
    unfold auxv_pre. exists av, ar.
    split; [intros k Hk; rewrite MB1 by lia; apply W1; exact Hk|].
    split; [intros j Hj k Hk; rewrite MB1 by lia; apply (W2 j Hj); exact Hk|].
    split; [intros k Hk; rewrite MB1 by lia; apply W3; exact Hk|].
    split; [intros k Hk; rewrite MB1 by lia; apply W4; exact Hk|].
    repeat split; lia. }
  assert (RO1 : ro_agree (ms_segs B) mem1).
  { intros a Hra. transitivity (Mem.mrd (ms_segs B) mem a); [|exact (HRO a Hra)].
    rewrite SEG in Hra.
    assert (Ha40 : bv_unsigned a < 2 ^ 40).
    { destruct (Z_lt_le_dec (bv_unsigned a) (2 ^ 40)) as [h|h]; [exact h|].
      rewrite (ro_hi a h) in Hra. discriminate. }
    unfold mem1. apply mrd_wr; rewrite ?length_le8; lia. }
  pose proof (rz_malloc L A R1 mem1 md (Z.max c 1) b CP RO1 G10 RES ROOM) as HM.
  rewrite MAL in HM.
  eapply rz_bind; [exact HM|].
  intros c2 (L' & A' & R2 & mem' & md' & q & -> & POST & Hq10 & Hq0 & Hq16 & FRESH & BLK & KEPT & RA' & GK & UB
    & INIT & LEN & RES').
  rewrite G1.
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & FR' & UB' & SC').
  pose proof (mr_model B _ (aa_laws API) L' A' mem' md' MR') as (Hh' & Hlz' & Hmat').
  pose proof FRESH as (Fq1 & Fq2 & _).
  assert (G2' : YK11.getr R2 2 = Z_to_bv 64 (S - 16)).
  { pose proof (RP' 2 ltac:(unfold callee_saved; lia)) as P2. etransitivity; [exact P2|]. exact G2. }
  assert (FR8 : forall x, S - 16 <= x < S ->
     mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem1 x /\
     (writable_at (ms_segs B) mem1 x <-> writable_at (ms_segs B) mem' x)).
  { intros x Hx. apply FR'.
    - left; lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) L A mem md x HMR Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) L' A' mem' md' x MR' Ho). lia.
    - unfold scratch_k, spZ. rewrite G2. rewrite (unsigned_lit (S - 16)) by lia. unfold ALLOC_STACK. lia.
    - intros []. }
  assert (BA : Mem.bytes_at rsegs mem' (S - 8) (le8 (reg_get regs 1))).
  { pose proof (bytes_at_write_same rsegs mem (S - 8) (le8 (reg_get regs 1)) ltac:(lia)
      ltac:(rewrite length_le8; lia)) as (W1 & W2 & W3).
    split; [lia|]. split; [exact W2|].
    intros i Hi. rewrite <- (W3 i Hi). rewrite length_le8 in Hi.
    change (mbyte rsegs mem' (S - 8 + Z.of_nat i) = mbyte rsegs mem1 (S - 8 + Z.of_nat i)).
    rewrite <- SEG. destruct (FR8 (S - 8 + Z.of_nat i) ltac:(lia)) as [F1 _]. exact F1. }
  assert (RD : ov_read_bytes rsegs mem' (wa (S - 8)) 8 = Some (le8 (reg_get regs 1))).
  { replace (wa (S - 8)) with (wa (S - 8 + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs mem' (S - 8) (le8 (reg_get regs 1)) 0 8%nat BA) by (rewrite ?length_le8; lia).
    change (Z.to_nat 0) with 0%nat. rewrite skipn_O. rewrite firstn_all2 by (rewrite length_le8; lia).
    reflexivity. }
  eapply rz_evt_canon;
    [ apply evt_seg; [exact SEG | eapply bo_post_c; [exact G2' | exact Hq10 | lia | lia | exact RD]]
    | exact Hh' | exact Hlz' | ].
  intros ms3 (can3 & -> & EQ3).
  destruct (eqv_mkst _ _ _ _ _ EQ3) as (R3 & -> & XR3).
  apply rz_ret.
  exists L', A', R3, mem', md', q.
  split; [rewrite (ret_pc_ok (reg_get regs 1) HRA); reflexivity|].
  split.
  { unfold call_post_k.
    split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact LL'|]. split; [exact PA'|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]];
        rewrite (getr_x _ _ _ XR3) by reflexivity;
        first
          [ symmetry; exact E2
          | match goal with |- _ = YK11.getr _ (Z_to_bv 5 ?k) =>
              transitivity (YK11.getr R2 (Z_to_bv 5 k)); [reflexivity|];
              rewrite (RP' k) by (unfold callee_saved; lia);
              rewrite (getr_x _ _ _ XR1) by reflexivity; reflexivity
            end ]. }
    split; [exists vm'; exact Emd|].
    split.
    { intros a Ha Ho Ho' Hs _.
      assert (Ha0' : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | apply (img_lt SEG) in Ha; lia]).
      unfold scratch_k in Hs. change (spZ regs) with S in Hs. unfold ALLOC_STACK in Hs.
      assert (Hs' : ~ scratch_k B ALLOC_STACK R1 a).
      { unfold scratch_k, spZ. rewrite G2. rewrite (unsigned_lit (S - 16)) by lia. unfold ALLOC_STACK. lia. }
      assert (Hout : a < S - 8 \/ S <= a) by lia.
      destruct (FR' a Ha Ho Ho' Hs' (fun x => x)) as [F1 F2].
      pose proof (WV1 a Ha0' Hout) as F3.
      split; [rewrite F1; apply MB1; assumption | tauto]. }
    split.
    { intros p n i Hin Hin' Hi. rewrite (UB' p n i Hin Hin' Hi).
      pose proof (mr_blocks B _ (aa_laws API) L A mem md p n i HMR Hin Hi) as (_ & Hb1 & Hb2 & _).
      apply MB1; lia. }
    intros a Ha. unfold scratch_k in Ha. change (spZ regs) with S in Ha. unfold ALLOC_STACK in Ha.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_le_dec a (S - 16)) as [Hlt|Hge].
      + apply SC'. unfold scratch_k, spZ. rewrite G2. rewrite (unsigned_lit (S - 16)) by lia. left. unfold ALLOC_STACK. lia.
      + destruct (FR8 a ltac:(lia)) as [_ W]. apply W. apply WM1. apply HSTK. lia.
    - apply SC'. unfold scratch_k. right. exact Ha. }
  split; [rewrite (getr_x _ _ 10 XR3) by reflexivity; reflexivity|].
  split; [exact Hq0|]. split; [exact Hq16|]. split; [exact FRESH|]. split; [exact BLK|].
  split.
  { intros a k i Hin Hg Hi. rewrite (KEPT a k i Hin Hg Hi).
    unfold blocks in Hin. apply in_map_iff in Hin. destruct Hin as ([p k'] & Ep & Hin). cbn [fst snd] in Ep.
    injection Ep as Ea Ek. subst a k'.
    pose proof (mr_blocks_range B _ (aa_laws API) L A mem md p k HMR Hin) as (Hb1 & Hb2).
    apply MB1; lia. }
  split; [exact RA'|].
  split.
  { unfold guard_kept in GK |- *. intros i Hi. rewrite (GK i Hi).
    assert (Og : owned B L A (ms_got_guard B + i))
      by (unfold owned, static_owned; right; right; right; right; right; left; lia).
    pose proof (mr_owned_low B _ (aa_laws API) L A mem md _ HMR Og). apply MB1; lia. }
  split; [exact UB|]. split; [exact INIT|]. split; [exact LEN|]. exact RES'.
Qed.

End P.
