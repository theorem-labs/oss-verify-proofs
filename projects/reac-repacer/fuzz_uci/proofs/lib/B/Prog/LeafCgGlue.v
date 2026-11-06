(* Modified by Theorem Labs: copied from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/B/Prog/LeafCgGlue.v at recipes commit 88154566652a310ff96f54a5442e5c73fdaad090 (a recipes commit newer than the unit's base 25e3d17bdb50) for reac-repacer/fuzz_uci; module path OSSVerify.Proofs.reac_repacer.fuzz_uci.lib. *)
(* LeafCgGlue: proof of the ONE generic leaf translation of decode image B's shared leaf kit (LeafCgKit.v):
   a footprint run of a leaf (ExecF.evtF at the call state, its post read off the return state) gives the cgif_file
   leaf obligation (SRr world walk to dleaf_post / dleaf_post_fx). Port of fuzz_decode to the released
   cgif_file_fuzzer structure (the port recipe, sec. 3); no function body
   is proved here.
   * Start state: the footprint run starts at the kit's ms_of_regs (decode's MS / mkR form), the SRr goal at cgif's
     cfg_at (YK11.mkst): they are register-equivalent (Regs6ss.ms_eqv), and a footprint run moves across ms_eqv with
     the same accesses (mstepsF_eqv, the footprint form of decode's RegisterBridge.msteps_register_transport).
   * The run then enters the world walk through the kit's bridge_evtF_stmt (cgif YA0nR.v SRr_fevt) at RNG_W W, and
     returns through SRr_ret_stmt (cgif YA0n.v:39 SRr_ret).
   * Post: AR by AR_frame_stmt (YG0d.v:437) + AR_stack_stmt + AR_sbm_stmt (A/AD1y.v:139); the bytes the leaf may
     write are visible (stack window: ecall_pre's apresent; WR: the premise) and present after the run (stack
     window: every run grows memory, YI04.v step_mem_grows; WR: mrd outside the image is the overlay byte);
     aview through aview_ext_stmt / aview_some_stmt; the return pc through ret_ok_stmt.
   Section Hypotheses: the kit facts bridge_evtF_stmt, SRr_ret_stmt, AR_frame_stmt, AR_stack_stmt, AR_sbm_stmt,
   aview_ext_stmt, aview_some_stmt, ret_ok_stmt. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YK1b YI04.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require ExecF PropExec Regs6ss.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.B.Prog Require Import LeafCgKit.
Import ListNotations.
Open Scope Z_scope.

(* ---- footprint runs move across register equivalence (Regs6ss.step_accesses_eqv) and grow memory ---- *)
Lemma mstepsF_eqv : forall segs RNG ms1 ms1', ExecF.mstepsF segs RNG ms1 ms1' ->
  forall ms2, Regs6ss.ms_eqv ms1 ms2 ->
  exists ms2', ExecF.mstepsF segs RNG ms2 ms2' /\ Regs6ss.ms_eqv ms1' ms2'.
Proof.
  intros segs RNG ms1 ms1' HT. induction HT as [m|m m1 m2 HS HT IH]; intros ms2 HE.
  - exists ms2. split; [apply ExecF.mstepsF_refl|exact HE].
  - destruct HS as (Hsvc & accs & Hstep & Hacc).
    pose proof (Regs6ss.step_accesses_eqv segs m ms2 HE) as Hrep.
    rewrite Hstep in Hrep.
    destruct (RiscvSemantics.step_accesses segs ms2) as [[msb accs']| |] eqn:Hstep2; cbn in Hrep;
      try contradiction.
    destruct Hrep as (Hab & Haccs).
    destruct (IH msb Hab) as (ms3 & HT' & HE').
    exists ms3. split; [|exact HE'].
    apply (ExecF.mstepsF_cons segs RNG ms2 msb ms3); [|exact HT'].
    pose proof HE as (HEr & HEf & HEpc & HEsvc & HErest).
    split; [rewrite <- HEsvc; exact Hsvc|].
    exists accs'. split; [exact Hstep2|]. rewrite <- Haccs. exact Hacc.
Qed.

Lemma mstepsF_grows : forall segs RNG ms ms', ExecF.mstepsF segs RNG ms ms' ->
  YK1b.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros segs RNG ms ms' HT. induction HT as [m|m m1 m2 HS HT IH].
  - apply YK1b.mem_grows_refl.
  - eapply YK1b.mem_grows_trans; [|exact IH].
    eapply YI04.step_mem_grows. exact (ExecF.mstepF_step segs RNG m m1 HS).
Qed.

Lemma evtF_eqv : forall segs RNG (P : machine_state -> Prop) ms1 ms2,
  ExecF.evtF segs RNG P ms1 -> Regs6ss.ms_eqv ms1 ms2 ->
  ExecF.evtF segs RNG
    (fun ms2' => exists ms1', P ms1' /\ Regs6ss.ms_eqv ms1' ms2' /\ YK1b.mem_grows (ms_mem ms1) (ms_mem ms1'))
    ms2.
Proof.
  intros segs RNG P ms1 ms2 (ms1' & HT & HP) HE.
  destruct (mstepsF_eqv segs RNG ms1 ms1' HT ms2 HE) as (ms2' & HT' & HE').
  exists ms2'. split; [exact HT'|]. exists ms1'. split; [exact HP|]. split; [exact HE'|].
  exact (mstepsF_grows segs RNG ms1 ms1' HT).
Qed.

(* ---- the return state: decode's MS form, register-equivalent, is a cgif mkst (decode's lf_eqv_mkst) ---- *)
Lemma eqv_MS_mkst : forall R F pc fc m ro ms,
  Regs6ss.ms_eqv (MS R F pc fc None m ro) ms ->
  exists R', ms = @YK11.mkst (YK11.mkFP F fc) R' pc m ro /\ Regs6ss.xregs_eqv R R'.
Proof.
  intros R F pc fc m ro [r f p s v c mm rr] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn in *. subst. exists r. split; [reflexivity|exact H1].
Qed.

Lemma getr_xeqv : forall R R', Regs6ss.xregs_eqv R R' -> forall r, YK11.getr R' r = YK11.getr R r.
Proof.
  intros R R' H r. unfold YK11.getr. rewrite !YK11.bv_eqb0_is_x0.
  destruct (is_x0 r) eqn:E; [reflexivity|]. symmetry. apply H. exact E.
Qed.

Section Eqv.
Context {fx : YK11.FPState}.
(* The footprint run's start state and the cgif call state are register-equivalent. *)
Lemma ms_of_regs_eqv : forall (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte),
  Regs6ss.ms_eqv (ms_of_regs pc regs mem) (YK11.mkst regs (w64 pc) mem (YK11.seg_rom rsegs)).
Proof.
  intros pc regs mem. split; [|repeat split].
  intros r Hr. destruct (Regs6ss.reg_of_nat r) as (n & -> & Hn).
  destruct n as [|n]; [cbv in Hr; discriminate|].
  do 31 (destruct n as [|n]; [reflexivity|]). lia.
Qed.
End Eqv.

(* ---- the written ranges ---- *)
Lemma not_in_wr_outside : forall WR x, ~ in_wr WR x -> outside WR x.
Proof.
  unfold in_wr. induction WR as [|[lo hi] WR IH]; intros x Hn; cbn [outside]; [exact I|].
  split.
  - intros Hin. apply Hn. apply Exists_cons_hd. exact Hin.
  - apply IH. intros Hw. apply Hn. apply Exists_cons_tl. exact Hw.
Qed.

Lemma in_wr_dec : forall WR x, in_wr WR x \/ ~ in_wr WR x.
Proof.
  intros WR x. unfold in_wr. induction WR as [|[lo hi] WR IH].
  - right. intros Hc. inversion Hc.
  - destruct IH as [Hw|Hw]; [left; apply Exists_cons_tl; exact Hw|].
    destruct (Z_le_gt_dec lo x) as [H1|H1].
    + destruct (Z_lt_ge_dec x hi) as [H2|H2].
      * left. apply Exists_cons_hd. cbn [fst snd]. lia.
      * right. intros Hc. inversion Hc; subst; cbn [fst snd] in *; [lia|contradiction].
    + right. intros Hc. inversion Hc; subst; cbn [fst snd] in *; [lia|contradiction].
Qed.

Lemma in_win_dec : forall lo hi WR x, (lo <= x < hi \/ in_wr WR x) \/ ~ (lo <= x < hi \/ in_wr WR x).
Proof.
  intros lo hi WR x. destruct (in_wr_dec WR x) as [Hw|Hw]; [left; right; exact Hw|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - left. left. lia.
  - right. intros [Hc|Hc]; [lia|exact (Hw Hc)].
  - right. intros [Hc|Hc]; [lia|exact (Hw Hc)].
Qed.

Lemma outside_cons_of : forall lo hi WR x, ~ (lo <= x < hi \/ in_wr WR x) -> outside ((lo, hi) :: WR) x.
Proof.
  intros lo hi WR x Hn. cbn [outside]. split.
  - intros Hc. apply Hn. left. exact Hc.
  - apply not_in_wr_outside. intros Hc. apply Hn. right. exact Hc.
Qed.

(* ---- outside the image, mrd reads the overlay ---- *)
Lemma find_segment_out : forall (sl : list Segment) a n, 0 < n ->
  (forall sg, In sg sl -> ~ (Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) ->
  find_segment sl a n = None.
Proof.
  induction sl as [|sg rest IH]; intros a n Hn Hout; cbn [find_segment]; [reflexivity|].
  assert (Hrest : forall sg', In sg' rest ->
    ~ (Z.of_N (seg_base sg') <= a < Z.of_N (seg_base sg') + Z.of_N (seg_size sg'))).
  { intros sg' Hin. apply Hout. right. exact Hin. }
  pose proof (Hout sg (or_introl eq_refl)) as Hsg.
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) a); cbn [andb];
  [ destruct (Z.leb_spec (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)));
    [exfalso; apply Hsg; lia|] |];
  apply IH; [exact Hn|exact Hrest|exact Hn|exact Hrest].
Qed.

Lemma seg_rom_out_img : forall a : word, ~ in_img (bv_unsigned a) -> PropExec.seg_rom rsegs a = None.
Proof.
  intros a Hn. unfold PropExec.seg_rom, memory_read.
  rewrite (find_segment_out rsegs (bv_unsigned a) (Z.of_N 1)); [reflexivity|lia|].
  intros sg Hin Hr. apply Hn. exists sg. split; [exact Hin|exact Hr].
Qed.

Lemma mem_of_mrd : forall m (a : word), ~ in_img (bv_unsigned a) ->
  (exists b, mrd rsegs m a = Some b) -> m a <> None.
Proof.
  intros m a Hn (b & Hb) Hm. unfold mrd in Hb. rewrite Hm in Hb.
  rewrite (seg_rom_out_img a Hn) in Hb. cbv iota in Hb. discriminate Hb.
Qed.

Section LeafCgGlue.
Context {fx : YK11.FPState}.
Variable world : Type.                                                (* YA0n.v:17 *)
Variable w_H : world -> word -> bool.                                 (* YA0n.v:18 *)
Variable SRr : world -> config -> (world -> config -> Prop) -> Prop.    (* YA0n.v:34 *)
Variable alayout : Type.                                              (* YG0f.v:42 *)
Variable astate : Type.                                               (* YG00.v:153 *)
Variable AR : alayout -> astate -> world -> (word -> option byte) -> Model -> Prop.  (* YG0n.v:489 *)
Variable aview : (word -> bool) -> (word -> option byte) -> Z -> option Z.          (* YG0n.v:17 *)
Variable same_but_materialized : Model -> Model -> Prop.              (* YK04.v:538 *)
Variable ly_stk_lo ly_stk_hi : alayout -> Z.                          (* YG0f.v *)
Variable ret_ok : word -> Prop.                                       (* YK0s.v:192 *)
Variable as_gp as_tp : Z.                                             (* asyms B *)
Variable aowned : alayout -> astate -> Z -> Prop.                     (* YG0n.v:235 *)
(* The kit's definitions and facts at these names (LeafCgKit.v; argument order = the kit's Section order). *)
Let ecall_pre := @LeafCgKit.ecall_pre world w_H alayout astate AR ly_stk_lo ly_stk_hi ret_ok as_gp as_tp.
Let RNG_W := @LeafCgKit.RNG_W world w_H.
Let dleaf_post := @LeafCgKit.dleaf_post fx world w_H alayout astate AR aview same_but_materialized.
Let dleaf_post_fx := @LeafCgKit.dleaf_post_fx fx world w_H alayout astate AR aview same_but_materialized.
Let bridge_evtF_stmt := @LeafCgKit.bridge_evtF_stmt world w_H SRr same_but_materialized.
Let SRr_ret_stmt := @LeafCgKit.SRr_ret_stmt world SRr.
Let AR_frame_stmt := @LeafCgKit.AR_frame_stmt world w_H alayout astate AR aview aowned.
Let AR_stack_stmt := @LeafCgKit.AR_stack_stmt world alayout astate AR ly_stk_lo ly_stk_hi aowned.
Let AR_sbm_stmt := @LeafCgKit.AR_sbm_stmt world alayout astate AR same_but_materialized.
Let aview_ext_stmt := @LeafCgKit.aview_ext_stmt aview.
Let aview_some_stmt := @LeafCgKit.aview_some_stmt aview.
Let ret_ok_stmt := @LeafCgKit.ret_ok_stmt ret_ok.
Let leaf_cg_of_evtF_stmt := @LeafCgKit.leaf_cg_of_evtF_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.
Let leaf_cg_of_evtF_fx_stmt := @LeafCgKit.leaf_cg_of_evtF_fx_stmt fx world w_H SRr alayout astate AR aview
  same_but_materialized ly_stk_lo ly_stk_hi ret_ok as_gp as_tp aowned.

Hypothesis BRIDGE : bridge_evtF_stmt.
Hypothesis SRRET : SRr_ret_stmt.
Hypothesis ARFRAME : AR_frame_stmt.
Hypothesis ARSTACK : AR_stack_stmt.
Hypothesis ARSBM : AR_sbm_stmt.
Hypothesis AVEXT : aview_ext_stmt.
Hypothesis AVSOME : aview_some_stmt.
Hypothesis RETOK : ret_ok_stmt.

(* RNG_W W avoids the hidden bytes by its definition. *)
Lemma fp_avoids_RNG_W : forall W, fp_avoids (w_H W) (RNG_W W).
Proof.
  intros W a n Ha. unfold RNG_W, LeafCgKit.RNG_W in Ha. rewrite MState.Z_to_bv_bv_unsigned in Ha. exact Ha.
Qed.

(* The memory part of the leaf post (shared by dleaf_post and dleaf_post_fx). *)
Lemma dleaf_mem_post : forall ly S W regs mem md md' mem' (K : Z) (WR : list (Z * Z)),
  ecall_pre ly S W regs mem md -> 0 <= K <= ESTACK ->
  (forall x, in_wr WR x -> 0 <= x < 2 ^ 64 /\ w_H W (Z_to_bv 64 x) = false /\ ~ aowned ly S x /\ ~ in_img x) ->
  YK1b.mem_grows mem mem' ->
  munch ((spZ regs - K, spZ regs) :: WR) mem mem' ->
  (forall x, (spZ regs - K <= x < spZ regs \/ in_wr WR x) -> exists b, mrd rsegs mem' (Z_to_bv 64 x) = Some b) ->
  same_but_materialized md md' ->
  AR ly S W mem' md' /\
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - ESTACK <= x < spZ regs) -> ~ in_wr WR x ->
     aview (w_H W) mem' x = aview (w_H W) mem x) /\
  (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).
Proof.
  intros ly S W regs mem md md' mem' K WR HPRE HK HWR HG HMUNCH HPRES Hsbm.
  pose proof HPRE as (HAR & HRA & HAL & HLO & HHI & HSTK & HGPTP).
  (* every byte the leaf may write is visible, and present after the run *)
  assert (HVIS : forall x, (spZ regs - K <= x < spZ regs \/ in_wr WR x) -> w_H W (Z_to_bv 64 x) = false).
  { intros x [Hx|Hx].
    - assert (Hx' : spZ regs - ESTACK <= x < spZ regs) by lia.
      destruct (HSTK x Hx') as (HxH & HxB). exact HxH.
    - destruct (HWR x Hx) as (Hxr & HxH & Hxo & Hxi). exact HxH. }
  assert (HRAW : forall x, (spZ regs - K <= x < spZ regs \/ in_wr WR x) -> mem' (Z_to_bv 64 x) <> None).
  { intros x Hin. destruct Hin as [Hx|Hx].
    - assert (Hx' : spZ regs - ESTACK <= x < spZ regs) by lia.
      destruct (HSTK x Hx') as (HxH & b & Hb).
      refine (HG (Z_to_bv 64 x) _). rewrite Hb. discriminate.
    - destruct (HWR x Hx) as (Hxr & HxH & Hxo & Hxi).
      apply mem_of_mrd; [rewrite (MState.unsigned_lit x Hxr); exact Hxi|].
      apply HPRES. right. exact Hx. }
  split; [|split].
  - apply (ARSBM ly S W mem' md md'); [|exact Hsbm].
    apply (ARFRAME ly S W mem md mem' HAR).
    + intros a Ha Hown. apply AVEXT. apply HMUNCH. rewrite MState.unsigned_lit by exact Ha.
      apply outside_cons_of. intros [Hs|Hw].
      * apply (ARSTACK ly S W mem md a HAR); [lia|exact Hown].
      * destruct (HWR a Hw) as (Har & HaH & Hao & Hai). exact (Hao Hown).
    + intros a Hv.
      destruct (in_win_dec (spZ regs - K) (spZ regs) WR (bv_unsigned (Z_to_bv 64 a))) as [Hin|Hout].
      * apply AVSOME.
        -- rewrite <- (MState.Z_to_bv_bv_unsigned (Z_to_bv 64 a)). exact (HVIS _ Hin).
        -- rewrite <- (MState.Z_to_bv_bv_unsigned (Z_to_bv 64 a)). exact (HRAW _ Hin).
      * rewrite (AVEXT (w_H W) mem mem' a); [exact Hv|].
        apply HMUNCH. apply outside_cons_of. exact Hout.
    + intros a Hh. apply HMUNCH. apply outside_cons_of. intros Hin.
      pose proof (HVIS _ Hin) as Hf. rewrite MState.Z_to_bv_bv_unsigned in Hf. congruence.
  - intros x Hx Hne Hnw. apply AVEXT. apply HMUNCH. rewrite MState.unsigned_lit by exact Hx.
    apply outside_cons_of. intros [Hs|Hw]; [apply Hne; lia|exact (Hnw Hw)].
  - intros x (HxH & b & Hb). split; [exact HxH|].
    destruct (mem' (Z_to_bv 64 x)) as [b'|] eqn:Hb'; [exists b'; reflexivity|].
    exfalso. refine (HG (Z_to_bv 64 x) _ Hb'). rewrite Hb. discriminate.
Qed.

Lemma leaf_cg_of_evtF : leaf_cg_of_evtF_stmt.
Proof.
  intros ly S W regs mem md PC K P WR RES X HPRE HK HWR HRUN HPOST.
  pose proof HPRE as (HAR & HRA & HSP).
  pose proof (evtF_eqv rsegs (RNG_W W) P _ _ HRUN (ms_of_regs_eqv PC regs mem)) as HRUN'.
  apply (BRIDGE W (YK11.mkst regs (w64 PC) mem (YK11.seg_rom rsegs)) md (RNG_W W) _ _ HRUN').
  - exact (fp_avoids_RNG_W W).
  - intros ms2 md' (ms1 & HP & HE & HG) Hsbm.
    destruct (HPOST ms1 HP) as (regs' & mem' & Hms1 & HMUNCH & HPRES & HAREGS & HRES & HX).
    subst ms1.
    destruct (eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R2 & Hms2 & HXR). subst ms2.
    destruct (dleaf_mem_post ly S W regs mem md md' mem' K WR HPRE HK HWR HG HMUNCH HPRES Hsbm)
      as (HAR' & HVIEW & HPRESENT).
    apply SRRET. split; [reflexivity|].
    exists R2, mem', md'.
    refine (conj _ (conj HAR' (conj _ (conj Hsbm (conj _ (conj HVIEW (conj HPRESENT HX))))))).
    + unfold cfg_at, raZ, w64. rewrite MState.Z_to_bv_bv_unsigned, (RETOK _ HRA). reflexivity.
    + intros r Hr. rewrite (getr_xeqv _ _ HXR). exact (HAREGS r Hr).
    + intros r Hr. rewrite (getr_xeqv _ _ HXR). exact (HRES r Hr).
Qed.

Lemma leaf_cg_of_evtF_fx : leaf_cg_of_evtF_fx_stmt.
Proof.
  intros ly S W regs mem md PC K P WR X HPRE HK HWR HRUN HPOST.
  pose proof HPRE as (HAR & HRA & HSP).
  pose proof (evtF_eqv rsegs (RNG_W W) P _ _ HRUN (ms_of_regs_eqv PC regs mem)) as HRUN'.
  apply (BRIDGE W (YK11.mkst regs (w64 PC) mem (YK11.seg_rom rsegs)) md (RNG_W W) _ _ HRUN').
  - exact (fp_avoids_RNG_W W).
  - intros ms2 md' (ms1 & HP & HE & HG) Hsbm.
    destruct (HPOST ms1 HP) as (regs' & F' & mem' & Hms1 & HF & HMUNCH & HPRES & HAREGS & HX).
    subst ms1.
    destruct (eqv_MS_mkst _ _ _ _ _ _ _ HE) as (R2 & Hms2 & HXR). subst ms2.
    destruct (dleaf_mem_post ly S W regs mem md md' mem' K WR HPRE HK HWR HG HMUNCH HPRES Hsbm)
      as (HAR' & HVIEW & HPRESENT).
    apply SRRET. split; [reflexivity|].
    exists (YK11.mkFP F' fp_csr), R2, mem', md'.
    refine (conj _ (conj eq_refl (conj HF (conj HAR' (conj _ (conj Hsbm (conj HVIEW (conj HPRESENT HX)))))))).
    + unfold raZ, w64. rewrite MState.Z_to_bv_bv_unsigned, (RETOK _ HRA). reflexivity.
    + intros r Hr. rewrite (getr_xeqv _ _ HXR). exact (HAREGS r Hr).
Qed.

End LeafCgGlue.
