(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_strtoll F_twoway_A F_twoway_C
     H_httpmsg_compare H_ListFind H_list_access H_ListAddTail H_obj H_prep H_phdr_A H_httpheader_free H_UpnpPrintf HU_list_kit HU_raw_find_str.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Definition germ_entry := 0x15360%Z.
Definition GERM_DEPTH : Z := 2432.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).

  Definition blk_img_ok : Prop := forall s LB m (b : BLK), RHEAP rsegs AI s LB m -> In b LB ->
    blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b.

  Definition germ_W (lo sp P tpe : Z) (hs : list hdr) : list (Z * Z) :=
    (lo, sp) :: (P + 384, P + 400) :: (P + 440, P + 480) :: (tpe, tpe + 4)
    :: map (fun h => (vA AI h, vA AI h + (vcap AI h + 1))) hs.

  Definition germ_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X A cur err hack pos entp csz lo : Z) (canary : word) (m : mem)
      : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r err' hack' pos' entp' clen' : Z) (errv' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ munch (germ_W lo (bv_unsigned sp) P (bv_unsigned tp - 164) hs) m m'
      /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ stk rsegs m' lo (bv_unsigned sp)
      /\ p_ent m' P (Z_to_bv 64 (A + cur)) (Z_to_bv 64 0)
      /\ p_ctl m' P err' hack' pos' entp' clen' csz cur
      /\ p_hlist AI m' P ns hs X
      /\ rw_cells rsegs m' (bv_unsigned tp - 164) [C4 errv']
      /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary]
      /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)]
      /\ ( (r = 0 /\ pos' = POS_COMPLETE /\ entp' = entp /\ err' = err /\ hack' = hack)
        \/ (r = 6 /\ pos' = pos /\ 2 <= entp' <= 4 /\ err' = err /\ hack' = hack)
        \/ (r = 3 /\ pos' = pos /\ entp' = entp /\ err' = 411)).

  Definition germ_stmt : Prop :=
    forall (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X A len cap cur : Z) (okm : option K) (bs : list byte)
           (meth isreq maj min rm sc err hack pos entp clen csz esp : Z) (eb el errv canary : word)
           (s : ai_PS rsegs AI) (LB : list BLK) (lo : Z)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      blk4096_ok AI -> blk_img_ok ->
      RHEAP rsegs AI s LB m -> bsub AI (hl_blocks AI ns hs) LB -> NoDup (map blk_id (hl_blocks AI ns hs)) ->
      p_meth m P meth -> p_rs m P rm sc -> p_ver m P isreq maj min ->
      p_hlist AI m P ns hs X -> X <= VMAX ->
      p_ent m P eb el -> p_msg AI m LB P A len cap okm bs -> p_ctl m P err hack pos entp clen csz esp -> p_scan m P cur ->
      0 <= cur <= len ->
      rw_cells rsegs m (bv_unsigned tp - 164) [C4 errv] ->
      rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
      rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] ->
      stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - GERM_DEPTH ->
      mem_inv rsegs m ->

      bv_unsigned sp <= P -> P + 504 <= 2^62 ->
      4096 + 164 <= bv_unsigned tp -> bv_unsigned tp - 164 + 4 <= lo ->
      (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164) ->
      (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164) ->
      (bv_unsigned tp - 164 + 4 <= INITWASCALLED \/ INITWASCALLED + 1 <= bv_unsigned tp - 164) ->
      0x2a000 <= bv_unsigned tp - 164 -> bv_unsigned tp - 164 + 4 <= 0x5d000 ->
      P mod 8 = 0 -> bv_unsigned sp mod 8 = 0 -> (bv_unsigned tp - 164) mod 4 = 0 ->
      a0 = Z_to_bv 64 P ->
      evt rsegs (germ_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ns hs X A cur err hack pos entp csz lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 germ_entry) fc None m (seg_rom rsegs)).
End W.

Ltac sstep := step; fix_lit_store.
Ltac pg := match goal with |- ?G => idtac G end.
Definition hide (P : Prop) := P.
Inductive hbox (P : Prop) : Prop := hbox_in : P -> hbox P.

Lemma rw_CB_len : forall m A n bs, rw_cells rsegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[W _] _]. cbn in W. LiaTuning.ctauto. Qed.

Lemma nul_split : forall (l1 l2 : list byte), exists s r, l1 ++ Z_to_bv 8 0 :: l2 = s ++ Z_to_bv 8 0 :: r /\ ~ In (Z_to_bv 8 0) s /\ (length s <= length l1)%nat.
Proof.
  induction l1 as [|a l1 IH]; intros l2.
  - exists [], l2. cbn. repeat split; [LiaTuning.ctauto| lia].
  - destruct (Z.eq_dec (bv_unsigned a) 0) as [E|NE].
    + exists [], (l1 ++ Z_to_bv 8 0 :: l2). assert (a = Z_to_bv 8 0) as -> by (apply bv_eq; rewrite E; reflexivity).
      cbn. repeat split; [LiaTuning.ctauto| lia].
    + destruct (IH l2) as (s & r & E & NI & L). exists (a :: s), r. cbn. rewrite E. repeat split; [| cbn in *; lia].
      intros [H|H]; [| exact (NI H)]. apply NE. subst a. reflexivity.
Qed.

Ltac post_callq segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PC" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  lazymatch goal with QSP : bv_unsigned (Z_to_bv 64 _) = _ |- _ => try rewrite !QSP in MUc; try rewrite !QSP in PO end;
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callq" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callq segs m ]
  end.

Section WALK.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Variables (P : Z) (ns : list (BLK * Z)) (hs : list hdr) (X A len cap cur : Z) (okm : option K) (bs : list byte).
  Variables (meth isreq maj min rm sc err hack pos entp clen csz esp : Z) (eb el canary : word).
  Variables (s : ai_PS rsegs AI) (LB : list BLK) (lo : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis B4096 : blk4096_ok AI.
  Hypothesis BIMG : blk_img_ok AI.
  Hypothesis HR0 : RHEAP rsegs AI s LB m0.
  Hypothesis BSUB : bsub AI (hl_blocks AI ns hs) LB.
  Hypothesis ND : NoDup (map blk_id (hl_blocks AI ns hs)).
  Hypothesis XV : X <= VMAX.
  Hypothesis CUR : 0 <= cur <= len.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOD : lo <= bv_unsigned sp - GERM_DEPTH.
  Hypothesis PSP : bv_unsigned sp <= P.
  Hypothesis PHI : P + 504 <= 2^62.
  Hypothesis TP1 : hbox (4096 + 164 <= bv_unsigned tp).
  Hypothesis TP2 : bv_unsigned tp - 164 + 4 <= lo.
  Hypothesis DE1 : bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164.
  Hypothesis DE2 : bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164.
  Hypothesis DE3 : bv_unsigned tp - 164 + 4 <= INITWASCALLED \/ INITWASCALLED + 1 <= bv_unsigned tp - 164.

  Hypothesis TPW1 : 0x2a000 <= bv_unsigned tp - 164.
  Hypothesis TPW2 : bv_unsigned tp - 164 + 4 <= 0x5d000.
  Hypothesis PA8 : hbox (P mod 8 = 0).
  Hypothesis SPA : hbox (bv_unsigned sp mod 8 = 0).
  Hypothesis TPA : hbox ((bv_unsigned tp - 164) mod 4 = 0).

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -144)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -144)).
  Notation TPE := (bv_unsigned tp - 164)%Z.

  Notation Wc := [(lo, bv_unsigned sp); (P + 384, P + 400); (P + 440, P + 480); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation GW := (germ_W AI lo (bv_unsigned sp) P (bv_unsigned tp - 164) hs).
  Notation POST := (germ_post AI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P ns hs X A cur err hack pos entp csz lo canary m0).

  Notation FRB m := (rw_cells rsegs m (q + 112) [C8 s2; C8 s1; C8 s0; C8 ra]).

  #[using="All"] Lemma sp_facts : lo + 2432 <= SP /\ 2432 + 4096 <= SP /\ SP + 504 <= 2^62 /\ (0x7FFF7F800000 <= alloc_ceiling <= 0x7FFFFF800000 /\ alloc_ceiling mod 8 = 0).
  Proof. clear -LOC LOD PSP PHI HCEIL. unfold GERM_DEPTH in LOD. pose proof alloc_ceiling_bounds. pose proof alloc_ceiling_aligned8. lia. Qed.
  #[using="All"] Lemma q_sp : bv_unsigned spw = q.
  Proof. pose proof sp_facts as SFq. apply unsigned_lit. clear -SFq. lia. Qed.

  #[using="All"] Lemma GW_of_Wc : forall m1 m2, munch GW m0 m1 -> munch Wc m1 m2 -> munch GW m0 m2.
  Proof.
    intros m1 m2 A1 B. eapply munch_trans; [exact A1|]. eapply munch_weaken; [| exact B].
    intros x Hx. unfold germ_W in Hx. cbn [outside] in *. LiaTuning.ctauto.
  Qed.

  #[using="All"] Lemma outside_vals : forall hs0 h x, In h hs0 -> outside (map (fun h => (vA AI h, vA AI h + (vcap AI h + 1))) hs0) x ->
    ~ (vA AI h <= x < vA AI h + (vcap AI h + 1)).
  Proof.
    induction hs0 as [|h0 hs0 IH]; intros h x Hh Ho; [destruct Hh|]. cbn [map outside] in Ho. destruct Ho as [H0 Ho].
    destruct Hh as [<-|Hh]; [exact H0| exact (IH _ _ Hh Ho)].
  Qed.

  #[using="All"] Lemma GW_of_Wb : forall m1 m2 h, munch GW m0 m1 -> In h hs ->
    munch [(lo, bv_unsigned sp); (vA AI h, vA AI h + (vcap AI h + 1))]%Z m1 m2 -> munch GW m0 m2.
  Proof.
    intros m1 m2 h A1 Hh B. eapply munch_trans; [exact A1|]. eapply munch_weaken; [| exact B].
    intros x Hx. unfold germ_W in Hx. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5).
    cbn [outside]. split; [exact O1|]. split; [| exact I]. exact (outside_vals hs h x Hh O5).
  Qed.

  #[using="All"] Lemma blk_facts : forall b, In b (hl_blocks AI ns hs) ->
    4096 <= blk_addr b /\ blk_addr b mod 16 = 0 /\ 0 <= blk_size b /\ blk_addr b + blk_size b <= alloc_ceiling
    /\ (blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b).
  Proof.
    intros b Hb. pose proof (BSUB b Hb) as HIN.
    destruct (ai_block_range rsegs AI _ _ _ _ HR0 HIN) as (R1 & R2 & R3 & R4 & _). split; [exact (B4096 _ _ _ _ HR0 HIN)|].
    pose proof (BIMG _ _ _ _ HR0 HIN) as SS. LiaTuning.ctauto.
  Qed.

  #[using="All"] Lemma hdr_blk_facts : forall h, In h hs ->
    (4096 <= hA AI h /\ hA AI h + 88 <= alloc_ceiling /\ hA AI h mod 16 = 0 /\ (hA AI h + 88 <= 0x2a000 \/ 0x5d000 <= hA AI h))
    /\ (4096 <= vA AI h /\ vA AI h + (vcap AI h + 1) <= alloc_ceiling /\ vA AI h mod 16 = 0
        /\ (vA AI h + (vcap AI h + 1) <= 0x2a000 \/ 0x5d000 <= vA AI h))
    /\ (4096 <= nA AI h /\ nA AI h + (ncap AI h + 1) <= alloc_ceiling /\ nA AI h mod 16 = 0 /\ (nA AI h + (ncap AI h + 1) <= 0x2a000 \/ 0x5d000 <= nA AI h)).
  Proof.
    intros h Hh.
    assert (IB : forall b, In b (hblocks AI h) -> In b (hl_blocks AI ns hs)).
    { intros b Hb. unfold hl_blocks. apply in_or_app. right. eapply (in_hdrs_blocks AI); eauto. }
    pose proof (blk_facts _ (IB _ (or_introl eq_refl))) as F1. pose proof (blk_facts _ (IB _ (or_intror (or_introl eq_refl)))) as F2.
    pose proof (blk_facts _ (IB _ (or_intror (or_intror (or_introl eq_refl))))) as F3. cbn [blk_addr blk_size fst snd] in F1, F2, F3. clear -F1 F2 F3. lia.
  Qed.

  #[using="All"] Lemma node_blk_facts : forall b it, In (b, it) ns -> 4096 <= blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling
    /\ (blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b).
  Proof.
    intros b it Hb. destruct (blk_facts b) as (F1 & _ & _ & F4 & F5); [| auto].
    unfold hl_blocks. apply in_or_app. left. apply in_map_iff. exists (b, it). auto.
  Qed.

  #[using="All"] Lemma hdrs_mem_in : forall hs0 m h, hdrs_mem AI m hs0 -> In h hs0 -> hdro_mem AI m h /\ hdro_pure AI h.
  Proof.
    induction hs0 as [|h0 hs0 IH]; intros m h HS Hh; [destruct Hh|]. cbn [hdrs_mem] in HS. destruct HS as (HM & HP & HS').
    destruct Hh as [<-|Hh]; [auto| exact (IH _ _ HS' Hh)].
  Qed.

  #[using="All"] Lemma dlseg_in_cells : forall ns0 m pv TAIL b it, dlseg AI m ns0 pv TAIL -> In (b, it) ns0 ->
    exists pv' nx, rw_cells rsegs m (blk_addr b) (node_cells pv' nx it).
  Proof.
    induction ns0 as [|[b0 it0] ns0 IH]; intros m pv TAIL b it DL Hb; [destruct Hb|]. cbn [dlseg] in DL.
    destruct DL as (_ & _ & _ & _ & NC & DL'). destruct Hb as [E|Hb]; [injection E as -> ->; eexists _, _; exact NC| exact (IH _ _ _ _ _ DL' Hb)].
  Qed.

  #[using="All"] Lemma p_hlist_transport_c : forall m m', p_hlist AI m P ns hs X -> munch Wc m m' -> wmono rsegs m m' -> p_hlist AI m' P ns hs X.
  Proof.
    intros m m' (LH & FL & FC & DL & HS & MAP & BND & ZL & X0) MU WM. pose proof sp_facts as SF.
    split; [| split; [| split; [| split; [| split; [| split; [exact MAP| auto]]]]]].
    - eapply rw_cells_transport; [exact LH| exact MU| exact WM| cbn; lia].
    - eapply rw_cells_transport; [exact FL| exact MU| exact WM| cbn; lia].
    - eapply rw_cells_transport; [exact FC| exact MU| exact WM| cbn; lia].
    - eapply dlseg_transport; [exact DL| exact MU| exact WM|]. intros b it Hb. destruct (node_blk_facts b it Hb) as (F1 & F4 & F5).
      destruct (dlseg_facts AI _ _ _ _ _ _ DL Hb) as (SZ & _). cbn. lia.
    - eapply hdrs_mem_transport; [exact HS| exact MU| exact WM|]. intros h A0 n Hh Hr. destruct (hdr_blk_facts h Hh) as (F1 & F2 & F3).
      destruct Hr as [E|[E|[E|[]]]]; injection E as <- <-; cbn; lia.
  Qed.

  Definition vblk (h : hdr) : BLK := (vk AI h, vA AI h, vcap AI h + 1).

  #[using="All"] Lemma vblk_in : forall h, In h hs -> In (vblk h) (hl_blocks AI ns hs).
  Proof. intros h Hh. unfold hl_blocks. apply in_or_app. right. eapply (in_hdrs_blocks AI); [exact Hh|]. right. left. reflexivity. Qed.

  #[using="All"] Lemma hdrs_blocks_app : forall l1 l2 : list hdr, hdrs_blocks AI (l1 ++ l2) = hdrs_blocks AI l1 ++ hdrs_blocks AI l2.
  Proof. intros l1 l2. unfold hdrs_blocks. rewrite map_app, concat_app. reflexivity. Qed.

  #[using="All"] Lemma blocks_apart : forall b1 b2 : BLK, In b1 (hl_blocks AI ns hs) -> In b2 (hl_blocks AI ns hs) -> b1 <> b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
  Proof. intros b1 b2 H1 H2 NE. eapply (ai_blocks_disjoint rsegs AI); [exact HR0| apply BSUB; exact H1| apply BSUB; exact H2| exact NE]. Qed.

  #[using="All"] Lemma node_neq : forall b it y, In (b, it) ns -> In y (hdrs_blocks AI hs) -> b <> y.
  Proof.
    intros b it y Hb Hy. eapply (nodup_in_neq AI (map fst ns) (hdrs_blocks AI hs)); [exact ND| | exact Hy].
    apply in_map_iff. exists (b, it). auto.
  Qed.

  #[using="All"] Lemma hdr_idx_neq : forall i j hi hj x y, nth_error hs i = Some hi -> nth_error hs j = Some hj -> i <> j ->
    In x (hblocks AI hi) -> In y (hblocks AI hj) -> x <> y.
  Proof.
    intros i j hi hj x y Hi Hj NE Hx Hy.
    destruct (nth_error_split hs i _ Hi) as (l1 & l2 & E & L1).
    assert (ND' : NoDup (map blk_id (map fst ns ++ hdrs_blocks AI l1 ++ hblocks AI hi ++ hdrs_blocks AI l2))).
    { replace (map fst ns ++ hdrs_blocks AI l1 ++ hblocks AI hi ++ hdrs_blocks AI l2) with (hl_blocks AI ns hs); [exact ND|].
      unfold hl_blocks. rewrite E, hdrs_blocks_app, (hdrs_blocks_cons AI hi l2). repeat rewrite <- app_assoc. reflexivity. }
    destruct (Nat.lt_ge_cases j i) as [LT|GE].
    -   assert (Hj' : In hj l1). { rewrite E in Hj. rewrite nth_error_app1 in Hj by lia. eapply nth_error_In; exact Hj. }
      apply not_eq_sym. eapply (nodup_in_neq AI (map fst ns ++ hdrs_blocks AI l1) (hblocks AI hi ++ hdrs_blocks AI l2)).
      + repeat rewrite <- app_assoc. exact ND'.
      + apply in_or_app. right. eapply (in_hdrs_blocks AI); eauto.
      + apply in_or_app. left. exact Hx.
    -   assert (Hj' : In hj l2).
      { rewrite E in Hj. rewrite nth_error_app2 in Hj by lia. rewrite L1 in Hj. destruct (j - i)%nat as [|k] eqn:Ek; [lia|]. cbn in Hj. eapply nth_error_In; exact Hj. }
      eapply (nodup_in_neq AI ((map fst ns ++ hdrs_blocks AI l1) ++ hblocks AI hi) (hdrs_blocks AI l2)).
      + repeat rewrite <- app_assoc. exact ND'.
      + apply in_or_app. right. exact Hx.
      + eapply (in_hdrs_blocks AI); eauto.
  Qed.

  #[using="All"] Lemma hdr_own_neq : forall i h, nth_error hs i = Some h -> (hk AI h, hA AI h, 88) <> vblk h /\ (nk AI h, nA AI h, ncap AI h + 1) <> vblk h.
  Proof.
    intros i h Hi. destruct (nth_error_split hs i _ Hi) as (l1 & l2 & E & L1).
    assert (ND' : NoDup (map blk_id ((map fst ns ++ hdrs_blocks AI l1) ++ hblocks AI h ++ hdrs_blocks AI l2))).
    { replace ((map fst ns ++ hdrs_blocks AI l1) ++ hblocks AI h ++ hdrs_blocks AI l2) with (hl_blocks AI ns hs); [exact ND|].
      unfold hl_blocks. rewrite E, hdrs_blocks_app, (hdrs_blocks_cons AI h l2). repeat rewrite <- app_assoc. reflexivity. }
    unfold vblk. split.
    - eapply (nodup_in_neq AI ((map fst ns ++ hdrs_blocks AI l1) ++ [(hk AI h, hA AI h, 88)]) ([(vk AI h, vA AI h, vcap AI h + 1); (nk AI h, nA AI h, ncap AI h + 1)] ++ hdrs_blocks AI l2)).
      + repeat rewrite <- app_assoc in *. exact ND'.
      + apply in_or_app. right. left. reflexivity.
      + left. reflexivity.
    - apply not_eq_sym. eapply (nodup_in_neq AI ((map fst ns ++ hdrs_blocks AI l1) ++ [(hk AI h, hA AI h, 88); (vk AI h, vA AI h, vcap AI h + 1)]) ([(nk AI h, nA AI h, ncap AI h + 1)] ++ hdrs_blocks AI l2)).
      + repeat rewrite <- app_assoc in *. exact ND'.
      + apply in_or_app. right. right. left. reflexivity.
      + left. reflexivity.
  Qed.

  #[using="All"] Lemma hdrs_mem_nth : forall hs0 m, hdrs_mem AI m hs0 <-> (forall i h', nth_error hs0 i = Some h' -> hdro_mem AI m h' /\ hdro_pure AI h').
  Proof.
    induction hs0 as [|h0 hs0 IH]; intros m; split; intros H.
    - intros [|i] h' E; discriminate.
    - exact I.
    - cbn [hdrs_mem] in H. destruct H as (HM & HP & HS'). intros [|i] h' E; cbn in E; [injection E as <-; auto|]. exact (proj1 (IH m) HS' i h' E).
    - cbn [hdrs_mem]. split; [| split]; [exact (proj1 (H 0%nat h0 eq_refl))| exact (proj2 (H 0%nat h0 eq_refl))|].
      apply (proj2 (IH m)). intros i h' E. exact (H (S i) h' E).
  Qed.

  #[using="All"] Lemma bytes_at_func : forall m a bs1 bs2, bytes_at rsegs m a bs1 -> bytes_at rsegs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
  Proof.
    intros m a bs1 bs2 (_ & _ & B1) (_ & _ & B2) L. apply nth_error_ext. intros i.
    destruct (Nat.lt_ge_cases i (length bs1)).
    - rewrite <- B1, <- B2 by lia. reflexivity.
    - rewrite (proj2 (nth_error_None bs1 i)), (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
  Qed.

  #[using="All"] Lemma mrd_munch : forall W m m' a, munch W m m' -> outside W a -> 0 <= a < 2^64 -> mrd rsegs m' (wa a) = mrd rsegs m (wa a).
  Proof. intros W m m' a MU HO Ha. unfold mrd. rewrite (MU (wa a)); [reflexivity|]. unfold wa. rewrite unsigned_lit by lia. exact HO. Qed.

  #[using="All"] Lemma p_hlist_relower : forall m m2 h vbs vbs2,
    p_hlist AI m P ns hs X -> In h hs ->
    munch [(lo, bv_unsigned sp); (vA AI h, vA AI h + (vcap AI h + 1))]%Z m m2 -> wmono rsegs m m2 ->
    rw_cells rsegs m (vA AI h) [CB (Z.to_nat (vcap AI h + 1)) vbs] ->
    rw_cells rsegs m2 (vA AI h) [CB (Z.to_nat (vcap AI h + 1)) vbs2] ->
    (forall j, nth_error vbs j = Some (Z_to_bv 8 0) -> nth_error vbs2 j = Some (Z_to_bv 8 0)) ->
    p_hlist AI m2 P ns hs X.
  Proof.
    intros m m2 h vbs vbs2 (LH & FL & FC & DL & HS & MAP & BND & ZL & X0) Hh MU WM VB VB2 ZP. pose proof sp_facts as SF.
    destruct (hdr_blk_facts h Hh) as (_ & (V1 & V2 & _) & _).
    pose proof (vblk_in h Hh) as VIN.
    assert (APART : forall b : BLK, In b (hl_blocks AI ns hs) -> b <> vblk h ->
              disjoint_from [(lo, bv_unsigned sp); (vA AI h, vA AI h + (vcap AI h + 1))]%Z (blk_addr b) (blk_size b)).
    { intros b Hb NE. destruct (blk_facts b Hb) as (F1 & _ & F3 & F4 & _). pose proof (blocks_apart b (vblk h) Hb VIN NE) as DJ.
      unfold vblk in DJ. cbn [blk_addr blk_size fst snd] in DJ. cbn. lia. }
    split; [| split; [| split; [| split; [| split; [| split; [exact MAP| auto]]]]]].
    - eapply rw_cells_transport; [exact LH| exact MU| exact WM| cbn; lia].
    - eapply rw_cells_transport; [exact FL| exact MU| exact WM| cbn; lia].
    - eapply rw_cells_transport; [exact FC| exact MU| exact WM| cbn; lia].
    - eapply dlseg_transport; [exact DL| exact MU| exact WM|]. intros b it Hb.
      destruct (dlseg_facts AI _ _ _ _ _ _ DL Hb) as (SZ & _). rewrite <- SZ.
      apply APART. { unfold hl_blocks. apply in_or_app. left. apply in_map_iff. exists (b, it). auto. }
      eapply node_neq; [exact Hb|]. eapply (in_hdrs_blocks AI); [exact Hh|]. right. left. reflexivity.
    - destruct (In_nth_error _ _ Hh) as [ih Hih].
      apply (proj2 (hdrs_mem_nth hs m2)). intros i h' Hi. pose proof (proj1 (hdrs_mem_nth hs m) HS i h' Hi) as [HM HP]. split; [| exact HP].
      assert (Hh' : In h' hs) by (eapply nth_error_In; exact Hi). unfold hdro_pure in HP.
      assert (IB : forall b, In b (hblocks AI h') -> In b (hl_blocks AI ns hs)).
      { intros b Hb. unfold hl_blocks. apply in_or_app. right. eapply (in_hdrs_blocks AI); eauto. }
      destruct HM as ([pad HC] & VC & [vb' [VB' VN']] & NMC & [nb' [NB' NN']]).

      assert (NE1 : (hk AI h', hA AI h', 88) <> vblk h).
      { destruct (Nat.eq_dec i ih) as [->|NE]; [rewrite Hih in Hi; injection Hi as <-; exact (proj1 (hdr_own_neq _ _ Hih))|].
        eapply hdr_idx_neq; [exact Hi| exact Hih| exact NE| left; reflexivity| right; left; reflexivity]. }
      assert (NE3 : (nk AI h', nA AI h', ncap AI h' + 1) <> vblk h).
      { destruct (Nat.eq_dec i ih) as [->|NE]; [rewrite Hih in Hi; injection Hi as <-; exact (proj2 (hdr_own_neq _ _ Hih))|].
        eapply hdr_idx_neq; [exact Hi| exact Hih| exact NE| right; right; left; reflexivity| right; left; reflexivity]. }
      pose proof (APART _ (IB _ (or_introl eq_refl)) NE1) as D1. pose proof (APART _ (IB _ (or_intror (or_intror (or_introl eq_refl)))) NE3) as D3.
      cbn [blk_addr blk_size fst snd] in D1, D3.
      split; [| split; [| split; [| split]]].
      + exists pad. eapply rw_cells_transport; [exact HC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
      + eapply rw_cells_transport; [exact VC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
      +
        destruct (Nat.eq_dec i ih) as [->|NE].
        * rewrite Hih in Hi. injection Hi as <-. exists vbs2. split; [exact VB2|]. apply ZP.
          pose proof (rw_CB_len _ _ _ _ VB) as L1. pose proof (rw_CB_len _ _ _ _ VB') as L2.
          rewrite (bytes_at_func m (vA AI h) vbs vb' (proj1 (u8arr_of_rw_cells _ _ _ _ _ VB)) (proj1 (u8arr_of_rw_cells _ _ _ _ _ VB')) ltac:(lia)). exact VN'.
        * assert (NE2 : vblk h' <> vblk h).
          { eapply hdr_idx_neq; [exact Hi| exact Hih| exact NE| right; left; reflexivity| right; left; reflexivity]. }
          pose proof (APART _ (IB _ (or_intror (or_introl eq_refl))) NE2) as D2. cbn [blk_addr blk_size fst snd] in D2.
          exists vb'. split; [| exact VN']. eapply rw_cells_transport; [exact VB'| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D2| lia| cbn; lia].
      + eapply rw_cells_transport; [exact NMC| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D1| lia| cbn; lia].
      + exists nb'. split; [| exact NN']. eapply rw_cells_transport; [exact NB'| exact MU| exact WM|]. eapply disjoint_from_sub; [exact D3| lia| cbn; lia].
  Qed.

  #[using="All"] Lemma ret : forall (r err' hack' pos' entp' clen' : Z) (errv' : word) x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
      m jA,
    hide (munch GW m0 m) -> wmono rsegs m0 m -> mem_inv rsegs m ->
    rw_cells rsegs m q [CB 112 jA] -> FRB m -> stk rsegs m lo q ->
    p_ent m P (Z_to_bv 64 (A + cur)) (Z_to_bv 64 0) -> p_ctl m P err' hack' pos' entp' clen' csz cur -> p_hlist AI m P ns hs X ->
    rw_cells rsegs m TPE [C4 errv'] -> rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] ->
    ( (r = 0 /\ pos' = POS_COMPLETE /\ entp' = entp /\ err' = err /\ hack' = hack)
      \/ (r = 6 /\ pos' = pos /\ 2 <= entp' <= 4 /\ err' = err /\ hack' = hack)
      \/ (r = 3 /\ pos' = pos /\ entp' = entp /\ err' = 411)) ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 r) x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x153ec) fc None m (seg_rom rsegs)).
  Proof.
    intros until jA. intros MU0 WM MI FRA FRBm ST PE PC PH ERR GOT CAN IW CASES. pose proof sp_facts as SF.
    pose proof (munch_refl Wc m) as MU.
    assert (FR : rw_cells rsegs m q ([CB 112 jA] ++ [C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact FRA| exact FRBm]. } clear FRA FRBm. cbn [app] in FR.
    pose proof PE as PE'. unfold p_ent in PE. destruct PC as (PCc & PCb).
    do 7 step.
    release_frame FR ST (bv_unsigned sp).
    unfold germ_post. apply evt_done.
    exists x5, x6, x7, (Z_to_bv 64 r), x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m, r, err', hack', pos', entp', clen', errv'.
    split; [reflexivity|]. split; [eapply GW_of_Wc; [exact MU0| exact MU]|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ST|]. split; [exact PE'|]. split; [split; [exact PCc| exact PCb]|]. split; [exact PH|].
    split; [exact ERR|]. split; [exact GOT|]. split; [exact CAN|]. split; [exact IW|]. exact CASES.
  Qed.

  Definition ctx (m : mem) : Prop :=
    hide (munch GW m0 m) /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ FRB m /\ stk rsegs m lo q
    /\ p_ent m P (Z_to_bv 64 (A + cur)) (Z_to_bv 64 0) /\ p_hlist AI m P ns hs X /\ p_meth m P meth /\ p_ver m P isreq maj min
    /\ (exists errv, rw_cells rsegs m TPE [C4 errv]) /\ rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells rsegs m ssp_guard [C8 canary] /\ rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)].

  Ltac open_ctx C :=
    let errv := fresh "errv" in let pad := fresh "pad" in
    destruct C as (MU0 & WM & MI & FRBm & ST & PE & PH & [PMc PMb] & [[pad PVc] PVb] & [errv ERR] & GOT & CAN & IW);
    unfold p_ent in PE; unfold got_ssp, ssp_guard in GOT, CAN; try unfold got_ssp, ssp_guard in DE1; try unfold got_ssp, ssp_guard in DE2.

  Ltac close_ctx :=
    lazymatch goal with |- ctx ?m' =>
      split; [ unfold hide in *;
               lazymatch goal with
               | MU : munch _ ?m1 m' |- _ => lazymatch goal with MU0 : munch _ m0 m1 |- _ => exact (GW_of_Wc _ _ MU0 MU) end
               | MU0 : munch _ m0 m' |- _ => exact MU0 end |];
      split; [ assumption |]; split; [assumption|]; split; [assumption|]; split; [assumption|];
      split; [assumption|];
      split; [ first [ assumption
                     | lazymatch goal with MU : munch _ ?m1 m', WMp : wmono _ ?m1 m', PH : p_hlist _ ?m1 _ _ _ _ |- _ =>
                         exact (p_hlist_transport_c _ _ PH MU WMp) end ] |];
      split; [split; assumption|]; split; [split; [eexists; eassumption| assumption]|];
      split; [eexists; eassumption|]; split; [assumption|]; split; assumption
    end.

  #[using="All"] Lemma frameA_forget3 : forall m cs0 cs1 cs2, rw_cells rsegs m q cs0 -> cells_size cs0 = 24%nat -> rw_cells rsegs m (q + 24) cs1 -> cells_size cs1 = 20%nat ->
    rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    exists jA, rw_cells rsegs m q [CB 112 jA].
  Proof.
    intros m cs0 cs1 cs2 H0 L0 H1 L1 H2 L2.
    assert (J1 : rw_cells rsegs m (q + 24) (cs1 ++ cs2)).
    { apply rw_cells_app. rewrite L1. split; [exact H1|]. replace (q + 24 + Z.of_nat 20) with (q + 44) by lia. exact H2. }
    assert (J : rw_cells rsegs m q (cs0 ++ cs1 ++ cs2)). { apply rw_cells_app. rewrite L0. split; [exact H0| exact J1]. }
    destruct (rw_cells_forget rsegs m q _ J) as [jA JA]. rewrite !cells_size_app, L0, L1, L2 in JA. exists jA. exact JA.
  Qed.

  #[using="All"] Lemma r6 : forall (entp' clen' : Z) x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
      m cs0 cs1 cs2,
    ctx m -> rw_cells rsegs m q cs0 -> cells_size cs0 = 24%nat -> rw_cells rsegs m (q + 24) cs1 -> cells_size cs1 = 20%nat ->
    rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp' clen' csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 2 <= entp' <= 4 -> 0 <= clen' < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x155bc) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs2. intros C F0 L0 F1 L1 F2 L2 PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF. open_ctx C.
    destruct (frameA_forget3 m cs0 cs1 cs2 F0 L0 F1 L1 F2 L2) as [jA FRA].
    zstep. zstep. eapply ret; try eassumption.
    - split; [exact PCC| lia].
    - right. left. repeat split; lia.
  Qed.

  #[using="All"] Lemma nolen : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
      m cs0 cs1 cs2,
    ctx m -> rw_cells rsegs m q cs0 -> cells_size cs0 = 24%nat -> rw_cells rsegs m (q + 24) cs1 -> cells_size cs1 = 20%nat ->
    rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15580) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs2. intros C F0 L0 F1 L1 F2 L2 PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF. pose proof C as C0. open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp. unfold p_ctl_cells in PCC.
    zstep. zstep. if_cases K0; zify_cond K0.
    -
      zstep. sstep. zstep.
      eapply r6; try eassumption; try reflexivity; try lia. close_ctx.
    -
      destruct (frameA_forget3 m cs0 cs1 cs2 F0 L0 F1 L1 F2 L2) as [jA FRA].
      assert (FIN : forall (hack' : Z) y10 m', (hack' = hack \/ hack' = 1) -> munch Wc m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        rw_cells rsegs m' (P + 440) [C4 (wz err); C4 (wz hack'); C4 (wz pos); C4 (wz entp); C4 (wz clen); C4 (wz 0); C8 (wz csz); C8 (wz cur)] ->
        FRB m' -> stk rsegs m' lo q -> rw_cells rsegs m' q [CB 112 jA] ->
        rw_cells rsegs m' (P + 384) [C8 (Z_to_bv 64 (A + cur)); C8 (Z_to_bv 64 0)] -> rw_cells rsegs m' P [C4 (wz 1); C4 (wz meth)] ->
        rw_cells rsegs m' (P + 264) [C8 (wz 0); C4 (wz isreq); C4 (wz maj); C4 (wz min); C4 pad] ->
        rw_cells rsegs m' TPE [C4 errv] -> rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m' ssp_guard [C8 canary] ->
        rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)] ->
        evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 (Z_to_bv 64 P) y10 (Z_to_bv 64 8) x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x1559c) fc None m' (seg_rom rsegs))).
      { intros hack' y10 m' Hh MU' WM' MI' PCC' FRB' ST' FRA' PE' PM' PV' ERR' GOT' CAN' IW'.
        clear MU WMp PCC FRBm ST PE PMc PVc ERR GOT CAN IW MI. unfold got_ssp, ssp_guard in GOT', CAN'.
        zstep. sstep. zstep. zstep.
        eapply (ret 3 411 hack' pos entp clen errv); try eassumption.
        + eapply GW_of_Wc; [exact MU0| exact MU'].
        + eapply wmono_trans; [exact WM| exact WM'].
        + split; [exact PCC'| lia].
        + eapply p_hlist_transport_c; [exact PH| exact MU'| exact WM'].
        + right. right. repeat split; lia. }
      zstep. zstep. zstep. if_cases K1; zify_cond K1.
      +   eapply (FIN hack); try eassumption. left; reflexivity.
      +   zstep. sstep. eapply (FIN 1); try eassumption. right; reflexivity.
  Qed.

  #[using="All"] Lemma in_ns_item : forall (ns0 : list (BLK * Z)) hs0 b it, map snd ns0 = map (hA AI) hs0 -> In (b, it) ns0 -> exists h, In h hs0 /\ it = hA AI h.
  Proof.
    induction ns0 as [|[b0 it0] ns0 IH]; intros [|h0 hs0] b it MAP Hb; cbn in MAP; try discriminate; [destruct Hb|].
    injection MAP as E MAP'. destruct Hb as [Hb|Hb].
    - injection Hb as -> ->. exists h0. split; [left; reflexivity| exact E].
    - destruct (IH hs0 b it MAP' Hb) as (h & H1 & H2). exists h. split; [right; exact H1| exact H2].
  Qed.

  #[using="All"] Lemma cb_string : forall m A0 n vbs k, rw_cells rsegs m A0 [CB n vbs] -> nth_error vbs k = Some (Z_to_bv 8 0) ->
    exists str rest, vbs = str ++ Z_to_bv 8 0 :: rest /\ ~ In (Z_to_bv 8 0) str /\ (length str <= k)%nat
                     /\ bytes_at rsegs m A0 (str ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m A0 (str ++ Z_to_bv 8 0 :: rest) /\ length vbs = n.
  Proof.
    intros m A0 n vbs k CBH NK. pose proof (rw_CB_len _ _ _ _ CBH) as LV.
    destruct (nth_error_split vbs k _ NK) as (l1 & l2 & E & L1).
    destruct (nul_split l1 l2) as (str & rest & E2 & NI & LS). rewrite <- E in E2.
    pose proof (rw_cells_bytes _ _ _ CBH) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite E2 in B.
    exists str, rest. split; [exact E2|]. split; [exact NI|]. split; [lia|]. split; [| split; [exact B| exact LV]].
    change (str ++ Z_to_bv 8 0 :: rest) with (str ++ [Z_to_bv 8 0] ++ rest) in B. rewrite app_assoc in B.
    apply bytes_at_app in B. destruct B as [B _]. exact B.
  Qed.

  #[using="All"] Lemma le4_mod32 : forall w : word, le4 w = le4 (Z_to_bv 64 (bv_unsigned w mod 2^32)).
  Proof.
    intros w. unfold le4. pose proof (Z.mod_pos_bound (bv_unsigned w) (2^32) ltac:(lia)).
    rewrite unsigned_lit by lia. symmetry. apply Z_to_le_bytes_mod. cbn. lia.
  Qed.

  #[using="All"] Lemma strtoll_call : forall (qq lo0 Ss E : Z) (str ejunk : list byte) (errv canary0 : word)
      (ra0 gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F0 : bvmap 5 word) (fc0 : bv 32) (m : mem),
    bytes_at rsegs m Ss (str ++ [Z_to_bv 8 0]) ->
    rw_cells rsegs m E [CB 8 ejunk] -> (E <> 0)%Z ->
    rw_cells rsegs m (bv_unsigned tp0 - 164) [C4 errv] ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary0] ->
    stk rsegs m lo0 qq -> mem_inv rsegs m ->
    (lo0 <= qq - STRTOL_DEPTH)%Z -> (ssp_guard + 8 <= lo0)%Z -> (0 <= qq < 2^63)%Z ->
    (4096 + 164 <= bv_unsigned tp0)%Z ->
    (4096 <= Ss)%Z -> (Ss + 2^41 <= 2^63)%Z -> (Z.of_nat (length str) + 1 <= 2^40)%Z ->
    (Ss + Z.of_nat (length str) + 1 <= qq - STRTOL_DEPTH \/ qq <= Ss)%Z ->
    (Ss + Z.of_nat (length str) + 1 <= got_ssp \/ got_ssp + 8 <= Ss)%Z -> (Ss + Z.of_nat (length str) + 1 <= ssp_guard \/ ssp_guard + 8 <= Ss)%Z ->
    (bv_unsigned tp0 - 164 + 4 <= lo0 \/ qq <= bv_unsigned tp0 - 164)%Z ->
    (bv_unsigned tp0 - 164 + 4 <= Ss \/ Ss + Z.of_nat (length str) + 1 <= bv_unsigned tp0 - 164)%Z ->
    (bv_unsigned tp0 - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp0 - 164)%Z -> (bv_unsigned tp0 - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp0 - 164)%Z ->
    ((E + 8 <= lo0 \/ qq <= E) /\ (E + 8 <= Ss \/ Ss + Z.of_nat (length str) + 1 <= E) /\
     (E + 8 <= bv_unsigned tp0 - 164 \/ bv_unsigned tp0 - 164 + 4 <= E) /\
     (E + 8 <= got_ssp \/ got_ssp + 8 <= E) /\ (E + 8 <= ssp_guard \/ ssp_guard + 8 <= E) /\ 0 <= E /\ E + 8 <= 2^64)%Z ->
    a0 = wz Ss -> a1 = wz E -> a2 = wz 10 ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' (errv' : word) (k : Z),
        ms' = MS (mkR ra0 (wz qq) gp0 tp0 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                 F0 (ret_pc ra0) fc0 None m' (seg_rom rsegs)
        /\ munch [(qq - 528, qq); (E, E + 8); (bv_unsigned tp0 - 164, bv_unsigned tp0 - 164 + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo0 qq
        /\ bytes_at rsegs m' Ss (str ++ [Z_to_bv 8 0])
        /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m' ssp_guard [C8 canary0]
        /\ rw_cells rsegs m' (bv_unsigned tp0 - 164) [C4 errv']
        /\ (0 <= k <= Z.of_nat (length str))%Z
        /\ rw_cells rsegs m' E [C8 (Z_to_bv 64 (Ss + k))])
      (MS (mkR ra0 (wz qq) gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F0 (wz strtoll_entry) fc0 None m (seg_rom rsegs)).
  Proof.
    clear. intros until m. intros STR EC EN ERR GOT CAN ST MI LO GLO QQ TP S4 SHI LEN D1 D2 D3 D4 D5 D6 D7 DE -> -> ->.
    assert (E0 : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
    eapply evt_mono.
    { eapply (strtoll_proof ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F0 fc0 m Ss str E 10 ejunk errv canary0 lo0);
        rewrite ?E0; eauto; try lia. }
    intros ms' Q. unfold strtol_post, STRTOL_DEPTH in Q. rewrite !E0 in Q. destruct_exs Q.
    destruct Q as (-> & MU & WM & MI' & ST' & STR' & GOT' & CAN' & ERR' & HK & EC').
    repeat (lazymatch goal with |- ex _ => eexists end). split; [reflexivity|].
    repeat (split; [eassumption|]). apply EC'. exact EN.
  Qed.

  #[using="All"] Lemma clen_join : forall (cw : word) y1 y5 y6 y7 y8 y9 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' cs0 cs1 cs2,
    ctx m' -> rw_cells rsegs m' q cs0 -> cells_size cs0 = 24%nat -> rw_cells rsegs m' (q + 24) cs1 -> cells_size cs1 = 20%nat ->
    rw_cells rsegs m' (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m' (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR y1 spw gp tp y5 y6 y7 y8 y9 y10 (Z_to_bv 64 P) y12 y13 y14 y15 y16 y17 cw s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x155b0) fc None m' (seg_rom rsegs)).
  Proof.
    intros until cs2. intros C F0 L0 F1 L1 F2 L2 PCC Be Bh Bp Bz Bu. pose proof sp_facts as SF. open_ctx C.
    pose proof (munch_refl Wc m') as MU. pose proof (wmono_refl rsegs m') as WMp. unfold p_ctl_cells in PCC.
    zstep. sstep. sstep.
    pose proof (Z.mod_pos_bound (bv_unsigned cw) (2^32) ltac:(lia)) as CW.
    lazymatch goal with PCC' : rw_cells _ ?mm _ [?c1; ?c2; ?c3; ?c4; C4 cw; ?c6; ?c7; ?c8] |- _ =>
      pose proof (rw_cells_recell rsegs mm (P + 440) [c1; c2; c3; c4] (C4 cw) (C4 (wz (bv_unsigned cw mod 2^32))) [c6; c7; c8] PCC' I
                    ltac:(cbn [cbytes]; symmetry; apply le4_mod32) eq_refl) as PCC2; clear PCC'; cbn [app] in PCC2 end.
    eapply (r6 2 (bv_unsigned cw mod 2^32)); try eassumption; try reflexivity; try lia. close_ctx.
  Qed.

  #[using="All"] Lemma clen_num : forall (h : hdr) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 m (j8 ja : list byte) cs2,
    In h hs -> ctx m -> rw_cells rsegs m q [CB 8 j8; C8 (Z_to_bv 64 (vA AI h)); C8 (Z_to_bv 64 (vlen AI h))] ->
    rw_cells rsegs m (q + 24) [CB 16 ja; C4 (Z_to_bv 64 3)] -> rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 (vA AI h)) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15518) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs2. intros Hh C F0 F1 F2 L2 PCC Be Bh Bp Bz Bu. pose proof sp_facts as SF. pose proof q_sp as QSP.
    open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp.
    pose proof TPA as [TPA']. pose proof TP1 as [TP1']. pose proof (word_lt64 tp) as TPB. pose proof alloc_ceiling_bounds as ACB.
    pose proof PH as PH0. destruct PH0 as (_ & _ & _ & DL & HS & MAP & BND & _).
    destruct (hdrs_mem_in _ _ _ HS Hh) as [HM HP]. destruct HM as ([pad2 HC] & VC & [vbs [VB VN]] & _). unfold hdro_pure in HP.
    unfold mbuf_cells in VC.
    destruct (hdr_blk_facts h Hh) as ((G1 & G2 & G3) & (G4 & G5 & G6 & G7) & _).
    assert (VL : vlen AI h <= VMAX) by (destruct (BND h Hh); lia). unfold VMAX in VL.
    zstep. call errno_location_spec. all: side (first [assumption | lia]).
    step. ubr. ub_align. sstep.
    lazymatch goal with F1 : rw_cells _ ?mm (q + 24) [CB 16 ?a; ?c] |- _ =>
      pose proof (rw_cells_split_CB rsegs mm (q + 24) [] 16 a [c] [8; 8]%nat F1 eq_refl) as F1'; clear F1; cbn [mk_CB_cells app] in F1';
      lazymatch type of F1' with rw_cells _ _ _ [?e0; ?e1; ?e2] => change (rw_cells rsegs mm (q + 24) ([e0] ++ [e1; e2])) in F1' end;
      apply rw_cells_app in F1'; destruct F1' as [E8 F1]; cbn [cells_size csize Nat.add] in F1; change (Z.of_nat 8) with 8%Z in F1 end.
    destruct (cb_string _ _ _ _ _ VB VN) as (str & rest & EV & NI & LS & SB & SB2 & LV).
    zstep. zstep. zstep. zstep.
    unfold STRTOL_DEPTH in *.
    callq (strtoll_call q lo (vA AI h) (q + 24) str (firstn 8 ja) (Z_to_bv 64 0) canary).
    all: side (first [exact SB | exact E8 | exact ST | assumption | reflexivity | (rewrite ?QSP; f_equal; lia)
                     | (unfold got_ssp, ssp_guard, STRTOL_DEPTH in *; lia)]).
    match goal with H : rw_cells _ _ (q + 24) [C8 _] |- _ => rename H into PEND end.
    assert (FJ : forall mm e, rw_cells rsegs mm (q + 24) [e] -> csize e = 8%nat -> rw_cells rsegs mm (q + 24 + 8) [CB 8 (firstn 8 (skipn 8 ja)); C4 (wz 3)] ->
                 rw_cells rsegs mm (q + 24) ([e] ++ [CB 8 (firstn 8 (skipn 8 ja)); C4 (wz 3)])).
    { intros mm e H1 He H2. apply rw_cells_app. split; [exact H1|]. cbn [cells_size]. rewrite He. exact H2. }
    zstep. zstep. step. if_cases K2; zify_cond K2.
    - pose proof (FJ _ _ PEND eq_refl F1) as FA. cbn [app] in FA. clear PEND F1.
      eapply clen_join; try eassumption; try reflexivity; try lia. close_ctx.
    - zstep. zstep. zstep. step. ubr.
      zstep. zstep. zstep. step. uub_b2z. ulit_branch.
      pose proof PEND as PEND2. replace (q + 24) with (SP + -120) in PEND2 by lia.
      zstep. zstep. zstep. zstep. zstep. zstep. clear PEND2.
      pose proof (FJ _ _ PEND eq_refl F1) as FA. cbn [app] in FA. clear PEND F1.
      eapply clen_join; try eassumption; try reflexivity; try lia. close_ctx.
  Qed.

  #[using="All"] Lemma clen_part : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31
      m (j0 ja : list byte) (w16 : word) cs2,
    ctx m -> rw_cells rsegs m q [CB 24 j0] -> rw_cells rsegs m (q + 24) [CB 16 ja; C4 w16] -> rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 (P + 288)) (Z_to_bv 64 P) x10 x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x154cc) fc None m (seg_rom rsegs)).
  Proof.
    intros until cs2. intros C F0 F1 F2 L2 PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF. pose proof q_sp as QSP. open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp.
    pose proof PA8 as [PA8']. pose proof SPA as [SPA'].
    pose proof (rw_cells_split_CB rsegs m q [] 24 j0 [] [8; 8; 8]%nat F0 eq_refl) as F0'; clear F0; cbn [mk_CB_cells app] in F0'.
    replace (q + 24) with (SP + -120) in F1 by lia.
    zstep. sstep.
    replace (SP + -120) with (q + 24) in F1 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => rename m1 into m1 end.
    pose proof (p_hlist_transport_c _ _ PH MU WMp) as PH1. destruct PH1 as (LH & FL & FC & DL & HS & MAP & BND & ZL & X0).
    assert (LL : rw_cells rsegs m1 (P + 288) (llist_cells (hd_addr AI ns (P + 312)) (last_addr AI ns (P + 288)) (zlength ns) 0 0 httpheader_free_entry httpmsg_compare_entry)).
    { apply (proj2 (llist_split m1 (P + 288) _ _ _ 0 0 _ _)). replace (P + 288 + 56) with (P + 344) by lia. replace (P + 288 + 80) with (P + 368) by lia.
      split; [exact LH| split; [exact FL| exact FC]]. }
    assert (LS : lseg m1 (lf_nodes AI ns hs) (hd_addr AI ns (P + 312)) (P + 288) (P + 288 + 24)).
    { replace (P + 288 + 24) with (P + 312) by lia. eapply lf_lseg; eauto.
      intros b it Hb. destruct (in_ns_item _ _ _ _ MAP Hb) as (h & Hh & ->). destruct (hdr_blk_facts h Hh) as ((G1 & _) & _). lia. }
    assert (SEPN : forall N it id, In (N, it, id) (lf_nodes AI ns hs) -> N + 24 <= lo /\ it + 24 <= lo).
    { intros N it id HN. destruct (lf_nodes_in2 AI ns hs N it id MAP HN) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (node_blk_facts _ _ Hb) as (NB1 & NB2 & NB3). destruct (dlseg_facts AI _ _ _ _ _ _ DL Hb) as (SZ & _).
      destruct (hdr_blk_facts h Hh) as ((G1 & G2 & _) & _). lia. }
    assert (SEPA : forall N it id, In (N, it, id) (lf_nodes AI ns hs) -> N mod 8 = 0 /\ it mod 8 = 0).
    { intros N it id HN. destruct (lf_nodes_in2 AI ns hs N it id MAP HN) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (blk_facts b) as (_ & BA & _).
      { unfold hl_blocks. apply in_or_app. left. apply in_map_iff. exists (b, hA AI h). auto. }
      destruct (hdr_blk_facts h Hh) as ((_ & _ & HA & _) & _). clear -BA HA. split; Z.div_mod_to_equations; lia. }
    clear LH FL FC.
    zstep. zstep. zstep. zstep.
    callq (ListFind_call q lo (P + 288) (q + 24) 3 (last_addr AI ns (P + 288)) (zlength ns) 0 0 httpheader_free_entry (lf_nodes AI ns hs) ja).
    all: side (first [exact LL | exact LS | exact F1 | exact ST | exact SEPN | exact SEPA | assumption | reflexivity | lia | (rewrite ?QSP; f_equal; lia)
                     | (clear -PA8' SPA'; Z.div_mod_to_equations; lia)]).
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    match goal with H : (?r = 0 \/ exists it, In (?r, it, 3) _)%Z |- _ => rename H into RES end.
    clear LL LS.
    zstep. if_cases K0; zify_cond K0.
    {   eapply nolen; try eassumption; try reflexivity; try lia. close_ctx. }
    destruct RES as [-> | [it HIN]]. { exfalso. first [apply K0; reflexivity | lia]. }
    destruct (lf_nodes_in2 AI ns hs _ _ _ MAP HIN) as (b & h & Hb & Hh & ER & _ & ->).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    pose proof (p_hlist_transport_c _ _ PH MU WMp) as PH2. destruct PH2 as (_ & _ & _ & DL2 & HS2 & _).
    destruct (dlseg_in_cells _ _ _ _ _ _ DL2 Hb) as (pv & nx & NC). rewrite <- ER in NC.
    destruct (hdrs_mem_in _ _ _ HS2 Hh) as [HM HP']. destruct HM as ([pad2 HC] & VC & _). unfold hdro_pure in HP'.
    unfold node_cells in NC. unfold mbuf_cells in VC.
    destruct (hdr_blk_facts h Hh) as ((G1 & G2 & G3 & G3') & (G4 & G5 & G6 & G7) & _).
    destruct (node_blk_facts _ _ Hb) as (NB1 & NB2 & NB3). rewrite <- ER in NB1, NB2.
    destruct (blk_facts b) as (_ & NB4 & NB5 & _).
    { unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hb). }
    lazymatch type of ER with ?rv = _ => subst rv end.
    assert (R8 : blk_addr b mod 8 = 0) by (clear -NB4; Z.div_mod_to_equations; lia).
    assert (HA8 : hA AI h mod 8 = 0) by (clear -G3; Z.div_mod_to_equations; lia).
    assert (VL : vlen AI h <= VMAX) by (destruct (BND h Hh); lia). unfold VMAX in VL.
    pose proof alloc_ceiling_bounds as ACB.
    assert (R64 : (0 <= blk_addr b < 2^64)%Z) by lia.
    assert (HA64 : (0 <= hA AI h < 2^64)%Z) by lia.
    assert (VA64 : (0 <= vA AI h < 2^64)%Z) by lia.
    uwalk_ub_to 0x15518.
    eapply (clen_num h); try eassumption; try reflexivity; try lia. close_ctx.
  Qed.

  #[using="All"] Lemma outside_vals_intro : forall hs0 x, (forall h', In h' hs0 -> ~ (vA AI h' <= x < vA AI h' + (vcap AI h' + 1))) ->
    outside (map (fun h' => (vA AI h', vA AI h' + (vcap AI h' + 1))) hs0) x.
  Proof.
    induction hs0 as [|h0 hs0 IH]; intros x H; cbn; [exact I|]. split; [apply H; left; reflexivity| apply IH; intros h' Hh'; apply H; right; exact Hh'].
  Qed.

  #[using="All"] Lemma blk_eq_dec : forall b1 b2 : BLK, {b1 = b2} + {b1 <> b2}.
  Proof.
    intros [[k1 a1] n1] [[k2 a2] n2].
    destruct (ai_K_eqb rsegs AI k1 k2) eqn:E.
    - apply (proj1 (ai_K_eqb_eq rsegs AI k1 k2)) in E. subst k2.
      destruct (Z.eq_dec a1 a2) as [->|NE]; [| right; intros H; injection H; intros; exact (NE ltac:(assumption))].
      destruct (Z.eq_dec n1 n2) as [->|NE]; [left; reflexivity| right; intros H; injection H; intros; exact (NE ltac:(assumption))].
    - right. intros H. injection H as -> -> ->. pose proof (proj2 (ai_K_eqb_eq rsegs AI k2 k2) eq_refl). congruence.
  Qed.

  #[using="All"] Lemma vslack_outside : forall h x, In h hs -> 0 <= vcap AI h ->
    vA AI h + (vcap AI h + 1) <= x < round_up8 (vA AI h + (vcap AI h + 1)) -> outside GW x.
  Proof.
    intros h x Hh VC0 Hx. pose proof sp_facts as SF.
    destruct (hdr_blk_facts h Hh) as (_ & (V1 & V2 & V3 & V4) & _). pose proof (vblk_in h Hh) as VIN.
    assert (RU : round_up8 (vA AI h + (vcap AI h + 1)) <= alloc_ceiling) by (unfold round_up8 in *; Z.div_mod_to_equations; lia).
    assert (RW : round_up8 (vA AI h + (vcap AI h + 1)) <= 0x2a000 \/ 0x5d000 <= vA AI h).
    { clear -V4 VC0 V1. unfold round_up8. destruct V4; [left | right]; Z.div_mod_to_equations; lia. }
    unfold germ_W. cbn [outside]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    apply outside_vals_intro. intros h' Hh' C.
    destruct (hdr_blk_facts h' Hh') as (_ & (W1 & W2 & W3 & _) & _). pose proof (vblk_in h' Hh') as VIN'.
    destruct (blk_eq_dec (vblk h') (vblk h)) as [E|NE].
    - unfold vblk in E. injection E as EK EA EC. lia.
    - pose proof (blocks_apart _ _ VIN' VIN NE) as DJ. unfold vblk in DJ. cbn [blk_addr blk_size fst snd] in DJ.
      clear -DJ C Hx W3 VC0. unfold round_up8 in *. Z.div_mod_to_equations. lia.
  Qed.

  #[using="All"] Lemma vslack_bytes : forall m h vbs', hide (munch GW m0 m) -> In h hs -> 0 <= vcap AI h ->
    u8arr rsegs m (vA AI h) vbs' -> length vbs' = Z.to_nat (vcap AI h + 1) ->
    exists sl, bytes_at rsegs m (vA AI h) (vbs' ++ sl)
               /\ Z.of_nat (length sl) = round_up8 (vA AI h + (vcap AI h + 1)) - (vA AI h + (vcap AI h + 1)).
  Proof.
    intros m h vbs' MU Hh VC0 [B _] L. pose proof sp_facts as SF. unfold hide in MU.
    destruct (hdr_blk_facts h Hh) as (_ & (V1 & V2 & V3 & _) & _). pose proof (vblk_in h Hh) as VIN. pose proof (BSUB _ VIN) as VLB.
    assert (RU : vA AI h + (vcap AI h + 1) <= round_up8 (vA AI h + (vcap AI h + 1)) <= alloc_ceiling) by (unfold round_up8 in *; Z.div_mod_to_equations; lia).
    destruct (bytes_at_extend (Z.to_nat (round_up8 (vA AI h + (vcap AI h + 1)) - (vA AI h + (vcap AI h + 1)))) m (vA AI h) vbs' B) as (sl & B2 & L2).
    - intros x Hx. destruct (ai_block_slack rsegs AI _ _ _ _ x HR0 VLB) as [v Hv]. { unfold vblk. cbn [blk_addr blk_size fst snd]. lia. }
      exists v. rewrite <- Hv. eapply mrd_munch; [exact MU| | lia]. eapply vslack_outside; [exact Hh| exact VC0| lia].
    - lia.
    - exists sl. split; [exact B2| lia].
  Qed.

  #[using="All"] Lemma upnp_call : forall (qq lo0 : Z)
      (ra0 gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
      (F0 : bvmap 5 word) (fc0 : bv 32) (m : mem),
    rw_cells rsegs m INITWASCALLED [C1 (Z_to_bv 8 0)] ->
    stk rsegs m lo0 qq -> (lo0 <= qq - 192)%Z -> (INITWASCALLED + 1 <= lo0)%Z -> (0 <= qq < 2^64)%Z -> mem_inv rsegs m ->
    evt rsegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
        ms' = MS (mkR ra0 (wz qq) gp0 tp0 t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                 F0 (ret_pc ra0) fc0 None m' (seg_rom rsegs)
        /\ munch [(qq - 192, qq)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo0 qq
        /\ rw_cells rsegs m' INITWASCALLED [C1 (Z_to_bv 8 0)])
      (MS (mkR ra0 (wz qq) gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F0 (wz UpnpPrintf_entry) fc0 None m (seg_rom rsegs)).
  Proof.
    clear. intros until m. intros IW ST LO IL QQ MI.
    assert (E0 : bv_unsigned (Z_to_bv 64 qq) = qq) by (apply unsigned_lit; lia).
    eapply evt_mono.
    { eapply (UpnpPrintf_spec ra0 (Z_to_bv 64 qq) gp0 tp0 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 F0 fc0 m lo0);
        rewrite ?E0; eauto; try lia. }
    intros ms' Q. unfold UpnpPrintf_post in Q. rewrite !E0 in Q. exact Q.
  Qed.

  #[using="All"] Lemma te_found : forall (b : BLK) (h : hdr) m (j0 ja : list byte) cs2
      x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31,
    ctx m -> rw_cells rsegs m q [CB 24 j0] -> rw_cells rsegs m (q + 24) [CB 16 ja; C4 (wz 22)] -> rw_cells rsegs m (q + 44) cs2 -> cells_size cs2 = 68%nat ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    In (b, hA AI h) ns -> In h hs ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 (P + 288)) (Z_to_bv 64 P) (Z_to_bv 64 (blk_addr b)) x11 x12 x13 x14 x15 x16 x17
                            x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15464) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros C F0 F1 F2 L2 PCC Be Bh Bp Bn Bc Bz Bu Hb Hh. pose proof sp_facts as SF. pose proof q_sp as QSP.
    pose proof C as C0. open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp. pose proof SPA as [SPA'].
    pose proof PH as PH0. destruct PH0 as (_ & _ & _ & DL & HS & MAP & BND & _).
    destruct (dlseg_in_cells _ _ _ _ _ _ DL Hb) as (pv & nx & NC). unfold node_cells in NC.
    destruct (hdrs_mem_in _ _ _ HS Hh) as [HM HP]. destruct HM as ([pad2 HC] & VC & [vbs [VB VN]] & _). pose proof HP as HP0. unfold hdro_pure in HP.
    unfold mbuf_cells in VC.
    destruct (hdr_blk_facts h Hh) as ((G1 & G2 & G3) & (G4 & G5 & G6 & G7) & _).
    destruct (node_blk_facts _ _ Hb) as (NB1 & NB2 & NB3).
    assert (NB4 : blk_addr b mod 16 = 0).
    { destruct (blk_facts b) as (_ & E & _); [| exact E]. unfold hl_blocks. apply in_or_app. left. exact (in_map fst _ _ Hb). }
    assert (VL : vlen AI h <= VMAX) by (destruct (BND h Hh); lia). unfold VMAX in VL.
    pose proof (rw_CB_len _ _ _ _ VB) as LVB.
    destruct (vslack_bytes m h vbs MU0 Hh ltac:(lia) (u8arr_of_rw_cells _ _ _ _ _ VB) LVB) as (sl & SLB & LSL).
    apply bytes_at_app in SLB. destruct SLB as [_ SLB]. rewrite LVB, Z2Nat.id in SLB by lia.
    assert (RU8 : vA AI h + (vcap AI h + 1) <= round_up8 (vA AI h + (vcap AI h + 1)) <= alloc_ceiling).
    { clear -G4 G5 SF. unfold round_up8. Z.div_mod_to_equations. lia. }
    assert (RW8 : round_up8 (vA AI h + (vcap AI h + 1)) <= 0x2a000 \/ 0x5d000 <= vA AI h).
    { clear -G7 G4. unfold round_up8. destruct G7; [left | right]; Z.div_mod_to_equations; lia. }
    assert (BA64 : (0 <= blk_addr b < 2^64)%Z).
    { destruct (blk_facts b) as (E1 & _ & E3 & E4 & _); [unfold hl_blocks; apply in_or_app; left; exact (in_map fst _ _ Hb)|].
      pose proof alloc_ceiling_bounds as ACB. lia. }
    assert (HA64 : (0 <= hA AI h < 2^64)%Z) by (pose proof alloc_ceiling_bounds; lia).
    assert (HA8 : (hA AI h mod 8 = 0)%Z) by (first [lia | (Z.div_mod_to_equations; lia)]).
    assert (BA8 : (blk_addr b mod 8 = 0)%Z) by (first [lia | (clear - NB4; Z.div_mod_to_equations; lia)]).
    uwalk_ub_to 0x155d4.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    lazymatch goal with F0 : rw_cells _ _ q [?c0; ?c1; ?c2] |- _ =>
      pose proof F0 as F0w;
      change (rw_cells rsegs m1 q ([c0] ++ [c1; c2])) in F0; apply rw_cells_app in F0; destruct F0 as [F0a MPC] end.
    pose proof (p_hlist_transport_c _ _ PH MU WMp) as PH1.
    let a0v := reg_val 10 in replace a0v with (Z_to_bv 64 (q + 8)) by (rewrite ?QSP; f_equal; lia).
    let a1v := reg_val 11 in replace a1v with (Z_to_bv 64 NAD) by (unfold NAD; f_equal; lia).
    eapply evt_cut.
    { eapply (rfs_call q lo (q + 8) (vA AI h) (vcap AI h + 1) (vlen AI h) vbs sl canary).
      all: side (first [exact MPC | exact VB | exact VN | exact SLB | exact ST | assumption | reflexivity
                       | (rewrite ?LSL; unfold round_up8, got_ssp, ssp_guard, NAD, GERM_DEPTH in *; Z.div_mod_to_equations; lia)]). }
    intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & vbs' & -> & MUr & WMr & MIr & STr & VBr & ZPr).
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    assert (MUw : munch [(lo, bv_unsigned sp); (vA AI h, vA AI h + (vcap AI h + 1))]%Z m1 m2).
    { eapply munch_weaken; [| exact MUr]. intros x Hx. cbn [outside] in *. lia. }
    pose proof (p_hlist_relower _ _ _ _ _ PH1 Hh MUw WMr VB VBr ZPr) as PH2.
    assert (MU2 : hide (munch GW m0 m2)). { unfold hide in *. exact (GW_of_Wb _ _ _ (GW_of_Wc _ _ MU0 MU) Hh MUw). }
    assert (WM2 : wmono rsegs m0 m2) by (first [ eapply wmono_trans; [exact WM| exact WMr] | eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WMp| exact WMr]] ]).
    clear MU MUw MU0.
    transport_after_call rsegs m1 m2 MUr WMr.
    clear MUr WMr WMp PH PH1 WM. try clear F0a. try clear MPC. rename MU2 into MU0. rename WM2 into WM. rename PH2 into PH.
    pose proof (munch_refl Wc m2) as MU. pose proof (wmono_refl rsegs m2) as WMp.
    assert (CTX2 : ctx m2) by close_ctx.
    zstep. if_cases K0; zify_cond K0.
    { destruct (rw_cells_forget rsegs m2 q _ F0w) as [j0' F0']. cbn [cells_size csize Nat.add] in F0'. clear F0w.
      eapply clen_part; try eassumption; try reflexivity; try lia. }
    clear CTX2. unfold p_ctl_cells in PCC.
    zstep. sstep.
    uwalk_ub_to 0x154c4. zstep.
    callq (upnp_call q lo).
    all: side (first [exact IW | assumption | reflexivity | (unfold GERM_DEPTH in *; lia)]).
    zstep. eapply (r6 3 clen); try eassumption; try reflexivity; try lia. close_ctx.
  Qed.

  #[using="All"] Lemma te_part : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 m jA,
    ctx m -> rw_cells rsegs m q [CB 112 jA] ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x15440) fc None m (seg_rom rsegs)).
  Proof.
    intros until jA. intros C FRA PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF. pose proof q_sp as QSP. open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp.
    zstep. sstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) => rename m1 into m1 end.

    lazymatch goal with FRA : rw_cells _ _ q [CB 40 ?jx; ?c1; ?c2] |- _ =>
      pose proof (rw_cells_split_CB rsegs m1 q [] 40 jx [c1; c2] [24; 16]%nat FRA eq_refl) as FRA'; clear FRA; cbn [mk_CB_cells app] in FRA' end.
    lazymatch goal with FRA' : rw_cells _ _ q [?e0; ?e1; ?e2; ?e3] |- _ =>
      change (rw_cells rsegs m1 q ([e0] ++ [e1; e2] ++ [e3])) in FRA'; apply rw_cells_app in FRA'; destruct FRA' as [F0 FRA'];
      apply rw_cells_app in FRA'; destruct FRA' as [F1 F2]; cbn [cells_size csize Nat.add] in F1, F2 end.
    replace (q + Z.of_nat 24) with (q + 24) in F1 by lia.
    replace (q + Z.of_nat 24 + Z.of_nat 20) with (q + 44) in F2 by lia.
    pose proof (p_hlist_transport_c _ _ PH MU WMp) as PH1. destruct PH1 as (LH & FL & FC & DL & HS & MAP & BND & ZL & X0).
    assert (LL : rw_cells rsegs m1 (P + 288) (llist_cells (hd_addr AI ns (P + 312)) (last_addr AI ns (P + 288)) (zlength ns) 0 0 httpheader_free_entry httpmsg_compare_entry)).
    { apply (proj2 (llist_split m1 (P + 288) _ _ _ 0 0 _ _)). replace (P + 288 + 56) with (P + 344) by lia. replace (P + 288 + 80) with (P + 368) by lia.
      split; [exact LH| split; [exact FL| exact FC]]. }
    assert (LS : lseg m1 (lf_nodes AI ns hs) (hd_addr AI ns (P + 312)) (P + 288) (P + 288 + 24)).
    { replace (P + 288 + 24) with (P + 312) by lia. eapply lf_lseg; eauto.
      intros b it Hb. destruct (in_ns_item _ _ _ _ MAP Hb) as (h & Hh & ->). destruct (hdr_blk_facts h Hh) as ((G1 & _) & _). lia. }
    assert (SEPN : forall N it id, In (N, it, id) (lf_nodes AI ns hs) -> N + 24 <= lo /\ it + 24 <= lo).
    { intros N it id HN. destruct (lf_nodes_in2 AI ns hs N it id MAP HN) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (node_blk_facts _ _ Hb) as (NB1 & NB2 & NB3). destruct (dlseg_facts AI _ _ _ _ _ _ DL Hb) as (SZ & _).
      destruct (hdr_blk_facts h Hh) as ((G1 & G2 & _) & _). lia. }
    pose proof PA8 as [PA8']. pose proof SPA as [SPA'].
    assert (SEPA : forall N it id, In (N, it, id) (lf_nodes AI ns hs) -> N mod 8 = 0 /\ it mod 8 = 0).
    { intros N it id HN. destruct (lf_nodes_in2 AI ns hs N it id MAP HN) as (b & h & Hb & Hh & -> & -> & ->).
      destruct (blk_facts b) as (_ & BA & _).
      { unfold hl_blocks. apply in_or_app. left. apply in_map_iff. exists (b, hA AI h). auto. }
      destruct (hdr_blk_facts h Hh) as ((_ & _ & HA & _) & _). clear -BA HA. split; Z.div_mod_to_equations; lia. }
    clear LH FL FC.
    zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch type of F1 with rw_cells _ _ _ [CB 16 ?ja; _] =>
      callq (ListFind_call q lo (P + 288) (q + 24) 22 (last_addr AI ns (P + 288)) (zlength ns) 0 0 httpheader_free_entry (lf_nodes AI ns hs) ja) end.
    all: side (first [exact LL | exact LS | exact F1 | exact ST | exact SEPN | exact SEPA | assumption | reflexivity | lia | (rewrite ?QSP; f_equal; lia)
                     | (clear -PA8' SPA'; Z.div_mod_to_equations; lia)]).
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    match goal with H : (?r = 0 \/ exists it, In (?r, it, 22) _)%Z |- _ => rename H into RES end.
    clear LL LS.
    zstep. if_cases K0; zify_cond K0.
    {   eapply clen_part; try eassumption; try reflexivity; try lia. close_ctx. }
    destruct RES as [-> | [it HIN]]. { exfalso. apply K0. reflexivity. }
    destruct (lf_nodes_in2 AI ns hs _ _ _ MAP HIN) as (b & h & Hb & Hh & ER & _ & ->).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m2 end.
    subst.
    lazymatch goal with |- context [Z_to_bv 64 ?r] => idtac end.
    eapply (te_found b h); try eassumption; try reflexivity; try lia. close_ctx.
  Qed.

  #[using="All"] Lemma done : forall x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 m jA,
    ctx m -> rw_cells rsegs m q [CB 112 jA] ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x153e0) fc None m (seg_rom rsegs)).
  Proof.
    intros until jA. intros C FRA PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF. open_ctx C.
    pose proof (munch_refl Wc m) as MU. pose proof (wmono_refl rsegs m) as WMp. unfold p_ctl_cells in PCC.
    zstep. zstep. sstep.
    eapply (ret 0 err hack 4 entp clen errv); try eassumption.
    - unfold hide in *. exact (GW_of_Wc _ _ MU0 MU).
    - split; [exact PCC| lia].
    - exact (p_hlist_transport_c _ _ PH MU WMp).
    - left. unfold POS_COMPLETE. repeat split; reflexivity.
  Qed.

  #[using="All"] Lemma body24 : forall x1 x5 x6 x7 x8 x9 x11 x12 x14 x15 x16 x17 x18 x28 x29 x30 x31 m jA,
    ctx m -> rw_cells rsegs m q [CB 112 jA] -> p_rs m P rm sc ->
    rw_cells rsegs m (P + 440) (p_ctl_cells err hack pos entp clen csz cur) ->
    0 <= err < 2^31 -> 0 <= hack <= 1 -> 0 <= pos <= 4 -> 0 <= entp <= 6 -> 0 <= clen < 2^32 -> 0 <= csz < 2^64 -> 0 <= cur < 2^64 ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 P) x11 x12 (Z_to_bv 64 isreq) x14 x15 x16 x17 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x153c0) fc None m (seg_rom rsegs)).
  Proof.
    intros until jA. intros C1 FRA PRS PCC Be Bh Bp Bn Bc Bz Bu. pose proof sp_facts as SF.
    destruct PRS as (PRc & PRb1 & PRb2). pose proof C1 as C. open_ctx C.
    zstep. if_cases K0; zify_cond K0.
    -
      zstep. rewrite (sx32_lit sc) by lia. zstep. zstep. if_cases K1; zify_cond K1.
      { eapply done; try eassumption; lia. }
      zstep. zstep. if_cases K2; zify_cond K2.
      { eapply done; try eassumption; lia. }
      zstep. zstep. zstep. if_cases K3; zify_cond K3.
      { eapply done; try eassumption; lia. }
      zstep. rewrite (sx32_lit rm) by lia. zstep. zstep. zstep. if_cases K4; zify_cond K4.
      { eapply done; try eassumption; lia. }
      zstep. zstep. if_cases K5; zify_cond K5.
      { eapply done; try eassumption; lia. }
      eapply te_part; try eassumption; lia.
    -
      zstep. rewrite (sx32_lit meth) by lia. zstep. zstep. if_cases K1; zify_cond K1.
      { eapply te_part; try eassumption; lia. }
      zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      { eapply te_part; try eassumption; lia. }
      eapply done; try eassumption; lia.
  Qed.

  #[using="All"] Lemma body : forall x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 errv,
    RHEAP rsegs AI s LB m0 ->
    p_meth m0 P meth -> p_rs m0 P rm sc -> p_ver m0 P isreq maj min -> p_hlist AI m0 P ns hs X ->
    p_ent m0 P eb el -> p_msg AI m0 LB P A len cap okm bs -> p_ctl m0 P err hack pos entp clen csz esp -> p_scan m0 P cur ->
    rw_cells rsegs m0 TPE [C4 errv] -> rw_cells rsegs m0 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m0 ssp_guard [C8 canary] ->
    rw_cells rsegs m0 INITWASCALLED [C1 (Z_to_bv 8 0)] ->
    stk rsegs m0 lo SP -> mem_inv rsegs m0 ->
    evt rsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 germ_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until errv. intros HR PM PRS PV PH PE PMSG PC PSC ERR GOT CAN IW ST MI. unfold germ_entry.
    pose proof sp_facts as SF. pose proof q_sp as QSP. pose proof PA8 as [PA8'].
    assert (ARNG : 0 <= A /\ A + cur < 2^64).
    { destruct (p_msg_facts AI _ _ _ _ _ _ _ _ s HR PMSG) as (F1 & F2 & _ & F4 & F5). destruct okm as [k|].
      - destruct (F5 ltac:(discriminate)) as (G1 & G2 & _). lia.
      - destruct (F4 eq_refl) as (G1 & G2 & _). lia. }
    assert (ANZ : 0 < cur -> 0 < A).
    { destruct (p_msg_facts AI _ _ _ _ _ _ _ _ s HR PMSG) as (F1 & F2 & _ & F4 & F5). destruct okm as [k|].
      - destruct (F5 ltac:(discriminate)) as (G1 & _). intros _. lia.
      - destruct (F4 eq_refl) as (G1 & G2 & _). lia. }
    destruct PM as [PMc PMb]. destruct PRS as (PRc & PRb1 & PRb2). destruct PV as [[pad PVc] PVb]. unfold p_ent in PE.
    destruct (p_msg_facts AI _ _ _ _ _ _ _ _ s HR PMSG) as (ML1 & ML2 & _). destruct PMSG as (MBC & _). unfold mbuf_cells in MBC.
    destruct PC as (PCC & Be & Bh & Bp & Bn & Bc & Bz & Bs). unfold p_ctl_cells in PCC. unfold p_scan in PSC.
    unfold got_ssp, ssp_guard in GOT, CAN. unfold LMAX in ML2.
    pose proof (munch_refl Wc m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    carve_frame 144%nat ST.
    zstep. do 4 sstep.
    uwalk_ub_to 0x153a0.
    destruct (Z.eq_dec A 0) as [A0|A0]; uwalk_ub_to 0x153c0.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    all: lazymatch goal with FR : rw_cells _ _ q (CB 112 ?jA :: ?rest) |- _ =>
      change (rw_cells rsegs m1 q ([CB 112 jA] ++ rest)) in FR; apply rw_cells_app in FR; destruct FR as [FRA FRBm];
      cbn [cells_size csize Nat.add] in FRBm; change (Z.of_nat 112) with 112%Z in FRBm end.
    all: assert (MU0 : hide (munch GW m0 m1)) by (unfold hide; eapply GW_of_Wc; [apply munch_refl| exact MU]).
    all: assert (PH1 : p_hlist AI m1 P ns hs X) by exact (p_hlist_transport_c _ _ PH MU WM).
    all: assert (C1 : ctx m1) by (split; [exact MU0|]; split; [exact WM|]; split; [assumption|]; split; [exact FRBm|]; split; [exact ST|];
      split; [unfold p_ent; replace (A + cur)%Z with (cur + A)%Z by lia; exact PE|];
      split; [exact PH1|]; split; [split; [exact PMc| exact PMb]|]; split; [split; [exists pad; exact PVc| exact PVb]|];
      split; [exists errv; exact ERR|]; split; [exact GOT|]; split; [exact CAN| exact IW]).
    all: eapply body24; try eassumption; try lia.
    all: split; [exact PRc| lia].
  Qed.
End WALK.

Lemma germ_spec {HCEIL : HasCeiling} : forall AI : alloc_if rsegs, germ_stmt AI.
Proof.
  intros AI. unfold germ_stmt. intros until m.
  intros B4096 BIMG HR BSUB ND PM PRS PV PH XV PE PMSG PC PSC CUR ERR GOT CAN IW ST LOC LOD MI PSP PHI TP1 TP2 DE1 DE2 DE3 TPW1 TPW2 PA8 SPA TPA ->.
  eapply body; eauto. all: constructor; assumption.
Qed.
