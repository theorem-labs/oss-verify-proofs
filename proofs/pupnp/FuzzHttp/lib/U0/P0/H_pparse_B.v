(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_obj H_prep H_map_str_to_int H_httpmsg_destroy H_membuffer_assign
     H_parse_uri_A H_UpnpPrintf H_entity_read_method H_pent_A H_pent_B H_pent_C H_phdr_B H_phdr_C H_phdr_D H_presp_A H_presp_C
     H_memptr_cmp H_pparse_stmt H_pparse_A.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Lemma bsub_perm {HCEIL : HasCeiling} : forall (AI : alloc_if rsegs) (OB OB' LB : list (block (ai_K rsegs AI))),
  Permutation OB OB' -> bsub AI OB LB -> bsub AI OB' LB.
Proof. intros AI OB OB' LB HP HS b Hb. apply HS. eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]. Qed.

Lemma nodup_ids_perm : forall {Kt} (OB OB' : list (block Kt)), Permutation OB OB' -> NoDup (map blk_id OB) -> NoDup (map blk_id OB').
Proof.
  intros Kt OB OB' HP ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP| exact ND].
Qed.

Lemma perm_rot : forall {A} (l1 l2 : list A), Permutation (l1 ++ l2) (l2 ++ l1).
Proof. intros. apply Permutation_app_comm. Qed.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).

  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L_ = 0x180f0.
  Hypothesis FREEPC : al_free_pc L_ = 0x17fb0.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.
  Hypothesis TPV : al_tp L_ = 0x3b820.
  Hypothesis ERRNOV : al_errno L_ = 0x3b77c.
  Hypothesis CAN : canary_ok AI.
  Hypothesis ERRNC : forall lo hi, al_client_static L_ lo hi -> hi <= al_errno L_ \/ al_errno L_ + 4 <= lo.
  Hypothesis BLK4096 : blk4096_ok AI.
  Hypothesis BLKIMG : blk_img_ok AI.
  Hypothesis BLKWIN : forall s LB m (b : BLK), RHEAP rsegs AI s LB m -> In b LB -> blk_addr b + blk_size b <= 0x2a000 \/ 0x5d000 <= blk_addr b.
  Hypothesis GERM : germ_stmt AI.
  Hypothesis SNC : strncasecmp_stmt.
  Hypothesis IMGW1 : In (0x10000, 0x2a000)%Z (al_img L_).
  Hypothesis IMGW2 : In (0x2a000, 0x5d000)%Z (al_img L_).
  Hypothesis GMST : exists lo hi, al_client_static L_ lo hi /\ lo <= GMAXA /\ GMAXA + 8 <= hi.
  Hypothesis IWST : exists lo hi, al_client_static L_ lo hi /\ lo <= INITWASCALLED /\ INITWASCALLED + 1 <= hi.
  Hypothesis GOTGMST : exists lo hi, al_client_static L_ lo hi /\ lo <= GOT_GMAX /\ GOT_GMAX + 8 <= hi.
  Hypothesis TABST : exists lo hi, al_client_static L_ lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi.
  Hypothesis ZST : exists lo hi, al_client_static L_ lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi.
  Hypothesis MTST : exists lo hi, al_client_static L_ lo hi /\ lo <= METHOD_TAB /\ METHOD_TAB + 176 <= hi.
  Hypothesis GIFST : exists lo hi, al_client_static L_ lo hi /\ lo <= GIF /\ GIF + 4 <= hi.
  Hypothesis GOTGIFST : exists lo hi, al_client_static L_ lo hi /\ lo <= GOT_GIF /\ GOT_GIF + 8 <= hi.

  Hypothesis REQL : reql_stmt AI.

  Notation bsub := (bsub AI).
  Notation okb := (okb AI).
  Notation hl_blocks := (hl_blocks AI).
  Notation ps_blocks := (ps_blocks AI).

  #[using="AC LOK MALPC FREEPC REALLOCPC SNC IMGW1 IMGW2 TABST ZST"] Lemma PH : parse_headers_stmt AI.
  Proof. exact (parser_parse_headers_spec AI AC LOK MALPC FREEPC REALLOCPC SNC IMGW1 IMGW2 TABST ZST). Qed.

  #[using="Type"] Lemma disjoint_from_forall : forall W a n, Forall (fun iv : ivl => a + n <= fst iv \/ snd iv <= a)%Z W -> disjoint_from W a n.
  Proof. induction W as [|[u v] W IH]; intros a n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

  #[using="Type"] Lemma outside_forall : forall W x, Forall (fun iv : ivl => ~ (fst iv <= x < snd iv))%Z W -> outside W x.
  Proof. induction W as [|[u v] W IH]; intros x H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

  #[using="Type"] Lemma outside_forall_iff : forall W x, outside W x <-> Forall (fun iv : ivl => ~ (fst iv <= x < snd iv))%Z W.
  Proof.
    induction W as [|[u v] W IH]; intros x; cbn.
    - split; [intros _; constructor| intros _; exact I].
    - split.
      + intros [H1 H2]. constructor; [cbn; lia| apply IH; exact H2].
      + intros H. inversion H; subst. cbn in *. split; [lia| apply IH; assumption].
  Qed.

  #[using="LOK"] Lemma static_disjoint : forall s LB m (W : list ivl) lo slo shi X0 n,
    RHEAP rsegs AI s LB m -> al_client_static L_ slo shi -> (slo <= X0)%Z -> (X0 + n <= shi)%Z -> (alloc_ceiling <= lo)%Z ->
    Forall (fun iv : ivl => lo <= fst iv \/ exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z W ->
    disjoint_from W X0 n.
  Proof.
    intros s LB m W lo slo shi X0 n HR ST S1 S2 CEIL FW. apply disjoint_from_forall.
    eapply Forall_impl; [| exact FW]. intros [u v] Hiv. cbn in *.
    destruct (lo_static_img rsegs AI LOK slo shi ST) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw) as W3.
    destruct Hiv as [Hiv|(b & Hb & B1 & B2)]; [lia|].
    destruct (ai_block_range rsegs AI _ _ _ _ HR Hb) as (_ & _ & _ & _ & RF). pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1. lia.
  Qed.

  #[using="LOK GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST"] Lemma stat_keep : forall s LB m m' (W : list ivl) (LBKc : list BLK) SP lo gmax gifv ws mws,
    pp_stat m gmax gifv ws mws -> hpx AI W LBKc SP m m' -> RHEAP rsegs AI s LB m -> (alloc_ceiling <= lo)%Z ->
    length ws = 66%nat -> length mws = 22%nat ->
    Forall (fun iv : ivl => lo <= fst iv \/ exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z W ->
    pp_stat m' gmax gifv ws mws.
  Proof.
    intros s LB m m' W LBKc SP lo gmax gifv ws mws (TAB & [zb ZB] & MTB & GG & GF & GM & IW & GGM) HP HR CEIL WSL MWL FW.
    destruct TABST as (l1 & h1 & ST1 & A1 & B1). destruct ZST as (l2 & h2 & ST2 & A2 & B2). destruct MTST as (l3 & h3 & ST3 & A3 & B3).
    destruct GOTGIFST as (l4 & h4 & ST4 & A4 & B4). destruct GIFST as (l5 & h5 & ST5 & A5 & B5). destruct GMST as (l6 & h6 & ST6 & A6 & B6).
    destruct IWST as (l7 & h7 & ST7 & A7 & B7). destruct GOTGMST as (l8 & h8 & ST8 & A8' & B8).
    Ltac sk HP HR ST CEIL FW := first
      [ eapply (hpx_rw_cells rsegs AI); [exact HP| eassumption| eapply client_range_static; [exact ST| cbn; lia| cbn; lia]| eapply static_disjoint; [exact HR| exact ST| cbn; lia| cbn; lia| exact CEIL| exact FW]]
      | eapply (hpx_bytes_at rsegs AI); [exact HP| eassumption| eapply client_range_static; [exact ST| cbn; lia| cbn; lia]| eapply static_disjoint; [exact HR| exact ST| cbn; lia| cbn; lia| exact CEIL| exact FW]] ].
    split. { destruct TAB as [TB TW]. pose proof (bytes_at_bound _ _ _ _ TB) as BB. rewrite u64s_length, WSL in BB. split.
             - eapply (hpx_bytes_at rsegs AI); [exact HP| exact TB| eapply client_range_static; [exact ST1| lia| rewrite u64s_length, WSL; cbn; lia]|].
               eapply static_disjoint; [exact HR| exact ST1| lia| rewrite u64s_length, WSL; cbn; lia| exact CEIL| exact FW].
             - eapply (hpx_wr_at rsegs AI); [exact HP| exact TW| eapply client_range_static; [exact ST1| lia| rewrite WSL; cbn; lia]|].
               eapply static_disjoint; [exact HR| exact ST1| lia| rewrite WSL; cbn; lia| exact CEIL| exact FW]. }
    split. { exists zb. eapply (hpx_bytes_at rsegs AI); [exact HP| exact ZB| eapply client_range_static; [exact ST2| lia| cbn; lia]|].
             eapply static_disjoint; [exact HR| exact ST2| lia| cbn; lia| exact CEIL| exact FW]. }
    split. { destruct MTB as [TB TW]. split.
             - eapply (hpx_bytes_at rsegs AI); [exact HP| exact TB| eapply client_range_static; [exact ST3| lia| rewrite u64s_length, MWL; cbn; lia]|].
               eapply static_disjoint; [exact HR| exact ST3| lia| rewrite u64s_length, MWL; cbn; lia| exact CEIL| exact FW].
             - eapply (hpx_wr_at rsegs AI); [exact HP| exact TW| eapply client_range_static; [exact ST3| lia| rewrite MWL; cbn; lia]|].
               eapply static_disjoint; [exact HR| exact ST3| lia| rewrite MWL; cbn; lia| exact CEIL| exact FW]. }
    split. { eapply (hpx_bytes_at rsegs AI); [exact HP| exact GG| eapply client_range_static; [exact ST4| lia| rewrite length_le8; cbn; lia]|].
             eapply static_disjoint; [exact HR| exact ST4| lia| rewrite length_le8; cbn; lia| exact CEIL| exact FW]. }
    split. { eapply (hpx_bytes_at rsegs AI); [exact HP| exact GF| eapply client_range_static; [exact ST5| lia| rewrite length_le4; cbn; lia]|].
             eapply static_disjoint; [exact HR| exact ST5| lia| rewrite length_le4; cbn; lia| exact CEIL| exact FW]. }
    split. { eapply (hpx_rw_cells rsegs AI); [exact HP| exact GM| eapply client_range_static; [exact ST6| lia| cbn; lia]|].
             eapply static_disjoint; [exact HR| exact ST6| lia| cbn; lia| exact CEIL| exact FW]. }
    split. { eapply (hpx_rw_cells rsegs AI); [exact HP| exact IW| eapply client_range_static; [exact ST7| lia| cbn; lia]|].
             eapply static_disjoint; [exact HR| exact ST7| lia| cbn; lia| exact CEIL| exact FW]. }
    eapply (hpx_bytes_at rsegs AI); [exact HP| exact GGM| eapply client_range_static; [exact ST8| lia| rewrite length_le8; cbn; lia]|].
    eapply static_disjoint; [exact HR| exact ST8| lia| rewrite length_le8; cbn; lia| exact CEIL| exact FW].
  Qed.

  #[using="Type"] Lemma cells_keep : forall m m' (W : list ivl) (LBKc : list BLK) SP X0 cs,
    rw_cells rsegs m X0 cs -> hpx AI W LBKc SP m m' -> (SP <= X0)%Z -> disjoint_from W X0 (Z.of_nat (cells_size cs)) -> rw_cells rsegs m' X0 cs.
  Proof. intros m m' W LBKc SP X0 cs H HP LE DJ. eapply (hpx_rw_cells rsegs AI); [exact HP| exact H| apply client_range_above; exact LE| exact DJ]. Qed.

  #[using="Type"] Lemma mown_keep : forall m m' (W : list ivl) (LBKc LB LB' : list BLK) SP SA scap (sok : option K) sbs,
    mown AI m LB SA scap sok sbs -> hpx AI W LBKc SP m m' ->
    bsub (okb sok SA scap) LBKc -> bsub (okb sok SA scap) LB' ->
    (forall k, sok = Some k -> disjoint_from W SA (scap + 1)) -> (0 <= scap)%Z ->
    mown AI m' LB' SA scap sok sbs.
  Proof.
    intros m m' W LBKc LB LB' SP SA scap sok sbs OWN HP S1 S2 DJ SC. destruct sok as [k|]; cbn in OWN |- *; [| exact OWN].
    destruct OWN as [HIN CB]. split; [apply S2; left; reflexivity|].
    eapply (hpx_rw_cells rsegs AI); [exact HP| exact CB| |].
    - eapply client_range_block; [apply S1; left; reflexivity| cbn; lia| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
    - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. apply (DJ k eq_refl).
  Qed.

  #[using="LOK"] Lemma hl_keep : forall s m m' (W : list ivl) (LBKc LB : list BLK) SP lo P ns hs X,
    p_hlist AI m P ns hs X -> hpx AI W LBKc SP m m' -> RHEAP rsegs AI s LB m ->
    bsub (hl_blocks ns hs) LBKc -> bsub LBKc LB -> (alloc_ceiling <= lo)%Z ->
    (SP <= P + 288)%Z -> disjoint_from W (P + 288) 96 -> Forall (fun iv : ivl => lo <= fst iv)%Z W ->
    p_hlist AI m' P ns hs X.
  Proof.
    intros s m m' W LBKc LB SP lo P ns hs X (LC & FLC & FF & DL & HS & IT & HB & NB & X0') HP HR S1 S2 CEIL LE DJ FW.
    unfold hl_blocks, H_prep.hl_blocks in S1. apply (bsub_app AI) in S1. destruct S1 as [SN SH].
    assert (HPB : heap_pres AI (map fst ns ++ hdrs_blocks AI hs) (Z.max SP (2^64)) m m').
    { eapply (heap_pres_of_hpx rsegs AI).
      - eapply (hpx_weaken rsegs AI); [exact HP| intros x Hx; exact Hx| lia|].
        intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (SN b Hb)| exact (SH b Hb)].
      - intros a Ha Hc. apply outside_forall_iff. eapply Forall_impl; [| exact FW]. intros [u v] Hu. cbn in *.
        destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b & Hb & Hr)]]; [lia| |].
        + destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). lia.
        + assert (HbL : In b LB) by (apply S2; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [exact (SN b Hb)| exact (SH b Hb)]).
          destruct (ai_block_range rsegs AI _ _ _ _ HR HbL) as (_ & _ & _ & R4 & _). unfold in_block in Hr. lia. }
    split. { eapply cells_keep; [exact LC| exact HP| lia| eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]]. }
    split. { eapply cells_keep; [exact FLC| exact HP| lia| eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]]. }
    split. { eapply cells_keep; [exact FF| exact HP| lia| eapply disjoint_from_sub; [exact DJ| lia| cbn; lia]]. }
    split. { eapply (dlseg_heap_pres AI); [exact DL| exact HPB|]. intros b it Hb. apply in_or_app. left. apply in_map_iff. exists (b, it). split; [reflexivity| exact Hb]. }
    split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPB|]. intros b Hb. apply in_or_app. right. exact Hb. }
    split; [exact IT|]. split; [exact HB|]. split; [exact NB| exact X0'].
  Qed.

  Section ACT.
    Variables (P q lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list BLK) (isreq0 : Z) (m0 : mem).
    Variables (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e gp : word) (F : bvmap 5 word) (fc : bv 32).
    Hypothesis QLO : (lo + PP_DEPTH <= q + 208)%Z.
    Hypothesis QLO2 : (lo <= q + 208 - PP_ADEPTH - al_stack L_)%Z.
    Hypothesis STK0 : (0 <= al_stack L_)%Z.
    Hypothesis LO0 : (0x5d000 <= lo)%Z.
    Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
    Hypothesis QP : (q + 208 <= P)%Z.
    Hypothesis PB : (P + 504 <= B)%Z.
    Hypothesis BHI : (B < 2^62)%Z.
    Hypothesis P8 : (P mod 8 = 0)%Z.
    Hypothesis Q16 : ((q + 208) mod 16 = 0)%Z.
    Hypothesis HT : hdr_tab_ok ws lo.
    Hypothesis MT : meth_tab_ok mws lo.
    Hypothesis GMX : (0 < gmax < 2^32)%Z.

    Notation TP := (wz (al_tp L_)).
    Notation CORE := (pp_core AI P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e).
    Notation POST := (pp_post AI ra (wz (q + 208)) gp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc P lo B gmax gifv ws mws LBK isreq0 m0).
    Notation ST pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m :=
      (pp_st AI P q pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 gp F fc m).

    Definition INV (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (st : pstate AI) : Prop :=
      CORE s LB m st /\ pp_side AI gmax st /\ ps_isreq st = isreq0.

    #[using="TPV P q"] Lemma TPR : (0 <= al_tp L_ < 2^64)%Z. Proof. rewrite TPV. lia. Qed.

    #[using="P lo B QLO LO0 QP PB BHI"] Lemma unsigned_q192 : bv_unsigned (wz (q + 208)) = (q + 208)%Z.
    Proof. apply unsigned_lit. unfold PP_DEPTH in QLO. lia. Qed.

    #[using="Type"] Lemma pp_st_eq : forall pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m,
      ST pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m
      = MS (mkR x1 (wz q) gp (wz (al_tp L_)) t0 t1 t2 (wz P) (wz (P + 480)) a0 a1 a2 a3 a4 a5 a6 a7
               (wz (-1)) (wz 47) (wz 2) (wz FMT_REQ09) (wz METHOD_TAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6)
           F (wz pc) fc None m (seg_rom rsegs).
    Proof. intros. reflexivity. Qed.

    #[using="TPV QLO LO0 QP PB BHI"] Lemma pp_exit : forall s LB m (st : pstate AI) (r : Z) x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      CORE s LB m st -> ps_isreq st = isreq0 -> (0 <= r <= 5)%Z ->
      SREACH AI POST (ST PP_EXIT x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros CO ISR RR.
      destruct CO as (HR & HE & MI & STK & [e ERR] & FSH & FX & PP & BSUB & ND & PST & HPX).
      eapply sreach_evt.
      { rewrite pp_st_eq. unfold PP_EXIT. eapply (pp_epi P q lo (al_tp L_)); try eassumption; unfold PP_DEPTH in QLO; try lia. }
      intros ms' [-> STK']. apply sreach_ret. unfold pp_post.
      do 14 eexists. exists m, r, st. rewrite unsigned_q192.
      split; [reflexivity|]. split; [exact MI|]. split; [exact STK'|]. split; [exact HE|]. split; [exists e; exact ERR|].
      split; [exact HPX|]. split; [exact HR|]. split; [exact PP|]. split; [exact ISR|]. split; [exact BSUB|]. split; [exact ND|]. split; [exact PST| exact RR].
    Qed.

    #[using="TPV QLO LO0 QP PB BHI"] Lemma pp_join_exit : forall s LB m (st : pstate AI) (r : Z) x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      CORE s LB m st -> ps_isreq st = isreq0 -> (0 <= r <= 5)%Z -> r <> 4 ->
      SREACH AI POST (ST PP_JOIN x1 t0 t1 t2 (wz r) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros CO ISR RR NE.
      eapply sreach_evt. { rewrite pp_st_eq. unfold PP_JOIN. eapply (pp_join P q (al_tp L_) TPR). exact RR. }
      intros ms' [[E _]|[_ ->]]; [lia|]. rewrite <- pp_st_eq. apply (pp_exit s LB m st r); assumption.
    Qed.

    Ltac cbn_ps := cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min
                        ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in *; unfold H_pparse_stmt.ps_blocks in *;
                   cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min
                        ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in *.
    Ltac perm_assoc := rewrite ?app_assoc; apply Permutation_refl.

    Ltac perm_rot1 := rewrite <- ?app_assoc; eapply Permutation_trans; [apply Permutation_app_comm|]; rewrite <- ?app_assoc; apply Permutation_refl.

    Ltac in_split H := repeat (apply in_app_or in H; destruct H as [H|H]).
    Ltac in_find H := first [exact H | apply in_or_app; left; in_find H | apply in_or_app; right; in_find H].
    Ltac bsub_tauto B := intros bb Hbb; apply B; in_split Hbb; in_find Hbb.
    Ltac in_tauto := intros bb Hbb; in_split Hbb; in_find Hbb.

    #[using="AC LOK MALPC FREEPC REALLOCPC TPV BLK4096 BLKIMG SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT"] Lemma arm_hdr : forall s LB m (st : pstate AI) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      INV s LB m st -> ps_pos st = POS_HEADERS ->
      (forall s' LB' m' (st' : pstate AI) x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6',
          INV s' LB' m' st' -> (pp_rank (ps_pos st') < pp_rank (ps_pos st))%Z ->
          SREACH AI POST (ST PP_HEAD x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6' m') s' LB') ->
      SREACH AI POST (ST parse_headers_entry (wz PP_JOIN) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros [CO [SIDE ISR]] POS IH.
      destruct st as [cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB].
      destruct CO as (HR & HE & MI & STK & [e ERR] & FSH & FX & PP & BSUB & ND & PST & HPX).
      destruct PP as (PSC & PMSG & CUR & PMETH & PURI & PRS_ & PSM & PVER & PHL & XV & PENT & PCTL & PURL & UBO).
      destruct SIDE as (BUD & SENT & SNE & SRESP & SMETH). cbn_ps. subst pos isreq. pose proof (SNE ltac:(discriminate)) as ENTP1.
      pose proof PST as (TAB & [zb ZB] & _). destruct HT as (WSL & HID & TS). pose proof MT as (MWL & _ & _).
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. unfold PP_DEPTH in QLO. unfold PP_ADEPTH in QLO2.
      destruct (msg_facts AI BLK4096 BLKIMG P _ _ _ _ _ _ _ _ HR PMSG) as (HL0 & HC0 & A0 & AHI & OKS & OKN). unfold LMAX in HC0.
      assert (PMETH11 : p_meth m P meth) by (destruct PMETH as [MC MR]; split; [exact MC| specialize (SMETH ltac:(discriminate)); lia]).
      pose proof PMETH11 as [_ METHR]. pose proof PHL as (_ & _ & _ & _ & _ & _ & _ & _ & X00).
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBP SUBK].
      rewrite pp_st_eq. replace (wz q) with (wz (q - 240 + 240)) by (f_equal; lia).
      eapply sreach_bind.
      { eapply (PH P (q - 240) lo B ws isreq0 maj min cur X len meth A cap okm bs (okb okm A cap ++ okb sok SA scap ++ UB ++ LBK) err hack POS_HEADERS entp clen csz esp ns hs LB s);
          try eassumption; try LiaTuning.alia.
        - replace (q - 240 + 240)%Z with q by lia. exact STK.
        - bsub_tauto BSUB.
        - eapply nodup_ids_perm; [| exact ND]. perm_assoc.
        - split; [exact TAB| exists zb; exact ZB].
        - intros k ->. apply in_or_app. left. left. reflexivity. }
      intros s' LB' ms' PO. unfold ph_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & cur' & meth' & err' & pos' & ns' & hs'
                      & -> & MI' & ST' & HE' & [e' ERR'] & HP' & HR' & PSC' & CUR' & PMSG' & PMETH' & MD & PVER' & PCTL' & ED & PHL' & BSUB' & ND' & TAB' & ZB' & RR & RP & RO).
      replace (q - 240 + 240)%Z with q in * by lia.
      rewrite (ret_pc_even PP_JOIN ltac:(unfold PP_JOIN; lia) eq_refl).

      assert (DJW : forall X0 n, (q <= X0)%Z ->
                (X0 + n <= P + 4 \/ (P + 8 <= X0 /\ X0 + n <= P + 288) \/ (P + 384 <= X0 /\ X0 + n <= P + 440) \/ (P + 452 <= X0 /\ X0 + n <= P + 488) \/ P + 496 <= X0)%Z ->
                disjoint_from (WH AI P okm A cap) X0 n).
      { intros X0 n H1 H2. unfold WH, mwin. destruct okm; cbn; repeat split; lia. }
      assert (FW : Forall (fun iv : ivl => lo <= fst iv \/ exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z (WH AI P okm A cap)).
      { unfold WH, mwin. repeat (apply Forall_cons; [left; cbn; lia|]). destruct okm as [km|]; [| apply Forall_nil].
        apply Forall_cons; [| apply Forall_nil]. right. exists (km, A, cap + 1)%Z. destruct (OKS km eq_refl) as (HIN & _). cbn. split; [exact HIN| lia]. }
      assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z ->
                (X0 + Z.of_nat (cells_size cs) <= P + 4 \/ (P + 8 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 288) \/ (P + 384 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 440)
                 \/ (P + 452 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 488) \/ P + 496 <= X0)%Z -> rw_cells rsegs m' X0 cs).
      { intros X0 cs H H1 H2. eapply cells_keep; [exact H| exact HP'| exact H1| apply DJW; [exact H1| exact H2]]. }
      set (LBKh := okb okm A cap ++ okb sok SA scap ++ UB ++ LBK) in *.
      assert (SUBKh : bsub LBKh LB) by (subst LBKh; bsub_tauto BSUB).
      set (st' := mkPS cur' A len cap okm bs meth' uc rm sc SA slen scap sok sbs isreq0 maj min ns' hs' (X + 2 * (cur' - cur))%Z ebw elw err' hack pos' entp clen csz esp ub UB).
      assert (CO' : CORE s' LB' m' st').
      { split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists e'; exact ERR'|].
        split; [apply (TR _ _ FSH); cbn; lia|].
        split. { destruct FX as ([j1 Q0] & QF16 & [j2 QF56]). split; [exists j1; apply (TR _ _ Q0); cbn; lia|]. split; [apply (TR _ _ QF16); cbn; lia| exists j2; apply (TR _ _ QF56); cbn; lia]. }
        split.
        {   subst st'. unfold p_parser. cbn_ps.
          split; [exact PSC'|]. split; [exact PMSG'|]. split; [lia|]. split; [destruct PMETH' as [MC' MR']; split; [exact MC'| lia]|].
          split; [destruct PURI as [UC USZ]; split; [apply (TR _ _ UC); rewrite ?USZ; cbn; rewrite ?USZ; lia| exact USZ]|].
          split; [destruct PRS_ as (RC & RR1 & RR2); split; [apply (TR _ _ RC); cbn; lia| split; [exact RR1| exact RR2]]|].
          split. { destruct PSM as (SMC & SOWN & SL & SC32). split; [apply (TR _ _ SMC); cbn; lia|]. split; [| split; [exact SL| exact SC32]].
                   eapply mown_keep; [exact SOWN| exact HP'| subst LBKh; in_tauto| | | lia].
                   - subst LBKh. bsub_tauto BSUB'.
                   - intros k ->. destruct SOWN as [SIN _].
                     destruct (ai_block_range rsegs AI _ _ _ _ HR SIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R3, R4.
                     unfold WH, mwin. destruct okm as [km|]; cbn; repeat split; try lia.
                     destruct (OKS km eq_refl) as (HIN & _).
                     assert (NE : (km, A, cap + 1)%Z <> (k, SA, scap + 1)%Z).
                     { intros E. apply (nodup_in_neq AI (hl_blocks ns hs ++ okb (Some km) A cap) (okb (Some k) SA scap ++ UB ++ LBK) (km, A, cap + 1)%Z (k, SA, scap + 1)%Z).
                       - eapply nodup_ids_perm; [| exact ND]. perm_assoc.
                       - apply in_or_app. right. left. reflexivity.
                       - apply in_or_app. left. left. reflexivity.
                       - rewrite E. reflexivity. }
                     pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR HIN SIN NE) as DJ. cbn in DJ. lia. }
          split; [exact PVER'|]. split; [exact PHL'|]. split; [lia|].
          split; [unfold p_ent in *; apply (TR _ _ PENT); cbn; lia|].
          split; [exact PCTL'|].
          split; [destruct PURL as [UC UR]; split; [apply (TR _ _ UC); cbn; lia| exact UR]| exact UBO]. }
        split. { subst st'. cbn_ps. subst LBKh. bsub_tauto BSUB'. }
        split. { subst st'. cbn_ps. subst LBKh. eapply nodup_ids_perm; [| exact ND']. perm_assoc. }
        split. { eapply (stat_keep s LB m m'); [exact PST| exact HP'| exact HR| exact CEIL| exact WSL| exact MWL| exact FW]. }

        eapply (hpx_trans rsegs AI); [exact HPX|].
        intros a Ha Hc Ho. apply (HP' a Ha).
        - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right]. exists b. split; [subst LBKh; in_split Hb; in_find Hb| exact Hr].
        - unfold pp_W in Ho. cbn [outside] in Ho. destruct Ho as [O1 _].
          unfold WH, mwin. cbn [outside app]. repeat split; try lia.
          destruct okm as [km|]; cbn; [| exact I]. split; [| exact I].
          destruct (OKS km eq_refl) as (HIN & _).
          destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & RF). cbn in R1, R3, R4, RF.
          destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b & Hb & Hr)]]; [lia| |].
          + destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2). pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1. lia.
          + assert (NE : b <> (km, A, cap + 1)%Z).
            { intros ->. apply (nodup_in_neq AI (hl_blocks ns hs ++ okb (Some km) A cap ++ okb sok SA scap ++ UB) LBK (km, A, cap + 1)%Z (km, A, cap + 1)%Z ND).
              - apply in_or_app. right. apply in_or_app. left. left. reflexivity.
              - exact Hb.
              - reflexivity. }
            pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR (SUBK b Hb) HIN NE) as DJ. cbn in DJ. unfold in_block in Hr. lia. }
      destruct (Z.eq_dec r 4) as [->|NE].
      -
        eapply sreach_evt. { eapply (pp_join P q (al_tp L_) TPR 4). lia. }
        intros ms2 [[_ ->]|[X4 _]]; [| lia]. rewrite <- pp_st_eq. eapply IH.
        + split; [exact CO'|]. split; [| reflexivity]. subst st'. unfold pp_side. cbn_ps. rewrite (RP eq_refl).
          split; [lia|]. split; [intros _; split; [exact (RO eq_refl)| rewrite ENTP1; unfold ent_ok; repeat split; intros; lia]|].
          split; [intros X3; exfalso; apply X3; reflexivity|]. split; [intros X3; discriminate| intros _; destruct PMETH' as [_ MR']; lia].
        + subst st'. cbn_ps. rewrite (RP eq_refl). cbn. lia.
      - exact (pp_join_exit s' LB' m' st' r (wz PP_JOIN) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7v s9v t3' t4' t5' t6' CO' eq_refl RR NE).
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 HT MT GMX Q16"] Lemma arm_ent : forall s LB m (st : pstate AI) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      INV s LB m st -> ps_pos st = POS_ENTITY ->
      SREACH AI POST (ST parse_entity_entry (wz 0x15db0) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros [CO [SIDE ISR]] POS.
      destruct st as [cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB].
      destruct CO as (HR & HE & MI & STK & [e ERR] & FSH & FX & PP & BSUB & ND & PST & HPX).
      destruct PP as (PSC & PMSG & CUR & PMETH & PURI & PRS_ & PSM & PVER & PHL & XV & PENT & PCTL & PURL & UBO).
      destruct SIDE as (BUD & SENT & SNE & SRESP & SMETH). cbn_ps. subst pos isreq.
      destruct (SENT eq_refl) as [OKM EOK]. destruct okm as [km|]; [| exfalso; apply OKM; reflexivity]. clear OKM.
      pose proof PST as (TAB & [zb ZB] & MTB & GG & GF & GM & IW & GGM). destruct HT as (WSL & HID & TS). pose proof MT as (MWL & _ & _).
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. unfold PP_DEPTH in QLO. unfold PP_ADEPTH in QLO2.
      destruct (msg_facts AI BLK4096 BLKIMG P _ _ _ _ _ _ _ _ HR PMSG) as (HL0 & HC0 & A0 & AHI & OKS & OKN). unfold LMAX in HC0.
      assert (PMETH11 : p_meth m P meth) by (destruct PMETH as [MC MR]; split; [exact MC| specialize (SMETH ltac:(discriminate)); lia]).
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBP SUBK].
      rewrite pp_st_eq. replace (wz q) with (wz (q - 144 + 144)) by (f_equal; lia).
      eapply sreach_bind.
      { eapply (parser_parse_entity_spec AI AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM PH GMST IWST TABST ZST
                  P (q - 144) lo B gmax (okb sok SA scap ++ UB ++ LBK) isreq0 maj min rm sc m ws);
          try eassumption; unfold pmod8; try lia.
        - replace (q - 144 + 144)%Z with q by lia. exact STK.
        - bsub_tauto BSUB.
        - eapply nodup_ids_perm; [| exact ND]. perm_assoc.
        - split; [exact TAB| exists zb; exact ZB]. }
      intros s' LB' ms' PO. unfold pent_post in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & cur' & A' & len' & cap' & okm' & bs' & ebw' & elw'
                      & err' & hack' & pos' & entp' & clen' & csz' & esp' & X' & meth' & ns' & hs'
                      & -> & MI' & ST' & HE' & [e' ERR'] & HP' & HR' & PSC' & PMSG' & CUR' & PENT' & PCTL' & PHL' & XV' & PMETH' & PVER' & PRS' & BSUB' & ND' & GM' & IW' & [RR NE]).
      replace (q - 144 + 144)%Z with q in * by lia.
      rewrite (ret_pc_even 0x15db0 ltac:(lia) eq_refl).
      assert (DJW : forall X0 n, (q <= X0)%Z ->
                (X0 + n <= P + 4 \/ (P + 8 <= X0 /\ X0 + n <= P + 288) \/ (P + 432 <= X0 /\ X0 + n <= P + 440) \/ (P + 480 <= X0 /\ X0 + n <= P + 488) \/ P + 496 <= X0)%Z ->
                disjoint_from (WE P) X0 n).
      { intros X0 n H1 H2. unfold WE. cbn. repeat split; lia. }
      assert (FW : Forall (fun iv : ivl => lo <= fst iv \/ exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z (WE P)).
      { unfold WE. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil. }
      assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z ->
                (X0 + Z.of_nat (cells_size cs) <= P + 4 \/ (P + 8 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 288) \/ (P + 432 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 440)
                 \/ (P + 480 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 488) \/ P + 496 <= X0)%Z -> rw_cells rsegs m' X0 cs).
      { intros X0 cs H H1 H2. eapply cells_keep; [exact H| exact HP'| exact H1| apply DJW; [exact H1| exact H2]]. }
      set (LBKe := okb sok SA scap ++ UB ++ LBK) in *.
      assert (SUBKe : bsub LBKe LB) by (subst LBKe; bsub_tauto BSUB).
      set (st' := mkPS cur' A' len' cap' okm' bs' meth' uc rm sc SA slen scap sok sbs isreq0 maj min ns' hs' X' ebw' elw' err' hack' pos' entp' clen' csz' esp' ub UB).
      assert (CO' : CORE s' LB' m' st').
      { split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists e'; exact ERR'|].
        split; [apply (TR _ _ FSH); cbn; lia|].
        split. { destruct FX as ([j1 Q0] & QF16 & [j2 QF56]). split; [exists j1; apply (TR _ _ Q0); cbn; lia|]. split; [apply (TR _ _ QF16); cbn; lia| exists j2; apply (TR _ _ QF56); cbn; lia]. }
        split.
        { subst st'. unfold p_parser. cbn_ps.
          split; [exact PSC'|]. split; [exact PMSG'|]. split; [lia|]. split; [destruct PMETH' as [MC' MR']; split; [exact MC'| lia]|].
          split; [destruct PURI as [UC USZ]; split; [apply (TR _ _ UC); rewrite ?USZ; cbn; rewrite ?USZ; lia| exact USZ]|].
          split; [exact PRS'|].
          split. { destruct PSM as (SMC & SOWN & SL & SC32). split; [apply (TR _ _ SMC); cbn; lia|]. split; [| split; [exact SL| exact SC32]].
                   eapply mown_keep; [exact SOWN| exact HP'| subst LBKe; in_tauto| | | lia].
                   - subst LBKe. bsub_tauto BSUB'.
                   - intros k ->. destruct SOWN as [SIN _].
                     destruct (ai_block_range rsegs AI _ _ _ _ HR SIN) as (R1 & R2 & R3 & R4 & _). cbn in R1, R3, R4.
                     unfold WE. cbn. repeat split; lia. }
          split; [exact PVER'|]. split; [exact PHL'|]. split; [exact XV'|].
          split; [exact PENT'|]. split; [exact PCTL'|].
          split; [destruct PURL as [UC UR]; split; [apply (TR _ _ UC); cbn; lia| exact UR]| exact UBO]. }
        split. { subst st'. cbn_ps. subst LBKe. bsub_tauto BSUB'. }
        split. { subst st'. cbn_ps. subst LBKe. eapply nodup_ids_perm; [| exact ND']. perm_assoc. }
        split. { eapply (stat_keep s LB m m'); [exact PST| exact HP'| exact HR| exact CEIL| exact WSL| exact MWL| exact FW]. }
        eapply (hpx_trans rsegs AI); [exact HPX|].
        intros a Ha Hc Ho. apply (HP' a Ha).
        - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right]. exists b. split; [subst LBKe; in_split Hb; in_find Hb| exact Hr].
        - unfold pp_W in Ho. cbn [outside] in Ho. destruct Ho as [O1 _]. unfold WE. cbn [outside]. repeat split; lia. }

      eapply sreach_evt. { eapply (pp_j2 P q (al_tp L_)). }
      intros ms2 ->. rewrite <- pp_st_eq.
      exact (pp_join_exit s' LB' m' st' r (wz 0x15db0) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7v s9v t3' t4' t5' t6' CO' eq_refl RR NE).
    Qed.

    #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG BLKWIN GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 HT MT Q16"] Lemma arm_resp : forall s LB m (st : pstate AI) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      INV s LB m st -> ps_pos st = POS_RESPONSE_LINE ->
      (forall s' LB' m' (st' : pstate AI) x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6',
          INV s' LB' m' st' -> (pp_rank (ps_pos st') < pp_rank (ps_pos st))%Z ->
          SREACH AI POST (ST PP_HEAD x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6' m') s' LB') ->
      SREACH AI POST (ST parse_responseline_entry (wz 0x15cb4) t0 t1 t2 (wz P) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros [CO [SIDE ISR]] POS IH.
      destruct st as [cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB].
      destruct CO as (HR & HE & MI & STK & [e ERR] & FSH & FX & PP & BSUB & ND & PST & HPX).
      destruct PP as (PSC & PMSG & CUR & PMETH & PURI & PRS_ & PSM & PVER & PHL & XV & PENT & PCTL & PURL & UBO).
      destruct SIDE as (BUD & SENT & SNE & SRESP & SMETH). cbn_ps. subst pos isreq. pose proof (SNE ltac:(discriminate)) as ENTP1.
      destruct (SRESP eq_refl) as [SCAPL SNUL].
      pose proof PST as (TAB & [zb ZB] & MTB & GG & GF & GM & IW & GGM). destruct HT as (WSL & HID & TS). pose proof MT as (MWL & _ & _).
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. unfold PP_DEPTH in QLO. unfold PP_ADEPTH in QLO2.
      destruct (msg_facts AI BLK4096 BLKIMG P _ _ _ _ _ _ _ _ HR PMSG) as (HL0 & HC0 & A0 & AHI & OKS & OKN). unfold LMAX in HC0.
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBP SUBK].
      assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      assert (PSMS : p_smsg AI m LB P SA slen scap sok sbs).
      { destruct PSM as (SMC & SOWN & SL & SC32). split; [exact SMC|]. split; [exact SOWN|]. split; [exact SL|]. split; [exact SCAPL| exact SNUL]. }
      rewrite pp_st_eq.
      eapply sreach_bind.
      { eapply (parser_parse_responseline_spec AI AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKWIN
                  (wz 0x15cb4) (wz q) gp t0 t1 t2 (wz P) (wz (P + 480)) (wz P) a1 a2 a3 a4 a5 a6 a7 (wz (-1)) (wz 47) (wz 2) (wz FMT_REQ09) (wz METHOD_TAB) s7v (wz 3) s9v (wz 1) (wz 4) t3 t4 t5 t6
                  F fc m s LB (UB ++ LBK ++ hl_blocks ns hs) P lo B cur A len cap okm bs SA slen scap sok sbs rm sc isreq0 maj min err hack POS_RESPONSE_LINE entp clen csz esp e);
          rewrite ?UQ; try eassumption; unfold RESP_DEPTH; try lia.
        - bsub_tauto BSUB.
        - eapply nodup_ids_perm; [| exact ND]. perm_rot1.
        - reflexivity. }
      intros s' LB' ms' PO. unfold presp_post in PO. rewrite ?UQ in PO.
      destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & cur' & sc' & maj' & min' & SA' & slen' & scap' & err' & pos' & sok' & sbs'
                      & -> & MI' & ST' & HE' & [e' ERR'] & HP' & HR' & BSUB' & ND' & PSC' & PMSG' & PRS' & PVER' & PSM' & PCTL' & RR & CURR & CASES).
      rewrite (ret_pc_even 0x15cb4 ltac:(lia) eq_refl).
      assert (DJW : forall X0 n, (q <= X0)%Z ->
                (X0 + n <= P + 224 \/ (P + 288 <= X0 /\ X0 + n <= P + 440) \/ (P + 452 <= X0 /\ X0 + n <= P + 488) \/ P + 496 <= X0)%Z ->
                disjoint_from (resp_W P) X0 n).
      { intros X0 n H1 H2. unfold resp_W. cbn. repeat split; lia. }
      assert (FW : Forall (fun iv : ivl => lo <= fst iv \/ exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z (resp_W P)).
      { unfold resp_W. repeat (apply Forall_cons; [left; cbn; lia|]). apply Forall_nil. }
      assert (FW2 : Forall (fun iv : ivl => lo <= fst iv)%Z (resp_W P)).
      { unfold resp_W. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. }
      assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z ->
                (X0 + Z.of_nat (cells_size cs) <= P + 224 \/ (P + 288 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 440) \/ (P + 452 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 488) \/ P + 496 <= X0)%Z ->
                rw_cells rsegs m' X0 cs).
      { intros X0 cs H H1 H2. eapply cells_keep; [exact H| exact HP'| exact H1| apply DJW; [exact H1| exact H2]]. }
      set (LBKr := UB ++ LBK ++ hl_blocks ns hs) in *.
      assert (SUBKr : bsub LBKr LB) by (subst LBKr; bsub_tauto BSUB).
      set (st' := mkPS cur' A len cap okm bs meth uc rm sc' SA' slen' scap' sok' sbs' isreq0 maj' min' ns hs X ebw elw err' hack pos' entp clen csz esp ub UB).
      assert (CO' : CORE s' LB' m' st').
      { split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exists e'; exact ERR'|].
        split; [apply (TR _ _ FSH); cbn; lia|].
        split. { destruct FX as ([j1 Q0] & QF16 & [j2 QF56]). split; [exists j1; apply (TR _ _ Q0); cbn; lia|]. split; [apply (TR _ _ QF16); cbn; lia| exists j2; apply (TR _ _ QF56); cbn; lia]. }
        split.
        { subst st'. unfold p_parser. cbn_ps.
          split; [exact PSC'|]. split; [exact PMSG'|]. split; [lia|].
          split; [destruct PMETH as [MC MR]; split; [apply (TR _ _ MC); cbn; lia| exact MR]|].
          split; [destruct PURI as [UC USZ]; split; [apply (TR _ _ UC); rewrite ?USZ; cbn; rewrite ?USZ; lia| exact USZ]|].
          split; [exact PRS'|].
          split; [exact PSM'|].
          split; [exact PVER'|].
          split. { eapply (hl_keep s m m'); [exact PHL| exact HP'| exact HR| subst LBKr; in_tauto| exact SUBKr| exact CEIL| lia| apply DJW; lia| exact FW2]. }
          split; [exact XV|].
          split; [unfold p_ent in *; apply (TR _ _ PENT); cbn; lia|].
          split; [exact PCTL'|].
          split; [destruct PURL as [UC UR]; split; [apply (TR _ _ UC); cbn; lia| exact UR]| exact UBO]. }
        split. { subst st'. cbn_ps. subst LBKr. bsub_tauto BSUB'. }
        split. { subst st'. cbn_ps. subst LBKr. eapply nodup_ids_perm; [| exact ND']. apply Permutation_sym. perm_rot1. }
        split. { eapply (stat_keep s LB m m'); [exact PST| exact HP'| exact HR| exact CEIL| exact WSL| exact MWL| exact FW]. }
        eapply (hpx_trans rsegs AI); [exact HPX|].
        intros a Ha Hc Ho. apply (HP' a Ha).
        - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right]. exists b. split; [subst LBKr; in_split Hb; in_find Hb| exact Hr].
        - unfold pp_W in Ho. cbn [outside] in Ho. destruct Ho as [O1 _]. unfold resp_W. cbn [outside]. repeat split; lia. }

      eapply sreach_evt. { eapply (pp_j1 P q (al_tp L_)). }
      intros ms2 ->. rewrite <- pp_st_eq.
      destruct (Z.eq_dec r 4) as [->|NE].
      - destruct CASES as [(_ & EP & _ & _ & _ & _ & OKM)|[X4 _]]; [| lia].
        eapply sreach_evt. { rewrite pp_st_eq. eapply (pp_join P q (al_tp L_) TPR 4). lia. }
        intros ms3 [[_ ->]|[X4 _]]; [| lia]. rewrite <- pp_st_eq. eapply IH.
        + split; [exact CO'|]. split; [| reflexivity]. subst st'. unfold pp_side. cbn_ps. rewrite EP.
          split; [lia|]. split; [intros X3; discriminate|]. split; [intros _; exact ENTP1|]. split; [intros X3; discriminate| intros _; apply SMETH; discriminate].
        + subst st'. cbn_ps. rewrite EP. cbn. lia.
      - exact (pp_join_exit s' LB' m' st' r (wz 0x15cb4) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s7v s9v t3' t4' t5' t6' CO' eq_refl RR NE).
    Qed.

    #[using="TPV REQL QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma arm_reql : forall s LB m (st : pstate AI) x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      INV s LB m st -> ps_pos st = POS_REQUEST_LINE ->
      (forall s' LB' m' (st' : pstate AI) x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6',
          INV s' LB' m' st' -> (pp_rank (ps_pos st') < pp_rank (ps_pos st))%Z ->
          SREACH AI POST (ST PP_HEAD x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6' m') s' LB') ->
      SREACH AI POST (ST PP_REQL x1 t0 t1 t2 (wz 0) a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros [CO [SIDE ISR]] POS IH.
      eapply sreach_bind.
      { eapply (REQL P q lo B gmax gifv ws mws LBK m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e
                 QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX); [exact CO| exact SIDE| exact POS]. }
      intros s' LB' ms' PO. unfold reql_post in PO.
      destruct PO as (x1' & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s7v' & s9v' & t3' & t4' & t5' & t6' & m' & r & st' & -> & CO' & ISR' & RR & OK).
      destruct (Z.eq_dec r 4) as [->|NE].
      - destruct (OK eq_refl) as [EP SIDE'].
        eapply sreach_evt. { rewrite pp_st_eq. eapply (pp_join P q (al_tp L_) TPR 4). lia. }
        intros ms3 [[_ ->]|[X4 _]]; [| lia]. rewrite <- pp_st_eq. eapply IH.
        + split; [exact CO'|]. split; [exact SIDE'| rewrite ISR'; exact ISR].
        + rewrite EP, POS. cbn. lia.
      - apply (pp_join_exit s' LB' m' st' r); [exact CO'| rewrite ISR'; exact ISR| exact RR| exact NE].
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG BLKWIN GERM SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST REQL QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma pp_step : forall s LB m (st : pstate AI) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      INV s LB m st ->
      (forall s' LB' m' (st' : pstate AI) x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6',
          INV s' LB' m' st' -> (pp_rank (ps_pos st') < pp_rank (ps_pos st))%Z ->
          SREACH AI POST (ST PP_HEAD x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7v' s9v' t3' t4' t5' t6' m') s' LB') ->
      SREACH AI POST (ST PP_HEAD x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      intros until t6. intros INV0 IH. pose proof INV0 as [CO [SIDE ISR]].
      pose proof CO as (HR & HE & MI & STK & _ & _ & _ & PP & _).
      pose proof PP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PCTL & _). destruct PCTL as (CTL & _ & _ & POSR & _).
      eapply sreach_evt.
      { rewrite pp_st_eq. unfold PP_HEAD. eapply (pp_head P q (al_tp L_) TPR); [exact MI| exact CTL| exact POSR]. }
      intros ms' ->.
      assert (CS : ps_pos st = 0 \/ ps_pos st = 1 \/ ps_pos st = 2 \/ ps_pos st = 3 \/ ps_pos st = 4) by lia.
      destruct CS as [EP|[EP|[EP|[EP|EP]]]]; rewrite EP; unfold pp_target, pp_ra, pp_a0; cbn [Z.eqb Pos.eqb].
      - rewrite <- pp_st_eq. eapply arm_reql; [exact INV0| exact EP| exact IH].
      - rewrite <- pp_st_eq. change 0x14904 with parse_responseline_entry. eapply arm_resp; [exact INV0| exact EP| exact IH].
      - rewrite <- pp_st_eq. change 0x14c4c with parse_headers_entry. eapply arm_hdr; [exact INV0| exact EP| exact IH].
      - rewrite <- pp_st_eq. change 0x15704 with parse_entity_entry. eapply arm_ent; [exact INV0| exact EP].
      - rewrite <- pp_st_eq. change 0x15fe0 with PP_EXIT. eapply (pp_exit s LB m st 3); [exact CO| exact ISR| lia].
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG BLKWIN GERM SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST REQL QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Lemma pp_loop : forall (k : nat) s LB m (st : pstate AI) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6,
      (pp_rank (ps_pos st) < Z.of_nat k)%Z -> INV s LB m st ->
      SREACH AI POST (ST PP_HEAD x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7v s9v t3 t4 t5 t6 m) s LB.
    Proof.
      induction k as [|k IHk]; intros until t6; intros HK INV0.
      - unfold pp_rank in HK. repeat (destruct (_ : bool) in HK); cbn in HK; lia.
      - eapply pp_step; [exact INV0|]. intros until t6'. intros INV' LT. eapply IHk; [| exact INV']. lia.
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG BLKWIN GERM SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST REQL QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q16 HT MT GMX"] Theorem pp_main : forall s LB (st : pstate AI) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : word),
      m0 = m0 ->
      RHEAP rsegs AI s LB m0 -> RENV rsegs AI m0 B -> mem_inv rsegs m0 -> stk rsegs m0 lo (q + 208) -> rw_cells rsegs m0 (al_errno L_) [C4 e] ->
      p_parser AI m0 LB P st -> pp_side AI gmax st -> ps_isreq st = isreq0 ->
      bsub (ps_blocks st ++ LBK) LB -> NoDup (map blk_id (ps_blocks st ++ LBK)) -> pp_stat m0 gmax gifv ws mws ->
      SREACH AI POST (MS (mkR ra (wz (q + 208)) gp TP t0 t1 t2 s0e s1e (wz P) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
                         F (wz parser_parse_entry) fc None m0 (seg_rom rsegs)) s LB.
    Proof.
      intros until e. intros _ HR HE MI STK ERR PP SIDE ISR BSUB ND PST.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. unfold PP_DEPTH in QLO. unfold PP_ADEPTH in QLO2.
      destruct HT as (WSL & _ & _). pose proof MT as (MWL & _ & _).
      eapply sreach_evt.
      { unfold parser_parse_entry. eapply (pp_entry P q lo (al_tp L_)); try exact TPR; try lia; [exact STK| exact MI| reflexivity]. }
      intros ms' (m1 & a0' & a1' & a2' & j1 & j2 & -> & MU & WM & MI1 & ST1 & Q0 & QF16 & QF56 & FSH).
      assert (HR1 : RHEAP rsegs AI s LB m1).
      { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
      assert (HE1 : RENV rsegs AI m1 B).
      { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
      assert (HP1 : hpx AI [] LB (q + 208) m0 m1).
      { eapply (hpx_seg rsegs AI); [exact LOK| exact HR| intros b Hb; exact Hb| exact MU| exact WM|]. constructor; [left; cbn; lia| constructor]. }
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      assert (TR : forall X0 cs, rw_cells rsegs m0 X0 cs -> (q + 208 <= X0)%Z -> rw_cells rsegs m1 X0 cs).
      { intros X0 cs H H1. eapply cells_keep; [exact H| exact HP1| exact H1| exact I]. }
      destruct (proj1 (bsub_app AI _ _ _) BSUB) as [SUBP SUBK].
      rewrite <- pp_st_eq.
      eapply (pp_loop 4%nat); [unfold pp_rank; repeat (destruct (_ : bool)); cbn; lia|].
      split; [| split; [exact SIDE| exact ISR]].
      split; [exact HR1|]. split; [exact HE1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [exists e; eapply rw_cells_transport; [exact ERR| exact MU| exact WM| cbn; lia]|].
      split; [exact FSH|]. split; [split; [exists j1; exact Q0| split; [exact QF16| exists j2; exact QF56]]|].
      split.
      { destruct st as [cur A len cap okm bs meth uc rm sc SA slen scap sok sbs isreq maj min ns hs X ebw elw err hack pos entp clen csz esp ub UB].
        destruct PP as (PSC & PMSG & CUR & PMETH & PURI & PRS_ & PSM & PVER & PHL & XV & PENT & PCTL & PURL & UBO). unfold p_parser. cbn_ps.
        split; [unfold p_scan in *; apply (TR _ _ PSC); lia|].
        split. { destruct PMSG as (MBC & OWN & HL & HC & NUL). split; [apply (TR _ _ MBC); lia|]. split; [| split; [exact HL| split; [exact HC| exact NUL]]].
                 eapply mown_keep; [exact OWN| exact HP1| | | intros; exact I| lia]; intros bb Hbb; apply BSUB; in_find Hbb. }
        split; [exact CUR|].
        split; [destruct PMETH as [MC MR]; split; [apply (TR _ _ MC); lia| exact MR]|].
        split; [destruct PURI as [UC USZ]; split; [apply (TR _ _ UC); lia| exact USZ]|].
        split; [destruct PRS_ as (RC & RR1 & RR2); split; [apply (TR _ _ RC); lia| split; [exact RR1| exact RR2]]|].
        split. { destruct PSM as (SMC & SOWN & SL & SC32). split; [apply (TR _ _ SMC); lia|]. split; [| split; [exact SL| exact SC32]].
                 eapply mown_keep; [exact SOWN| exact HP1| | | intros; exact I| lia]; intros bb Hbb; apply BSUB; in_find Hbb. }
        split; [destruct PVER as [[pad VC] VR]; split; [exists pad; apply (TR _ _ VC); lia| exact VR]|].
        split. { eapply (hl_keep s m0 m1); [exact PHL| exact HP1| exact HR| intros bb Hbb; apply BSUB; in_find Hbb| intros bb Hbb; exact Hbb| exact CEIL| lia| exact I| apply Forall_nil]. }
        split; [exact XV|].
        split; [unfold p_ent in *; apply (TR _ _ PENT); lia|].
        split; [destruct PCTL as [CTL CTR]; split; [apply (TR _ _ CTL); lia| exact CTR]|].
        split; [destruct PURL as [UC UR]; split; [apply (TR _ _ UC); lia| exact UR]| exact UBO]. }
      split; [exact BSUB|]. split; [exact ND|].
      split; [eapply (stat_keep s LB m0 m1); [exact PST| exact HP1| exact HR| exact CEIL| exact WSL| exact MWL| apply Forall_nil]|].
      eapply (hpx_weaken rsegs AI); [exact HP1| intros x _; exact I| lia| exact SUBK].
    Qed.
  End ACT.

  #[using="AC LOK MALPC FREEPC REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG BLKWIN GERM SNC IMGW1 IMGW2 GMST IWST GOTGMST TABST ZST MTST GIFST GOTGIFST REQL"] Theorem parser_parse_proof : parser_parse_stmt AI.
  Proof.
    unfold parser_parse_stmt.
    intros P lo B gmax gifv ws mws LBK st s LB ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e.
    intros QLO QLO2 STK0 LO0 CEIL SPP PB BHI P8 SP16 HT MT GMX HR HE MI ST ERR PP SIDE BSUB ND PST ->.
    pose proof (word_lt64 sp) as SPR.
    set (spv := bv_unsigned sp) in *. assert (ESP : sp = wz spv) by (subst spv; symmetry; apply Z_to_bv_bv_unsigned).
    set (q := (spv - 208)%Z). assert (Hq : spv = (q + 208)%Z) by (unfold q; lia). clearbody q spv. subst spv. rewrite ESP.
    eapply (pp_main P q lo B gmax gifv ws mws LBK (ps_isreq st) m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 gp F fc); try eassumption; try reflexivity; try lia.
  Qed.
End W.
