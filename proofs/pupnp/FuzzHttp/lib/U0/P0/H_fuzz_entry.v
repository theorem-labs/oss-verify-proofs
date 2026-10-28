(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr MState SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_obj H_prep H_fuzz_stmt H_statics H_parser_init
     H_httpheader_free H_httpmsg_compare H_membuffer_assign H_membuffer_append H_httpmsg_destroy H_httpmsg_destroyN H_pparse_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section HP.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Hypothesis LOK : layout_ok AI.

  #[using="LOK"] Lemma stack_not_client : forall s (LB0 LB : list BLK) m0 SP a,
    RHEAP rsegs AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
    (alloc_ceiling <= a < SP)%Z -> client_addr AI LB SP a -> False.
  Proof.
    intros s LB0 LB m0 SP a HR SUB Ha Hc.
    destruct Hc as [Hc|[(lo & hi & Hst & Hr)|(b & Hb & Hr)]].
    - lia.
    - destruct (lo_static_img rsegs AI LOK lo hi Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). lia.
    - destruct (ai_block_range rsegs AI s LB0 m0 b HR (SUB b Hb)) as (_ & _ & _ & Hc' & _). lia.
  Qed.

  #[using="LOK"] Lemma hpx_stack_heap_pres : forall s (LB0 LB : list BLK) m0 W SP' SP m m',
    RHEAP rsegs AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
    hpx AI W LB SP' m m' -> (SP' <= SP)%Z ->
    Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
    heap_pres AI LB SP m m'.
  Proof.
    intros s LB0 LB m0 W SP' SP m m' HR SUB HP HS FA.
    eapply heap_pres_of_hpx. { eapply hpx_weaken; [exact HP| intros xo Hxo; exact Hxo| exact HS| intros b Hb; exact Hb]. }
    intros a Ha Hc. apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [lo' hi'] [H1 H2] Hr. cbn in *.
    eapply (stack_not_client s LB0 LB m0 SP a); [exact HR| exact SUB| lia| exact Hc].
  Qed.

  #[using="LOK"] Lemma munch_stack_heap_pres : forall s (LB0 LB : list BLK) m0 W SP m m',
    RHEAP rsegs AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
    munch W m m' -> wmono rsegs m m' ->
    Forall (fun iv => alloc_ceiling <= fst iv /\ snd iv <= SP)%Z W ->
    heap_pres AI LB SP m m'.
  Proof.
    intros s LB0 LB m0 W SP m m' HR SUB MU WM FA.
    eapply heap_pres_seg; [exact LOK| exact HR| exact SUB| exact MU| exact WM|].
    unfold seg_ok. eapply Forall_impl; [| exact FA]. cbn. intros iv H. left. exact H.
  Qed.

  Hypothesis GDCS : forall a, gd_addr a -> exists lo hi, al_client_static L_ lo hi /\ (lo <= a < hi)%Z.

  #[using="GDCS"] Lemma gd_client : forall (LB : list BLK) SP A n,
    (forall a, A <= a < A + n -> gd_addr a)%Z -> client_range AI LB SP A n.
  Proof.
    intros LB SP A n H a Ha. destruct (GDCS a (H a Ha)) as (lo & hi & ST & R). right; left. exists lo, hi. split; [exact ST| exact R].
  Qed.

  #[using="GDCS"] Lemma GD_heap_pres : forall (LB : list BLK) SP m m', GD m -> heap_pres AI LB SP m m' -> GD m'.
  Proof.
    intros LB SP m m' G HP. eapply GD_ext; [exact G|]. intros a Ha.
    assert (AR : (0 <= a < 2^64)%Z) by (unfold gd_addr in Ha; lia).
    destruct (GDCS a Ha) as (lo & hi & ST & R). destruct (HP a AR ltac:(right; left; exists lo, hi; split; [exact ST| exact R])) as [E _]. exact E.
  Qed.

  #[using="GDCS"] Lemma pp_stat_heap_pres : forall (LB : list BLK) SP m m' gmax gifv ws mws,
    pp_stat m gmax gifv ws mws -> length ws = 66%nat -> length mws = 22%nat -> heap_pres AI LB SP m m' -> pp_stat m' gmax gifv ws mws.
  Proof.
    intros LB SP m m' gmax gifv ws mws (T1 & [zb T2] & T3 & T4 & T5 & T6 & T7 & T8) WSL MWSL HP. unfold pp_stat.
    split. { destruct T1 as [B1 W1]. split.
             - eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact B1|]. apply gd_client. rewrite u64s_length, WSL. unfold gd_addr. cbn. intros; lia.
             - eapply (heap_pres_wr_at rsegs AI); [exact HP| exact W1|]. apply gd_client. rewrite WSL. unfold gd_addr. cbn. intros; lia. }
    split. { exists zb. eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact T2|]. apply gd_client. unfold gd_addr. cbn. intros; lia. }
    split. { destruct T3 as [B1 W1]. split.
             - eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact B1|]. apply gd_client. rewrite u64s_length, MWSL. unfold gd_addr. cbn. intros; lia.
             - eapply (heap_pres_wr_at rsegs AI); [exact HP| exact W1|]. apply gd_client. rewrite MWSL. unfold gd_addr. cbn. intros; lia. }
    split. { eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact T4|]. apply gd_client. rewrite length_le8. unfold gd_addr. cbn. intros; lia. }
    split. { eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact T5|]. apply gd_client. rewrite length_le4. unfold gd_addr. cbn. intros; lia. }
    split. { eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact T6|]. apply gd_client. unfold gd_addr. cbn. intros; lia. }
    split. { eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact T7|]. apply gd_client. unfold gd_addr. cbn. intros; lia. }
    eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact T8|]. apply gd_client. rewrite length_le8. unfold gd_addr. cbn. intros; lia.
  Qed.

  #[using="Type"] Lemma p_parser_heap_pres : forall m m' (LB LBh : list BLK) SP P st,
    p_parser AI m LB P st -> heap_pres AI LBh SP m m' -> (SP <= P)%Z -> bsub AI (ps_blocks AI st) LBh ->
    p_parser AI m' LB P st.
  Proof.
    intros m m' LB LBh SP P st PAR HP SPP SUB.
    destruct PAR as (SCN & MSG & CURR & METH & URI & RS & SMSG & VER & HL & XV & ENT & CTL & URL & UBO).
    unfold ps_blocks in SUB. apply (bsub_app AI) in SUB. destruct SUB as [SUBhl SUB]. apply (bsub_app AI) in SUB. destruct SUB as [SUBm SUB].
    apply (bsub_app AI) in SUB. destruct SUB as [SUBs SUBu]. unfold hl_blocks in SUBhl. apply (bsub_app AI) in SUBhl. destruct SUBhl as [SUBn SUBh].
    assert (MV : forall A cs, rw_cells rsegs m A cs -> (SP <= A)%Z -> rw_cells rsegs m' A cs).
    { intros A cs H HA. eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact H|]. apply client_range_above. exact HA. }
    assert (MOWN : forall A cap ok bs, mown AI m LB A cap ok bs -> bsub AI (okb AI ok A cap) LBh -> (0 <= cap)%Z -> mown AI m' LB A cap ok bs).
    { intros A cap [k|] bs OW SB CAP; cbn in OW |- *; [| exact OW]. destruct OW as [KIN KB]. split; [exact KIN|].
      eapply (heap_pres_rw_cells rsegs AI); [exact HP| exact KB|]. eapply client_range_block; [apply SB; left; reflexivity| cbn; lia|].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia. }
    split; [apply MV; [exact SCN| lia]|].
    split. { destruct MSG as (MBC & OWN & R). split; [apply MV; [exact MBC| lia]|]. split; [refine (MOWN _ _ _ _ OWN SUBm _); lia| exact R]. }
    split; [exact CURR|].
    split. { destruct METH as [MC MR]. split; [apply MV; [exact MC| lia]| exact MR]. }
    split. { destruct URI as [UC UL]. split; [apply MV; [exact UC| lia]| exact UL]. }
    split. { destruct RS as (RC & R1 & R2). split; [apply MV; [exact RC| lia]|]. split; [exact R1| exact R2]. }
    split. { destruct SMSG as (SC & SOWN & R). split; [apply MV; [exact SC| lia]|]. split; [refine (MOWN _ _ _ _ SOWN SUBs _); lia| exact R]. }
    split. { destruct VER as [(pad & VC) VR]. split; [exists pad; apply MV; [exact VC| lia]| exact VR]. }
    split. { destruct HL as (LC & FLC & FF & DL & HS & REST). split; [apply MV; [exact LC| lia]|]. split; [apply MV; [exact FLC| lia]|]. split; [apply MV; [exact FF| lia]|].
             split. { eapply (dlseg_heap_pres AI); [exact DL| exact HP|]. intros b it Hb. apply SUBn. exact (in_map fst _ _ Hb). }
             split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HP| exact SUBh]. }
             exact REST. }
    split; [exact XV|].
    split; [apply MV; [exact ENT| lia]|].
    split. { destruct CTL as [CC CR]. split; [apply MV; [exact CC| lia]| exact CR]. }
    split. { destruct URL as [UC UR]. split; [apply MV; [exact UC| lia]| exact UR]. }
    exact UBO.
  Qed.

  #[using="Type"] Lemma p_parser_mono : forall m (LB LB' : list BLK) P st,
    p_parser AI m LB P st -> bsub AI (ps_blocks AI st) LB' -> p_parser AI m LB' P st.
  Proof.
    intros m LB LB' P st PAR SUB.
    destruct PAR as (SCN & MSG & CURR & METH & URI & RS & SMSG & VER & HL & XV & ENT & CTL & URL & UBO).
    unfold ps_blocks in SUB. apply (bsub_app AI) in SUB. destruct SUB as [SUBhl SUB]. apply (bsub_app AI) in SUB. destruct SUB as [SUBm SUB].
    apply (bsub_app AI) in SUB. destruct SUB as [SUBs SUBu].
    assert (MOWN : forall A cap ok bs, mown AI m LB A cap ok bs -> bsub AI (okb AI ok A cap) LB' -> mown AI m LB' A cap ok bs).
    { intros A cap [k|] bs OW SB; cbn in OW |- *; [| exact OW]. destruct OW as [KIN KB]. split; [apply SB; left; reflexivity| exact KB]. }
    split; [exact SCN|]. split. { destruct MSG as (MBC & OWN & R). split; [exact MBC|]. split; [exact (MOWN _ _ _ _ OWN SUBm)| exact R]. }
    split; [exact CURR|]. split; [exact METH|]. split; [exact URI|]. split; [exact RS|].
    split. { destruct SMSG as (SC & SOWN & R). split; [exact SC|]. split; [exact (MOWN _ _ _ _ SOWN SUBs)| exact R]. }
    split; [exact VER|]. split; [exact HL|]. split; [exact XV|]. split; [exact ENT|]. split; [exact CTL|]. split; [exact URL| exact UBO].
  Qed.
End HP.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Hypothesis LOK : layout_ok AI.
  Hypothesis FREEPC : al_free_pc L_ = 0x17fb0.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.

  Hypothesis GDCS : forall a, gd_addr a -> exists lo hi, al_client_static L_ lo hi /\ (lo <= a < hi)%Z.

  Variable GUARDW : word.
  Hypothesis SSP0 : forall s LB m, RHEAP rsegs AI s LB m ->
    rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells rsegs m ssp_guard [C8 GUARDW].

  Hypothesis PP : parser_parse_stmt AI.

  Let CE : 0x7FFF7F800000 <= alloc_ceiling <= 0x7FFFFF800000 := alloc_ceiling_bounds.
  Let CE8 : alloc_ceiling mod 8 = 0 := alloc_ceiling_aligned8.

  Definition set_msg (st : pstate AI) (A' len' cap' : Z) (ok' : option K) (bs' : list byte) : pstate AI :=
    mkPS (ps_cur st) A' len' cap' ok' bs' (ps_meth st) (ps_uc st) (ps_rm st) (ps_sc st)
         (ps_SA st) (ps_slen st) (ps_scap st) (ps_sok st) (ps_sbs st) (ps_isreq st) (ps_maj st) (ps_min st)
         (ps_ns st) (ps_hs st) (ps_X st) (ps_ebw st) (ps_elw st)
         (ps_err st) (ps_hack st) (ps_pos st) (ps_entp st) (ps_clen st) (ps_csz st) (ps_esp st) (ps_ub st) (ps_UB st).
  Definition set_err (st : pstate AI) (err' : Z) : pstate AI :=
    mkPS (ps_cur st) (ps_A st) (ps_len st) (ps_cap st) (ps_okm st) (ps_bs st) (ps_meth st) (ps_uc st) (ps_rm st) (ps_sc st)
         (ps_SA st) (ps_slen st) (ps_scap st) (ps_sok st) (ps_sbs st) (ps_isreq st) (ps_maj st) (ps_min st)
         (ps_ns st) (ps_hs st) (ps_X st) (ps_ebw st) (ps_elw st)
         err' (ps_hack st) (ps_pos st) (ps_entp st) (ps_clen st) (ps_csz st) (ps_esp st) (ps_ub st) (ps_UB st).

  Definition ps_other (st : pstate AI) : list BLK := hl_blocks AI (ps_ns st) (ps_hs st) ++ okb AI (ps_sok st) (ps_SA st) (ps_scap st) ++ ps_UB st.

  #[using="Type"] Lemma ps_blocks_perm : forall st, Permutation (ps_blocks AI st) (okb AI (ps_okm st) (ps_A st) (ps_cap st) ++ ps_other st).
  Proof.
    intros st. unfold ps_blocks, ps_other. apply Permutation_app_swap_app.
  Qed.

  #[using="Type"] Lemma nodup_ids_perm : forall (OB OB' : list BLK), Permutation OB OB' -> NoDup (map blk_id OB) -> NoDup (map blk_id OB').
  Proof. intros OB OB' PM ND. rewrite <- (Permutation_map blk_id PM). exact ND. Qed.

  #[using="Type"] Lemma nodup_ids_eq : forall (LB : list BLK) b1 b2, NoDup (map blk_id LB) -> In b1 LB -> In b2 LB -> blk_id b1 = blk_id b2 -> b1 = b2.
  Proof.
    induction LB as [|b LB IH]; intros b1 b2 ND H1 H2 E; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | eapply IH; eauto].
    - exfalso. apply NI. rewrite E. apply base.list_elem_of_In. apply in_map. exact H2.
    - exfalso. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact H1.
  Qed.

  #[using="Type"] Lemma fresh_ids_cons : forall s LBf mf (bn : BLK) OB,
    RHEAP rsegs AI s LBf mf -> In bn LBf -> bsub AI OB LBf -> (forall b, In b OB -> b <> bn) ->
    NoDup (map blk_id OB) -> NoDup (map blk_id (bn :: OB)).
  Proof.
    intros s LBf mf bn OB HR HIN SUB NE ND. cbn. constructor; [| exact ND].
    intros HI. apply base.list_elem_of_In in HI. apply in_map_iff in HI. destruct HI as (b' & E & Hb').
    apply (NE b' Hb'). eapply nodup_ids_eq; [exact (ai_blocks_nodup rsegs AI _ _ _ HR)| apply SUB; exact Hb'| exact HIN| exact E].
  Qed.

  #[using="Type"] Lemma ids_ne_head : forall (b b' : BLK) (OB : list BLK),
    NoDup (map blk_id (b :: OB)) -> In b' OB -> blk_id b' <> blk_id b.
  Proof.
    intros b b' OB ND H E. cbn in ND. inversion ND as [|x l NI ND']; subst. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact H.
  Qed.

  #[using="HCEIL CE"] Lemma nul_of_firstn : forall (bs pre : list byte) (n : Z),
    firstn (Z.to_nat (n + 1)) bs = pre ++ [Z_to_bv 8 0] -> Z.of_nat (length pre) = n -> (0 <= n)%Z ->
    nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0).
  Proof.
    intros bs pre n E L N. rewrite <- (firstn_skipn (Z.to_nat (n + 1)) bs). rewrite E.
    rewrite nth_error_app1 by (rewrite app_length; cbn; lia). rewrite nth_error_app2 by lia.
    replace (Z.to_nat n - length pre)%nat with 0%nat by lia. reflexivity.
  Qed.

  #[using="LOK CE"] Lemma hpx_blocks_heap_pres : forall s (LB0 LBh : list BLK) m0 W SP m m',
    RHEAP rsegs AI s LB0 m0 -> bsub AI LBh LB0 -> hpx AI W LBh SP m m' -> (SP <= 2^64)%Z ->
    Forall (fun iv => alloc_ceiling <= fst iv)%Z W ->
    heap_pres AI LBh (2^64) m m'.
  Proof.
    intros s LB0 LBh m0 W SP m m' HR SUB HP SPH FA.
    eapply heap_pres_of_hpx. { eapply hpx_weaken; [exact HP| intros xo Hxo; exact Hxo| exact SPH| intros b Hb; exact Hb]. }
    intros a Ha [Hc|[(lo' & hi' & Hst & Hr)|(b & Hb & Hr)]]; [lia| |].
    - destruct (lo_static_img rsegs AI LOK lo' hi' Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw).
      apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [l h] H1. cbn in *. lia.
    - destruct (ai_block_range rsegs AI _ _ _ _ HR (SUB b Hb)) as (_ & _ & _ & R4 & _).
      apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [l h] H1. cbn in *. unfold in_block in Hr. lia.
  Qed.

  #[using="LOK CE"] Lemma p_parser_msg_update : forall s (LB0 : list BLK) m0 m m' (LB LB' LBh : list BLK) SP P st A' len' cap' ok' bs',
    RHEAP rsegs AI s LB0 m0 -> bsub AI LBh LB0 ->
    p_parser AI m LB P st -> hpx AI [(P + 400, P + 400 + 32)]%Z LBh SP m m' -> (alloc_ceiling <= SP)%Z -> (SP <= P)%Z -> (P + 504 <= 2^64)%Z ->
    bsub AI (ps_other st) LBh -> bsub AI (ps_other st) LB' ->
    rw_cells rsegs m' (P + 400) (mbuf_cells A' len' cap') -> mown AI m' LB' A' cap' ok' bs' ->
    (0 <= len' <= cap')%Z -> (cap' + 1 <= LMAX)%Z ->
    match ok' with None => len' = 0 | Some _ => nth_error bs' (Z.to_nat len') = Some (Z_to_bv 8 0) end ->
    (ps_cur st <= len')%Z ->
    p_parser AI m' LB' P (set_msg st A' len' cap' ok' bs').
  Proof.
    intros s LB0 m0 m m' LB LB' LBh SP P st A' len' cap' ok' bs' HR SUB0 PAR HP CSP SPP PHI SUBh SUB' MBC' OWN' LC' CAP' NUL' CUR'.
    pose proof (hpx_blocks_heap_pres s LB0 LBh m0 _ SP m m' HR SUB0 HP ltac:(lia) ltac:(constructor; [cbn; lia| constructor])) as HPb.
    destruct PAR as (SCN & MSG & CURR & METH & URI & RS & SMSG & VER & HL & XV & ENT & CTL & URL & UBO).
    unfold ps_other in SUBh, SUB'. apply (bsub_app AI) in SUBh. destruct SUBh as [SUBhl SUBh]. apply (bsub_app AI) in SUBh. destruct SUBh as [SUBs SUBu].
    apply (bsub_app AI) in SUB'. destruct SUB' as [SUBhl' SUB']. apply (bsub_app AI) in SUB'. destruct SUB' as [SUBs' SUBu'].
    unfold hl_blocks in SUBhl. apply (bsub_app AI) in SUBhl. destruct SUBhl as [SUBn SUBhh].
    assert (MV : forall A cs, rw_cells rsegs m A cs -> (SP <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 400 \/ P + 400 + 32 <= A)%Z -> rw_cells rsegs m' A cs).
    { intros A cs H HA HD. eapply (hpx_rw_cells rsegs AI); [exact HP| exact H| apply client_range_above; exact HA| cbn; lia]. }
    unfold p_parser, set_msg. cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB].
    split; [apply MV; [exact SCN| lia| cbn; lia]|].
    split. { split; [exact MBC'|]. split; [exact OWN'|]. split; [exact LC'|]. split; [exact CAP'| exact NUL']. }
    split; [lia|].
    split. { destruct METH as [MC MR]. split; [apply MV; [exact MC| lia| cbn; lia]| exact MR]. }
    split. { destruct URI as [UC UL]. split; [apply MV; [exact UC| lia| rewrite UL; cbn; lia]| exact UL]. }
    split. { destruct RS as (RC & R1 & R2). split; [apply MV; [exact RC| lia| cbn; lia]|]. split; [exact R1| exact R2]. }
    split. { destruct SMSG as (SC & SOWN & R). split; [apply MV; [exact SC| lia| cbn; lia]|]. split; [| exact R].
             destruct (ps_sok st) as [k|]; cbn in SOWN |- *; [| exact SOWN]. destruct SOWN as [KIN KB]. split; [apply SUBs'; left; reflexivity|].
             eapply (heap_pres_rw_cells rsegs AI); [exact HPb| exact KB|]. eapply client_range_block; [apply SUBs; left; reflexivity| cbn; lia|].
             cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia. }
    split. { destruct VER as [(pad & VC) VR]. split; [exists pad; apply MV; [exact VC| lia| cbn; lia]| exact VR]. }
    split. { destruct HL as (LC & FLC & FF & DL & HS & REST). split; [apply MV; [exact LC| lia| cbn; lia]|]. split; [apply MV; [exact FLC| lia| cbn; lia]|]. split; [apply MV; [exact FF| lia| cbn; lia]|].
             split. { eapply (dlseg_heap_pres AI); [exact DL| exact HPb|]. intros b it Hb. apply SUBn. exact (in_map fst _ _ Hb). }
             split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPb| exact SUBhh]. }
             exact REST. }
    split; [exact XV|].
    split; [apply MV; [exact ENT| lia| cbn; lia]|].
    split. { destruct CTL as [CC CR]. split; [apply MV; [exact CC| lia| cbn; lia]| exact CR]. }
    split. { destruct URL as [UC UR]. split; [apply MV; [exact UC| lia| cbn; lia]| exact UR]. }
    exact UBO.
  Qed.

  #[using="LOK CE"] Lemma munch_statics_heap_pres : forall W m m',
    munch W m m' -> wmono rsegs m m' -> Forall (fun iv => alloc_ceiling <= fst iv)%Z W ->
    heap_pres AI ([] : list BLK) (2^64) m m'.
  Proof.
    intros W m m' MU WM FA. eapply (heap_pres_of_munch rsegs AI); [exact MU| exact WM|].
    intros a Ha [Hc|[(lo' & hi' & Hst & Hr)|(b & Hb & _)]]; [lia| | destruct Hb].
    destruct (lo_static_img rsegs AI LOK lo' hi' Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw).
    apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [l h] H1. cbn in *. lia.
  Qed.

  #[using="LOK CE"] Lemma p_parser_ctl_update : forall s (LB0 : list BLK) m0 m m' (LB LBh : list BLK) SP P st err' hack' pos' entp' clen' csz' esp',
    RHEAP rsegs AI s LB0 m0 -> bsub AI LBh LB0 ->
    p_parser AI m LB P st -> hpx AI [(P + 440, P + 480)]%Z LBh SP m m' -> (alloc_ceiling <= SP)%Z -> (SP <= P)%Z -> (P + 504 <= 2^64)%Z ->
    bsub AI (ps_blocks AI st) LBh ->
    rw_cells rsegs m' (P + 440) (p_ctl_cells err' hack' pos' entp' clen' csz' esp') ->
    (0 <= err' < 2^31)%Z -> (0 <= hack' <= 1)%Z -> (0 <= pos' <= 4)%Z -> (0 <= entp' <= 6)%Z -> (0 <= clen' < 2^32)%Z -> (0 <= csz' < 2^64)%Z -> (0 <= esp' < 2^64)%Z ->
    p_parser AI m' LB P (mkPS (ps_cur st) (ps_A st) (ps_len st) (ps_cap st) (ps_okm st) (ps_bs st) (ps_meth st) (ps_uc st) (ps_rm st) (ps_sc st)
         (ps_SA st) (ps_slen st) (ps_scap st) (ps_sok st) (ps_sbs st) (ps_isreq st) (ps_maj st) (ps_min st)
         (ps_ns st) (ps_hs st) (ps_X st) (ps_ebw st) (ps_elw st) err' hack' pos' entp' clen' csz' esp' (ps_ub st) (ps_UB st)).
  Proof.
    intros until esp'. intros HR SUB0 PAR HP CSP SPP PHI SUBb CC' R1 R2 R3 R4 R5 R6 R7.
    pose proof (hpx_blocks_heap_pres s LB0 LBh m0 _ SP m m' HR SUB0 HP ltac:(lia) ltac:(constructor; [cbn; lia| constructor])) as HPb.
    destruct PAR as (SCN & MSG & CURR & METH & URI & RS & SMSG & VER & HL & XV & ENT & CTL & URL & UBO).
    unfold ps_blocks in SUBb. apply (bsub_app AI) in SUBb. destruct SUBb as [SUBhl SUBb]. apply (bsub_app AI) in SUBb. destruct SUBb as [SUBm SUBb].
    apply (bsub_app AI) in SUBb. destruct SUBb as [SUBs SUBu]. unfold hl_blocks in SUBhl. apply (bsub_app AI) in SUBhl. destruct SUBhl as [SUBn SUBhh].
    assert (MV : forall A cs, rw_cells rsegs m A cs -> (SP <= A)%Z -> (A + Z.of_nat (cells_size cs) <= P + 440 \/ P + 480 <= A)%Z -> rw_cells rsegs m' A cs).
    { intros A cs H HA HD. eapply (hpx_rw_cells rsegs AI); [exact HP| exact H| apply client_range_above; exact HA| cbn; lia]. }
    assert (MOWN : forall A cap ok bs, mown AI m LB A cap ok bs -> bsub AI (okb AI ok A cap) LBh -> (0 <= cap)%Z -> mown AI m' LB A cap ok bs).
    { intros A cap [k|] bs OW SB CAP; cbn in OW |- *; [| exact OW]. destruct OW as [KIN KB]. split; [exact KIN|].
      eapply (heap_pres_rw_cells rsegs AI); [exact HPb| exact KB|]. eapply client_range_block; [apply SB; left; reflexivity| cbn; lia|].
      cbn [cells_size csize Nat.add blk_addr blk_size fst snd]. lia. }
    unfold p_parser. cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB].
    split; [apply MV; [exact SCN| lia| cbn; lia]|].
    split. { destruct MSG as (MBC & OWN & R). split; [apply MV; [exact MBC| lia| cbn; lia]|]. split; [refine (MOWN _ _ _ _ OWN SUBm _); lia| exact R]. }
    split; [exact CURR|].
    split. { destruct METH as [MC MR]. split; [apply MV; [exact MC| lia| cbn; lia]| exact MR]. }
    split. { destruct URI as [UC UL]. split; [apply MV; [exact UC| lia| rewrite UL; cbn; lia]| exact UL]. }
    split. { destruct RS as (RC & Q1 & Q2). split; [apply MV; [exact RC| lia| cbn; lia]|]. split; [exact Q1| exact Q2]. }
    split. { destruct SMSG as (SC & SOWN & R). split; [apply MV; [exact SC| lia| cbn; lia]|]. split; [refine (MOWN _ _ _ _ SOWN SUBs _); lia| exact R]. }
    split. { destruct VER as [(pad & VC) VR]. split; [exists pad; apply MV; [exact VC| lia| cbn; lia]| exact VR]. }
    split. { destruct HL as (LC & FLC & FF & DL & HS & REST). split; [apply MV; [exact LC| lia| cbn; lia]|]. split; [apply MV; [exact FLC| lia| cbn; lia]|]. split; [apply MV; [exact FF| lia| cbn; lia]|].
             split. { eapply (dlseg_heap_pres AI); [exact DL| exact HPb|]. intros b it Hb. apply SUBn. exact (in_map fst _ _ Hb). }
             split. { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPb| exact SUBhh]. }
             exact REST. }
    split; [exact XV|].
    split; [apply MV; [exact ENT| lia| cbn; lia]|].
    split. { split; [exact CC'|]. lia. }
    split. { destruct URL as [UC UR]. split; [apply MV; [exact UC| lia| cbn; lia]| exact UR]. }
    exact UBO.
  Qed.

  #[using="AC LOK REALLOCPC GDCS PP CE"] Theorem parser_append_spec : forall (P lo B gmax : Z) (gifv : word) (ws mws : list word) (LBK : list BLK) (st : pstate AI)
      (s : ai_PS rsegs AI) (LB : list BLK) (SRC n : Z) (src : list byte) (bsrc : BLK)
      (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (e : word),
    (lo + PP_DEPTH + 16 <= bv_unsigned sp)%Z -> (lo <= bv_unsigned sp - 16 - PP_ADEPTH - al_stack L_)%Z -> (0 <= al_stack L_)%Z ->
    (0x5d000 <= lo)%Z -> (alloc_ceiling <= lo)%Z ->
    (bv_unsigned sp <= P)%Z -> (P + 504 <= B)%Z -> (B < 2^62)%Z -> (P mod 8 = 0)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
    hdr_tab_ok ws lo -> meth_tab_ok mws lo -> (0 < gmax < 2^32)%Z ->
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
    rw_cells rsegs m (al_errno L_) [C4 e] ->
    p_parser AI m LB P st ->
    (forall A' cap' ok' bs', pp_side AI gmax (set_msg st A' (ps_len st + n) cap' ok' bs')) ->
    (ps_cap st + n + 6 <= LMAX)%Z ->
    bsub AI (ps_blocks AI st ++ LBK) LB -> NoDup (map blk_id (ps_blocks AI st ++ LBK)) ->
    pp_stat m gmax gifv ws mws ->

    bytes_at rsegs m SRC src -> Z.of_nat (length src) = n -> (0 <= n)%Z ->
    In bsrc LBK -> (blk_addr bsrc <= SRC)%Z -> (SRC + n <= blk_addr bsrc + blk_size bsrc)%Z ->
    SREACH AI (pp_post AI ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P lo B gmax gifv ws mws LBK (ps_isreq st) m)
      (MS (mkR ra sp gp (wz (al_tp L_)) t0 t1 t2 s0 s1 (wz P) (wz SRC) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz parser_append_entry) fc None m (seg_rom rsegs)) s LB.
  Proof.
    intros until e. intros QLO QLO2 STK0 LO0 CEIL SPP PB BHI P8 SP16 HT MT GMX HR HE MI ST ERR PAR SIDE CAPB BSUB ND STAT BSRC SLEN N0 BIN B1 B2.
    pose proof (word_lt64 sp) as SPR. unfold PP_DEPTH, PP_ADEPTH in *. assert (LMAXE : LMAX = 2^26 + 16) by reflexivity.
    assert (EQ16 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 16)) = (bv_unsigned sp - 16)%Z) by (apply unsigned_lit; lia).
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    assert (WSL : length ws = 66%nat /\ length mws = 22%nat) by (destruct HT as (H1 & _); destruct MT as (H2 & _); split; assumption). destruct WSL as [WSL MWSL].
    assert (BSRC_LB : In bsrc LB) by (apply BSUB; apply in_or_app; right; exact BIN).
    destruct (ai_block_range rsegs AI _ _ _ _ HR BSRC_LB) as (SR1 & SR2 & SR3 & SR4 & _).

    pose proof (nodup_ids_perm _ _ (Permutation_app_tail LBK (ps_blocks_perm st)) ND) as NDp. rewrite <- app_assoc in NDp.
    assert (SUBo : bsub AI (ps_other st ++ LBK) LB).
    { intros b Hb. apply BSUB. apply in_or_app. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
      eapply Permutation_in; [apply Permutation_sym; apply ps_blocks_perm|]. apply in_or_app. right. exact Hb. }
    assert (KEEPo : bsub AI (ps_other st ++ LBK) (lb_keep AI (ps_okm st) LB)).
    { intros b Hb. destruct (ps_okm st) as [k|] eqn:EOK; cbn [lb_keep]; [| apply SUBo; exact Hb].
      apply (in_lb_remove AI); [apply SUBo; exact Hb|].
      unfold ps_blocks in NDp. rewrite ?EOK in NDp. cbn [okb app] in NDp.
      exact (ids_ne_head _ _ _ NDp Hb). }

    eapply sreach_evt. { eapply (pa_pro P lo); try eassumption; lia. }
    intros ms' (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : heap_pres AI LB (bv_unsigned sp) m m1).
    { eapply (munch_stack_heap_pres AI LOK s LB LB m); [exact HR| intros b Hb; exact Hb| exact MU1| exact WM1|]. constructor; [cbn; lia| constructor]. }
    pose proof (p_parser_heap_pres AI m m1 LB LB (bv_unsigned sp) P st PAR HP1 ltac:(lia) ltac:(intros b Hb; apply BSUB; apply in_or_app; left; exact Hb)) as PAR1.
    pose proof (pp_stat_heap_pres AI GDCS LB (bv_unsigned sp) m m1 _ _ _ _ STAT WSL MWSL HP1) as STAT1.
    transport_after_call rsegs m m1 MU1 WM1. clear MI. rename BSRC into BSRC1.
    pose proof PAR1 as PARc. destruct PARc as (SCN & MSG & CURR & METH & URI & RS & SMSG & VER & HL & XV & ENT & CTL & URL & UBO).
    pose proof MSG as MSGc. destruct MSGc as (MBC & OWN & MLC & MCAP & MNUL).
    destruct (p_msg_facts AI m1 LB P _ _ _ _ _ s HR1 MSG) as (_ & _ & LBS & NONEF & SOMEF).

    assert (NZ : n = 0 \/ 1 <= n) by lia. destruct NZ as [N00|N1].
    {
      rewrite !N00 in *.
      assert (ARNG : (0 <= ps_A st < 2^64)%Z).
      { pose proof alloc_ceiling_bounds as CEB. destruct (ps_okm st) as [k|] eqn:EOK; cbn in OWN.
        - destruct OWN as [HIN _]. destruct (ai_block_range rsegs AI s LB m1 _ HR1 HIN) as (R1 & _ & _ & R4 & _). cbn in R1, R4. lia.
        - lia. }
      eapply sreach_evt. { eapply (mba_zero lo (P + 400) (ps_A st) (ps_len st) (ps_cap st) SRC); rewrite ?EQ16; try eassumption; unfold LMAX in *; lia. }
      intros ms' (mz & a2z & a3' & a4' & a6' & -> & MUz & WMz & MIz & STz & MBCz). rewrite ?EQ16 in MUz, STz.
      assert (HRz : RHEAP rsegs AI s LB mz).
      { eapply (ai_heap_frame rsegs AI); [exact HR1| exact MUz| exact WMz|]. constructor; [left; cbn; lia| constructor]. }
      assert (HEz : RENV rsegs AI mz B).
      { eapply (ai_env_frame rsegs AI); [exact HR1| exact HE1| exact MUz| exact WMz|]. constructor; [left; cbn; lia| constructor]. }
      assert (HPz : heap_pres AI LB (bv_unsigned sp) m1 mz).
      { eapply (munch_stack_heap_pres AI LOK s LB LB m1); [exact HR1| intros b Hb; exact Hb| exact MUz| exact WMz|]. constructor; [cbn; lia| constructor]. }
      pose proof (p_parser_heap_pres AI m1 mz LB LB (bv_unsigned sp) P st PAR1 HPz ltac:(lia) ltac:(intros b Hb; apply BSUB; apply in_or_app; left; exact Hb)) as PARz.
      pose proof (pp_stat_heap_pres AI GDCS LB (bv_unsigned sp) m1 mz _ _ _ _ STAT1 WSL MWSL HPz) as STATz.
      pose proof (heap_pres_trans rsegs AI _ _ _ _ _ HP1 HPz) as HPmz.
      repeat match goal with H : munch _ _ m1 |- _ => clear H | H : wmono _ _ m1 |- _ => clear H end.
      transport_after_call rsegs m1 mz MUz WMz. clear MI1 HR1 HE1 PAR1 STAT1.
      replace (ret_pc (Z_to_bv 64 0x16040)) with (Z_to_bv 64 0x16040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof PARz as PARc1. destruct PARc1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CTL1 & _). destruct CTL1 as [CC1 CR1].
      eapply sreach_evt. { eapply (pa_post P 0 lo); try eassumption; lia. }
      intros ms' (m3 & MU3 & WM3 & MI3 & ST3 & [(RNZ & _ & ->)|(_ & -> & ->)]); [exfalso; lia|].
      assert (HX1 : hpx AI (pp_W P) LBK (bv_unsigned sp) m mz).
      { apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPmz| lia| intros b Hb; apply BSUB; apply in_or_app; right; exact Hb]. }
      eapply sreach_mono.
      { eapply (PP P lo B gmax gifv ws mws LBK st s LB); try eassumption; try reflexivity; try (unfold PP_DEPTH, PP_ADEPTH; lia).
        specialize (SIDE (ps_A st) (ps_cap st) (ps_okm st) (ps_bs st)). rewrite Z.add_0_r in SIDE. destruct st; exact SIDE. }
      cbv beta. intros s' LB' ms' PO. unfold pp_post in PO |- *. destruct_exs PO.
      destruct PO as (-> & MI4 & ST4 & HE4 & ERR4 & HPX4 & HR4 & PAR4 & ISR4 & BS4 & ND4 & STAT4 & RR4).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [exact ERR4|].
      split; [eapply (hpx_trans rsegs AI); [exact HX1| exact HPX4]|]. split; [exact HR4|]. split; [exact PAR4|].
      split; [exact ISR4|]. split; [exact BS4|]. split; [exact ND4|]. split; [exact STAT4| exact RR4]. }
    eapply sreach_bind.
    { eapply (membuffer_append_spec AI AC LOK REALLOCPC) with (lo := lo) (B := B) (MB := (P + 400)%Z) (SRC := SRC) (n := n)
        (A := ps_A st) (len := ps_len st) (cap := ps_cap st) (ok := ps_okm st) (bs := ps_bs st) (src := src);
        rewrite ?EQ16; try eassumption; try reflexivity; try lia.
      - intros NN. destruct (ps_okm st); [exact MNUL| exfalso; apply NN; reflexivity].
      - apply mbloc_stack; lia.
      - eapply client_range_block; [apply KEEPo; apply in_or_app; right; exact BIN| exact B1| exact B2]. }
    intros sx2 LB2 ms2 Q2. unfold membuffer_append_post in Q2. rewrite !EQ16 in Q2. destruct_exs Q2.
    destruct Q2 as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HPX2 & HR2 & KSUB2 & MBC2 & LC2 & CAP32 & CAPB2 & OWN2 & FRESH2 & PFX2 & R2).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    lazymatch type of OWN2 with mown _ _ _ ?a ?c ?o ?b => rename a into A2; rename c into cap2; rename o into ok2; rename b into bs2 end.
    lazymatch type of MBC2 with rw_cells _ _ _ (mbuf_cells _ ?l _) => rename l into len2 end.
    lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r2 end.
    replace (ret_pc (Z_to_bv 64 0x16040)) with (Z_to_bv 64 0x16040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

    assert (HPs2 : heap_pres AI ([] : list BLK) (2^64) m1 m2).
    { eapply heap_pres_of_hpx. { eapply hpx_weaken; [exact HPX2| intros xo Hxo; exact Hxo| lia| intros b Hb; destruct Hb]. }
      intros a Ha [Hc|[(lo' & hi' & Hst & Hr)|(b & Hb & _)]]; [lia| | destruct Hb].
      destruct (lo_static_img rsegs AI LOK lo' hi' Hst) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). cbn. lia. }
    pose proof (pp_stat_heap_pres AI GDCS [] (2^64) m1 m2 _ _ _ _ STAT1 WSL MWSL HPs2) as STAT2.
    pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX2 FR1 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FR2.
    assert (KEEPo2 : bsub AI (ps_other st ++ LBK) LB2) by (intros b Hb; apply KSUB2; apply KEEPo; exact Hb).
    assert (HX12 : hpx AI (pp_W P) LBK (bv_unsigned sp) m m2).
    { eapply (hpx_trans rsegs AI). { apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HP1| lia| intros b Hb; apply BSUB; apply in_or_app; right; exact Hb]. }
      eapply (hpx_weaken rsegs AI); [exact HPX2| | lia| intros b Hb; apply KEEPo; apply in_or_app; right; exact Hb].
      unfold pp_W, sub_fp. intros xo OX. cbn [outside] in OX |- *. lia. }

    assert (NUL2 : match ok2 with None => len2 = 0 | Some _ => nth_error bs2 (Z.to_nat len2) = Some (Z_to_bv 8 0) end /\ (len2 = ps_len st + n \/ (r2 = -104 /\ len2 = ps_len st))%Z).
    { destruct R2 as [(-> & EL & PF)|(-> & -> & -> & -> & -> & -> & ->)].
      - split; [| left; exact EL]. destruct ok2 as [k2|].
        + eapply (nul_of_firstn bs2 (firstn (Z.to_nat (ps_len st)) (ps_bs st) ++ src)); [| | lia].
          * rewrite (PF ltac:(lia)). rewrite <- app_assoc. reflexivity.
          * rewrite app_length, firstn_length. destruct (ps_okm st) as [k|]; [| destruct (NONEF eq_refl) as (_ & EL0 & _); destruct OWN as (_ & _ & ->); cbn; lia]. lia.
        + exfalso. cbn in OWN2. lia.
      - split; [exact MNUL| right; split; reflexivity]. }
    destruct NUL2 as [NUL2 LEN2].
    assert (PAR2 : p_parser AI m2 LB2 P (set_msg st A2 len2 cap2 ok2 bs2)).
    { eapply (p_parser_msg_update s LB m1 m1 m2 LB LB2 (lb_keep AI (ps_okm st) LB) (bv_unsigned sp - 16) P st); try eassumption; try LiaTuning.alia.
      - intros b Hb. exact (lb_keep_sub rsegs AI _ _ _ Hb).
      - intros b Hb. apply KEEPo. apply in_or_app. left. exact Hb.
      - intros b Hb. apply KEEPo2. apply in_or_app. left. exact Hb. }

    pose proof PAR2 as PARc2. destruct PARc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CTL2 & _). destruct CTL2 as [CC2 CR2].
    cbn [set_msg ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp] in CC2.
    assert (R2' : (r2 = 0 \/ r2 = -104)%Z) by (destruct R2 as [(E & _)|(E & _)]; lia).
    eapply sreach_evt. { eapply (pa_post P r2 lo); try eassumption; lia. }
    intros ms' (m3 & MU3 & WM3 & MI3 & ST3 & [(RNZ & CC3 & ->)|(-> & -> & ->)]).
    -
      destruct R2 as [(E0 & _)|(_ & -> & -> & -> & -> & -> & ->)]; [exfalso; lia|].
      assert (HX3 : hpx AI [(P + 440, P + 480)]%Z LB (bv_unsigned sp - 16) m2 m3).
      { eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; exact Hb| exact MU3| exact WM3|].
        constructor; [| constructor]. right; right. cbn. lia. }
      assert (PAR3 := p_parser_ctl_update sx2 LB m2 m2 m3 LB LB (bv_unsigned sp - 16) P _ 500 (ps_hack st) (ps_pos st) (ps_entp st) (ps_clen st) (ps_csz st) (ps_esp st)
                        HR2 ltac:(intros b Hb; exact Hb) PAR2 HX3 ltac:(lia) ltac:(lia) ltac:(lia)).
      cbn [set_msg ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB] in PAR3.
      specialize (PAR3 ltac:(unfold ps_blocks; cbn [ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB]; intros b Hb; apply BSUB; apply in_or_app; left; exact Hb) CC3).
      destruct CR2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      specialize (PAR3 ltac:(lia) Q2 Q3 Q4 Q5 Q6 Q7).
      pose proof (rw_cells_transport rsegs _ m2 m3 _ _ ERR2 MU3 WM3 ltac:(cbn; lia)) as ERR3.
      apply sreach_ret. unfold pp_post. do 14 eexists. exists m3, 3. eexists.
      split; [reflexivity|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply (ai_env_frame rsegs AI); [exact HR2| exact HE2| exact MU3| exact WM3|]. constructor; [left; cbn; lia| constructor]. }
      split; [exists e2; exact ERR3|].
      split. { eapply (hpx_trans rsegs AI); [exact HX12|]. eapply (hpx_seg rsegs AI); [exact LOK| exact HR2| intros b Hb; apply KEEPo2; apply in_or_app; right; exact Hb| exact MU3| exact WM3|].
               constructor; [| constructor]. right; right. cbn. lia. }
      split. { eapply (ai_heap_frame rsegs AI); [exact HR2| exact MU3| exact WM3|]. constructor; [left; cbn; lia| constructor]. }
      split; [exact PAR3|]. split; [reflexivity|].
      split. { unfold ps_blocks. cbn [ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB]. exact BSUB. }
      split. { unfold ps_blocks. cbn [ps_ns ps_hs ps_okm ps_A ps_cap ps_sok ps_SA ps_scap ps_UB]. exact ND. }
      split. { eapply (pp_stat_heap_pres AI GDCS [] (2^64)); [exact STAT2| exact WSL| exact MWSL|]. eapply munch_statics_heap_pres; [exact MU3| exact WM3|]. constructor; [cbn; lia| constructor]. }
      lia.
    -
      destruct LEN2 as [EL2|[E0 _]]; [| exfalso; lia].
      set (st2 := set_msg st A2 len2 cap2 ok2 bs2) in PAR2.
      assert (BS2 : bsub AI (ps_blocks AI st2 ++ LBK) LB2).
      { intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| apply KEEPo2; apply in_or_app; right; exact Hb].
        apply (Permutation_in _ (ps_blocks_perm st2)) in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        - subst st2. cbn [set_msg ps_okm ps_A ps_cap] in Hb. destruct ok2 as [k2|]; cbn in Hb; [| destruct Hb]. destruct Hb as [<-|[]]. cbn in OWN2. exact (proj1 OWN2).
        - apply KEEPo2. apply in_or_app. left. exact Hb. }
      assert (ND2 : NoDup (map blk_id (ps_blocks AI st2 ++ LBK))).
      { eapply nodup_ids_perm. { apply Permutation_app_tail. apply Permutation_sym. apply ps_blocks_perm. }
        rewrite <- app_assoc. change (ps_other st2) with (ps_other st). subst st2. cbn [set_msg ps_okm ps_A ps_cap].
        assert (NDo : NoDup (map blk_id (ps_other st ++ LBK))).
        { unfold ps_blocks in NDp. destruct (ps_okm st) as [k|]; cbn [okb app] in NDp; [| exact NDp]. cbn [map] in NDp. inversion NDp; assumption. }
        destruct ok2 as [k2|]; cbn [okb app]; [| exact NDo].
        eapply (fresh_ids_cons sx2 LB2 m2); [exact HR2| cbn in OWN2; exact (proj1 OWN2)| exact KEEPo2| | exact NDo].
        intros b Hb. exact (FRESH2 b (KEEPo b Hb)). }
      eapply sreach_mono.
      { eapply (PP P lo B gmax gifv ws mws LBK st2 sx2 LB2); try eassumption; try reflexivity; try (unfold PP_DEPTH, PP_ADEPTH; lia).
        subst st2. rewrite EL2. apply SIDE. }
      cbv beta. intros s' LB' ms' PO. unfold pp_post in PO |- *. destruct_exs PO.
      destruct PO as (-> & MI4 & ST4 & HE4 & ERR4 & HPX4 & HR4 & PAR4 & ISR4 & BS4 & ND4 & STAT4 & RR4).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [exact ERR4|].
      split; [eapply (hpx_trans rsegs AI); [exact HX12| exact HPX4]|]. split; [exact HR4|]. split; [exact PAR4|].
      split; [rewrite ISR4; reflexivity|]. split; [exact BS4|]. split; [exact ND4|]. split; [exact STAT4| exact RR4].
  Qed.

  Definition st_init (isreq rm pos : Z) : pstate AI :=
    mkPS 0 0 0 0 None [] 0 [CB 216 (repeat (Z_to_bv 8 0) 216)] rm 0 0 0 0 None [] isreq 0 0 [] [] 0 (wz 0) (wz 0) 400 0 pos 1 0 0 0 0 [].

  #[using="CE"] Lemma init_parser : forall m (LB : list BLK) P isreq rm pos,
    parser_init_cells m P isreq rm pos -> (0 <= isreq <= 1)%Z -> (0 <= rm <= 11)%Z -> (0 <= pos <= 4)%Z ->
    p_parser AI m LB P (st_init isreq rm pos) /\ rw_cells rsegs m (P + 500) [C4 (wz 0)].
  Proof.
    intros m LB P isreq rm pos (K1 & K2 & K3 & SB & K4 & LL & FL & FFC & ENT & MB & K5) IR RR PR.
    unfold pinit_k5 in K5.
    change (rw_cells rsegs m (P + 432) ([C8 (wz 0)] ++ ([C4 (wz 400); C4 (wz 0); C4 (wz pos); C4 (wz 1); C4 (wz 0); C4 (wz 0); C8 (wz 0); C8 (wz 0)] ++ ([C8 (wz (P + 400)); C8 (wz 0); C4 (wz 0)] ++ [C4 (wz 0)])))) in K5.
    apply rw_cells_app in K5. destruct K5 as [URL K5]. cbn [cells_size csize Nat.add] in K5. replace (P + 432 + Z.of_nat 8)%Z with (P + 440)%Z in K5 by lia.
    apply rw_cells_app in K5. destruct K5 as [CTL K5]. cbn [cells_size csize Nat.add] in K5. replace (P + 440 + Z.of_nat 40)%Z with (P + 480)%Z in K5 by lia.
    apply rw_cells_app in K5. destruct K5 as [SCN PAD]. cbn [cells_size csize Nat.add] in PAD. replace (P + 480 + Z.of_nat 20)%Z with (P + 500)%Z in PAD by lia.
    assert (LMAXE : LMAX = 2^26 + 16) by reflexivity. assert (VMAXE : VMAX = 2^29) by reflexivity.
    split; [| exact PAD].
    unfold p_parser, st_init. cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB].
    split; [exact SCN|].
    split. { split; [exact MB|]. split; [cbn; repeat split; reflexivity|]. split; [lia|]. split; [lia| reflexivity]. }
    split; [lia|].
    split; [split; [exact K1| lia]|].
    split; [split; [exact K2| reflexivity]|].
    split; [split; [exact K3| lia]|].
    split. { split; [exact SB|]. split; [cbn; repeat split; reflexivity|]. lia. }
    split. { split; [exists (wz 0); exact K4| lia]. }
    split. { unfold p_hlist. cbn [hd_addr last_addr zlength length Z.of_nat dlseg hdrs_mem map].
             split; [exact LL|]. split; [exact FL|]. split; [exact FFC|]. split; [exact I|]. split; [exact I|]. split; [reflexivity|].
             split; [intros h Hh; destruct Hh|]. match goal with |- ?g => idtac "ZL" g end. unfold zlength. cbn. lia. }
    split; [lia|].
    split; [exact ENT|].
    split. { split; [exact CTL| lia]. }
    split. { split; [exact URL| lia]. }
    cbn. reflexivity.
  Qed.

  #[using="Type"] Lemma cell8_same : forall m A (x y : word), rw_cells rsegs m A [C8 x] -> rw_cells rsegs m A [C8 y] -> x = y.
  Proof.
    intros m A x y R1 R2.
    pose proof (rw_cells_readn rsegs m A [C8 x] 0%nat _ 8 R1 eq_refl eq_refl) as E1. pose proof (rw_cells_readn rsegs m A [C8 y] 0%nat _ 8 R2 eq_refl eq_refl) as E2.
    cbn [cbytes] in E1, E2. rewrite E1 in E2.
    apply (f_equal (fun o : option (list byte) => match o with Some l => le_bytes_to_word l | None => Z_to_bv 64 0 end)) in E2.
    cbv beta iota in E2. rewrite !le_bytes_to_word_le8 in E2. exact E2.
  Qed.

  Ltac stk_add ST H :=
    lazymatch type of H with rw_cells _ _ ?A _ =>
      lazymatch type of ST with stk _ _ _ ?hi => replace hi with A in ST by (cbn; lia) end;
      let S := fresh in pose proof (stk_release rsegs _ _ _ _ ST H ltac:(lia)) as S; clear ST; rename S into ST
    end.

  Hypothesis STKB : (0 <= al_stack L_ <= 8192)%Z.

  #[using="AC LOK FREEPC REALLOCPC GDCS GUARDW SSP0 PP CE STKB"] Theorem fuzz_one_proof : fuzz_one_stmt AI.
  Proof.
    unfold fuzz_one_stmt. intros until data. intros BUF DLEN NR DOR HR HE SPB BHI ST CEIL LO SP16 ERR MI G SS1 SS2 -> -> -> FRM.
    pose proof (word_lt64 sp) as SPR. unfold PARSER_STACK in LO.
    assert (LMAXE : LMAX = 2^26 + 16) by reflexivity. assert (VMAXE : VMAX = 2^29) by reflexivity.
    assert (CAN0 : canary = GUARDW) by (destruct (SSP0 _ _ _ HR) as [_ S2]; exact (cell8_same _ _ _ _ SS2 S2)).
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    assert (NZ : n = 0 \/ 1 <= n) by lia. destruct NZ as [-> | N1].
    {
      eapply sreach_evt. { apply fz_zero. }
      intros ms' ->. apply sreach_ret. unfold fuzz_one_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split.
      { split; [exact MI|]. split; [exact ST|]. split; [exact HE|]. split; [exists errv; exact ERR|]. apply heap_pres_refl. }
      split; [exact HR|]. split; [intros b Hb; exact Hb|]. split; [exact G|]. split; [exact SS1| exact SS2]. }

    destruct data as [|b0 rest]; [cbn in DLEN; exfalso; lia|]. cbn [length] in DLEN.
    destruct DOR as [[E0 _]|[k KIN]]; [exfalso; lia|].
    destruct (ai_block_range rsegs AI _ _ _ _ HR KIN) as (DB1 & DB2 & DB3 & DB4 & _). cbn [blk_addr blk_size fst snd] in DB1, DB2, DB3, DB4.
    eapply sreach_evt. { eapply (fz_pro D n lo b0 rest); try eassumption; try LiaTuning.alia. }
    intros ms' (m1 & junk & a2' & MU1 & WM1 & MI1 & ST1 & PJ & FS & CASES).
    assert (HR1 : RHEAP rsegs AI s LB m1).
    { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HE1 : RENV rsegs AI m1 B).
    { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU1| exact WM1|]. constructor; [left; cbn; lia| constructor]. }
    assert (HP1 : heap_pres AI LB (bv_unsigned sp) m m1).
    { eapply (munch_stack_heap_pres AI LOK s LB LB m); [exact HR| intros b Hb; exact Hb| exact MU1| exact WM1|]. constructor; [cbn; lia| constructor]. }
    pose proof (GD_heap_pres AI GDCS _ _ _ _ G HP1) as G1.
    pose proof (rw_cells_transport rsegs _ m m1 _ _ ERR MU1 WM1 ltac:(cbn; lia)) as ERR1.
    pose proof (bytes_at_transport rsegs _ m m1 _ _ BUF MU1 ltac:(cbn [disjoint_from length]; lia)) as BUF1.
    clear MI.
    set (P := (bv_unsigned sp - 528)%Z) in *.
    assert (EQP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
    assert (PAL : (P mod 8 = 0)%Z) by (subst P; clear - SP16 SPR; Z.div_mod_to_equations; lia).
    assert (PAL16 : (P mod 16 = 0)%Z) by (subst P; clear - SP16 SPR; Z.div_mod_to_equations; lia).

    assert (CONT : forall (isreq rm pos : Z) x1 t0' t1' t2' a0' a1' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2,
      (0 <= isreq <= 1)%Z -> (0 <= rm <= 11)%Z -> (pos = 0 \/ pos = 1)%Z ->
      parser_init_cells m2 P isreq rm pos -> mem_inv rsegs m2 -> stk rsegs m2 lo P ->
      munch [(P - 64, P); (P, P + 504)]%Z m1 m2 -> wmono rsegs m1 m2 ->
      SREACH AI (fuzz_one_post AI ra sp gp (wz (al_tp L_)) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB lo B canary m)
        (MS (mkR x1 (wz P) gp (wz (al_tp L_)) t0' t1' t2' (wz (D + 1)) (wz (n - 1)) a0' a1' a2'' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz 0x14004) fc None m2 (seg_rom rsegs)) s LB).
    { intros until m2. intros IR RR POS INIT MI2 ST2 MU2 WM2.
      assert (HR2 : RHEAP rsegs AI s LB m2).
      { eapply (ai_heap_frame rsegs AI); [exact HR1| exact MU2| exact WM2|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      assert (HE2 : RENV rsegs AI m2 B).
      { eapply (ai_env_frame rsegs AI); [exact HR1| exact HE1| exact MU2| exact WM2|]. constructor; [left; cbn; lia|]. constructor; [left; cbn; lia| constructor]. }
      assert (HP2 : heap_pres AI LB (bv_unsigned sp) m1 m2).
      { eapply (munch_stack_heap_pres AI LOK s LB LB m1); [exact HR1| intros b Hb; exact Hb| exact MU2| exact WM2|]. constructor; [cbn; lia|]. constructor; [cbn; lia| constructor]. }
      pose proof (heap_pres_trans rsegs AI _ _ _ _ _ HP1 HP2) as HP02.
      pose proof (GD_heap_pres AI GDCS _ _ _ _ G1 HP2) as G2.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ ERR1 MU2 WM2 ltac:(cbn; lia)) as ERR2.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FS MU2 WM2 ltac:(cbn; lia)) as FS2.
      pose proof (bytes_at_transport rsegs _ m1 m2 _ _ BUF1 MU2 ltac:(cbn [disjoint_from length]; lia)) as BUF2.
      destruct (GD_statics m2 G2) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8).
      assert (STAT2 : pp_stat m2 GMAX_VAL GIFV HDR_WS MT_WS) by (unfold pp_stat; repeat (split; [assumption|]); assumption).
      destruct (init_parser m2 LB P isreq rm pos INIT IR RR ltac:(lia)) as [PAR2 PAD2].

      eapply sreach_evt. { apply fz_mid. } intros msx ->.
      change (Z_to_bv 64 (bv_unsigned sp - 528)) with (Z_to_bv 64 P).
      assert (SRC : bytes_at rsegs m2 (D + 1) rest).
      { change (b0 :: rest) with ([b0] ++ rest) in BUF2. apply bytes_at_app in BUF2. destruct BUF2 as [_ B2]. exact B2. }
      eapply sreach_bind.
      { eapply (parser_append_spec P lo B GMAX_VAL GIFV HDR_WS MT_WS LB (st_init isreq rm pos) s LB (D + 1) (n - 1) rest (k, D, n));
          rewrite ?EQP; try eassumption; try reflexivity; unfold PP_DEPTH, PP_ADEPTH, GMAX_VAL; cbn [blk_addr blk_size fst snd]; try lia.
        - exact (hdr_tab_facts lo ltac:(lia)).
        - exact (meth_tab_facts lo ltac:(lia)).
        - intros A' cap' ok' bs'. unfold pp_side, set_msg, st_init, POS_ENTITY, POS_RESPONSE_LINE, POS_HEADERS.
          cbn [ps_cur ps_A ps_len ps_cap ps_okm ps_bs ps_meth ps_uc ps_rm ps_sc ps_SA ps_slen ps_scap ps_sok ps_sbs ps_isreq ps_maj ps_min ps_ns ps_hs ps_X ps_ebw ps_elw ps_err ps_hack ps_pos ps_entp ps_clen ps_csz ps_esp ps_ub ps_UB].
          split; [lia|]. split; [intros E; exfalso; lia|]. split; [intros _; reflexivity|]. split; [intros _; split; [lia| intros X; exfalso; apply X; reflexivity]|]. intros; lia.
        - cbn [ps_cap st_init]. lia.
        - unfold ps_blocks, st_init. cbn. intros b Hb. exact Hb.
        - unfold ps_blocks, st_init. cbn. exact (ai_blocks_nodup rsegs AI _ _ _ HR2). }
      intros sx3 LB3 ms3 PO3. unfold pp_post in PO3. rewrite !EQP in PO3. destruct_exs PO3.
      destruct PO3 as (-> & MI3 & ST3 & HE3 & [e3 ERR3] & HPX3 & HR3 & PAR3 & ISR3 & BS3 & ND3 & STAT3 & RR3).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      lazymatch type of PAR3 with p_parser _ _ _ _ ?x => rename x into st3 end.
      replace (ret_pc (Z_to_bv 64 0x14014)) with (Z_to_bv 64 0x14014) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX3 PAD2 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as PAD3.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX3 FS2 ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as FS3.
      assert (HP3 : heap_pres AI LB (bv_unsigned sp) m2 m3).
      { eapply (hpx_stack_heap_pres AI LOK s LB LB m); [exact HR| intros b Hb; exact Hb| exact HPX3| lia|]. constructor; [cbn; lia| constructor]. }
      pose proof (GD_heap_pres AI GDCS _ _ _ _ G2 HP3) as G3.

      eapply sreach_evt. { apply fz_mid2. } intros msy ->.
      pose proof PAR3 as PARc. destruct PARc as (SCN3 & MSG3 & CUR3 & METH3 & URI3 & RS3 & SMSG3 & VER3 & HL3 & XV3 & ENT3 & CTL3 & URL3 & UBO3).
      destruct MSG3 as (MBC3 & OWN3 & MLC3 & MCAP3 & MNUL3). destruct SMSG3 as (SBC3 & SOWN3 & SLC3 & SCAP3).
      destruct METH3 as [MC3 MR3]. destruct URI3 as [UC3 UL3]. destruct RS3 as (RC3 & RR1 & RR2). destruct VER3 as [(pad3 & VC3) VR3].
      destruct HL3 as (LC3 & FLC3 & FF3 & DL3 & HS3 & ITEMS3 & HB3 & NB3 & X03). destruct CTL3 as [CC3 CR3]. destruct URL3 as [UU3 UR3].
      eapply sreach_bind.
      { eapply (httpmsg_destroy_specN AI AC LOK FREEPC) with (lo := lo) (B := B) (P := P) (LBK := LB)
          (MBb := okb AI (ps_okm st3) (ps_A st3) (ps_cap st3)) (SBb := okb AI (ps_sok st3) (ps_SA st3) (ps_scap st3)) (UB := ps_UB st3)
          (ns := ps_ns st3) (hs := ps_hs st3) (fcmp := httpmsg_compare_entry);
          rewrite ?EQP; try eassumption; try reflexivity; try lia.
        - replace (P + 288 + 80)%Z with (P + 368)%Z by lia. exact FF3.
        - unfold httpmsg_compare_entry. lia.
        - destruct (ps_okm st3) as [km|]; cbn in OWN3 |- *; [reflexivity| lia].
        - destruct (ps_sok st3) as [ks|]; cbn in SOWN3 |- *; [reflexivity| lia].
        - intros b Hb. apply BS3. unfold ps_blocks, hl_blocks. revert Hb. rewrite <- !app_assoc. intros Hb. exact Hb.
        - unfold ps_blocks, hl_blocks in ND3. rewrite <- !app_assoc in ND3. exact ND3. }
      intros sx4 LB4 ms4 PO4. unfold httpmsg_destroy_postN in PO4. rewrite !EQP in PO4. destruct_exs PO4.
      destruct PO4 as (-> & MI4 & ST4 & HE4 & [e4 ERR4] & HPX4 & HR4 & KSUB4 & IC4 & LC4 & FLC4 & FF4 & MBC4 & SBC4 & UU4).
      lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
      replace (ret_pc (Z_to_bv 64 0x1401c)) with (Z_to_bv 64 0x1401c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      Ltac mv4 HPX H := let H' := fresh in pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX H ltac:(apply client_range_above; lia) ltac:(cbn; lia)) as H'; clear H; rename H' into H.
      rewrite UL3 in *|| idtac.
      mv4 HPX4 UC3. mv4 HPX4 RC3. mv4 HPX4 VC3. mv4 HPX4 ENT3. mv4 HPX4 CC3. mv4 HPX4 SCN3. mv4 HPX4 PAD3. mv4 HPX4 FS3.

      pose proof ST4 as STK.
      stk_add STK IC4. stk_add STK UC3. stk_add STK RC3. stk_add STK SBC4. stk_add STK VC3. stk_add STK LC4. stk_add STK FLC4.
      replace (P + 288 + 80)%Z with (P + 368)%Z in FF4 by lia. stk_add STK FF4. stk_add STK ENT3. stk_add STK MBC4. stk_add STK UU4.
      stk_add STK CC3. stk_add STK SCN3. stk_add STK PAD3.
      lazymatch type of STK with stk _ _ _ ?hi => replace hi with (bv_unsigned sp - 528 + 504)%Z in STK by (cbn; lia) end.
      replace (P + 504)%Z with (bv_unsigned sp - 528 + 504)%Z in FS3 by lia.
      eapply sreach_evt. { eapply (fz_epi lo); try eassumption; subst P; lia. }
      intros msz [-> STF].

      assert (HP4 : heap_pres AI LB (bv_unsigned sp) m3 m4).
      { eapply (hpx_stack_heap_pres AI LOK s LB LB m); [exact HR| intros b Hb; exact Hb| exact HPX4| lia|].
        repeat (constructor; [cbn; lia|]). constructor. }
      apply sreach_ret. unfold fuzz_one_post. repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|].
      split. { split; [exact MI4|]. split; [exact STF|]. split; [exact HE4|]. split; [exists e4; exact ERR4|].
               eapply (heap_pres_trans rsegs AI); [exact HP02|]. eapply (heap_pres_trans rsegs AI); [exact HP3| exact HP4]. }
      split; [exact HR4|]. split; [exact KSUB4|].
      split; [exact (GD_heap_pres AI GDCS _ _ _ _ G3 HP4)|].
      rewrite CAN0. exact (SSP0 _ _ _ HR4). }
    destruct CASES as [[EV ->]|[OD ->]].
    -
      eapply sreach_evt. { eapply (parser_request_init_spec P junk); rewrite ?EQP; try eassumption; lia. }
      intros ms' Q. destruct_exs Q. destruct Q as (-> & MU2 & WM2 & MI2 & ST2 & INIT2). rewrite !EQP in *.
      replace (ret_pc (Z_to_bv 64 0x13ff8)) with (Z_to_bv 64 0x13ff8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply sreach_evt. { apply fz_j. } intros ms' ->.
      eapply (CONT 1 0 0); try eassumption; try LiaTuning.alia. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn. intros y Hy. lia.
    -
      eapply sreach_evt. { eapply (parser_response_init_spec P junk 2); rewrite ?EQP; try eassumption; lia. }
      intros ms' Q. destruct_exs Q. destruct Q as (-> & MU2 & WM2 & MI2 & ST2 & INIT2). rewrite !EQP in *.
      replace (ret_pc (Z_to_bv 64 0x14004)) with (Z_to_bv 64 0x14004) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      eapply (CONT 0 2 1); try eassumption; try LiaTuning.alia.
  Qed.
End W.
