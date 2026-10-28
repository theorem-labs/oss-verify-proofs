(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX AsStack0 AsAuxv ECH_AImg ECH_Xpres ECH_ARep ECH_ALib
  ECH_ALibMF ECH_Iface ECH_AStmt_C1 ECH_AC1_zalloc ECH_AC1_free ECH_AC1_malloc ECH_AC1_dup ECH_AStmt_C3 ECH_AStmt_C4 ECH_AStmt_C5 ECH_AStmt_C7 ECH_AStmt_C10 ECH_AStmt_C13
  ECH_AStmt_C6 ECH_AStmt_C8 ECH_AStmt_C9 ECH_AKit ECH_AKitSeg ECH_AsKit ECH_AC13_entry ECH_AC13_store ECH_AC7_kit ECH_AC7_rd ECH_AC7_rd2 ECH_AC7_bioread ECH_ARostr ECH_ALibMid ECH_AC11_fail ECH_AC12_addstr ECH_AC13 ECH_AC14_kit
  ECH_AC14_bio2buf_seg ECH_AC14_ladder_seg ECH_AC14_ladloop ECH_AC14_fmt_seg ECH_AC14_flat_seg ECH_AC14_entry_seg ECH_AStmt_C14 F_strspn N6_strspn F_time ECH_AC14_b2b ECH_AC14_fmt.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ENTRY_BYTES (rem : Z) : Z := 20 * rem + 2048.   (* [comment removed for export] *)
Definition ENTRY_CNT (rem : Z) : Z := (2 * rem) / 5 + 56.  (* [comment removed for export] *)
Definition ENTRY_KEPT (elen : Z) : Z := 13 * elen + 512.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ENTRY_CM (elen : Z) : Z := 3584 * elen + 8192.
Definition ENTRY_CF (elen : Z) : Z := 2304 * elen + 8192.

Section S0.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Definition SKB (st : Z) (S' : storerep) : list block := match es_entries_o S' with None => [] | Some (K, _) => blocks_SK (es_entries S') K end.
  Definition EBS (S' : storerep) : list block :=
    match es_entries_o S' with None => [] | Some (K, es) => concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine (sk_elems K) es)) end.
  Definition nent (S' : storerep) : Z := match es_entries_o S' with Some (_, es) => Z.of_nat (length es) | None => 0 end.
  Lemma blocks_STORE_split : forall st S', blocks_STORE st S' = (es_id S', st, STORE_SIZE) :: SKB st S' ++ EBS S'.
  Proof. intros st [e [[K es]|] i]; reflexivity. Qed.
  (* [comment removed for export] *)
  Definition dledger (S' : storerep) (c : Z) : Prop :=
       5 * Z.of_nat (length (EBS S')) <= 2 * c /\ lb_bytes (EBS S') <= 13 * c + 512 * nent S' /\ 23 * nent S' <= c /\ 0 <= c.
  Lemma dledger_mono : forall S' c c', dledger S' c -> c <= c' -> dledger S' c'.
  Proof. intros S' c c' (L1 & L2 & L3 & L4) LE'. unfold dledger. repeat split; lia. Qed.

  (* [comment removed for export] *)
  Lemma dec_stack : forall M M', mid_step M M' ->
       DECEXTS_STACK M' + 464 <= READCFG_STACK M /\ FCC_STACK M' + 464 <= READCFG_STACK M /\ RAISE_STACK (mid_err M') + 464 <= READCFG_STACK M
    /\ SKPUSH_STACK + 464 <= READCFG_STACK M /\ ENTRYFREE_STACK + 464 <= READCFG_STACK M /\ CZALLOC_STACK + 464 <= READCFG_STACK M
    /\ CARRAY_STACK + 464 <= READCFG_STACK M /\ CMEMDUP_STACK + 464 <= READCFG_STACK M /\ PKMEMDUP_STACK + 464 <= READCFG_STACK M
    /\ PKSTRNDUP_STACK + 464 <= READCFG_STACK M /\ SKNEW_STACK + 464 <= READCFG_STACK M
    /\ BIOFREEALL_STACK + 464 <= READCFG_STACK M /\ CFREE_STACK + 464 <= READCFG_STACK M /\ AFS_STACK + 464 <= READCFG_STACK M
    /\ AINTRIN_STACK + 464 <= READCFG_STACK M /\ ASTRSPN_STACK + 464 <= READCFG_STACK M /\ 9152 <= READCFG_STACK M.
  Proof.
    intros [f c e E v] [f' c' e' E' v'] (_ & _ & SE & _). cbn [mid_ctx mid_err] in SE. unfold READCFG_STACK, DECEXTS_STACK, FCC_STACK, mid_stack. cbn [mid_ctx mid_err].
    destruct e' as [|k'].
    - destruct e as [|k]; [| discriminate (SE k eq_refl)]. destruct c as [|x]; vm_compute; repeat split; discriminate.
    - destruct e as [|k]; destruct c as [|x]; vm_compute; repeat split; discriminate.
  Qed.
End S0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section OBJX.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma ENTRYobj_frameX : forall L0 SP X m m' ee E,
    ENTRYobj L0 m ee E -> xpres H L0 SP X m m' -> (forall b, In b (blocks_ENTRY ee E) -> avoids X (blk_addr b) (blk_size b)) -> ENTRYobj L0 m' ee E.
  Proof.
    intros L0 SP X m m' ee E EO XP AV. pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & EIN & O1 & O2 & O3 & O4 & XT).
    unfold ENTRYobj. split; [| split; [exact EIN| split; [exact O1| split; [exact O2| split; [exact O3| split; [exact O4|]]]]]].
    - exists pad1, pad2, pad3, pad4. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      eapply (xpres_rw_cells' H); [exact XP| exact HC| |].
      + right; right; left. exists (en_id E, ee, ENTRY_SIZE). split; [exact EIN|]. unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add length]. unfold ENTRY_SIZE. lia.
      + unfold entry_cells. cbn [cells_size csize Nat.add length]. exact (AV _ ltac:(left; reflexivity)).
    - revert XT. unfold EXTS. destruct (en_exts_o E) as [[K es]|] eqn:XO; intros XT; [| exact XT].
      destruct XT as (PP & SO & LEN & F2).
      assert (SUBX : forall b, In b (blocks_EXTS (en_exts E) (Some (K, es))) -> In b (blocks_ENTRY ee E)).
      { intros b Hb. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). rewrite XO. exact Hb. }
      rewrite blocks_EXTS_some in SUBX.
      split; [exact PP|]. split; [| split; [exact LEN|]].
      + eapply (SKobj_frameX H); [exact SO| exact XP| |].
        * exact (AV _ (SUBX _ ltac:(apply in_or_app; left; left; reflexivity))).
        * intros NC. exact (AV _ (SUBX _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))).
      + eapply (EXTs_frameX H); [exact F2| exact XP|]. intros b Hb. exact (AV _ (SUBX _ ltac:(apply in_or_app; right; exact Hb))).
  Qed.

  Lemma ENTRYs_frameX : forall L0 SP X m m' ps es,
    Forall2 (fun q E => ENTRYobj L0 m q E) ps es -> xpres H L0 SP X m m' ->
    (forall b, In b (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine ps es))) -> avoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun q E => ENTRYobj L0 m' q E) ps es.
  Proof.
    intros L0 SP X m m' ps es F2. induction F2 as [|q E ps' es' HE F IH]; intros XP K; [constructor|].
    cbn [concat map combine fst snd] in K. constructor.
    - eapply ENTRYobj_frameX; [exact HE| exact XP|]. intros b Hb. apply K. apply in_or_app. left. exact Hb.
    - apply IH; [exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.

  Lemma STOREobj_frameX : forall L0 SP X m m' a S', STOREobj L0 m a S' -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_STORE a S') -> avoids X (blk_addr b) (blk_size b)) -> STOREobj L0 m' a S'.
  Proof.
    intros L0 SP X m m' a S' (HC & HIN & ENS) XP K.
    pose proof (K _ ltac:(left; reflexivity)) as A0. cbn [blk_addr blk_size fst snd] in A0.
    unfold STOREobj. split.
    { eapply (xpres_rw_cells' H); [exact XP| exact HC| |].
      - right; right; left. exists (es_id S', a, STORE_SIZE). split; [exact HIN|]. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold STORE_SIZE. lia.
      - cbn [cells_size csize Nat.add]. eapply avoids_sub; [exact A0| lia| unfold STORE_SIZE; lia]. }
    split; [exact HIN|].
    revert ENS K. unfold ENTRIES, blocks_STORE. destruct (es_entries_o S') as [[K0 es]|]; intros ENS K; [| exact ENS].
    destruct ENS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply (SKobj_frameX H); [exact SO| exact XP| |].
      + exact (K _ ltac:(right; apply in_or_app; left; left; reflexivity)).
      + intros NC. exact (K _ ltac:(right; apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity)).
    - split; [exact LEN|]. eapply ENTRYs_frameX; [exact F2| exact XP|]. intros b Hb. apply K. right. apply in_or_app. right. exact Hb.
  Qed.

  Lemma STOREobj_LB_mono : forall LB LB' m a S', STOREobj LB m a S' -> (forall b, In b LB -> In b LB') -> STOREobj LB' m a S'.
  Proof.
    intros LB LB' m a S' (HC & HIN & ENS) SUB. split; [exact HC|]. split; [apply SUB; exact HIN|].
    revert ENS. unfold ENTRIES. destruct (es_entries_o S') as [[K es]|]; intros ENS; [| exact ENS].
    destruct ENS as (X1 & SO & LEN & F2). split; [exact X1|]. split; [eapply SKobj_LB_mono; [exact SO| exact SUB]|]. split; [exact LEN|].
    clear - F2 SUB. induction F2 as [|q E qs Es HE HF IH]; [apply Forall2_nil| apply Forall2_cons; [eapply ENTRYobj_LB_mono; [exact HE| exact SUB]| exact IH]].
  Qed.

  (* [comment removed for export] *)
  Lemma ENTRY_shad_frameX : forall LB L0 SP X m m' ee E,
    ENTRY_shad m ee E -> ENTRYobj LB m ee E -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_ENTRY ee E) -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> ENTRY_shad m' ee E.
  Proof.
    intros LB L0 SP X m m' ee E ESH EO XP AV. pose proof ESH as (ETOP & EAD & ES1 & ES2 & ES3 & ES4 & XSH). pose proof EO as (_ & _ & O1 & O2 & O3 & O4 & XT).
    assert (OSH : forall Pf o, ofield LB Pf o -> (forall b, In b (blocks_of Pf o) -> In b (blocks_ENTRY ee E)) -> oshad m Pf o -> oshad m' Pf o).
    { intros Pf o OFo INE OSo. eapply (oshad_xpresX H); [| exact OSo| exact XP]. destruct o as [[i1 n1]|]; [| exact I].
      pose proof (AV (i1, Pf, n1) (INE _ ltac:(left; reflexivity))) as (I1' & A1' & S1'). cbn [blk_addr blk_size fst snd] in A1', S1'. split; [exact I1'|]. split; [exact A1'| exact S1']. }
    pose proof (AV _ ltac:(left; reflexivity)) as (EIN' & AVE & SAVE). cbn [blk_addr blk_size fst snd] in AVE, SAVE.
    unfold ENTRY_shad. split; [exact ETOP|]. split; [eapply (addressable_xpres_blkX H); [exact EIN'| exact ETOP| exact EAD| exact XP| exact SAVE]|].
    split; [apply (OSH _ _ O1); [intros b Hb; right; apply in_or_app; left; exact Hb| exact ES1]|].
    split; [apply (OSH _ _ O2); [intros b Hb; right; apply in_or_app; right; apply in_or_app; left; exact Hb| exact ES2]|].
    split; [apply (OSH _ _ O3); [intros b Hb; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES3]|].
    split; [apply (OSH _ _ O4); [intros b Hb; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb| exact ES4]|].
    revert XSH XT. unfold EXTS_shad, EXTS. destruct (en_exts_o E) as [[K es]|] eqn:XO; intros XSH XT; [| exact I].
    destruct XSH as ((SKSH & T1 & T2) & F2SH). destruct XT as (PP & SO & LEN & F2).
    assert (SUBX : forall b, In b (blocks_SK (en_exts E) K ++ EBof K es) -> In b (blocks_ENTRY ee E)).
    { intros b Hb. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). rewrite XO, blocks_EXTS_some. exact Hb. }
    split.
    - split; [| split; [exact T1| exact T2]]. destruct SKSH as [SKH SKD]. split.
      + pose proof (AV _ (SUBX _ ltac:(apply in_or_app; left; left; reflexivity))) as (I1 & _ & S1). eapply (addressable_xpres_blkX H); [exact I1| exact T1| exact SKH| exact XP| exact S1].
      + intros NC. pose proof (AV _ (SUBX _ ltac:(apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity))) as (I1 & _ & S1).
        eapply (addressable_xpres_blkX H); [exact I1| exact (T2 NC)| exact (SKD NC)| exact XP| exact S1].
    - eapply (EXTs_shad_xpresX H); [exact F2SH| exact XP|]. intros b Hb. exact (AV _ (SUBX _ ltac:(apply in_or_app; right; exact Hb))).
  Qed.

  Lemma ENTRYs_shad_frameX : forall LB L0 SP X m m' ps es,
    Forall2 (fun q E => ENTRY_shad m q E) ps es -> Forall2 (fun q E => ENTRYobj LB m q E) ps es -> xpres H L0 SP X m m' ->
    (forall b, In b (concat (map (fun pe => blocks_ENTRY (fst pe) (snd pe)) (combine ps es))) -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
    Forall2 (fun q E => ENTRY_shad m' q E) ps es.
  Proof.
    intros LB L0 SP X m m' ps es F2. induction F2 as [|q E ps' es' HE F IH]; intros FO XP K; [constructor|].
    cbn [concat map combine fst snd] in K. inversion FO; subst. constructor.
    - eapply ENTRY_shad_frameX; [exact HE| eassumption| exact XP|]. intros b Hb. apply K. apply in_or_app. left. exact Hb.
    - apply IH; [assumption| exact XP|]. intros b Hb. apply K. apply in_or_app. right. exact Hb.
  Qed.

  Lemma STORE_shad_frameX : forall LB L0 SP X m m' a S', STORE_shad m a S' -> STOREobj LB m a S' -> xpres H L0 SP X m m' ->
    (forall b, In b (blocks_STORE a S') -> In b L0 /\ avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> STORE_shad m' a S'.
  Proof.
    intros LB L0 SP X m m' a S' (TOP & AD & ENS) (HC & HIN & EN) XP K.
    pose proof (K _ ltac:(left; reflexivity)) as (I0 & A0 & S0). cbn [blk_addr blk_size fst snd] in A0, S0.
    unfold STORE_shad. split; [exact TOP|]. split; [eapply (addressable_xpres_blkX H); [exact I0| exact TOP| exact AD| exact XP| exact S0]|].
    revert ENS EN K. unfold ENTRIES_shad, ENTRIES, blocks_STORE. destruct (es_entries_o S') as [[K0 es]|]; intros ENS EN K; [| exact I].
    destruct ENS as ((SKSH & T1 & T2) & F2SH). destruct EN as (PP & SO & LEN & F2). split.
    - split; [| split; [exact T1| exact T2]]. destruct SKSH as [SKH SKD]. split.
      + pose proof (K _ ltac:(right; apply in_or_app; left; left; reflexivity)) as (I1 & _ & S1). eapply (addressable_xpres_blkX H); [exact I1| exact T1| exact SKH| exact XP| exact S1].
      + intros NC. pose proof (K _ ltac:(right; apply in_or_app; left; unfold blocks_SK; rewrite (proj2 (Z.eqb_neq _ _) NC); right; left; reflexivity)) as (I1 & _ & S1).
        eapply (addressable_xpres_blkX H); [exact I1| exact (T2 NC)| exact (SKD NC)| exact XP| exact S1].
    - eapply ENTRYs_shad_frameX; [exact F2SH| exact F2| exact XP|]. intros b Hb. apply K. right. apply in_or_app. right. exact Hb.
  Qed.
End OBJX.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HX : asan_rt_hyps_x H.
  Hypothesis RAISE : araise_stmt H.
  Let HH : asan_rt_hyps H := proj1 HX.
  Let SM6 : stack_malloc_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 HX)))).
  Let SF6 : stack_free_6_stmt H := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))).
  Let SSF8 : set_shadow_f8_stmt := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HX))))))).
  Let PERM : rheap_perm H := HHx_rheap_perm H HX.

  (* [comment removed for export] *)
  Variables (PF9new : ctxphase -> list (Z * list Z)) (PF9free : list (Z * list Z)).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LIB LB : list block) (LF : list fframe)
            (M : libmid) (x : ctxinfo) (st mb lo B : Z) (S : storerep) (R : membio) (ds : list byte) (errv : word) (CH : list (Z * Z)).
  Hypotheses (VIS0 : as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                         F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs))
             (A0 : a0 = Z_to_bv 64 st) (A1 : a1 = Z_to_bv 64 mb)
             (SO : STOREobj LB m st S) (SE : es_entries S = 0) (SEO : es_entries_o S = None) (STL : st + STORE_SIZE <= lo) (SSH : STORE_shad m st S)
             (MBO : MEMBIO H LB m mb R) (MP0 : mb_pos R = 0) (MN0 : mb_nread R = 0) (MBB : MEMBIO_below mb R lo) (MBS : MEMBIO_sep mb R)
             (MSH : MEMBIO_shad m mb R) (PAY : PAYLOAD_shad m R)
             (DS : bytes_at asegs m (mb_buf R) ds) (DSL : zlength ds = mb_len R)
             (PAYL : 1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD)
             (PAYL2 : 1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S)
             (NDsm : List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R)))
             (LM : LIBMID LIB m M) (SUBL : forall b, In b LIB -> In b LB) (CTX : mid_ctx M = CtxReady x) (MF1 : mid_flag M = 1)
             (DJ6 : forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b')
             (HP : as_RHEAP H s (mid_errblocks M ++ LB) m) (KREL : as_AKREL H s (mkCfg msF mo))
             (BUD : lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H)
             (BUDC : Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H)
             (AUX : as_rauxv_ok H m B) (SPB : bv_unsigned sp <= B) (BHI : B < 2^64) (SPA : bv_unsigned sp mod 16 = 0)
             (ST : stk asegs m lo (bv_unsigned sp)) (CEIL : aceil <= lo) (LO : lo <= bv_unsigned sp - READCFG_STACK M) (ST0 : stack0 m lo (bv_unsigned sp))
             (ERR : rw_cells asegs m (errno_addr tp) [C4 errv]) (MI : mem_inv asegs m) (TP : tp = Z_to_bv 64 ATP) (AC : ACONST m)
             (MCO : mid_closed_ok H M)
             (RFS : as_RFS H LF m) (LFB : (length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) (ATH : athr_cells m)
             (CHN : as_chain H m (bv_unsigned s0) CH) (CHB : forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp')
             (PF : pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) (ALW : READCFG_COST H M <= as_AL H s)
             (RAE : bv_unsigned ra mod 2 = 0).

  (* [comment removed for export] *)
  Local Notation L0c := (L0 LB M).
  Local Notation S1c := (S1 sp).
  Local Notation KGc := (KG sp).
  Local Notation POSTc := (POST H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds).
  Local Notation XFc := (XF M st mb R).
  Local Notation SAVESc := (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Local Notation CH1c := (CH1 ra sp CH).
  Local Notation LF1c := (LF1 LF).
  Local Notation XSFc := (XSF H).
  Local Notation LEDGERc := (LEDGER H s).
  Local Notation pf_sitec := (pf_site H PF9new PF9free ra sp M CH PF).
  Local Notation rp_okKc := (rp_okK H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH).
  (* [comment removed for export] *)
  Local Notation "'RCI' f" := (f H HX RAISE PF9new PF9free ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LIB LB LF M x st mb lo B S R ds errv CH
                                 VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE)
    (at level 10, f at level 0).

  (* [comment removed for export] *)
  Local Notation AFWc := (AFW H ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m s LIB LB LF M st mb lo B R ds CH).

  (* [comment removed for export] *)
  Variables (p : bptr) (A nA : Z) (pbin : bptr) (Bb nB : Z) (bs : list byte) (R' : membio) (bt : Z) (TB : list block).
  Variable BT : mem -> Prop.
  Variables (ff fp n : Z) (fj24 tpb fj128 fj2 jz jg e5 : list byte) (w224 : word).
  Hypotheses (NAR : 1 <= mb_len R <= nA /\ nA <= 512 * 3)                 (* [comment removed for export] *)
             (NBR : 0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN)
             (MST : mb_static R R') (POS : mb_pos R' = mb_len R)
             (BTR : 0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072)
             (BT_frame : forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem),
                 BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP ->
                 (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) ->
                 mem_inv asegs m2 -> BT m2)
             (FRESH : fresh_frame H LF 6 ff fp).
  (* [comment removed for export] *)
  Hypothesis AUXV : aauxv_ok m B.
  Local Notation SH := (Z.shiftr ff 3 + ASHB).

  (* [comment removed for export] *)
  Definition drest (Lx NB LE : list block) : list block := Lx ++ NB ++ TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB.
  (* [comment removed for export] *)
  Definition dnb (NB : list block) : Prop := Z.of_nat (length NB) <= DECODE_CNT /\ lb_bytes NB <= DECODE_BYTES.
  (* [comment removed for export] *)
  Definition dsg2 (wee v192 v200 v208 v224 v232 : word) : list cell :=
    arp_sg2 (wz (SH + 10)) (wz ff) (wz ff) wee (wz ASHB) (wz A) v192 v200 v208 (wz ff) v224 v232.
  (* [comment removed for export] *)
  Definition dff (tpl : Z) (lb : byte) : list cell := arp_fframe2 S1c tpl fj24 lb tpb fj128 n fj2 fp.
  (* [comment removed for export] *)
  Definition dfsh (shb b2 : byte) (shd : list byte) : list cell :=
    arp_fshadow (poison_bytes 4 0xf1) shb (poison_bytes 3 0xf2) b2 (b8 0xf2) shd (poison_bytes 16 0xf2) (b8 0xf8) e5.

  (* [comment removed for export] *)
  Definition adwkG (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr1 : list cell) (wee v192 v200 v208 v224 v232 : word) (fr3 : list cell)
      (tpl : Z) (shb b2 : byte) (shd : list byte) (um uf : Z) (m' : mem) (s' : as_St H) : Prop :=
       as_RHEAP H s' (mid_errblocks M' ++ drest Lx NB LE) m'
    (* [comment removed for export] *)
    /\ LIBMID (LE ++ LIB) m' M' /\ mid_step M M' /\ mid_newlib_ok M M' LE /\ mid_ctx M' = mid_ctx M
    /\ Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT /\ lb_bytes (mid_errblocks M') <= ERRSTR_BYTES
    /\ Z.of_nat (length LE) + errph_cnt (mid_err M') <= errph_cnt (mid_err M)
    /\ lb_bytes LE + errph_bytes (mid_err M') <= errph_bytes (mid_err M)
    (* [comment removed for export] *)
    /\ STOREobj (NB ++ LE ++ LB) m' st S' /\ STORE_shad m' st S' /\ es_id S' = es_id S /\ Permutation (blocks_STORE st S') ((es_id S, st, STORE_SIZE) :: NB)
    /\ List.NoDup (map blk_id (blocks_STORE st S'))
    /\ (forall K es, es_entries_o S' = Some (K, es) -> sk_comp K = 0 /\ sk_cap K <= 2 * Z.of_nat (length (sk_elems K)) + 4)
    (* [comment removed for export] *)
    /\ MEMBIO H LB m' mb R' /\ MEMBIO_shad m' mb R' /\ bytes_at asegs m' (mb_buf R) ds
    /\ bytes_at asegs m' Bb bs
    /\ (exists junk, rw_cells asegs m' Bb [CB (length bs) bs; CB (Z.to_nat nB - length bs) junk]) /\ addressable m' Bb nB
    /\ (exists junk, rw_cells asegs m' A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) junk]) /\ addressable m' A nA
    /\ BT m'
    (* [comment removed for export] *)
    /\ rw_cells asegs m' S1c [CB 16 jz] /\ rw_cells asegs m' (S1c + 16) fr1 /\ cells_size fr1 = 128%nat
    /\ rw_cells asegs m' (S1c + 144) (dsg2 wee v192 v200 v208 v224 v232) /\ rw_cells asegs m' (S1c + 240) fr3 /\ cells_size fr3 = 104%nat
    /\ rw_cells asegs m' (S1c + 344) [CB (Z.to_nat KGc) jg] /\ rw_cells asegs m' (bv_unsigned sp + -104) SAVESc
    (* [comment removed for export] *)
    /\ (exists lb, rw_cells asegs m' ff (dff tpl lb)) /\ rw_cells asegs m' SH (dfsh shb b2 shd) /\ length shd = 256%nat /\ as_RFS H (LF1c ff fp) m'
    (* [comment removed for export] *)
    /\ (exists errv', rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'])
    /\ as_rauxv_ok H m' B /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo S1c /\ stack0 m' lo (bv_unsigned sp)
    /\ as_chain H m' (bv_unsigned sp) CH1c
    /\ (exists XSq, Forall (fs_scratch H LF) XSq /\ (forall q, rin_ivs (XSFc ff fp) q -> rin_ivs XSq q) /\ xpres H LB (bv_unsigned sp) (XSq ++ XFc) m m')
    /\ LEDGERc s' um uf.

  (* [comment removed for export] *)
  Definition dsg1 (w16 w32 w40 w48 : word) : list cell :=
    arp_sg1 w16 (wz AR_INTERNAL_ERROR) w32 w40 w48 (wz 0) (wz AECH_VERSION) (wz ARP_FILE) (wz bt) (wz Bb) (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32)).
  (* [comment removed for export] *)
  Definition adwk (Lx NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (wee v192 v200 v208 v224 v232 : word)
      (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl : Z) (um uf : Z) (m' : mem) (s' : as_St H) : Prop :=
    adwkG Lx NB S' M' LE (dsg1 w16 w32 w40 w48) wee v192 v200 v208 v224 v232 (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s'.

  (* [comment removed for export] *)
  Definition dbud (Lr : list block) (M' : libmid) (hb hc : Z) : Prop :=
       lb_bytes Lr + errph_bytes (mid_err M') + ERRSTR_BYTES + hb <= as_LIVE_MAX H
    /\ Z.of_nat (length Lr) + errph_cnt (mid_err M') + ERRSTR_CNT + hc <= as_LIVE_CNT_MAX H.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dK_tailA (NB : list block) (S' : storerep) : Prop :=
    forall (Lx : list block) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl um uf : Z) (shb shb2 : byte) (shd : list byte)
           (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee line : Z) (E : entrep)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      adwkG Lx NB S' M' LE (dsg1 w16 w32 w40 w48) (wz ee) v192 v200 v208 v224 v232 (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl shb shb2 shd um uf m' s' ->   (* [comment removed for export] *)
      ENTRYobj (drest Lx NB LE) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx -> 0 <= line < 2^31 ->
      dbud (drest Lx NB LE) M' (4 * ERRDEBUG_BYTES) 8 ->
      um + errph_bytes (mid_err M') + 4 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + 4 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->   (* [comment removed for export] *)
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  s2w (Z_to_bv 64 SH) (Z_to_bv 64 line) s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_TA) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition dK_tailZ (NB : list block) (S' : storerep) : Prop :=
    forall (Lx : list block) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl um uf : Z) (shb shb2 : byte) (shd : list byte)
           (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (E : entrep)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s2w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word),
      adwkG Lx NB S' M' LE (dsg1 w16 w32 w40 w48) (wz ee) v192 v200 v208 v224 v232 (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl shb shb2 shd um uf m' s' ->   (* [comment removed for export] *)
      ENTRYobj (drest Lx NB LE) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      dbud (drest Lx NB LE) M' (4 * ERRDEBUG_BYTES) 8 ->
      um + errph_bytes (mid_err M') + 4 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + 4 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->   (* [comment removed for export] *)
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  s2w (Z_to_bv 64 SH) s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_TZ) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition dK_tailX (NB : list block) (S' : storerep) : Prop :=
    forall (Lx NB2 : list block) (S2 : storerep) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word)
           (tpl um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (ee : Z) (E : entrep)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w u3 u4 u5 u6 : word),
      adwk Lx NB2 S2 M' LE w16 w32 w40 w48 (wz ee) v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      EBS S2 = EBS S' /\ nent S2 = nent S' /\ Z.of_nat (length (SKB st S2)) <= 2 /\ lb_bytes (SKB st S2) <= 88 + 16 * nent S' ->
      ENTRYobj (drest Lx NB2 LE) m' ee E -> ENTRY_shad m' ee E -> Permutation (blocks_ENTRY ee E) Lx ->
      dbud (drest Lx NB2 LE) M' (2 * ERRDEBUG_BYTES) 4 ->
      um + errph_bytes (mid_err M') + 2 * ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + lb_bytes Lx + 2 * ERRDEBUG_BYTES + 8192 <= DECODE_CUM_BYTES ->   (* [comment removed for export] *)
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 A) (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 Bb) (Z_to_bv 64 ff) (Z_to_bv 64 ee) (Z_to_bv 64 ff) (Z_to_bv 64 bt) u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_TX) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition dK_adv (cur rem : Z) (NB : list block) (S' : storerep) (um0 uf0 : Z) (ph0 : errphase) : Prop :=
    forall (NB2 NBe : list block) (S2 : storerep) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (wee v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word)
           (tpl um uf elen : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (rax u0 u1 u2 a0w b1 b2 b3 b4 b5 b6 b7 s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      adwk [] NB2 S2 M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      19 <= elen -> 4 + elen <= rem ->
      um <= um0 + ENTRY_CM elen + (errph_bytes ph0 - errph_bytes (mid_err M')) -> uf <= uf0 + ENTRY_CF elen + (errph_bytes ph0 - errph_bytes (mid_err M')) ->
      EBS S2 = EBS S' ++ NBe /\ nent S2 = nent S' + 1 /\ Z.of_nat (length (SKB st S2)) <= 2 /\ lb_bytes (SKB st S2) <= 88 + 16 * nent S2 ->
      5 * Z.of_nat (length NBe) <= 2 * (elen + 4) -> lb_bytes NBe <= ENTRY_KEPT elen ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 2) (Z_to_bv 64 SH) (Z_to_bv 64 (cur + 4 + elen)) s5w s6w (Z_to_bv 64 (rem - 4)) s8w s9w (Z_to_bv 64 elen) s11w u3 u4 u5 u6)   (* [comment removed for export] *)
                          F (Z_to_bv 64 ADF_ADV) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition dK_skip (cur rem : Z) (NB : list block) (S' : storerep) (um0 uf0 : Z) (ph0 : errphase) : Prop :=
    forall (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (wee v192 v200 v208 v224 v232 : word) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word)
           (tpl um uf elen : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5w s6w s8w s9w s11w u3 u4 u5 u6 : word),
      adwk [] NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      0 <= elen -> 4 + elen <= rem ->
      um <= um0 + ENTRY_CM elen + (errph_bytes ph0 - errph_bytes (mid_err M')) -> uf <= uf0 + ENTRY_CF elen + (errph_bytes ph0 - errph_bytes (mid_err M')) ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 2) (Z_to_bv 64 SH) (Z_to_bv 64 (cur + 4 + elen)) s5w s6w (Z_to_bv 64 (rem - 4)) s8w s9w (Z_to_bv 64 elen) s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_ADV) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition rp_entry_stmt : Prop :=
    forall (cur rem : Z) (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (w16 w32 w40 w48 : word) (wee v192 v200 v208 v224 v232 : word)
           (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word) (tpl um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (rax u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s4w s5w s6w s9w s10w s11w u3 u4 u5 u6 : word),
      adwk [] NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s' ->
      Bb + 2 <= cur -> 1 <= rem -> cur + rem <= Bb + zlength bs ->
      dbud (drest [] NB LE) M' (ENTRY_BYTES rem) (ENTRY_CNT rem) ->
      um + errph_bytes (mid_err M') + ENTRY_CM rem <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + ENTRY_CF rem <= DECODE_CUM_BYTES -> nent S' <= 65 ->
      dK_adv cur rem NB S' um uf (mid_err M') -> dK_skip cur rem NB S' um uf (mid_err M') -> dK_tailA NB S' -> dK_tailZ NB S' -> dK_tailX NB S' ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7
                                  (Z_to_bv 64 2) (Z_to_bv 64 SH) s4w s5w s6w (Z_to_bv 64 rem) (Z_to_bv 64 cur) s9w s10w s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 ADF_HEAD) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  Local Ltac img_static := unfold A_malloc_impl, A_realloc_impl, A_free_impl, A_got_CRYPTO_malloc, A_mem_buf_method, O_METH_BREAD, A_mem_inited; cbn; lia.

  (* [comment removed for export] *)
  Lemma rc_facts_c :
       S = store_empty (es_id S) /\ In (es_id S, st, STORE_SIZE) L0c /\ ablock_range H st STORE_SIZE
    /\ (forall b, In b L0c -> ablock_range H (blk_addr b) (blk_size b)) /\ (forall b, In b LB -> In b L0c)
    /\ List.NoDup (map blk_id L0c) /\ 9152 <= READCFG_STACK M /\ 0 <= lo /\ MEMFLAG m 1
    /\ (forall b', In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> In b' L0c)
    /\ (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) ->
          blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ afsb_ok H /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
    /\ rp_s1 (bv_unsigned sp) mod 32 = 0 /\ bv_unsigned sp - 464 <= rp_s1 (bv_unsigned sp) <= bv_unsigned sp - 448 /\ bv_unsigned sp < 2^64.
  Proof. exact (RCI rc_facts). Qed.

  Lemma adwk_G : forall Lx NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s',
    adwk Lx NB S' M' LE w16 w32 w40 w48 wee v192 v200 v208 v224 v232 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 tpl um uf m' s'
    = adwkG Lx NB S' M' LE (dsg1 w16 w32 w40 w48) wee v192 v200 v208 v224 v232 (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s'.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma drest_app : forall Lx NB LE, drest Lx NB LE = Lx ++ drest [] NB LE.
  Proof. clear. intros. reflexivity. Qed.
  Lemma drest_sub : forall Lx NB LE,
       (forall b, In b LB -> In b (drest Lx NB LE)) /\ (forall b, In b (drest [] NB LE) -> In b (drest Lx NB LE))
    /\ (forall b, In b LE -> In b (drest Lx NB LE)) /\ (forall b, In b NB -> In b (drest Lx NB LE)) /\ (forall b, In b TB -> In b (drest Lx NB LE))
    /\ In (pbin, Bb, nB) (drest Lx NB LE) /\ In (p, A, nA) (drest Lx NB LE) /\ (forall b, In b Lx -> In b (drest Lx NB LE))
    /\ (forall b, In b (NB ++ LE ++ LB) -> In b (drest [] NB LE)) /\ (forall b, In b (LE ++ LIB) -> In b (drest [] NB LE)).
  Proof using SUBL.
    clear - SUBL. intros Lx NB LE. unfold drest.
    repeat split; try (intros b0 Hb0; pose proof (SUBL b0) as SB0);
      rewrite ?in_app_iff in *; cbn [In] in *; rewrite ?in_app_iff in *; cbn [In] in *; tauto.
  Qed.

  Lemma adwkG_heap_facts : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s',
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s' ->
       (forall b, In b (mid_errblocks M' ++ drest Lx NB LE) -> ablock_range H (blk_addr b) (blk_size b))
    /\ List.NoDup (map blk_id (mid_errblocks M' ++ drest Lx NB LE))
    /\ (forall b b', In b (mid_errblocks M' ++ drest Lx NB LE) -> In b' (mid_errblocks M' ++ drest Lx NB LE) -> blk_id b <> blk_id b' ->
           blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b)
    /\ idsdisj Lx (drest [] NB LE) /\ idsdisj (mid_errblocks M') (drest Lx NB LE).
  Proof using HX.
    intros until s'. intros DW. pose proof DW as (HP' & _).
    pose proof (ah_nodup H HH _ _ _ HP') as ND.
    split; [intros b Hb; exact (ah_blocks H HH _ _ _ _ HP' Hb)|]. split; [exact ND|].
    split; [intros b b' Hb Hb' NE; exact (ah_disj H HH _ _ _ _ _ HP' Hb Hb' NE)|].
    destruct (nd_app _ _ ND) as [D1 ND1]. rewrite drest_app in ND1. destruct (nd_app _ _ ND1) as [D2 _]. split; [exact D2| exact D1].
  Qed.

  (* [comment removed for export] *)
  Lemma drest_ids : forall E' Lx NB LE, List.NoDup (map blk_id (E' ++ drest Lx NB LE)) ->
       idsdisj E' (drest Lx NB LE) /\ idsdisj Lx (drest [] NB LE) /\ idsdisj NB (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)
    /\ idsdisj TB ((pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) /\ idsdisj [(pbin, Bb, nB)] ((p, A, nA) :: LE ++ LB) /\ idsdisj [(p, A, nA)] (LE ++ LB) /\ idsdisj LE LB.
  Proof.
    clear. intros E' Lx NB LE ND. unfold drest in ND.
    destruct (nd_app _ _ ND) as [D0 ND0]. destruct (nd_app _ _ ND0) as [D1 ND1]. destruct (nd_app _ _ ND1) as [D2 ND2]. destruct (nd_app _ _ ND2) as [D3 ND3].
    destruct (nd_app [(pbin, Bb, nB)] _ ND3) as [D4 ND4]. destruct (nd_app [(p, A, nA)] _ ND4) as [D5 ND5]. destruct (nd_app _ _ ND5) as [D6 _].
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma mb_blocks_LB' : forall b, In b (blocks_MEMBIO mb R') -> In b LB.
  Proof using MBO MST.
    intros b Hb. rewrite (mb_static_blocks mb R R' MST) in Hb.
    destruct MBO as (_ & _ & _ & _ & I1 & I2 & I3 & I4 & _). unfold blocks_MEMBIO in Hb. destruct Hb as [<-|[<-|[<-|[<-|[]]]]]; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma adwkG_es : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s' c,
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s' -> mid_err M' = ErrReady c -> In (ec_es c) (LE ++ LIB) /\ blk_size (ec_es c) = ERRST_SIZE.
  Proof using CTX.
    intros until c. intros DW EQ. pose proof DW as (_ & LM1 & _ & _ & CTX1 & _).
    destruct LM1 as (_ & _ & _ & EPm & _). rewrite CTX1, CTX, EQ in EPm. cbn [ERRPH_mid ERRPH] in EPm. destruct EPm as [_ CH0].
    pose proof CH0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I5 & Z5 & _). split; [exact I5| exact Z5].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dwin (Lx : list block) (iv : Z * Z) : Prop :=
       (lo <= fst iv /\ snd iv <= S1c) \/ (S1c + 16 <= fst iv /\ snd iv <= S1c + 240) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 344)
    \/ (ff + 32 <= fst iv /\ snd iv <= ff + 40) \/ (SH + 4 <= fst iv /\ snd iv <= SH + 5) \/ (SH + 8 <= fst iv /\ snd iv <= SH + 266) \/ (ff + 64 <= fst iv /\ snd iv <= ff + 65)
    \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

  Lemma adwkG_w : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' m2 W (fr1' : list cell) (wee' v192' v200' v208' v224' v232' : word) (fr3' : list cell) (tpl' : Z) (lb' shb' b2' : byte) (shd' : list byte),
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' ->
    munch W m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 -> stk asegs m2 lo S1c -> Forall (dwin Lx) W ->
    rw_cells asegs m2 (S1c + 16) fr1' -> cells_size fr1' = 128%nat -> rw_cells asegs m2 (S1c + 144) (dsg2 wee' v192' v200' v208' v224' v232') ->
    rw_cells asegs m2 (S1c + 240) fr3' -> cells_size fr3' = 104%nat ->
    rw_cells asegs m2 ff (dff tpl' lb') -> rw_cells asegs m2 SH (dfsh shb' b2' shd') -> length shd' = 256%nat ->
    adwkG Lx NB S' M' LE fr1' wee' v192' v200' v208' v224' v232' fr3' tpl' shb' b2' shd' um uf m2 s1'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until shd'. intros DW MU WM MI2 STK2 FW0 FR1' SZ1' FR2' FR3' SZ3' FF' FSH' LSH'.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_mono (ff + 4096) _ FQ6) as SYU. pose proof (sh_mono _ _ AF2) as SYA.
    pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1. rewrite S0 in W1.
    pose proof (aapp_not_shadowland _ _ AF4) as NSF.
    assert (ERNG : 0 <= errno_addr (Z_to_bv 64 ATP) <= 0xc04000 - 4) by (clear; vm_compute; split; discriminate).
    destruct (adwkG_heap_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & ND & DISJ & D2 & D1).
    pose proof (drest_sub Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    set (Lall := mid_errblocks M' ++ drest Lx NB LE) in *.
    assert (INX : forall b, In b Lx -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SLX; exact Hb).
    assert (IN0 : forall b, In b (drest [] NB LE) -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SL0; exact Hb).
    (* [comment removed for export] *)
    assert (FWc : forall iv, dwin Lx iv -> fswin H iv \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)).
    { intros iv [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; [left; left| left; left| left; left| left; right; left| left; right; right| left; right; right| left; right; left| right; exact K];
        unfold AFS_SIZE; rewrite ?SHF in K; [clear - K CEIL; lia| clear - K AS1; lia| clear - K AS1; lia| clear - K FQ5 FQ6; lia| clear - K SYL SYU SY8; lia| clear - K SYL SYU SY8; lia| clear - K FQ5 FQ6; lia]. }
    assert (CW : Forall (aclient_write_ok H Lall) W).
    { eapply Forall_impl; [| exact FW0]. cbn beta. intros iv Hiv. destruct (FWc iv Hiv) as [K|(b & Hb & K1 & K2)]; [apply fswin_cw; exact K|].
      right; right; left. exists b. split; [exact (INX _ Hb)| split; [exact K1| exact K2]]. }
    (* [comment removed for export] *)
    assert (LOWa : forall Aq nq, aapp Aq nq -> Aq + nq <= aceil -> (Aq + nq + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= Aq - 16) ->
                   (forall b, In b Lx -> Aq + nq <= blk_addr b \/ blk_addr b + blk_size b <= Aq) -> avoids W Aq nq).
    { intros Aq nq AP AQ AF AB. unfold avoids. eapply Forall_impl; [| exact FW0]. cbn beta. pose proof (aapp_not_shadowland _ _ AP) as NS.
      intros iv Hiv. destruct (FWc iv Hiv) as [[K|[[K1 K2]|[K1 K2]]]|(b & Hb & K1 & K2)].
      - left. clear - K AQ. lia.
      - clear - K1 K2 AF. unfold AFS_SIZE in *. lia.
      - clear - K1 K2 NS W1 W3 SYA. unfold ALOWSH_LO, AHI_LO, AFS_SIZE in *. lia.
      - pose proof (AB b Hb). clear - H0 K1 K2. lia. }
    assert (LOWq : forall Aq nq, aapp Aq nq -> Aq + nq <= aceil -> (Aq + nq + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= Aq - 16) ->
                   (forall b, In b Lx -> Aq + nq <= blk_addr b \/ blk_addr b + blk_size b <= Aq) -> disjoint_from W Aq nq).
    { intros Aq nq AP AQ AF AB. apply djF. exact (LOWa Aq nq AP AQ AF AB). }
    assert (BWa : forall b Aq nq, In b (drest [] NB LE) -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> avoids W Aq nq).
    { intros b Aq nq Hb HA HB N0. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      eapply avoids_sub; [| exact HA| exact HB]. apply LOWa; [exact E7| exact E5| exact E6|].
      intros b' Hb'. pose proof (DISJ b b' (IN0 _ Hb) (INX _ Hb') ltac:(intros EQ; exact (D2 _ _ Hb' Hb (eq_sym EQ)))). clear - H0. lia. }
    assert (BWq : forall b Aq nq, In b (drest [] NB LE) -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> disjoint_from W Aq nq /\ Forall (winX Aq nq) W).
    { intros b Aq nq Hb HA HB N0. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      assert (ABx : forall b', In b' Lx -> blk_addr b + blk_size b + 16 <= blk_addr b' \/ blk_addr b' + blk_size b' + 16 <= blk_addr b).
      { intros b' Hb'. apply (DISJ b b' (IN0 _ Hb) (INX _ Hb')). intros EQ. exact (D2 _ _ Hb' Hb (eq_sym EQ)). }
      split.
      - apply (ECH_AKit.disjoint_from_sub W (blk_addr b) (blk_size b)); [| exact HA| exact HB| exact N0]. apply LOWq; [exact E7| exact E5| exact E6|].
        intros b' Hb'. pose proof (ABx b' Hb'). clear - H0. lia.
      - eapply Forall_impl; [| exact FW0]. cbn beta. pose proof (aapp_not_shadowland _ _ E7) as NS.
        intros iv Hiv. destruct (FWc iv Hiv) as [[K|[[K1 K2]|[K1 K2]]]|(b' & Hb' & K1 & K2)]; unfold winX.
        + right; left. unfold AHI_LO. clear - K ACB. lia.
        + unfold ALOWSH_LO, AHI_LO, AFS_SIZE in *. clear - K1 K2 NSF. rewrite ?ASHADOW_BASE_val. lia.
        + right; right. unfold AFS_SIZE in *. unfold nsh, sh in *. clear - K1 K2 E2 E6 HA HB N0. Z.div_mod_to_equations. lia.
        + (* [comment removed for export] *) pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'.
          unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' NS. rewrite ?ASHADOW_BASE_val in *. unfold sh, nsh. rewrite ?ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    assert (XP : xpres H (drest [] NB LE) (bv_unsigned sp) W m1 m2).
    { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa. }
    assert (XP0 : xpres H (drest [] NB LE) (bv_unsigned sp) [(ff + 32, ff + 40); (SH + 4, SH + 5); (SH + 8, SH + 266); (ff + 64, ff + 65)] m1 m2).
    { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [Ca HXa]. apply outside_of_not_rin. intros RW. destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra).
      pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]].
      - eapply ((RCI client_not_frame) _ _ _ _ _ HP1 (fun b Hb => IN0 b Hb) Ca). clear - K Ra Q2. first [lia | match goal with |- ?G => idtac "CNF" G end; repeat match goal with Hh : ?T |- _ => idtac Hh ":" T; revert Hh end; fail].
      - eapply ((RCI client_not_frame) _ _ _ _ _ HP1 (fun b Hb => IN0 b Hb) Ca). clear - K Ra Q2 LO STK0. lia.
      - eapply ((RCI client_not_frame) _ _ _ _ _ HP1 (fun b Hb => IN0 b Hb) Ca). clear - K Ra Q2 LO STK0. lia.
      - apply HXa. cbn. left. clear - K Ra. lia.
      - apply HXa. cbn. right; left. clear - K Ra. lia.
      - apply HXa. cbn. right; right; left. clear - K Ra. lia.
      - apply HXa. cbn. right; right; right; left. clear - K Ra. lia.
      - pose proof (client_outside_block H HH s1' Lall m1 b (drest [] NB LE) (bv_unsigned sp) a HP1 (INX _ Hb) IN0
                      ltac:(intros c c' Hc Hc' E; destruct Hc as [<-|[]]; exact (D2 _ _ Hb Hc' E)) ltac:(clear - AS1 Q2; lia) Ca) as OB.
        clear - OB K1 K2 Ra. lia. }
    (* [comment removed for export] *)
    assert (DJS : forall Aq nq, aceil <= Aq -> ((S1c <= Aq /\ Aq + nq <= S1c + 16) \/ S1c + 344 <= Aq) -> disjoint_from W Aq nq).
    { intros Aq nq HA HB. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta.
      assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= aceil) by (intros b Hb; pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _); exact E5).
      intros iv [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]]; [clear - K HA HB AS1; lia| clear - K HB; lia| clear - K HB; lia| clear - K HA FQ6 FB2; lia
        | rewrite SHF in K; clear - K HA SYU SY8 SYA SHC; lia| rewrite SHF in K; clear - K HA SYU SY8 SYA SHC; lia| clear - K HA FQ6 FB2; lia| pose proof (HBL b Hb); clear - H0 K1 K2 HA; lia]. }
    unfold adwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - eapply (ah_RHEAP_frame H HH); [exact HP1| exact MU| exact WM| exact CW].
    - (* [comment removed for export] *)
      assert (XPall : xpres H Lall (bv_unsigned sp) W m1 m2).
      { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [_ HXa]. apply outside_of_not_rin. exact HXa. }
      eapply (LIBMID_xobj H HH s1' m1 (LE ++ LIB) Lall (bv_unsigned sp) W [(lo, bv_unsigned sp); (ff, ff + 4096); (sh ff, sh ff + 512)] Lx m1 m2 M' x);
        [exact HP1| exact LM1| rewrite CTX1; exact CTX| exact XPall| | | exact INX| | |].
      + intros b Hb. apply IN0. apply SLL0. exact Hb.
      + intros b Hb. subst Lall. apply in_or_app. left. exact Hb.
      + intros b b' Hb Hb' EQ. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        * exact (D2 _ _ Hb' (SLL0 _ Hb) (eq_sym EQ)).
        * exact (D1 _ _ Hb (SLX _ Hb') EQ).
      + apply Forall_cons; [left; cbn [fst]; exact CEIL|]. apply Forall_cons; [right; left; cbn [fst snd]; unfold AFS_SIZE; clear - FQ5 FQ6; lia|].
        apply Forall_cons; [right; right; cbn [fst snd]; unfold AFS_SIZE; clear - SYL SYU SY8; lia| apply Forall_nil].
      + intros a Ra. destruct (rin_ivs_In _ _ Ra) as (iv & Hiv & Riv). pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K.
        destruct K as [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]].
        1-3: right; cbn; left; clear - K Riv Q2 LO STK0; lia.
        * right; cbn; right; left; clear - K Riv; lia.
        * right; cbn; right; right; left; rewrite SHF in K; clear - K Riv; lia.
        * right; cbn; right; right; left; rewrite SHF in K; clear - K Riv; lia.
        * right; cbn; right; left; clear - K Riv; lia.
        * left. exists b. split; [exact Hb| clear - K1 K2 Riv; lia].
    - (* [comment removed for export] *)
      eapply (STOREobj_frameX H); [exact SO1| eapply (xpres_weaken H); [exact XP| apply Z.le_refl| exact S30| intros q Hq; exact Hq]|].
      intros b Hb. pose proof (STOREobj_owned_law _ _ _ _ SO1 b Hb) as HbN. exact (BWa b _ _ (S30 _ HbN) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b (IN0 _ (S30 _ HbN))) as (_ & _ & E3 & _); exact E3)).
    - (* [comment removed for export] *)
      eapply (STORE_shad_frameX H (NB ++ LE ++ LB) (drest [] NB LE)); [exact SSH1| exact SO1| eapply (xpres_weaken H); [exact XP| apply Z.le_refl| intros q Hq; exact Hq| intros q Hq; exact Hq]|].
      intros b Hb. pose proof (STOREobj_owned_law _ _ _ _ SO1 b Hb) as HbN. pose proof (BRS b (IN0 _ (S30 _ HbN))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      split; [exact (S30 _ HbN)|]. split; [exact (BWa b _ _ (S30 _ HbN) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3)|].
      unfold shavoids. eapply Forall_impl; [| exact (proj2 (BWq b _ _ (S30 _ HbN) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3))]. cbn beta.
      pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(clear - E1; lia) E3 ltac:(unfold AAPP_HI; clear - E5 ACB; lia)) as SNH.
      assert (SB0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; clear - E1; Z.div_mod_to_equations; lia).
      intros iv [K|[K|[K|K]]]; [right; clear - K SB0; lia| left; clear - K SNH; lia| left; exact K| right; exact K].
    - (* [comment removed for export] *)
      eapply (AMEMBIO_munch H LB W m1 m2); [exact MBO1| exact MU| exact WM|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros b Hb. cbn beta.
      exact (djF_inv _ _ _ _ (proj1 (BWq b _ _ (SLB0 _ (mb_blocks_LB' _ Hb)) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) ltac:(pose proof (BRS b (IN0 _ (SLB0 _ (mb_blocks_LB' _ Hb)))) as (_ & _ & E3 & _); exact E3))) Hiv).
    - (* [comment removed for export] *)
      destruct MSH1 as (X1 & X2 & X3 & X4). pose proof MBO1 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      assert (TA : forall b Aq nq, In b (drest [] NB LE) -> blk_addr b <= Aq -> Aq + nq <= blk_addr b + blk_size b -> 0 <= nq -> addressable m1 Aq nq -> addressable m2 Aq nq).
      { intros b Aq nq Hb HA HB N0 AD. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
        eapply addressable_acrossX; [exact AD| exact MU| exact WM| clear - E1 HA; lia| unfold AAPP_HI; clear - E5 HB ACB; lia| exact (proj2 (BWq b Aq nq Hb HA HB N0))]. }
      unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      split; [| split; [| split]].
      + eapply (TA (mb_id R', mb, 128)); [apply SLB0; exact J1| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X1].
      + eapply (TA (mb_bbid R', mb_bb R', 16)); [apply SLB0; exact J2| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X2].
      + eapply (TA (mb_bmid R', mb_bm R', 32)); [apply SLB0; exact J3| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X3].
      + eapply (TA (mb_rpid R', mb_rp R', 32)); [apply SLB0; exact J4| apply Z.le_refl| apply Z.le_refl| clear; lia| exact X4].
    - (* [comment removed for export] *)
      destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]]. pose proof DSL as DSL1. unfold zlength in DSL1.
      eapply bytes_at_transport; [exact DSm1| exact MU|]. exact (proj1 (BWq (pD, mb_buf R, mb_len R) (mb_buf R) (Z.of_nat (length ds)) (SLB0 _ PIN) ltac:(apply Z.le_refl) ltac:(cbn; rewrite DSL1; apply Z.le_refl) ltac:(clear; lia))).
    - (* [comment removed for export] *)
      eapply bytes_at_transport; [exact DSb1| exact MU|]. unfold zlength in NBR. exact (proj1 (BWq (pbin, Bb, nB) Bb (Z.of_nat (length bs)) IB0 ltac:(apply Z.le_refl) ltac:(cbn; clear - NBR; lia) ltac:(clear; lia))).
    - (* [comment removed for export] *)
      unfold zlength in NBR. exists jb1. eapply rw_cells_transport; [exact CBb1| exact MU| exact WM|].
      eapply (ECH_AKit.disjoint_from_sub W Bb nB); [exact (proj1 (BWq (pbin, Bb, nB) Bb nB IB0 ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) ltac:(clear - NBR; lia)))| apply Z.le_refl| cbn [cells_size csize Nat.add]; clear - NBR; lia| cbn [cells_size csize Nat.add]; clear - NBR; lia].
    - (* [comment removed for export] *)
      pose proof (BRS _ (IN0 _ IB0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      eapply addressable_acrossX; [exact ADb1| exact MU| exact WM| clear - E1; lia| unfold AAPP_HI; clear - E5 ACB; lia| exact (proj2 (BWq (pbin, Bb, nB) Bb nB IB0 ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) E3))].
    - (* [comment removed for export] *)
      pose proof (BRS _ (IN0 _ IA0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7. pose proof DSL as DSL2. unfold zlength in DSL2.
      exists ja1. eapply rw_cells_transport; [exact CBa1| exact MU| exact WM|].
      eapply (ECH_AKit.disjoint_from_sub W A nA); [exact (proj1 (BWq (p, A, nA) A nA IA0 ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) E3))| apply Z.le_refl| cbn [cells_size csize Nat.add]; clear - NAR DSL2; lia| cbn [cells_size csize Nat.add]; clear - NAR DSL2; lia].
    - (* [comment removed for export] *)
      pose proof (BRS _ (IN0 _ IA0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      eapply addressable_acrossX; [exact ADa1| exact MU| exact WM| clear - E1; lia| unfold AAPP_HI; clear - E5 ACB; lia| exact (proj2 (BWq (p, A, nA) A nA IA0 ltac:(apply Z.le_refl) ltac:(cbn; apply Z.le_refl) E3))].
    - (* [comment removed for export] *)
      eapply (BT_frame (drest [] NB LE) (bv_unsigned sp) W); [exact BT1| exact XP| exact STB0| clear - AS1 Q2; lia| | exact MI2].
      intros b Hb. pose proof (BRS b (IN0 _ (STB0 _ Hb))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      split; [exact (BWa b _ _ (STB0 _ Hb) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3)|].
      unfold shavoids. eapply Forall_impl; [| exact (proj2 (BWq b _ _ (STB0 _ Hb) ltac:(apply Z.le_refl) ltac:(apply Z.le_refl) E3))]. cbn beta.
      pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(clear - E1; lia) E3 ltac:(unfold AAPP_HI; clear - E5 ACB; lia)) as SNH.
      assert (SB0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; clear - E1; Z.div_mod_to_equations; lia).
      intros iv [K|[K|[K|K]]]; [right; clear - K SB0; lia| left; clear - K SNH; lia| left; exact K| right; exact K].
    - (* [comment removed for export] *) eapply rw_cells_transport; [exact FR0| exact MU| exact WM| apply DJS; [exact AS1| left; cbn; clear; lia]].
    - (* [comment removed for export] *) eapply rw_cells_transport; [exact FRG| exact MU| exact WM| apply DJS; [clear - AS1; lia| right; clear; lia]].
    - (* [comment removed for export] *) eapply rw_cells_transport; [exact FRS| exact MU| exact WM| apply DJS; [clear - AS1 Q2; lia| right; clear - Q2; lia]].
    - exists lb'. exact FF'.
    - (* [comment removed for export] *)
      eapply (ah_RFS_frame H HH); [exact RFS1| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]].
      1-3: left; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; clear - K AF2 CEIL ACB AS1; lia.
      + right. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (fsz 6) with 4096. clear - K; lia.
      + left. rewrite SHF in K. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. clear - K NSF SYL SYU SY8 SYA W1 W3 S0 SHC. unfold ALOWSH_LO, AHI_LO in *. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
      + left. rewrite SHF in K. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *. clear - K NSF SYL SYU SY8 SYA W1 W3 S0 SHC. unfold ALOWSH_LO, AHI_LO in *. unfold sh in *. rewrite ?ASHADOW_BASE_val in *. lia.
      + right. exists (6, ff, fp). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. change (fsz 6) with 4096. clear - K; lia.
      + left. pose proof (BRS b (INX _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, AIMG_TOP in *. clear - K1 K2 E4 E6. lia.
    - (* [comment removed for export] *) exists errv1. eapply rw_cells_transport; [exact ERR1| exact MU| exact WM|]. apply djF. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv Hiv. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. destruct (FWc iv Hiv) as [[K|[[K1 K2]|[K1 K2]]]|(b' & Hb' & K1 & K2)].
      + left. clear - K ERNG CEIL ACB. lia.
      + left. clear - K1 ERNG AF1. lia.
      + left. clear - K1 ERNG W1. lia.
      + left. pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & E4 & _). unfold AIMG_TOP in E4. clear - K1 ERNG E4. lia.
    - (* [comment removed for export] *) eapply (ah_rauxv_frame H HH); [exact AUX1| exact MU| exact WM| exact CW].
    - (* [comment removed for export] *) eapply ACONST_frame; [exact AC1| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv Hiv. destruct (FWc iv Hiv) as [[K|[[K1 K2]|[K1 K2]]]|(b' & Hb' & K1 & K2)]; destruct iv as [l h]; cbn [fst snd] in *.
      + apply aconst_ok_hi. unfold AHI_LO. clear - K ACB. lia.
      + eapply (aconst_ok_aapp _ _ _ _ AF4); [exact K1| exact K2].
      + apply aconst_ok_high; [clear - K1 W1 S0; unfold AIMG_TOP; lia| right; left; clear - K1 K2 W1 W3 SYA SHC ACB; unfold AHI_LO in *; lia].
      + pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & _ & _ & _ & E7'). eapply (aconst_ok_aapp _ _ _ _ E7'); [exact K1| exact K2].
    - (* [comment removed for export] *) eapply stack0_transport; [exact STK1| exact MU| exact WM|]. eapply Forall_impl; [| exact FW0]. cbn beta.
      intros iv Hiv. destruct (FWc iv Hiv) as [[K|[[K1 K2]|[K1 K2]]]|(b' & Hb' & K1 & K2)]; destruct iv as [l h]; cbn [fst snd] in *.
      + apply stack0_ok_app. unfold AHI_LO. clear - K ACB. lia.
      + eapply (stack0_ok_aapp _ _ _ _ AF4); [exact K1| exact K2].
      + right. cbn [snd]. clear - K2 SYA. unfold AFS_SIZE in *. lia.
      + pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & _ & _ & _ & E7'). eapply (stack0_ok_aapp _ _ _ _ E7'); [exact K1| exact K2].
    - (* [comment removed for export] *)
      eapply (achain_below H HH m1 m2 _ _ _ (bv_unsigned sp)); [exact CHN1| intros fp' ra' [E|Hin]; [injection E as <- <-; apply Z.le_refl| pose proof (CHB _ _ Hin) as CB'; clear - CB'; lia]| exact MU|].
      eapply Forall_impl; [| exact FW0]. cbn beta.
      assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= aceil) by (intros b Hb; pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _); exact E5).
      intros iv [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]]; left; [clear - K Q2; lia| clear - K Q2; lia| clear - K Q2; lia| clear - K FQ6 FB2 AS1 Q2; lia
        | rewrite SHF in K; clear - K SY8 SYU SYA SHC AS1 Q2; lia| rewrite SHF in K; clear - K SY8 SYU SYA SHC AS1 Q2; lia| clear - K FQ6 FB2 AS1 Q2; lia| pose proof (HBL b Hb); clear - H0 K2 AS1 Q2; lia].
    - (* [comment removed for export] *)
      destruct XA1 as (XSq & FXq & INq & XA1). exists XSq. split; [exact FXq|]. split; [exact INq|].
      eapply (xpres_trans H); [exact XA1|]. eapply (xpres_of_munch_gen H); [exact MU| exact WM|].
      intros a Ha [Ca HXa]. apply outside_of_not_rin. intros RW. destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra).
      pose proof (proj1 (Forall_forall _ _) FW0 iv Hiv) as K.
      destruct K as [K|[K|[K|[K|[K|[K|[K|(b & Hb & K1 & K2)]]]]]]].
      1-3: exact ((RCI client_not_frame) _ _ _ _ _ HP SUB0 Ca ltac:(clear - K Ra Q2 LO STK0; lia)).
      + apply HXa. apply rin_ivs_app. left. apply INq. unfold XSF. cbn [rin_ivs fst snd]. right; right; left. change (fsz 6) with 4096. clear - K Ra; lia.
      + apply HXa. apply rin_ivs_app. left. apply INq. unfold XSF. cbn [rin_ivs fst snd]. right; right; right; left. change (fshn 6) with 512. rewrite SHF in K. clear - K Ra; lia.
      + apply HXa. apply rin_ivs_app. left. apply INq. unfold XSF. cbn [rin_ivs fst snd]. right; right; right; left. change (fshn 6) with 512. rewrite SHF in K. clear - K Ra; lia.
      + apply HXa. apply rin_ivs_app. left. apply INq. unfold XSF. cbn [rin_ivs fst snd]. right; right; left. change (fsz 6) with 4096. clear - K Ra; lia.
      + (* [comment removed for export] *)
        pose proof (client_outside_block H HH s1' Lall m1 b LB (bv_unsigned sp) a HP1 (INX _ Hb) (fun b0 Hb0 => IN0 _ (SLB0 _ Hb0))
                      ltac:(intros c c' Hc Hc' E; destruct Hc as [<-|[]]; exact (D2 _ _ Hb (SLB0 _ Hc') E)) ltac:(clear - AS1 Q2; lia) Ca) as OB.
        clear - OB K1 K2 Ra. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma adwkG_x : forall Lx Lx' NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf um' uf' m1 s1' m2 s2' (errv2 : word),
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' ->
    xpres H (mid_errblocks M' ++ drest [] NB LE) S1c [] m1 m2 ->
    as_RHEAP H s2' (mid_errblocks M' ++ drest Lx' NB LE) m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c -> as_rauxv_ok H m2 B ->
    rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> LEDGERc s2' um' uf' ->
    adwkG Lx' NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until errv2. intros DW XP HP2 MI2 AC2 STK2 AUX2 ERR2 LED2.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    destruct (adwkG_heap_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ DW) as (BRS & ND & DISJ & D2 & D1).
    pose proof (drest_sub Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    set (Lall := mid_errblocks M' ++ drest Lx NB LE) in *. set (Lq := mid_errblocks M' ++ drest [] NB LE) in *.
    assert (IN0 : forall b, In b (drest [] NB LE) -> In b Lq) by (intros b Hb; subst Lq; apply in_or_app; right; exact Hb).
    assert (INQ : forall b, In b Lq -> In b Lall) by (intros b Hb; subst Lq Lall; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb| right; apply SL0; exact Hb]).
    assert (SQ : forall b, In b LB -> In b Lq) by (intros b Hb; apply IN0; apply SLB0; exact Hb).
    pose proof ((RCI xnil_carry) ff fp m1 m2 s1' Lall Lq FRESH XP HP1 INQ SQ) as (TRFS & TLM & Ts & Tf & Tsh & Tb & Tby & Ta & Tacc & T0 & Tch & Txa & Tmb & Tms).
    assert (BEL : forall b, In b Lq -> blk_addr b + blk_size b <= S1c) by (intros b Hb; pose proof (BRS b (INQ _ Hb)) as (_ & _ & _ & _ & E5 & _); clear - E5 AS1; lia).
    unfold adwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - exact (TLM _ M' x LM1 ltac:(rewrite CTX1; exact CTX) ltac:(intros b Hb; apply IN0; apply SLL0; exact Hb) ltac:(intros b Hb; subst Lq; apply in_or_app; left; exact Hb)).
    - eapply (STOREobj_frame_law H (NB ++ LE ++ LB) (NB ++ LE ++ LB) m1 m2 st S' S1c); [exact SO1| intros b Hb; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| |].
      + eapply (xpres_weaken H); [exact XP| apply Z.le_refl| intros b Hb; apply IN0; apply S30; exact Hb| intros q Hq; exact Hq].
      + intros b Hb. apply BEL. apply IN0. apply S30. exact (STOREobj_owned_law _ _ _ _ SO1 b Hb).
    - eapply (STORE_shad_frame_law H Lq m1 m2 st S' S1c); [exact SSH1| intros b Hb; apply IN0; apply S30; exact (STOREobj_owned_law _ _ _ _ SO1 b Hb)| exact XP|].
      intros b Hb. apply BEL. apply IN0. apply S30. exact (STOREobj_owned_law _ _ _ _ SO1 b Hb).
    - exact (Tmb R' MST MBO1).
    - exact (Tms R' MST MBO1 MSH1).
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN _]]. pose proof DSL as DSL1. unfold zlength in DSL1.
      eapply (Tby (pD, mb_buf R, mb_len R)); [exact (SQ _ PIN)| cbn; clear; lia| cbn; rewrite DSL1; clear; lia| exact DSm1].
    - unfold zlength in NBR. eapply (Tby (pbin, Bb, nB)); [exact (IN0 _ IB0)| cbn; clear; lia| cbn; clear - NBR; lia| exact DSb1].
    - pose proof (BRS _ (INQ _ (IN0 _ IB0))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E2, E3.
      unfold zlength in NBR. exists jb1. eapply (Tb (pbin, Bb, nB)); [exact (IN0 _ IB0)| cbn; clear; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - NBR; lia| exact CBb1].
    - pose proof (BRS _ (INQ _ (IN0 _ IB0))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E2, E3.
      eapply (Ta (pbin, Bb, nB)); [exact (IN0 _ IB0)| apply Z.le_refl| apply Z.le_refl| clear - E2; Z.div_mod_to_equations; lia| exact E3| exact ADb1].
    - pose proof (BRS _ (INQ _ (IN0 _ IA0))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E2, E3. pose proof DSL as DSL2. unfold zlength in DSL2.
      exists ja1. eapply (Tb (p, A, nA)); [exact (IN0 _ IA0)| cbn; clear; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - NAR DSL2; lia| exact CBa1].
    - pose proof (BRS _ (INQ _ (IN0 _ IA0))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E2, E3.
      eapply (Ta (p, A, nA)); [exact (IN0 _ IA0)| apply Z.le_refl| apply Z.le_refl| clear - E2; Z.div_mod_to_equations; lia| exact E3| exact ADa1].
    - eapply (BT_frame Lq S1c []); [exact BT1| exact XP| intros b Hb; apply IN0; apply STB0; exact Hb| exact AS1| intros b Hb; split; apply Forall_nil| exact MI2].
    - exact (Ts _ _ FR0 ltac:(apply Z.le_refl)).
    - exact (Ts _ _ FR1 ltac:(clear; lia)).
    - exact (Ts _ _ FR2 ltac:(clear; lia)).
    - exact (Ts _ _ FR3 ltac:(clear; lia)).
    - exact (Ts _ _ FRG ltac:(clear; lia)).
    - exact (Ts _ _ FRS ltac:(clear - Q2; lia)).
    - destruct FF1 as [lb1 FF1]. exists lb1. exact (Tf _ FF1 ltac:(unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; pose proof FF1 as [[WF _] _]; clear - WF; cbn in WF; lia)).
    - rewrite SHF in FSH1 |- *. exact (Tsh _ FSH1 ltac:(unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - LSH1; lia)).
    - exact (TRFS RFS1).
    - exists errv2. exact ERR2.
    - exact (T0 STK1).
    - exact (Tch _ _ CHN1 ltac:(intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia])).
    - destruct XA1 as (XSq & FXq & INq & XA1). exists XSq. split; [exact FXq|]. split; [exact INq|]. exact (Txa _ _ XA1).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mid_step_trans_ : forall M0 M1 M2, mid_step M0 M1 -> mid_step M1 M2 -> mid_step M0 M2.
  Proof.
    clear. intros [f0 c0 e0 E0 v0] [f1 c1 e1 E1 v1] [f2 c2 e2 E2 v2] (A1 & B1 & C1 & V1) (A2 & B2 & C2 & V2). cbn [mid_flag mid_ctx mid_err mid_vdso] in *.
    split; [exact A2|]. split; [intros b Hb; exact (B2 b (B1 b Hb))|]. split; [intros c Hc; exact (C2 c (C1 c Hc))| intros Hv; exact (V2 (V1 Hv))].
  Qed.

  (* [comment removed for export] *)
  Lemma adwkG_libXV : forall Lx Lx' NB S' M' M'' LE LEn fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf um' uf' m1 s1' m2 s2' (X XS : list (Z * Z))
                           (fr1' : list cell) (wee' v192' v200' v208' v224' v232' : word) (fr3' : list cell) (errv2 : word),
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M'' = mid_ctx M' ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES ->
    xpres H (drest Lx NB LE) S1c (X ++ ECH_AC14_kit.XR (mid_err M') XS) m1 m2 ->
    Forall (fun iv : Z * Z => (S1c + 16 <= fst iv /\ snd iv <= S1c + 240) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 344)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)
                              \/ iv = (A_vdso_func, A_vdso_func + 8)) X ->
    Forall (fs_scratch H (LF1c ff fp)) XS ->
    as_RHEAP H s2' (mid_errblocks M'' ++ drest Lx' NB (LEn ++ LE)) m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c ->
    as_rauxv_ok H m2 B -> rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> as_RFS H (LF1c ff fp) m2 -> LEDGERc s2' um' uf' ->
    rw_cells asegs m2 (S1c + 16) fr1' -> cells_size fr1' = 128%nat -> rw_cells asegs m2 (S1c + 144) (dsg2 wee' v192' v200' v208' v224' v232') ->
    rw_cells asegs m2 (S1c + 240) fr3' -> cells_size fr3' = 104%nat ->
    adwkG Lx' NB S' M'' (LEn ++ LE) fr1' wee' v192' v200' v208' v224' v232' fr3' tpl shb b2 shd um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until errv2. intros DW LM2 STP2 NEW2 CTX2 EC2 EB2 XP FX FXS HP2 MI2 AC2 STK2 AUX2 ERR2 RFS2 LED2 FR1' SZ1' FR2' FR3' SZ3'.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    pose proof (fresh_frame_facts H _ _ _ _ FRESH) as (_ & FQ1 & FQ2 & FQ64 & FQ8 & FP1 & FP2 & FP3 & FP4 & FQ5 & FQ6 & FB1 & FB2 & FB3).
    change (fsz 6) with 4096 in FQ2, FQ6. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP in FQ1, FQ2, FP1, FP2, FP3, FP4, FQ5, FQ6, FB1, FB2.
    assert (S0 : sh 0xc04000 = 0x80178800) by reflexivity.
    assert (SHF : SH = sh ff) by (unfold sh, ASHB; rewrite Z.shiftr_div_pow2 by (clear; lia); rewrite ASHADOW_BASE_val; change (2 ^ 3) with 8; clear; lia).
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; clear - ACB; lia).
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (sh_add8 ff 512) as SY8. replace (ff + 8 * 512) with (ff + 4096) in SY8 by (clear; lia).
    pose proof (sh_mono (as_FSB H) ff ltac:(clear - FQ5; lia)) as SYL. pose proof (sh_mono (ff + 4096) _ FQ6) as SYU. pose proof (sh_mono _ _ AF2) as SYA.
    pose proof (sh_aapp_range _ _ AF4 ltac:(unfold AFS_SIZE; clear; lia)) as (W1 & W2 & W3). unfold nsh in W2. unfold AIMG_TOP in W1. rewrite S0 in W1.
    pose proof (aapp_not_shadowland _ _ AF4) as NSF.
    destruct (adwkG_heap_facts Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' DW) as (BRS & ND & DISJ & D2 & D1).
    destruct (drest_ids _ _ _ _ ND) as (_ & _ & DNB & DTB & DBIN & DLBUF & DLE).
    pose proof (drest_sub Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (drest_sub [] NB LE) as (SLB0 & _ & SLE0 & SNB0 & STB0 & IB0 & IA0 & _ & S30 & SLL0).
    set (Lall := mid_errblocks M' ++ drest Lx NB LE) in *.
    assert (INX : forall b, In b Lx -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SLX; exact Hb).
    assert (IN0 : forall b, In b (drest [] NB LE) -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SL0; exact Hb).
    assert (ID0 : forall b, In b (drest [] NB LE) -> In b (drest Lx NB LE)) by (intros b Hb; apply SL0; exact Hb).
    pose proof SO as (_ & SINB & _).
    pose proof LM1 as (_ & MFa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ESH1 & EBL1). pose proof STP as (MF1' & _). rewrite MF1' in MFa.
    pose proof LM2 as (_ & MFb & _). pose proof STP2 as (MF2' & _). rewrite MF2' in MFb.
    (* [comment removed for export] *)
    assert (HES : forall c0, mid_err M' = ErrReady c0 -> In (ec_es c0) Lall /\ blk_size (ec_es c0) = ERRST_SIZE /\ In (ec_es c0) (LE ++ LIB)).
    { intros c0 EQ. destruct (adwkG_es Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' c0 DW EQ) as [I5 Z5]. split; [exact (IN0 _ (SLL0 _ I5))|]. split; [exact Z5| exact I5]. }
    assert (INR : forall l, In l (LE ++ LIB) -> In l (TB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB)).
    { intros l Hl. apply in_or_app; right; right; right. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; apply in_or_app; [left; exact Hl| right; exact (SUBL _ Hl)]. }
    assert (NLIBst : forall b, In b (blocks_STORE st S') -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl. pose proof (Permutation_in _ SPM Hb) as [<-|HbN].
      - apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl SINB)| exact (DJ6 _ _ Hl (or_introl eq_refl))].
      - intros EQ. exact (DNB _ _ HbN (INR _ Hl) (eq_sym EQ)). }
    assert (NLIBmb : forall b, In b (blocks_MEMBIO mb R') -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl (mb_blocks_LB' _ Hb))|].
      rewrite (mb_static_blocks mb R R' MST) in Hb. exact (DJ6 _ _ Hl (or_intror Hb)). }
    assert (NLIBtb : forall b, In b TB -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b).
    { intros b Hb l Hl EQ. apply in_app_or in Hl. destruct Hl as [Hl|Hl].
      - exact (DTB _ _ Hb ltac:(right; right; apply in_or_app; left; exact Hl) (eq_sym EQ)).
      - exact (DTB _ _ Hb ltac:(right; right; apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ)). }
    assert (NLIBbin : forall l, In l (LE ++ LIB) -> blk_id l <> blk_id (pbin, Bb, nB)).
    { intros l Hl EQ. apply in_app_or in Hl. destruct Hl as [Hl|Hl].
      - exact (DBIN _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; left; exact Hl) (eq_sym EQ)).
      - exact (DBIN _ _ (or_introl eq_refl) ltac:(right; apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ)). }
    assert (NLIBpay : forall pD, In (pD, mb_buf R, mb_len R) LB -> forall l, In l (LE ++ LIB) -> blk_id l <> blk_id (pD, mb_buf R, mb_len R)).
    { intros pD PIN l Hl. apply in_app_or in Hl. destruct Hl as [Hl|Hl]; [exact (DLE _ _ Hl PIN)|].
      destruct (PAYL ltac:(clear - NAR; lia)) as [pD' [PIN' PNL]]. cbn [blk_id fst snd]. intros E.
      pose proof (nodup_id_inj _ l (pD, mb_buf R, mb_len R) ND (IN0 _ (SLB0 _ (SUBL _ Hl))) (IN0 _ (SLB0 _ PIN)) E) as El. subst l.
      pose proof (PNL _ Hl) as NE. cbn [blk_id fst snd] in NE.
      pose proof (DISJ (pD, mb_buf R, mb_len R) (pD', mb_buf R, mb_len R) (IN0 _ (SLB0 _ PIN)) (IN0 _ (SLB0 _ PIN')) NE) as DD. cbn [blk_addr blk_size fst snd] in DD. clear - DD NAR. lia. }
    (* [comment removed for export] *)
    assert (AVB : forall b, In b (drest [] NB LE) -> (forall l, In l (LE ++ LIB) -> blk_id l <> blk_id b) ->
                  avoids (X ++ ECH_AC14_kit.XR (mid_err M') XS) (blk_addr b) (blk_size b) /\ shavoids (X ++ ECH_AC14_kit.XR (mid_err M') XS) (blk_addr b) (blk_size b)).
    { intros b Hb NLIB. pose proof (BRS b (IN0 _ Hb)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      destruct (ECH_AC14_kit.XR_block H HX (mid_err M') s1' Lall m1 (LF1c ff fp) m1 XS b HP1 RFS1 FXS (IN0 _ Hb)
                  ltac:(intros c0 EQ; destruct (HES c0 EQ) as (I1 & Z1 & IL); split; [exact I1| split; [exact (NLIB _ IL)| exact Z1]])) as [AVR SAVR].
      pose proof (sh_nsh_high (blk_addr b) (blk_size b) ltac:(clear - E1; lia) E3 ltac:(unfold AAPP_HI; clear - E5 ACB; lia)) as SNH.
      pose proof (aapp_not_shadowland _ _ E7) as NS.
      split; (unfold avoids, shavoids; apply Forall_app; split; [| assumption]); (eapply Forall_impl; [| exact FX]; cbn beta; intros iv [K|[K|[(b' & Hb' & K1 & K2)|K]]]).
      - left. clear - K E5 AS1. lia.
      - left. clear - K E5 AS1. lia.
      - assert (NE : blk_id b' <> blk_id b) by (intros EQ; exact (D2 _ _ Hb' Hb EQ)). pose proof (DISJ b' b (INX _ Hb') (IN0 _ Hb) NE). clear - H0 K1 K2. lia.
      - (* [comment removed for export] *) subst iv. cbn [fst snd]. right. unfold A_vdso_func. unfold AIMG_TOP in E4. clear - E4. lia.
      - left. unfold AHI_LO in *. clear - K SNH AS1 ACB. lia.
      - left. unfold AHI_LO in *. clear - K SNH AS1 ACB. lia.
      - pose proof (BRS b' (INX _ Hb')) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'.
        assert (SB0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; clear - E1; Z.div_mod_to_equations; lia).
        unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' SNH SB0. rewrite ?ASHADOW_BASE_val in *. lia.
      - subst iv. cbn [fst snd]. right. assert (SB0 : ASHADOW_BASE <= sh (blk_addr b)) by (unfold sh; clear - E1; Z.div_mod_to_equations; lia).
        unfold A_vdso_func. rewrite ASHADOW_BASE_val in SB0. clear - SB0. lia. }
    (* [comment removed for export] *)
    assert (AVS : forall Aq nq, aceil <= Aq -> ((S1c <= Aq /\ Aq + nq <= S1c + 16) \/ S1c + 344 <= Aq) ->
                  avoids (X ++ ECH_AC14_kit.XR (mid_err M') XS) Aq nq).
    { intros Aq nq HA HB. unfold avoids. apply Forall_app. split; [| exact (ECH_AC14_kit.XR_stack H HX (mid_err M') (LF1c ff fp) m1 XS Aq nq RFS1 FXS HA EBL1)].
      eapply Forall_impl; [| exact FX]. cbn beta.
      assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= aceil) by (intros b Hb; pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _); exact E5).
      intros iv [K|[K|[(b & Hb & K1 & K2)|K]]]; [clear - K HB; lia| clear - K HB; lia| pose proof (HBL b Hb); clear - H0 K1 K2 HA; lia| subst iv; cbn [fst snd]; unfold A_vdso_func; clear - HA ACB; lia]. }
    (* [comment removed for export] *)
    assert (AVF : avoids (X ++ ECH_AC14_kit.XR (mid_err M') XS) ff 4096).
    { unfold avoids, ECH_AC14_kit.XR. apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]].
      - eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|[(b & Hb & K1 & K2)|K]]]; [clear - K AS1 FQ6 FB2; lia| clear - K AS1 FQ6 FB2; lia| | subst iv; cbn [fst snd]; unfold A_vdso_func; clear - FQ1; lia].
        pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & E6 & _). unfold AFS_SIZE in E6. clear - K1 K2 E6 FQ5 FQ6. lia.
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC.
        exact (fsobj_scratch H HH (LF1c ff fp) ff 4096 m1 iv RFS1 (fsobj_inframe H (LF1c ff fp) (6, ff, fp) ff 4096 ltac:(left; reflexivity) ltac:(cbn; apply Z.le_refl) ltac:(cbn; change (fsz 6) with 4096; apply Z.le_refl))
                 ltac:(clear - FQ1; lia) ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - FQ6 FB2 ACB; lia) (aapp_sub (as_FSB H) AFS_SIZE ff 4096 FB3 ltac:(clear - FQ5; lia) ltac:(unfold AFS_SIZE; clear - FQ6; lia)) SC).
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - FQ1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - FQ1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err M') as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & SZ & _).
        pose proof (BRS _ IE) as (_ & _ & _ & _ & _ & E6 & _). rewrite SZ in E6. unfold AFS_SIZE in E6. apply Forall_cons; [cbn [fst snd]; clear - E6 FQ5 FQ6; lia| apply Forall_nil]. }
    assert (AVSH : avoids (X ++ ECH_AC14_kit.XR (mid_err M') XS) (sh ff) 512).
    { unfold avoids, ECH_AC14_kit.XR. apply Forall_app. split; [| apply Forall_app; split; [| apply Forall_app; split; [| apply Forall_app; split]]].
      - eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|[(b & Hb & K1 & K2)|K]]]; [clear - K AS1 SY8 SYU SYA SHC; lia| clear - K AS1 SY8 SYU SYA SHC; lia| | subst iv; cbn [fst snd]; unfold A_vdso_func; clear - SYL W1; lia].
        pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & _ & E7'). pose proof (aapp_not_shadowland _ _ E7') as NS'. unfold ALOWSH_LO, AHI_LO in *. clear - K1 K2 NS' SYL SY8 SYU SYA W1 W3 SHC. lia.
      - eapply Forall_impl; [| exact FXS]. cbn beta. intros iv SC.
        pose proof (fsobj_scratch_sh H HH (LF1c ff fp) ff 4096 m1 iv RFS1 (fsobj_inframe H (LF1c ff fp) (6, ff, fp) ff 4096 ltac:(left; reflexivity) ltac:(cbn; apply Z.le_refl) ltac:(cbn; change (fsz 6) with 4096; apply Z.le_refl))
                 ltac:(clear - FQ1; lia) ltac:(clear; lia) ltac:(unfold AAPP_HI; clear - FQ6 FB2 ACB; lia) SC) as K. unfold nsh in K. change ((4096 + 7) / 8) with 512 in K. exact K.
      - unfold ERR_XE, ERRNO_X, ARERRNO, ATP, ERR_X, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret,
          A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main.
        cbn [app]. clear - SYL W1. repeat (apply Forall_cons; [right; cbn; lia|]). apply Forall_nil.
      - unfold memflag_foot, A_mem_inited. clear - SYL W1. apply Forall_cons; [right; cbn; lia| apply Forall_nil].
      - destruct (mid_err M') as [|c0] eqn:EQ; cbn [errph_foot]; [apply Forall_nil|]. destruct (HES c0 eq_refl) as (IE & SZ & _).
        pose proof (BRS _ IE) as (_ & _ & _ & _ & _ & _ & E7). rewrite SZ in E7. pose proof (aapp_not_shadowland _ _ E7) as NS.
        apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO in *; clear - NS SYL SY8 SYU SYA W1 W3 SHC; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (LEN : Z.of_nat (length LEn) + errph_cnt (mid_err M'') <= errph_cnt (mid_err M') /\ lb_bytes LEn + errph_bytes (mid_err M'') <= errph_bytes (mid_err M')).
    { destruct NEW2 as (LA & LE2 & PM & CA & CE). rewrite CTX1, CTX in CA. destruct STP2 as (_ & _ & SE2 & _).
      subst LA. cbn [app] in PM.
      destruct (mid_err M') as [|c1] eqn:E1; destruct (mid_err M'') as [|c2] eqn:E2.
      - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia.
      - cbn [errph_delta] in CE. destruct CE as (Qa & Qb & _). rewrite (Permutation_length PM), (lb_bytes_perm _ _ PM). cbn [errph_cnt errph_bytes]. clear - Qa Qb. lia.
      - discriminate (SE2 c1 eq_refl).
      - rewrite CE in PM. apply Permutation_sym in PM. apply Permutation_nil in PM. subst LEn. cbn. clear. lia. }
    destruct LEN as [LEc LEb].
    unfold adwkG. repeat match goal with |- _ /\ _ => split end; try assumption.
    - rewrite <- app_assoc. exact LM2.
    - exact (mid_step_trans_ _ _ _ STP STP2).
    - exact (mid_newlib_ok_trans _ _ _ _ _ STP NEW STP2 NEW2).
    - rewrite CTX2. exact CTX1.
    - rewrite length_app, Nat2Z.inj_add. clear - LC LEc. lia.
    - rewrite lb_bytes_app. clear - LBY LEb. lia.
    - eapply STOREobj_LB_mono; [eapply (STOREobj_frameX H (NB ++ LE ++ LB) S1c); [exact SO1| |]|].
      + eapply (xpres_weaken H); [exact XP| apply Z.le_refl| intros b Hb; apply ID0; apply S30; exact Hb| intros q Hq; exact Hq].
      + intros b Hb. exact (proj1 (AVB b (S30 _ (STOREobj_owned_law _ _ _ _ SO1 b Hb)) (NLIBst b Hb))).
      + intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
        apply in_app_or in Hb. destruct Hb as [Hb|Hb]; apply in_or_app; [left; apply in_or_app; right; exact Hb| right; exact Hb].
    - eapply (STORE_shad_frameX H (NB ++ LE ++ LB) (drest Lx NB LE) S1c); [exact SSH1| exact SO1| exact XP|].
      intros b Hb. pose proof (STOREobj_owned_law _ _ _ _ SO1 b Hb) as HbN. split; [exact (ID0 _ (S30 _ HbN))| exact (AVB b (S30 _ HbN) (NLIBst b Hb))].
    - eapply (AMEMBIO_xpres H LB (drest Lx NB LE) S1c); [exact MBO1| intros b Hb; exact (ID0 _ (SLB0 _ (mb_blocks_LB' _ Hb)))| exact XP|].
      apply Forall_forall. intros iv Hiv. apply Forall_forall. intros bk Hbk.
      exact (proj1 (Forall_forall _ _) (proj1 (AVB bk (SLB0 _ (mb_blocks_LB' _ Hbk)) (NLIBmb _ Hbk))) iv Hiv).
    - destruct MSH1 as (X1 & X2 & X3 & X4). pose proof MBO1 as MBq. destruct MBq as (_ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
      assert (TA : forall b, In b (blocks_MEMBIO mb R') -> addressable m1 (blk_addr b) (blk_size b) -> addressable m2 (blk_addr b) (blk_size b)).
      { intros b Hb AD. pose proof (BRS b (IN0 _ (SLB0 _ (mb_blocks_LB' _ Hb)))) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). destruct b as [[ib Ab] nb]. cbn [blk_addr blk_size fst snd] in *.
        eapply (addressable_xpres_blkX H); [exact (ID0 _ (SLB0 _ (mb_blocks_LB' _ Hb)))| unfold AAPP_HI; clear - E5 ACB; lia| exact AD| exact XP| exact (proj2 (AVB _ (SLB0 _ (mb_blocks_LB' _ Hb)) (NLIBmb _ Hb)))]. }
      unfold blocks_MEMBIO in TA. unfold MEMBIO_shad. unfold BIO_SIZE, BIOBUFMEM_SIZE, BUFMEM_SIZE in *.
      split; [| split; [| split]].
      + exact (TA (mb_id R', mb, 128) ltac:(left; reflexivity) X1).
      + exact (TA (mb_bbid R', mb_bb R', 16) ltac:(right; left; reflexivity) X2).
      + exact (TA (mb_bmid R', mb_bm R', 32) ltac:(right; right; left; reflexivity) X3).
      + exact (TA (mb_rpid R', mb_rp R', 32) ltac:(right; right; right; left; reflexivity) X4).
    - destruct (PAYL ltac:(clear - NAR; lia)) as [pD [PIN PNL]]. pose proof DSL as DSL1. unfold zlength in DSL1.
      eapply (xpres_bytes_at' H); [exact XP| exact DSm1| right; right; left; exists (pD, mb_buf R, mb_len R); split; [exact (ID0 _ (SLB0 _ PIN))| cbn; rewrite DSL1; clear; lia]|].
      rewrite DSL1. pose proof (proj1 (AVB (pD, mb_buf R, mb_len R) (SLB0 _ PIN) (NLIBpay _ PIN))) as K. cbn [blk_addr blk_size fst snd] in K. exact K.
    - pose proof (proj1 (AVB (pbin, Bb, nB) IB0 NLIBbin)) as K. cbn [blk_addr blk_size fst snd] in K. unfold zlength in NBR.
      eapply (xpres_bytes_at' H); [exact XP| exact DSb1| right; right; left; exists (pbin, Bb, nB); split; [exact (ID0 _ IB0)| cbn; clear - NBR; lia]|].
      eapply avoids_sub; [exact K| clear; lia| clear - NBR; lia].
    - (* [comment removed for export] *)
      pose proof (proj1 (AVB (pbin, Bb, nB) IB0 NLIBbin)) as K. cbn [blk_addr blk_size fst snd] in K. unfold zlength in NBR.
      exists jb1. eapply (xpres_rw_cells' H); [exact XP| exact CBb1| right; right; left; exists (pbin, Bb, nB); split; [exact (ID0 _ IB0)| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - NBR; lia]|].
      eapply avoids_sub; [exact K| apply Z.le_refl| cbn [cells_size csize Nat.add]; clear - NBR; lia].
    - (* [comment removed for export] *)
      pose proof (BRS _ (IN0 _ IB0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      pose proof (proj2 (AVB (pbin, Bb, nB) IB0 NLIBbin)) as K. cbn [blk_addr blk_size fst snd] in K.
      eapply (addressable_xpres_blkX H); [exact (ID0 _ IB0)| unfold AAPP_HI; clear - E5 ACB; lia| exact ADb1| exact XP| exact K].
    - (* [comment removed for export] *)
      pose proof (proj1 (AVB (p, A, nA) IA0 ltac:(intros l Hl EQ; apply in_app_or in Hl; destruct Hl as [Hl|Hl]; [exact (DLBUF _ _ (or_introl eq_refl) ltac:(apply in_or_app; left; exact Hl) (eq_sym EQ))| exact (DLBUF _ _ (or_introl eq_refl) ltac:(apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ))]))) as K.
      cbn [blk_addr blk_size fst snd] in K. pose proof DSL as DSL2. unfold zlength in DSL2.
      exists ja1. eapply (xpres_rw_cells' H); [exact XP| exact CBa1| right; right; left; exists (p, A, nA); split; [exact (ID0 _ IA0)| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; clear - NAR DSL2; lia]|].
      eapply avoids_sub; [exact K| apply Z.le_refl| cbn [cells_size csize Nat.add]; clear - NAR DSL2; lia].
    - (* [comment removed for export] *)
      pose proof (BRS _ (IN0 _ IA0)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      pose proof (proj2 (AVB (p, A, nA) IA0 ltac:(intros l Hl EQ; apply in_app_or in Hl; destruct Hl as [Hl|Hl]; [exact (DLBUF _ _ (or_introl eq_refl) ltac:(apply in_or_app; left; exact Hl) (eq_sym EQ))| exact (DLBUF _ _ (or_introl eq_refl) ltac:(apply in_or_app; right; exact (SUBL _ Hl)) (eq_sym EQ))]))) as K.
      cbn [blk_addr blk_size fst snd] in K.
      eapply (addressable_xpres_blkX H); [exact (ID0 _ IA0)| unfold AAPP_HI; clear - E5 ACB; lia| exact ADa1| exact XP| exact K].
    - eapply (BT_frame (drest Lx NB LE) S1c); [exact BT1| exact XP| intros b Hb; exact (ID0 _ (STB0 _ Hb))| exact AS1| | exact MI2].
      intros b Hb. exact (AVB b (STB0 _ Hb) (NLIBtb _ Hb)).
    - eapply (xpres_rw_cells' H); [exact XP| exact FR0| left; apply Z.le_refl| apply AVS; [exact AS1| left; cbn; clear; lia]].
    - eapply (xpres_rw_cells' H); [exact XP| exact FRG| left; clear; lia| apply AVS; [clear - AS1; lia| right; clear; lia]].
    - eapply (xpres_rw_cells' H); [exact XP| exact FRS| left; clear - Q2; lia| apply AVS; [clear - AS1 Q2; lia| right; clear - Q2; lia]].
    - destruct FF1 as [lb1 FF1]. exists lb1. pose proof FF1 as [[WF _] _]. cbn in WF.
      eapply (xpres_rw_cells' H); [exact XP| exact FF1| right; right; right; right; left; unfold dff, arp_fframe2; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - WF FQ5 FQ6; lia|].
      unfold dff, arp_fframe2. cbn [cells_size csize Nat.add length]. eapply avoids_sub; [exact AVF| apply Z.le_refl| clear - WF; lia].
    - rewrite SHF in FSH1 |- *.
      eapply (xpres_rw_cells' H); [exact XP| exact FSH1| right; right; right; right; right; left; unfold dfsh, arp_fshadow; cbn [cells_size csize Nat.add length]; unfold AFS_SIZE; clear - LSH1 SYL SYU SY8; lia|].
      unfold dfsh, arp_fshadow. cbn [cells_size csize Nat.add length]. eapply avoids_sub; [exact AVSH| apply Z.le_refl| clear - LSH1; lia].
    - exists errv2. exact ERR2.
    - (* [comment removed for export] *)
      eapply (stack0_xpres H); [exact XP| exact STK1|]. apply Forall_app. split; [| exact (ECH_AC14_kit.XR_stack0 H HX (mid_err M') s1' Lall m1 (LF1c ff fp) m1 XS HP1 RFS1 FXS ltac:(intros c0 EQ; destruct (HES c0 EQ) as (I1 & Z1 & _); split; [exact I1| exact Z1]))].
      eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|[(b & Hb & K1 & K2)|K]]]; [| | | subst iv; right; cbn [fst snd]; unfold A_vdso_func, sh; rewrite ASHADOW_BASE_val; clear - ACB; lia]; destruct iv as [l h]; cbn [fst snd] in *.
      + apply stack0_ok_app. unfold AHI_LO. clear - K AS1 ACB. lia.
      + apply stack0_ok_app. unfold AHI_LO. clear - K AS1 ACB. lia.
      + pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & _ & _ & E7'). eapply (stack0_ok_aapp _ _ _ _ E7'); [exact K1| exact K2].
    - (* [comment removed for export] *)
      eapply (chain_via_xpres_off H HH (drest Lx NB LE) S1c); [exact CHN1| exact XP| intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]|].
      apply Forall_app. split; [| eapply Forall_impl; [| exact (ECH_AC14_kit.XR_low H HX (mid_err M') s1' Lall m1 (LF1c ff fp) m1 XS HP1 RFS1 FXS ltac:(intros c0 EQ; destruct (HES c0 EQ) as (I1 & Z1 & _); split; [exact I1| exact Z1]))]; cbn beta; intros iv K; left; exact K].
      eapply Forall_impl; [| exact FX]. cbn beta.
      assert (HBL : forall b, In b Lx -> blk_addr b + blk_size b <= aceil) by (intros b Hb; pose proof (BRS b (INX _ Hb)) as (_ & _ & _ & _ & E5 & _); exact E5).
      intros iv [K|[K|[(b & Hb & K1 & K2)|K]]]; [right| right| left; pose proof (HBL b Hb); clear - H0 K2; lia| left; subst iv; cbn [fst snd]; unfold A_vdso_func; clear - ACB; lia];
        intros fp' ra' [E|Hin]; [injection E as <- <-; left; cbn; clear - K Q2; lia| pose proof (CHB _ _ Hin) as CB'; left; cbn; clear - K CB' Q2; lia| injection E as <- <-; left; cbn; clear - K Q2; lia| pose proof (CHB _ _ Hin) as CB'; left; cbn; clear - K CB' Q2; lia].
    - (* [comment removed for export] *)
      destruct XA1 as (XSq & FXq & INq & XA1).
      exists (XSq ++ XS). split; [apply Forall_app; split; [exact FXq| eapply Forall_impl; [intros iv; apply (fs_scratch_mono H)| exact FXS]]|].
      split; [intros q Hq; apply rin_ivs_app; left; exact (INq q Hq)|].
      eapply (xpres_trans H); [eapply (xpres_weaken H); [exact XA1| apply Z.le_refl| intros b Hb; exact Hb| intros q Hq; apply rin_ivs_app in Hq; apply rin_ivs_app; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq| right; exact Hq]]|].
      (* [comment removed for export] *)
      assert (XPm : xpres H (drest Lx NB LE) S1c ((X ++ XS ++ ERR_XE ++ errph_foot (mid_err M')) ++ memflag_foot ++ []) m1 m2).
      { eapply (xpres_weaken H); [exact XP| apply Z.le_refl| intros b Hb; exact Hb|]. intros q Hq.
        apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; left; exact Hq|]. unfold ECH_AC14_kit.XR in Hq.
        apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
        apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [left; apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; left; exact Hq|].
        apply rin_ivs_app in Hq; destruct Hq as [Hq|Hq]; [right; apply rin_ivs_app; left; exact Hq| left; apply rin_ivs_app; right; apply rin_ivs_app; right; apply rin_ivs_app; right; exact Hq]. }
      pose proof (ECH_AC14_kit.axpres_drop_memflag H (drest Lx NB LE) S1c (X ++ XS ++ ERR_XE ++ errph_foot (mid_err M')) [] m1 m2 MFa MFb XPm) as XPd. rewrite app_nil_r in XPd.
      intros a Ha [Ca HXa]. apply XPd; [exact Ha|]. split.
      + eapply (aclient_addr_weaken H); [exact Ca| clear - Q2; lia| intros b Hb; exact (SLB _ Hb)].
      + intros RW. apply rin_ivs_app in RW. destruct RW as [RW|RW]; [| apply rin_ivs_app in RW; destruct RW as [RW|RW]; [| apply rin_ivs_app in RW; destruct RW as [RW|RW]]].
        * (* [comment removed for export] *)
          destruct (rin_ivs_In _ _ RW) as (iv & Hiv & Ra). pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as K. cbn beta in K.
          destruct K as [K|[K|[(b & Hb & K1 & K2)|K]]].
          -- exact ((RCI client_not_frame) _ _ _ _ _ HP SUB0 Ca ltac:(clear - K Ra Q2 LO STK0; lia)).
          -- exact ((RCI client_not_frame) _ _ _ _ _ HP SUB0 Ca ltac:(clear - K Ra Q2 LO STK0; lia)).
          -- pose proof (client_outside_block H HH s1' Lall m1 b LB (bv_unsigned sp) a HP1 (INX _ Hb) (fun b0 Hb0 => IN0 _ (SLB0 _ Hb0))
                          ltac:(intros c c' Hc Hc' E; destruct Hc as [<-|[]]; exact (D2 _ _ Hb (SLB0 _ Hc') E)) ltac:(clear - AS1 Q2; lia) Ca) as OB.
             clear - OB K1 K2 Ra. lia.
          -- (* [comment removed for export] *)
             subst iv. apply HXa. apply rin_ivs_app. right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; left.
             unfold VDSO_X. cbn [rin_ivs fst snd]. left. exact Ra.
        * apply HXa. apply rin_ivs_app. left. apply rin_ivs_app. right. exact RW.
        * apply HXa. apply rin_ivs_app. right. unfold XF. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; left. exact RW.
        * destruct (mid_err M') as [|c] eqn:EQ; [destruct RW|]. cbn [errph_foot rin_ivs fst snd] in RW. destruct RW as [RW|[]].
          destruct (HES c eq_refl) as (I5 & Z5 & IL).
          destruct (mid_err M) as [|c0] eqn:EQ0.
          -- (* [comment removed for export] *)
             assert (IE : In (ec_es c) LE).
             { destruct NEW as (LA & LE2 & PM & CA & CE). rewrite CTX in CA. cbn in CA. subst LA. cbn [app] in PM. rewrite ?EQ0, ?EQ in CE. cbn [errph_delta] in CE.
               destruct CE as (_ & _ & FA). eapply Permutation_in; [apply Permutation_sym; exact PM|].
               exact (proj1 (Forall_forall _ _) FA (ec_es c) ltac:(unfold chain_blocks; cbn [In]; tauto)). }
             pose proof (client_outside_block H HH s1' Lall m1 (ec_es c) LB (bv_unsigned sp) a HP1 (IN0 _ (SLE0 _ IE)) (fun b0 Hb0 => IN0 _ (SLB0 _ Hb0))
                          ltac:(intros c1 c' Hc Hc' E; destruct Hc as [<-|[]]; exact (DLE _ _ IE Hc' E)) ltac:(clear - AS1 Q2; lia) Ca) as OB.
             rewrite Z5 in OB. clear - OB RW. lia.
          -- destruct STP as (_ & _ & SE0 & _). rewrite EQ0, EQ in SE0. pose proof (SE0 c0 eq_refl) as EE. injection EE as <-.
             apply HXa. apply rin_ivs_app. right. unfold XF. rewrite EQ0. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. apply rin_ivs_app; right. cbn [errph_foot rin_ivs fst snd]. left. exact RW.
  Qed.

  (* [comment removed for export] *)
  Lemma adwkG_libX : forall Lx Lx' NB S' M' M'' LE LEn fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf um' uf' m1 s1' m2 s2' (X XS : list (Z * Z))
                           (fr1' : list cell) (wee' v192' v200' v208' v224' v232' : word) (fr3' : list cell) (errv2 : word),
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' ->
    LIBMID (LEn ++ LE ++ LIB) m2 M'' -> mid_step M' M'' -> mid_newlib_ok M' M'' LEn -> mid_ctx M'' = mid_ctx M' ->
    Z.of_nat (length (mid_errblocks M'')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M'') <= ERRSTR_BYTES ->
    xpres H (drest Lx NB LE) S1c (X ++ ECH_AC14_kit.XR (mid_err M') XS) m1 m2 ->
    Forall (fun iv : Z * Z => (S1c + 16 <= fst iv /\ snd iv <= S1c + 240) \/ (S1c + 240 <= fst iv /\ snd iv <= S1c + 344)
                              \/ (exists b, In b Lx /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)) X ->
    Forall (fs_scratch H (LF1c ff fp)) XS ->
    as_RHEAP H s2' (mid_errblocks M'' ++ drest Lx' NB (LEn ++ LE)) m2 -> mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c ->
    as_rauxv_ok H m2 B -> rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> as_RFS H (LF1c ff fp) m2 -> LEDGERc s2' um' uf' ->
    rw_cells asegs m2 (S1c + 16) fr1' -> cells_size fr1' = 128%nat -> rw_cells asegs m2 (S1c + 144) (dsg2 wee' v192' v200' v208' v224' v232') ->
    rw_cells asegs m2 (S1c + 240) fr3' -> cells_size fr3' = 104%nat ->
    adwkG Lx' NB S' M'' (LEn ++ LE) fr1' wee' v192' v200' v208' v224' v232' fr3' tpl shb b2 shd um' uf' m2 s2'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until errv2. intros DW LM2 STP2 NEW2 CTX2 EC2 EB2 XP FX. eapply adwkG_libXV; [exact DW| exact LM2| exact STP2| exact NEW2| exact CTX2| exact EC2| exact EB2| exact XP|].
    eapply Forall_impl; [| exact FX]. cbn beta. intros iv [K|[K|K]]; [left; exact K| right; left; exact K| right; right; left; exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma adwkG_time : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' m2 errv2,
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m1 s1' ->
    munch [(S1c - ATIME_STACK, S1c); (A_vdso_func, A_vdso_func + 8); (errno_addr (Z_to_bv 64 ATP), errno_addr (Z_to_bv 64 ATP) + 4)] m1 m2 -> wmono asegs m1 m2 ->
    mem_inv asegs m2 -> stk asegs m2 lo S1c -> ACONST m2 -> as_rauxv_ok H m2 B ->
    as_RHEAP H s1' (mid_errblocks M' ++ drest Lx NB LE) m2 ->
    rw_cells asegs m2 A_vdso_func [C8 (Z_to_bv 64 0)] -> rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] ->
    adwkG Lx NB S' (mkMID (mid_flag M') (mid_ctx M') (mid_err M') (mid_E M') true) LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m2 s1'.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV.
    intros until errv2. intros DW MU WM MI2 STK2 AC2 AUX2 HP2 VD2 ERR2.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & _ & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    pose proof AFSB as (AF1 & AF2 & AF3 & AF4). unfold AIMG_TOP in AF1. unfold AFS_SIZE in AF2.
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    assert (ERNGv : errno_addr (Z_to_bv 64 ATP) = 12458988) by reflexivity.
    (* [comment removed for export] *)
    assert (TSW : lo <= S1c - ATIME_STACK) by (unfold ATIME_STACK; clear - LO STK0 Q2; lia).
    set (Lall := mid_errblocks M' ++ drest Lx NB LE) in *.
    pose proof (drest_sub Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    (* [comment removed for export] *)
    assert (DJhi : forall Aq nq, S1c <= Aq -> disjoint_from [(S1c - ATIME_STACK, S1c); (A_vdso_func, A_vdso_func + 8); (errno_addr (Z_to_bv 64 ATP), errno_addr (Z_to_bv 64 ATP) + 4)] Aq nq).
    { intros Aq nq HA. rewrite ERNGv. cbn [disjoint_from fst snd]. unfold ATIME_STACK, A_vdso_func. clear - HA AS1 ACB. repeat split; lia. }
    (* [comment removed for export] *)
    assert (XPV0 : xpres H Lall S1c (VDSO_X ++ ERRNO_X) m1 m2).
    { eapply (xpres_of_munch_gen H); [exact MU| exact WM|]. intros a Ha [Ca HXa]. cbn [outside fst snd].
      assert (NS : ~ (S1c - ATIME_STACK <= a < S1c)).
      { intros K. eapply ((RCI client_not_frame) s1' Lall Lall m1 a); [exact HP1| intros b Hb; exact Hb| | clear - K TSW Q2; lia].
        destruct Ca as [Ca|Ca]; [exfalso; clear - Ca K; lia| right; exact Ca]. }
      assert (NV : ~ (A_vdso_func <= a < A_vdso_func + 8)) by (intros K; apply HXa; apply rin_ivs_app; left; unfold VDSO_X; cbn [rin_ivs fst snd]; left; exact K).
      assert (NE : ~ (errno_addr (Z_to_bv 64 ATP) <= a < errno_addr (Z_to_bv 64 ATP) + 4)).
      { intros K. apply HXa. apply rin_ivs_app. right. unfold ERRNO_X. cbn [rin_ivs fst snd]. left. change ARERRNO with (errno_addr (Z_to_bv 64 ATP)). exact K. }
      clear - NS NV NE. repeat split; assumption. }
    assert (XPV : xpres H (drest Lx NB LE) S1c (VDSO_X ++ ERRNO_X) m1 m2).
    { eapply (xpres_weaken H); [exact XPV0| apply Z.le_refl| intros b Hb; subst Lall; apply in_or_app; right; exact Hb| intros q Hq; exact Hq]. }
    pose proof LM1 as (_ & MFa & _). pose proof STP as (MF1' & CX' & ER' & VD').
    eapply (adwkG_libXV Lx Lx NB S' M' _ LE [] fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf um uf m1 s1' m2 s1' VDSO_X [] fr1 wee v192 v200 v208 v224 v232 fr3 errv2); [exact DW| | | | reflexivity| exact EC| exact EB| | | apply Forall_nil| cbn [app]; exact HP2
      | exact MI2| exact AC2| exact STK2| exact AUX2| exact ERR2| | exact LED1
      | eapply rw_cells_transport; [exact FR1| exact MU| exact WM| apply DJhi; clear; lia]| exact SZ1
      | eapply rw_cells_transport; [exact FR2| exact MU| exact WM| apply DJhi; clear; lia]
      | eapply rw_cells_transport; [exact FR3| exact MU| exact WM| apply DJhi; clear; lia]| exact SZ3].
    - (* [comment removed for export] *)
      cbn [app].
      assert (XRG : forall a, rin_ivs (VDSO_X ++ ERRNO_X) a -> (A_vdso_func <= a < A_vdso_func + 8) \/ (12458988 <= a < 12458988 + 4)).
      { intros a Ha. unfold VDSO_X, ERRNO_X in Ha. cbn [rin_ivs fst snd app] in Ha. change ARERRNO with (errno_addr (Z_to_bv 64 ATP)) in Ha. rewrite ERNGv in Ha. clear - Ha. tauto. }
      assert (SUBLq : forall b, In b (LE ++ LIB) -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; right; apply SL0; apply SLL; exact Hb).
      assert (SUBEq : forall b, In b (mid_errblocks M') -> In b Lall) by (intros b Hb; subst Lall; apply in_or_app; left; exact Hb).
      assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
      eapply (LIBMID_xagree H (LE ++ LIB) Lall S1c (VDSO_X ++ ERRNO_X) m1 m2 M' x (mid_flag M') true); [exact LM1| rewrite CTX1; exact CTX| exact XPV0| exact SUBLq| exact SUBEq| | | | | | | exact VD2|].
      + intros a K HLX. destruct (XRG a K) as [K'|K']; [right; exact K'|]. exfalso. revert HLX. revert K'. clear. unfold LIBX, LIBX0, LIBXW. cbn [rin_ivs fst snd app]. intros [K1 K2] HLX. lia.
      + intros a K Rg. destruct (XRG a K) as [Kq|Kq]; unfold A_vdso_func in *; clear - Kq Rg; lia.
      + intros a K HB. pose proof (in_block_where H HH _ _ _ _ _ HP1 SUBLq HB) as W0. unfold AIMG_TOP in W0. destruct (XRG a K) as [K'|K']; unfold A_vdso_func in *; clear - K' W0; lia.
      + intros a K HB. pose proof (in_block_sh_where H HH _ _ _ _ _ HP1 SUBLq HB) as W0. rewrite S0 in W0. destruct (XRG a K) as [K'|K']; unfold A_vdso_func in *; clear - K' W0; lia.
      + intros a K HB. pose proof (in_block_sh_where H HH _ _ _ _ _ HP1 SUBEq HB) as W0. rewrite S0 in W0. destruct (XRG a K) as [K'|K']; unfold A_vdso_func in *; clear - K' W0; lia.
      + destruct MFa as (fb & MFc & MFd). exists fb. split; [| exact MFd].
        eapply rw_cells_transport; [exact MFc| exact MU| exact WM|]. rewrite ERNGv. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ fst snd].
        unfold A_mem_inited, A_vdso_func, ATIME_STACK. clear - AS1 ACB. repeat split; lia.
      + intros a K HB. pose proof (in_block_where H HH _ _ _ _ _ HP1 SUBEq HB) as W0. unfold AIMG_TOP in W0. destruct (XRG a K) as [K'|K']; unfold A_vdso_func in *; clear - K' W0; lia.
    - unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [exact MF1'| split; [intros b K; exact K| split; [intros c K; exact K| intros _; reflexivity]]].
    - exists [], []. cbn [mid_ctx mid_err app]. split; [apply Permutation_refl|]. split; [destruct (mid_ctx M'); reflexivity| destruct (mid_err M'); reflexivity].
    - cbn [mid_err app]. eapply (xpres_weaken H); [exact XPV| apply Z.le_refl| intros b Hb; exact Hb|].
      intros q Hq. apply rin_ivs_app in Hq. apply rin_ivs_app. destruct Hq as [Hq|Hq]; [left; exact Hq| right]. unfold ECH_AC14_kit.XR.
      apply rin_ivs_app; right. apply rin_ivs_app; left. unfold ERR_XE. apply rin_ivs_app; left. exact Hq.
    - apply Forall_cons; [right; right; right; reflexivity| apply Forall_nil].
    - (* [comment removed for export] *)
      eapply (ah_RFS_frame H HH); [exact RFS1| exact MU| exact WM|]. unfold afs_write_ok. rewrite ERNGv.
      apply Forall_cons; [left; cbn [fst snd]; clear - TSW CEIL AF2 ACB; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE, ATIME_STACK in *; split; lia|].
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, A_vdso_func; clear - AF1; split; lia|].
      apply Forall_cons; [left; cbn [fst snd]; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP; clear - AF1; split; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition DLOOP_CM : Z := 2^23 - 2^20.    Definition DLOOP_CF : Z := 2^23 - 2^20.
  Definition DLOOP_BYTES : Z := 124000.       Definition DLOOP_CNT : Z := 700.

  (* [comment removed for export] *)
  Definition rp_errl_stmt : Prop :=
    forall (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr1 fr3 : list cell) (wee v192 v200 v208 v224 v232 : word) (tpl um uf : Z)
           (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model) (rv : Z)
           (u0 u1 u2 a1w a2w b3 b4 b5 b6 b7 s4w s6w s9w u3 u4 u5 u6 : word),
      adwkG [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s' -> (rv = 0 \/ rv = 1) -> dnb NB ->
      uf + 8192 <= DECODE_CUM_BYTES -> um <= DECODE_CUM_BYTES ->
      as_VIS H s' msF' = MS (mkR (Z_to_bv 64 AFM_ERRL_R1) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 bt) a1w a2w b3 b4 b5 b6 b7
                                  (Z_to_bv 64 A) (Z_to_bv 64 SH) s4w (Z_to_bv 64 rv) s6w (Z_to_bv 64 Bb) (Z_to_bv 64 ff) s9w (Z_to_bv 64 ff) (Z_to_bv 64 bt) u3 u4 u5 u6)
                          F (Z_to_bv 64 P_BIO_free_all) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Definition btfree_stmt : Prop :=
    forall (NB : list block) (S' : storerep) (M' : libmid) (LE : list block) (fr1 fr3 : list cell) (wee v192 v200 v208 v224 v232 : word) (tpl um uf : Z)
           (m1 : mem) (s1' : as_St H) (msF1 : machine_state) (mo1 : Model) (ra0 : Z)
           (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6 : word) (Q : config -> Prop),
      adwkG [] NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m1 s1' -> 0 <= ra0 < 2^64 -> ra0 mod 2 = 0 -> dnb NB ->
      pf_ok (as_TR H) PF9free ra0 CH1c ->                                        (* [comment removed for export] *)
      uf + 4096 <= DECODE_CUM_BYTES -> um <= DECODE_CUM_BYTES ->
      as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) (Z_to_bv 64 bt) b1 b2 b3 b4 b5 b6 b7
                                  s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                          F (Z_to_bv 64 P_BIO_free_all) fc None m1 (seg_rom asegs) ->
      as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
      (forall (m2 : mem) (s2' : as_St H) (msF2 : machine_state) (mo2 : Model) (errv2 : word) (uf2 : Z) (XS : list (Z * Z))
              (v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 : word),
         as_VIS H s2' msF2 = MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) v0 v1 v2 sp (Z_to_bv 64 S1c) c0 c1 c2 c3 c4 c5 c6 c7
                                     s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w v3 v4 v5 v6)
                             F (ret_pc (Z_to_bv 64 ra0)) fc None m2 (seg_rom asegs) ->
         as_AKREL H s2' (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
         as_RHEAP H s2' (mid_errblocks M' ++ NB ++ (pbin, Bb, nB) :: (p, A, nA) :: LE ++ LB) m2 ->
         mem_inv asegs m2 -> ACONST m2 -> stk asegs m2 lo S1c -> stack0 m2 lo (bv_unsigned sp) ->
         rw_cells asegs m2 (errno_addr (Z_to_bv 64 ATP)) [C4 errv2] -> as_rauxv_ok H m2 B -> as_RFS H (LF1c ff fp) m2 ->
         LIBMID (LE ++ LIB) m2 M' -> STOREobj (NB ++ LE ++ LB) m2 st S' -> STORE_shad m2 st S' ->
         MEMBIO H LB m2 mb R' -> MEMBIO_shad m2 mb R' -> bytes_at asegs m2 (mb_buf R) ds ->
         (exists junk, rw_cells asegs m2 Bb [CB (length bs) bs; CB (Z.to_nat nB - length bs) junk]) -> addressable m2 Bb nB ->
         (exists junk, rw_cells asegs m2 A [CB (Z.to_nat (mb_len R)) ds; CB (Z.to_nat (nA - mb_len R)) junk]) -> addressable m2 A nA ->
         rw_cells asegs m2 S1c [CB 16 jz] -> rw_cells asegs m2 (S1c + 16) fr1 -> rw_cells asegs m2 (S1c + 144) (dsg2 wee v192 v200 v208 v224 v232) -> rw_cells asegs m2 (S1c + 240) fr3 ->
         rw_cells asegs m2 (S1c + 344) [CB (Z.to_nat KGc) jg] -> rw_cells asegs m2 (bv_unsigned sp + -104) SAVESc ->
         (exists lb, rw_cells asegs m2 ff (dff tpl lb)) -> rw_cells asegs m2 SH (dfsh (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8)) ->
         as_chain H m2 (bv_unsigned sp) CH1c ->
         Forall (fs_scratch H LF) XS -> (forall q, rin_ivs (XSFc ff fp) q -> rin_ivs XS q) -> xpres H LB (bv_unsigned sp) (XS ++ XFc) m m2 ->
         LEDGERc s2' um uf2 -> uf2 <= uf + 4096 ->
         as_SR H Q (mkCfg msF2 mo2)) ->
      as_SR H Q (mkCfg msF1 mo1).

  (* [comment removed for export] *)
  Definition rp_flat_stmt : Prop :=
    forall (M' : libmid) (LE : list block) (w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 wee v192 v200 v208 v224 v232
                                            x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : word)
           (tpl um uf : Z) (m' : mem) (s' : as_St H) (msF' : machine_state) (mo' : Model)
           (rax u0 u1 u2 a0w a1w a2w b3 b4 b5 b6 b7 s5w s9w u3 u4 u5 u6 : word),
      adwkG [] [] S M' LE (arp_sg1 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 (wz 0) (wz (ff + 80)) (wz (ff + 64)) (wz 0) (wz st) (wz (ff + 32))) wee v192 v200 v208 v224 v232
            (arp_sg3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) tpl (b8 0xf8) (b8 0xf8) (poison_bytes 256 0xf8) um uf m' s' ->
      um + errph_bytes (mid_err M') + DLOOP_CM <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + DLOOP_CF <= DECODE_CUM_BYTES ->
      dbud (drest [] [] LE) M' DLOOP_BYTES DLOOP_CNT ->
      as_VIS H s' msF' = MS (mkR rax (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) a0w a1w a2w b3 b4 b5 b6 b7
                                  (Z_to_bv 64 A) (Z_to_bv 64 SH) (Z_to_bv 64 ASHB) s5w (Z_to_bv 64 (zlength bs)) (Z_to_bv 64 Bb) (Z_to_bv 64 ff) s9w (Z_to_bv 64 ff)
                                  (Z_to_bv 64 bt) u3 u4 u5 u6)   (* [comment removed for export] *)
                          F (Z_to_bv 64 ADF_DEC) fc None m' (seg_rom asegs) ->
      as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
      as_SR H POSTc (mkCfg msF' mo').

  (* [comment removed for export] *)
  Lemma arglue_of_arp : forall raA raB tgt xv yv zv spq gpq tpq s0q s1q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q Fq fcq,
    arp_glue raA raB tgt xv yv zv -> arglue raA raB tgt (Z_to_bv 64 xv) (Z_to_bv 64 yv) (Z_to_bv 64 zv) spq gpq tpq s0q s1q s2q s3q s4q s5q s6q s7q s8q s9q s10q s11q Fq fcq.
  Proof. clear. intros until fcq. intros G. unfold arglue. intros. apply G. assumption. Qed.

  (* [comment removed for export] *)
  Lemma adw_raiseF : forall (fn : Z) (gs gsl : list byte), AROSTR fn gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < fn ->
    forall (spw gpw t0' t1' t2' s0w s1w a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6' : word)
           (Fx : bvmap 5 word) (fcx : bv 32) (msFx : machine_state) (mx : mem) (mox : Model) (sx : as_St H) (LIBc Lc : list block) (LFc : list fframe)
           (Mx : libmid) (xx : ctxinfo) (lox Bx : Z) (errvx : word) (CHc : list (Z * Z)) (ra1 ra2 ra3 line reason : Z) (Q : config -> Prop),
      as_VIS H sx msFx = MS (mkR (Z_to_bv 64 ra1) spw gpw (Z_to_bv 64 ATP) t0' t1' t2' s0w s1w a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6')
                           Fx (Z_to_bv 64 P_ERR_new) fcx None mx (seg_rom asegs) ->
      as_RHEAP H sx (mid_errblocks Mx ++ Lc) mx -> as_AKREL H sx (mkCfg msFx mox) ->
      LIBMID LIBc mx Mx -> (forall b, In b LIBc -> In b Lc) -> mid_ctx Mx = CtxReady xx -> mid_flag Mx = 1 ->
      lb_bytes (mid_errblocks Mx ++ Lc) + errph_bytes (mid_err Mx) + ERRDEBUG_BYTES <= as_LIVE_MAX H ->
      Z.of_nat (length (mid_errblocks Mx ++ Lc)) + errph_cnt (mid_err Mx) + 2 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H mx Bx -> bv_unsigned spw <= Bx -> bv_unsigned spw mod 16 = 0 ->
      stk asegs mx lox (bv_unsigned spw) -> aceil <= lox -> lox <= bv_unsigned spw - RAISE_STACK (mid_err Mx) -> errph_sh0 (mid_err Mx) mx lox spw ->
      rw_cells asegs mx (errno_addr (Z_to_bv 64 ATP)) [C4 errvx] -> mem_inv asegs mx -> ACONST mx ->
      as_RFS H LFc mx -> (length LFc + ERRPH_LF (mid_err Mx) <= AFS_MAXLIVE)%nat ->
      as_chain H mx (bv_unsigned s0w) CHc -> (forall fp' ra', In (fp', ra') CHc -> bv_unsigned spw + 16 <= fp') ->
      pf_ok (as_TR H) (PF_errnew (mid_err Mx)) ra1 CHc -> pf_ok (as_TR H) PF_errdebug ra2 CHc -> pf_ok (as_TR H) PF_errseterr ra3 CHc ->
      errph_closed_ok H (mid_err Mx) -> RAISE_COST H (mid_err Mx) <= as_AL H sx ->
      0 <= line < 2^31 -> 0 < reason < 2^23 ->
      0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
      arglue ra1 ra2 P_ERR_set_debug (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 line) (Z_to_bv 64 fn) spw gpw (Z_to_bv 64 ATP) s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w Fx fcx ->     (* [comment removed for export] *)
      arglue ra2 ra3 P_ERR_set_error (Z_to_bv 64 AERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) spw gpw (Z_to_bv 64 ATP) s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w Fx fcx ->
      (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (errv' : word)
              (LE : list block) (M' : libmid) (c : errchain) (XS : list (Z * Z)),
         as_VIS H s' msF' = MS (mkR (Z_to_bv 64 ra3) spw gpw (Z_to_bv 64 ATP) u0 u1 u2 s0w s1w b0 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                             Fx (ret_pc (Z_to_bv 64 ra3)) fcx None m' (seg_rom asegs) ->
         as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mox mo' -> mem_inv asegs m' -> ACONST m' -> stk asegs m' lox (bv_unsigned spw) -> as_rauxv_ok H m' Bx ->
         as_RHEAP H s' (mid_errblocks M' ++ LE ++ Lc) m' ->
         LIBMID (LE ++ LIBc) m' M' -> mid_step Mx M' -> mid_newlib_ok Mx M' LE ->
         mid_flag M' = 1 -> mid_ctx M' = CtxReady xx -> mid_err M' = ErrReady c -> mid_vdso M' = mid_vdso Mx -> errph_delta (mid_err Mx) LE c ->
         Z.of_nat (length (mid_errblocks M')) <= ERRSTR_CNT -> lb_bytes (mid_errblocks M') <= ERRSTR_BYTES ->
         rw_cells asegs m' (errno_addr (Z_to_bv 64 ATP)) [C4 errv'] ->
         Forall (fs_scratch H LFc) XS -> xpres H Lc (bv_unsigned spw) (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err Mx)) mx m' ->
         as_RFS H LFc m' -> as_AL H s' >= as_AL H sx - RAISE_COST H (mid_err Mx) ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msFx mox).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros fn gs gsl RFN GSNE GSL FNP. intros until Q. intros VISx HPx KRELx LMx SUBx CXx F1x BYx CNx AUXx SPBx SPAx STx CEILx LOx SH0x ERRx MIx ACx RFx LFBx CHNx CHBx P1 P2 P3 CLO ALx LNR REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    pose proof LMx as (IM & MF & CP & EPm & EX & VD & CL & FIT & GM & GE & GX & MM & MB & HT & RL & SH & BL).
    destruct Mx as [f cph eph E v]. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. subst cph f.
    unfold mid_errblocks in *. cbn [mid_flag mid_ctx mid_err mid_E mid_vdso] in *. cbn [ERRPH_mid] in EPm.
    assert (EP : ERRPH Lc mx eph) by (eapply ERRPH_mono; [exact EPm| exact SUBx]).
    assert (CPc : CTXPH Lc mx (CtxReady xx)) by (eapply (CTXPH_mono LIBc Lc SUBx); exact CP).
    unfold arglue in G1, G2. unfold araise_stmt in RAISE.
    eapply RAISE with (lo := lox) (B := Bx) (LB := Lc) (s := sx) (ph := eph) (E := E) (x := xx) (errv := errvx) (LF := LFc) (CH := CHc)
      (file := ARP_FILE) (fs := S_ARP_FILE) (fsl := K_ARP_FILE) (func := fn) (gs := gs) (gsl := gsl)
      (line := line) (lib := AERR_LIB_SSL) (reason := reason) (ra1 := ra1) (ra2 := ra2) (ra3 := ra3).
    all: try first [exact VISx| exact HPx| exact KRELx| exact AUXx| exact SPBx| exact SPAx| exact STx| exact CEILx| exact LOx| exact SH0x| exact ERRx| exact MIx| exact ACx| exact MF| exact IM| exact GM| exact RL
                    | exact EP| exact EX| exact BL| exact SH| exact CPc| exact RFx| exact LFBx| exact CHNx| exact CHBx| exact P1| exact P2| exact P3| exact CLO| exact ALx
                    | exact R_ARP_FILE| exact RFN| exact GSNE| exact GSL| exact FNP| exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E].
    all: lazymatch goal with
         | |- lb_bytes _ + raise_bytes _ <= _ => unfold raise_bytes; clear - BYx; lia
         | |- Z.of_nat _ + raise_cnt _ <= _ => unfold raise_cnt; clear - CNx; lia
         | |- Z_to_bv 64 ATP = _ => reflexivity
         | |- _ <> [] => discriminate
         | |- Z.of_nat (length S_ARP_FILE) < _ => rewrite S_ARP_FILE_len; clear; lia
         | |- 0 < ARP_FILE => unfold ARP_FILE; clear; lia
         | |- 0 < AERR_LIB_SSL < 256 => unfold AERR_LIB_SSL; clear; lia
         | |- AERR_LIB_SSL <> 2 => unfold AERR_LIB_SSL; clear; lia
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mq : mem), mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_debug) _ _ _ _) _ =>
             intros; eapply G1; assumption
         | |- forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mq : mem), mem_inv _ _ -> evt _ (fun _ => exists _ _ _ _ _ _ _ _ _ _ _ _, _ = MS _ _ (Z_to_bv 64 P_ERR_set_error) _ _ _ _) _ =>
             intros; eapply G2; assumption
         | |- ?G => idtac "ARP_RAISE_LEFT" G
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LBN c p1 p2 Ad1 Ad2
           VIS' KREL' MP' MI' AC' ST' AUX' HP' MF' IM' GM' RL' ERR' DL RSZ EP' CP' EST' SHC' XS SCR XP' RF' AL'.
    set (n1 := Z.of_nat (length S_ARP_FILE) + 1) in *. set (n2 := Z.of_nat (length gs) + 1) in *.
    set (E' := errst_raise E Ad1 p1 n1 line Ad2 p2 n2 AERR_LIB_SSL reason) in *.
    pose proof (errst_fits_raise E Ad1 p1 n1 line Ad2 p2 n2 AERR_LIB_SSL reason FIT RSZ) as FIT'. change (errst_fits E') in FIT'.
    pose proof (LIBMID_errcall H HH sx mx s' LIBc Lc (bv_unsigned spw) XS LFc LBN mx m' (mkMID 1 (CtxReady xx) eph E v) xx c E'
                  HPx SUBx LMx eq_refl RFx SCR XP' HP' CP' EP' DL EST' FIT' SHC' MF') as LM'.
    cbn [mid_vdso] in LM'.
    assert (LEN' : length (es_slots E') = 16%nat) by exact (proj1 (proj1 EST')).
    pose proof (errst_fits_bounds E' LEN' FIT') as [EC' EB'].
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LBN (mkMID 1 (CtxReady xx) (ErrReady c) E' v) c XS);
      cbn [mid_flag mid_ctx mid_err mid_E mid_vdso mid_errblocks]; try reflexivity.
    all: try first [exact VIS'| exact KREL'| exact MP'| exact MI'| exact AC'| exact ST'| exact AUX'| exact HP'| exact LM'| exact DL| exact EC'| exact EB'| exact ERR'| exact SCR| exact XP'| exact RF'| exact AL'].
    - (* [comment removed for export] *) unfold mid_step. cbn [mid_flag mid_ctx mid_err mid_vdso]. split; [reflexivity|]. split; [intros b Hb; exact Hb|].
      split; [| intros Hv; exact Hv]. intros c0 ->. cbn [errph_delta] in DL. destruct DL as [-> _]. reflexivity.
    - (* [comment removed for export] *) unfold mid_newlib_ok. cbn [mid_ctx mid_err]. exists [], LBN. split; [apply Permutation_refl|]. split; [reflexivity|].
      destruct eph as [|c0]; [exact DL|]. cbn [errph_delta] in DL. destruct DL as [_ ->]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma errph_closed_of_step : forall M', mid_step M M' -> errph_closed_ok H (mid_err M').
  Proof using MCO.
    intros M' (_ & _ & SEx & _). pose proof MCO as MC. unfold mid_closed_ok in MC. destruct (mid_err M) as [|c0] eqn:E0.
    - destruct (mid_err M') as [|c']; [exact MC| exact I].
    - rewrite (SEx c0 eq_refl). exact I.
  Qed.

  Lemma drest_LEn : forall Lx NB LE LEn, Permutation (LEn ++ drest Lx NB LE) (drest Lx NB (LEn ++ LE)).
  Proof.
    clear. intros. unfold drest. pose proof (Permutation_app_swap_app LEn (Lx ++ NB ++ TB ++ [(pbin, Bb, nB); (p, A, nA)]) (LE ++ LB)) as K.
    repeat rewrite <- app_assoc in K. cbn [app] in K. repeat rewrite <- app_assoc. cbn [app]. exact K.
  Qed.

  Lemma adwk_raise : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' msF1 mo1 (fn : Z) (gs gsl : list byte) (ra1 ra2 ra3 line reason : Z) (Q : config -> Prop)
      (t0' t1' t2' a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6' : word),
    AROSTR fn gs gsl -> gs <> [] -> Z.of_nat (length gs) < 32 -> 0 < fn ->
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf m1 s1' ->
    as_VIS H s1' msF1 = MS (mkR (Z_to_bv 64 ra1) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) t0' t1' t2' sp (Z_to_bv 64 S1c) a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6')
                        F (Z_to_bv 64 P_ERR_new) fc None m1 (seg_rom asegs) ->
    as_AKREL H s1' (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
    dbud (drest Lx NB LE) M' ERRDEBUG_BYTES 2 ->
    um + errph_bytes (mid_err M') + ERRDEBUG_BYTES <= DECODE_CUM_BYTES -> uf + errph_bytes (mid_err M') + ERRDEBUG_BYTES <= DECODE_CUM_BYTES ->
    pf_ok (as_TR H) (PF_errnew (mid_err M')) ra1 CH1c -> pf_ok (as_TR H) PF_errdebug ra2 CH1c -> pf_ok (as_TR H) PF_errseterr ra3 CH1c ->
    0 <= line < 2^31 -> 0 < reason < 2^23 ->
    0 <= ra1 < 2^64 -> ra1 mod 2 = 0 -> 0 <= ra2 < 2^64 -> ra2 mod 2 = 0 -> 0 <= ra3 < 2^64 -> ra3 mod 2 = 0 ->
    arglue ra1 ra2 P_ERR_set_debug (Z_to_bv 64 ARP_FILE) (Z_to_bv 64 line) (Z_to_bv 64 fn) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 S1c) s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w F fc ->     (* [comment removed for export] *)
    arglue ra2 ra3 P_ERR_set_error (Z_to_bv 64 AERR_LIB_SSL) (Z_to_bv 64 reason) (Z_to_bv 64 0) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) sp (Z_to_bv 64 S1c) s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w F fc ->
    (forall (u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (msF2 : machine_state) (m2 : mem) (mo2 : Model) (s2' : as_St H) (LEn : list block) (M'' : libmid) (c : errchain) (XS : list (Z * Z)),
       as_VIS H s2' msF2 = MS (mkR (Z_to_bv 64 ra3) (Z_to_bv 64 S1c) gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 S1c) b0 b1 b2 b3 b4 b5 b6 b7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w u3 u4 u5 u6)
                           F (ret_pc (Z_to_bv 64 ra3)) fc None m2 (seg_rom asegs) ->
       as_AKREL H s2' (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
       adwkG Lx NB S' M'' (LEn ++ LE) fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd (um + (errph_bytes (mid_err M') + ERRDEBUG_BYTES)) (uf + (errph_bytes (mid_err M') + ERRDEBUG_BYTES)) m2 s2' ->
       mid_step M' M'' -> mid_err M'' = ErrReady c -> errph_delta (mid_err M') LEn c ->                                              (* [comment removed for export] *)
       Forall (fs_scratch H (LF1c ff fp)) XS -> xpres H (drest Lx NB LE) S1c (XS ++ ERR_XE ++ memflag_foot ++ errph_foot (mid_err M')) m1 m2 ->   (* [comment removed for export] *)
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF1 mo1).
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH.
    intros until t6'. intros RFN GSNE GSL FNP DW VIS1 KREL1 MP1 BD UMB UFB P1 P2 P3 LNR REAS R1 R1E R2 R2E R3 R3E G1 G2 K.
    pose proof DW as (HP1 & LM1 & STP & NEW & CTX1 & EC & EB & LC & LBY & SO1 & SSH1 & SID & SPM & SND & SKI & MBO1 & MSH1 & DSm1 & DSb1 & [jb1 CBb1] & ADb1 & [ja1 CBa1] & ADa1 & BT1
                      & FR0 & FR1 & SZ1 & FR2 & FR3 & SZ3 & FRG & FRS & FF1 & FSH1 & LSH1 & RFS1 & [errv1 ERR1] & AUX1 & MI1 & AC1 & ST1 & STK1 & CHN1 & XA1 & LED1).
    destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & ND0 & STK0 & LO0 & MF0 & OBJ0 & DJA & AFSB & ACB & Q1 & Q2 & SPR). change (rp_s1 (bv_unsigned sp)) with S1c in Q1, Q2.
    assert (AS1 : aceil <= S1c) by (clear - CEIL LO STK0 Q2; lia).
    pose proof (drest_sub Lx NB LE) as (SLB & SL0 & SLE & SNB & STB & IB & IA & SLX & S3 & SLL).
    pose proof (dec_stack M M' STP) as (_ & _ & STKR & _).
    pose proof STP as (MF1' & CXS & _). pose proof (CXS x CTX) as CTX1'.
    pose proof (errph_bytes_range (mid_err M')) as EBR.
    assert (CHBx : forall fp' ra', In (fp', ra') CH1c -> S1c + 16 <= fp').
    { intros fp' ra' [E|Hin]; [injection E as <- <-; clear - Q2; lia| pose proof (CHB _ _ Hin) as CB'; clear - CB' Q2; lia]. }
    eapply (adw_raiseF fn gs gsl RFN GSNE GSL FNP (Z_to_bv 64 S1c) gp t0' t1' t2' sp (Z_to_bv 64 S1c) a0w a1w a2w a3w a4w a5w a6w a7w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3' t4' t5' t6'
              F fc msF1 m1 mo1 s1' (LE ++ LIB) (drest Lx NB LE) (LF1c ff fp) M' x lo B errv1 CH1c ra1 ra2 ra3 line reason Q VIS1 HP1 KREL1 LM1 ltac:(intros b Hb; apply SL0; apply SLL; exact Hb) CTX1' MF1').
    all: rewrite ?unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    all: try first [exact ST1| exact CEIL| exact ERR1| exact MI1| exact AC1| exact RFS1| exact CHBx| exact P1| exact P2| exact P3| exact LNR| exact REAS| exact R1| exact R1E| exact R2| exact R2E| exact R3| exact R3E| exact G1| exact G2| exact AUX1].
    all: lazymatch goal with
         | |- lb_bytes _ + errph_bytes _ + ERRDEBUG_BYTES <= _ => destruct BD as [B1 B2]; rewrite lb_bytes_app; clear - B1 EB; lia
         | |- Z.of_nat _ + errph_cnt _ + 2 <= _ => destruct BD as [B1 B2]; rewrite length_app, Nat2Z.inj_add; clear - B2 EC; lia
         | |- _ <= B => clear - SPB Q2; lia
         | |- _ mod 16 = 0 => clear - Q1; Z.div_mod_to_equations; lia
         | |- lo <= _ - _ => clear - LO STKR Q2; lia
         | |- as_chain _ _ _ _ => exact CHN1
         | |- (length _ + _ <= _)%nat => unfold LF1; cbn [length]; unfold READCFG_LF, READCFG_MAXLIVE, AFS_MAXLIVE in LFB |- *; destruct (mid_err M'); cbn [ERRPH_LF]; clear - LFB; lia
         | |- errph_closed_ok _ _ => exact (errph_closed_of_step M' STP)
         | |- RAISE_COST _ _ <= _ => unfold RAISE_COST, raise_bytes; eapply ((RCI LEDGER_pay) s1' um uf); [exact LED1| unfold ERRDEBUG_BYTES; clear - EBR; lia| unfold ERRDEBUG_BYTES; clear - EBR; lia| clear - UMB; lia| clear - UFB; lia]
         | |- errph_sh0 _ _ _ _ => eapply (errph_sh0_sub (mid_err M') m1 lo sp (Z_to_bv 64 S1c));
                                   [destruct (mid_err M'); [exact STK1| exact I]| rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q2 CEIL LO STK0; lia
                                   | rewrite unsigned_lit by (clear - Q2 SPR CEIL LO STK0 LO0; lia); clear - Q1; Z.div_mod_to_equations; lia]
         | |- ?G => idtac "ADWK_RAISE_LEFT" G
         end.
    (* [comment removed for export] *)
    intros u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' errv' LEn M'' c XS VIS' KREL' MP' MI' AC' ST' AUX' HP' LM' STEP' NEW' F' CX' ME' VD' DL' EC' EB' ERR' FXS XP' RF' AL'.
    rewrite ?unsigned_lit in ST', XP' by (clear - Q2 SPR CEIL LO STK0 LO0; lia).
    eapply (K u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 msF' m' mo' s' LEn M'' c XS VIS' KREL' (ah_mpres_trans H HH _ _ _ MP1 MP')); [| exact STEP'| exact ME'| exact DL'| exact FXS| exact XP'].
    eapply (adwkG_libX Lx Lx NB S' M' M'' LE LEn fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb shb2 shd um uf _ _ m1 s1' m' s' [] XS fr1 wee v192 v200 v208 v224 v232 fr3 errv');
      [exact DW| exact LM'| exact STEP'| exact NEW'| rewrite CX'; symmetry; exact CTX1'| exact EC'| exact EB'| cbn [app]; exact XP'| apply Forall_nil| exact FXS| | exact MI'| exact AC'| exact ST'| exact AUX'| exact ERR'| exact RF'
      | | | exact SZ1| | | exact SZ3].
    - eapply PERM; [exact HP'|]. eapply Permutation_trans; [apply Permutation_sym; apply (Permutation_app_head (mid_errblocks M'')); apply Permutation_sym; apply drest_LEn|]. rewrite app_assoc. apply Permutation_refl.
    - eapply ((RCI LEDGER_step) s1' s' um uf); [exact LED1| unfold ERRDEBUG_BYTES; clear - EBR; lia| unfold ERRDEBUG_BYTES; clear - EBR; lia| unfold RAISE_COST, raise_bytes in AL'; clear - AL'; lia].
    - eapply (xpres_rw_cells' H); [exact XP'| exact FR1| left; clear; lia| cbn [app]; eapply (ECH_AC14_kit.XR_stack H HX); [exact RFS1| exact FXS| clear - AS1; lia| pose proof LM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EBL); exact EBL]].
    - eapply (xpres_rw_cells' H); [exact XP'| exact FR2| left; clear; lia| cbn [app]; eapply (ECH_AC14_kit.XR_stack H HX); [exact RFS1| exact FXS| clear - AS1; lia| pose proof LM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EBL); exact EBL]].
    - eapply (xpres_rw_cells' H); [exact XP'| exact FR3| left; clear; lia| cbn [app]; eapply (ECH_AC14_kit.XR_stack H HX); [exact RFS1| exact FXS| clear - AS1; lia| pose proof LM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EBL); exact EBL]].
  Qed.

  (* [comment removed for export] *)
  Lemma adwkG_auxv : forall Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s',
    adwkG Lx NB S' M' LE fr1 wee v192 v200 v208 v224 v232 fr3 tpl shb b2 shd um uf m' s' -> aauxv_ok m' B.
  Proof using VIS0 A0 A1 SO SE SEO STL SSH MBO MP0 MN0 MBB MBS MSH PAY DS DSL PAYL PAYL2 NDsm LM SUBL CTX MF1 DJ6 HP KREL BUD BUDC AUX SPB BHI SPA ST CEIL LO ST0 ERR MI TP AC MCO RFS LFB ATH CHN CHB PF ALW RAE HH HX RAISE SM6 SF6 SSF8 PERM NAR NBR MST POS BTR BT_frame FRESH AUXV.
    intros until s'. intros DW.
    pose proof DW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XA1 & _).
    destruct XA1 as (XSq & FXq & _ & XP). destruct rc_facts_c as (SEQ & SIN & SBR & BLK0 & SUB0 & _).
    pose proof (aauxv_ok_bounds _ _ AUXV) as AB.
    eapply (aauxv_ok_xpres H LB (bv_unsigned sp) (XSq ++ XF M st mb R) m m' B); [exact AUXV| exact XP| exact SPB|].
    apply Forall_app. split.
    - apply Forall_forall. intros [l h] Hiv. pose proof (fs_scratch_range H HH _ _ _ RFS (proj1 (Forall_forall _ _) FXq _ Hiv)) as [K1 [_ K2]]. cbn [fst snd] in K1, K2.
      apply aauxv_win_ok_low; [exact AB| exact K2| right; unfold AAUXV_CELL; unfold AIMG_TOP in K1; clear - K1; lia].
    - unfold XF. pose proof SBR as (_ & _ & _ & SB4 & SB5 & _). unfold AIMG_TOP in SB4.
      destruct MBO as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & G4 & G5 & _) & _ & (_ & _ & _ & I4 & I5 & _) & _). unfold AIMG_TOP in G4, I4.
      apply Forall_app; split; [apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| exact SB5| right; unfold AAUXV_CELL; clear - SB4; lia]| apply Forall_nil]|].
      apply Forall_app; split; [unfold MEMBIO_foot; apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| exact G5| right; unfold AAUXV_CELL; clear - G4; lia]|];
                                apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| exact I5| right; unfold AAUXV_CELL; clear - I4; lia]| apply Forall_nil]|].
      apply Forall_app; split; [unfold ERR_XE, ERRNO_X, ERR_X; pose proof aceil_range as ACR;
                                repeat (apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| cbn [snd]; unfold ARERRNO, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main, ATP; clear - ACR; lia| cbn [fst snd]; unfold AAUXV_CELL, ARERRNO, A_err_string_lock, A_int_error_hash, A_err_string_once, A_err_string_ret, A_master_once, A_master_key, A_master_once_ret, A_tevent_once, A_tevent_ret, A_glob_tevent_reg, A_load_strings_once, A_load_strings_ret, A_optsdone, A_td_tsd_used, A_td_cancelbuf, A_keys, A_next_key, A_key_lock, A_tsd_main, ATP; clear; lia]|]); apply Forall_nil|].
      apply Forall_app; split; [unfold VDSO_X; apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| cbn [snd]; unfold A_vdso_func; pose proof aceil_range as ACR; clear - ACR; lia| cbn [fst snd]; unfold AAUXV_CELL, A_vdso_func; clear; lia]| apply Forall_nil]|].
      pose proof LM as (_ & _ & _ & EPm & _). unfold errph_foot. destruct (mid_err M) as [|c]; [apply Forall_nil|].
      cbn [ERRPH_mid] in EPm. rewrite CTX in EPm. destruct EPm as [_ CHc]. destruct CHc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I9 & Z9 & _).
      pose proof (BLK0 _ (SUB0 _ (SUBL _ I9))) as (_ & _ & _ & E4 & E5 & _). rewrite Z9 in E5. unfold AIMG_TOP in E4.
      apply Forall_cons; [apply aauxv_win_ok_low; [exact AB| exact E5| right; unfold AAUXV_CELL; clear - E4; lia]| apply Forall_nil].
  Qed.
End RC.

(* [comment removed for export] *)
Definition rp_entry_shape `{HCEIL : HeapCeil} (H : asr) : Prop :=
    forall (PF9new : ctxphase -> list (Z * list Z)),
    forall (PF9free : list (Z * list Z)),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    forall (F : bvmap 5 word),
    forall (fc : bv 32),
    forall (msF : machine_state),
    forall (m : mem),
    forall (mo : Model),
    forall (s : as_St H),
    forall (LIB LB : list block),
    forall (LF : list fframe),
    forall (M : libmid),
    forall (x : ctxinfo),
    forall (st mb lo B : Z),
    forall (S : storerep),
    forall (R : membio),
    forall (ds : list byte),
    forall (errv : word),
    forall (CH : list (Z * Z)),
      (as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 P_OSSL_ECHSTORE_read_echconfiglist) fc None m (seg_rom asegs)) ->
      (a0 = Z_to_bv 64 st) ->
      (a1 = Z_to_bv 64 mb) ->
      (STOREobj LB m st S) ->
      (es_entries S = 0) ->
      (es_entries_o S = None) ->
      (st + STORE_SIZE <= lo) ->
      (STORE_shad m st S) ->
      (MEMBIO H LB m mb R) ->
      (mb_pos R = 0) ->
      (mb_nread R = 0) ->
      (MEMBIO_below mb R lo) ->
      (MEMBIO_sep mb R) ->
      (MEMBIO_shad m mb R) ->
      (PAYLOAD_shad m R) ->
      (bytes_at asegs m (mb_buf R) ds) ->
      (zlength ds = mb_len R) ->
      (1 <= mb_len R -> exists pD, In (pD, mb_buf R, mb_len R) LB /\ forall b, In b LIB -> blk_id b <> pD) ->
      (1 <= mb_len R -> forall pD, In (pD, mb_buf R, mb_len R) LB -> pD <> es_id S) ->
      (List.NoDup (map blk_id ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R))) ->
      (LIBMID LIB m M) ->
      (forall b, In b LIB -> In b LB) ->
      (mid_ctx M = CtxReady x) ->
      (mid_flag M = 1) ->
      (forall b b', In b LIB -> In b' ((es_id S, st, STORE_SIZE) :: blocks_MEMBIO mb R) -> blk_id b <> blk_id b') ->
      (as_RHEAP H s (mid_errblocks M ++ LB) m) ->
      (as_AKREL H s (mkCfg msF mo)) ->
      (lb_bytes (mid_errblocks M ++ LB) + mid_bytes M + DECODE_BYTES + ERRSTR_BYTES <= as_LIVE_MAX H) ->
      (Z.of_nat (length (mid_errblocks M ++ LB)) + mid_cnt M + DECODE_CNT + ERRSTR_CNT <= as_LIVE_CNT_MAX H) ->
      (as_rauxv_ok H m B) ->
      (bv_unsigned sp <= B) ->
      (B < 2^64) ->
      (bv_unsigned sp mod 16 = 0) ->
      (stk asegs m lo (bv_unsigned sp)) ->
      (aceil <= lo) ->
      (lo <= bv_unsigned sp - READCFG_STACK M) ->
      (stack0 m lo (bv_unsigned sp)) ->
      (rw_cells asegs m (errno_addr tp) [C4 errv]) ->
      (mem_inv asegs m) ->
      (tp = Z_to_bv 64 ATP) ->
      (ACONST m) ->
      (mid_closed_ok H M) ->
      (as_RFS H LF m) ->
      ((length LF + READCFG_LF <= READCFG_MAXLIVE)%nat) ->
      (athr_cells m) ->
      (as_chain H m (bv_unsigned s0) CH) ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      (pf_ok (as_TR H) (PF_readcfg PF9new PF9free M) (bv_unsigned ra) CH) ->
      (READCFG_COST H M <= as_AL H s) ->
      (bv_unsigned ra mod 2 = 0) ->
    forall (p : bptr),
    forall (A nA : Z),
    forall (pbin : bptr),
    forall (Bb nB : Z),
    forall (bs : list byte),
    forall (R' : membio),
    forall (bt : Z),
    forall (TB : list block),
    forall (BT : mem -> Prop),
    forall (ff fp n : Z),
    forall (fj24 tpb fj128 fj2 jz jg e5 : list byte),
    forall (w224 : word),
      (1 <= mb_len R <= nA /\ nA <= 512 * 3) ->
      (0 <= zlength bs <= nB /\ nB <= mb_len R /\ mb_len R < OSSL_ECH_MAX_ECHCONFIG_LEN) ->
      (mb_static R R') ->
      (mb_pos R' = mb_len R) ->
      (0 <= bt < 2^64 /\ Z.of_nat (length TB) <= 7 /\ lb_bytes TB <= 3072) ->
      (forall (L : list block) (SP : Z) (X : list (Z * Z)) (m1 m2 : mem), BT m1 -> xpres H L SP X m1 m2 -> (forall b, In b TB -> In b L) -> aceil <= SP -> (forall b, In b TB -> avoids X (blk_addr b) (blk_size b) /\ shavoids X (blk_addr b) (blk_size b)) -> mem_inv asegs m2 -> BT m2) ->
      (fresh_frame H LF 6 ff fp) ->
    aauxv_ok m B ->
    rp_entry_stmt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LIB LB LF M st mb lo B S R ds CH p A nA pbin Bb nB bs R' bt TB BT ff fp n fj24 tpb fj128 fj2 jz jg e5.
