(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC5_small ECH_AC5_popfree ECH_AC13_small ECH_AC13_ext.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AEF_R1 : Z := R_ossl_echstore_entry_free_CRYPTO_free.      (* [comment removed for export] *)
Definition AEF_R2 : Z := R_ossl_echstore_entry_free_CRYPTO_free_2.    (* [comment removed for export] *)
Definition AEF_RK : Z := R_ossl_echstore_entry_free_EVP_PKEY_free.   (* [comment removed for export] *)
Definition AEF_R3 : Z := R_ossl_echstore_entry_free_CRYPTO_free_3.    (* [comment removed for export] *)
Definition AEF_R4 : Z := R_ossl_echstore_entry_free_CRYPTO_free_4.    (* [comment removed for export] *)
Definition AEF_RS : Z := R_ossl_echstore_entry_free_sk_set_thunks.    (* [comment removed for export] *)
Definition AEF_RP : Z := R_ossl_echstore_entry_free_sk_pop_free.      (* [comment removed for export] *)
Definition ASHB13 : Z := 0x7fff8000.
Definition aef_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma nodup_ids_app_ne : forall (l1 l2 : list block) b1 b2,
  List.NoDup (map blk_id (l1 ++ l2)) -> In b1 l1 -> In b2 l2 -> blk_id b1 <> blk_id b2.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b1 b2 ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ _ ND' H1 H2)].
  intros E. apply NI. rewrite map_app. apply in_or_app. right. rewrite E. apply in_map. exact H2.
Qed.
Lemma ndx_l : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l2 -> ~ In b l1.
Proof. intros l1 l2 b ND H2 H1. exact (nodup_ids_app_ne l1 l2 b b ND H1 H2 eq_refl). Qed.
Lemma ndx_r : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l1 -> ~ In b l2.
Proof. intros l1 l2 b ND H1 H2. exact (nodup_ids_app_ne l1 l2 b b ND H1 H2 eq_refl). Qed.
Lemma nd_tail : forall (l1 l2 : list block), List.NoDup (map blk_id (l1 ++ l2)) -> List.NoDup (map blk_id l2).
Proof. intros l1 l2 ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND. Qed.

Lemma perm_chain5 {A} : forall (hd : A) (B1 B2 B3 B4 B5 L L2 L3 L4 L5 L6 L7 : list A),
  Permutation (B1 ++ L2) L -> Permutation (B2 ++ L3) L2 -> Permutation (B4 ++ L4) L3 -> Permutation (B3 ++ L5) L4 ->
  Permutation (B5 ++ L6) L5 -> Permutation (hd :: L7) L6 ->
  Permutation ((hd :: B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7) L.
Proof.
  intros hd B1 B2 B3 B4 B5 L L2 L3 L4 L5 L6 L7 P1 P2 P3 P4 P5 P6.
  assert (Q : Permutation L (B1 ++ B2 ++ B4 ++ B3 ++ B5 ++ hd :: L7)).
  { eapply Permutation_trans; [apply Permutation_sym; exact P1|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P2|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P3|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P4|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_sym; exact P5|]. apply Permutation_app_head.
    apply Permutation_sym. exact P6. }
  apply Permutation_sym. eapply Permutation_trans; [exact Q|].
  change ((hd :: B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7) with (hd :: (B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ L7).
  assert (R : Permutation (B1 ++ B2 ++ B4 ++ B3 ++ B5 ++ hd :: L7) ((B1 ++ B2 ++ B3 ++ B4 ++ B5) ++ hd :: L7)).
  { rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    rewrite (app_assoc B4 B3), (app_assoc B3 B4). apply Permutation_app_tail. apply Permutation_app_comm. }
  eapply Permutation_trans; [exact R|]. apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma e_blocks_SK_with_thunk {HCEIL : HeapCeil} : forall a K w f, blocks_SK a (sk_with_thunk K w f) = blocks_SK a K.
Proof. intros. reflexivity. Qed.
Lemma e_sk_elems_with_thunk {HCEIL : HeapCeil} : forall K w f, sk_elems (sk_with_thunk K w f) = sk_elems K.
Proof. intros. reflexivity. Qed.
Lemma e_sk_free_thunk_set {HCEIL : HeapCeil} : forall K f, sk_free_thunk (sk_with_thunk K O_SK_FREETH f) = f.
Proof. intros. reflexivity. Qed.
Lemma e_sk_cap_with_thunk {HCEIL : HeapCeil} : forall K w f, sk_cap (sk_with_thunk K w f) = sk_cap K.
Proof. intros. reflexivity. Qed.
Lemma e_sk_data_with_thunk {HCEIL : HeapCeil} : forall K w f, sk_data (sk_with_thunk K w f) = sk_data K.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KEEP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma ofield_keep : forall LB LB' P o, ofield LB P o -> (forall b, In b (blocks_of P o) -> In b LB') -> ofield LB' P o.
  Proof.
    intros LB LB' P [[i n]|] OF K; cbn in OF |- *; [| exact OF]. destruct OF as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. apply K. left. reflexivity.
  Qed.
  Lemma ofield_owned : forall LB P o b, ofield LB P o -> In b (blocks_of P o) -> In b LB.
  Proof. intros LB P [[i n]|] b OF Hb; cbn in OF, Hb; [| destruct Hb]. destruct Hb as [<-|[]]. exact (proj2 (proj2 OF)). Qed.
  Lemma ofield_match : forall LB P o, ofield LB P o -> match o with None => P = 0 | Some (id, n) => In (id, P, n) LB end.
  Proof. intros LB P [[i n]|] OF; cbn in OF |- *; [exact (proj2 (proj2 OF))| exact OF]. Qed.
  Lemma ofield_inm : forall LB P o, ofield LB P o -> match o with None => True | Some (id, n) => In (id, P, n) LB end.
  Proof. intros LB P [[i n]|] OF; cbn in OF |- *; [exact (proj2 (proj2 OF))| exact I]. Qed.

  Lemma EXTobj_LB_mono : forall LB LB' m p X, EXTobj LB m p X -> (forall b, In b LB -> In b LB') -> EXTobj LB' m p X.
  Proof. intros LB LB' m p X (HC & HIN & OF) SUB. split; [exact HC|]. split; [apply SUB; exact HIN| eapply ofield_LB_mono; eauto]. Qed.

  Lemma EXTs_owned : forall LB m ps es b,
    Forall2 (fun p X => EXTobj LB m p X) ps es -> In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB.
  Proof.
    intros LB m ps es b F2. induction F2 as [|p X ps' es' E F IH]; cbn [concat map combine fst snd]; [intros []|].
    intros Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [| exact (IH Hb)].
    exact (EXTobj_owned_law LB m p X E b Hb).
  Qed.

  Lemma EXTs_frame : forall LB LB1 LB' SP m m' ps es,
    Forall2 (fun p X => EXTobj LB m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    (forall b, In b LB1 -> In b LB') ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => EXTobj LB' m' p X) ps es.
  Proof.
    intros LB LB1 LB' SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP SUB XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply EXTobj_LB_mono; [| exact SUB]. eapply (EXTobj_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact SUB| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  Lemma EXTs_shad_frame : forall LB1 SP m m' ps es,
    Forall2 (fun p X => EXT_shad m p X) ps es ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> In b LB1) ->
    xpres H LB1 SP [] m m' ->
    (forall b, In b (concat (map (fun px => blocks_EXT (fst px) (snd px)) (combine ps es))) -> blk_addr b + blk_size b <= SP) ->
    Forall2 (fun p X => EXT_shad m' p X) ps es.
  Proof.
    intros LB1 SP m m' ps es F2. induction F2 as [|p X ps' es' E F IH]; intros KEEP XP BEL; [constructor|].
    cbn [concat map combine fst snd] in KEEP, BEL.
    constructor.
    - eapply (EXT_shad_frame_law H); [exact E| | exact XP|].
      + intros b Hb. apply KEEP. apply in_or_app. left. exact Hb.
      + intros b Hb. apply BEL. apply in_or_app. left. exact Hb.
    - apply IH; [| exact XP|]; intros b Hb; [apply KEEP| apply BEL]; apply in_or_app; right; exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma SKobj_frame : forall LB LB' SP m m' a K,
    SKobj LB m a K -> (forall b, In b (blocks_SK a K) -> In b LB') -> xpres H LB' SP [] m m' -> SKobj LB' m' a K.
  Proof.
    intros LB LB' SP m m' a K SO KEEP XP.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. unfold sk_hdr_cells in HB. cbn [cells_size csize Nat.add] in HB.
    assert (HIN' : In (sk_id K, a, SK_SIZE) LB') by (apply KEEP; left; reflexivity).
    unfold SKobj. split.
    { exists pad. split; [exact PL|]. eapply (xpres_rw_cells' H); [exact XP| exact HDR| | constructor].
      right; right; left. exists (sk_id K, a, SK_SIZE). split; [exact HIN'|]. unfold sk_hdr_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold SK_SIZE. lia. }
    split; [exact POS|]. split; [exact HIN'|]. split; [exact NC|]. split; [exact CAP|]. split; [exact SRT|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    assert (DIN' : In (sk_did K, sk_data K, 8 * sk_cap K) LB').
    { apply KEEP. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
    pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact DIN'|]. split.
    - eapply (xpres_u64arr H); [exact XP| exact AR|]. split; [| constructor]. right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|].
      cbn [blk_addr blk_size fst snd]. rewrite ?length_map. lia.
    - exists junk. eapply (xpres_rw_cells' H); [exact XP| exact JK| | constructor]. right; right; left. exists (sk_did K, sk_data K, 8 * sk_cap K). split; [exact DIN'|].
      cbn [blk_addr blk_size fst snd cells_size csize]. unfold sk_num, zlength. rewrite Nat.add_0_r, Z2Nat.id by lia. lia.
  Qed.
  Lemma SKobj_owned : forall LB m a K b, SKobj LB m a K -> In b (blocks_SK a K) -> In b LB.
  Proof.
    intros LB m a K b SO Hb. destruct SO as (_ & _ & HIN & NC & _ & _ & _ & DAT).
    unfold blocks_SK in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    destruct (Z.eqb_spec (sk_cap K) 0) as [E|NE]; [destruct Hb|]. destruct Hb as [<-|[]].
    destruct DAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [lia| exact DIN].
  Qed.

  Lemma EXTS_keep : forall LB LB' SP m m' P xs,
    EXTS LB m P xs -> (forall b, In b (blocks_EXTS P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_EXTS P xs) -> blk_addr b + blk_size b <= SP) -> EXTS LB' m' P xs.
  Proof.
    intros LB LB' SP m m' P xs XS KEEP XP BEL. revert XS KEEP BEL. unfold EXTS, blocks_EXTS.
    destruct xs as [[K es]|]; intros XS KEEP BEL; [| exact XS].
    destruct XS as (XP0 & SO & LEN & F2). split; [exact XP0|]. split.
    - eapply SKobj_frame; [exact SO| intros b Hb; apply KEEP; apply in_or_app; left; exact Hb| exact XP].
    - split; [exact LEN|]. eapply (EXTs_frame LB LB' LB' SP m m'); [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| auto| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
  Lemma EXTS_owned : forall LB m P xs b, EXTS LB m P xs -> In b (blocks_EXTS P xs) -> In b LB.
  Proof.
    intros LB m P xs b. unfold EXTS, blocks_EXTS. destruct xs as [[K es]|]; intros XS Hb; [| destruct Hb].
    destruct XS as (_ & SO & _ & F2). apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [eapply SKobj_owned; eauto| eapply EXTs_owned; eauto].
  Qed.

  (* [comment removed for export] *)
  Lemma EXTS_shad_keep : forall LB' SP m m' P xs,
    EXTS_shad m P xs -> (forall b, In b (blocks_EXTS P xs) -> In b LB') -> xpres H LB' SP [] m m' ->
    (forall b, In b (blocks_EXTS P xs) -> blk_addr b + blk_size b <= SP) -> EXTS_shad m' P xs.
  Proof.
    intros LB' SP m m' P xs XSH KEEP XP BEL. revert XSH KEEP BEL. unfold EXTS_shad, blocks_EXTS.
    destruct xs as [[K es]|]; intros XSH KEEP BEL; [| exact I].
    destruct XSH as ((SH & T1 & T2) & F2). split.
    - split; [| split; [exact T1| exact T2]]. destruct SH as [SHH SHD]. split.
      + eapply (addressable_xpres_blk H); [apply KEEP; apply in_or_app; left; left; reflexivity| exact T1| exact SHH| exact XP].
      + intros NC. eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SHD NC)| exact XP].
        apply KEEP. apply in_or_app. left. unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; exact NC). right. left. reflexivity.
    - eapply EXTs_shad_frame; [exact F2| intros b Hb; apply KEEP; apply in_or_app; right; exact Hb| exact XP|].
      intros b Hb. apply BEL. apply in_or_app. right. exact Hb.
  Qed.
End KEEP.

(* [comment removed for export] *)
Section LAWS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma ENTRYobj_owned_law : EP_owned entrep ENTRYobj blocks_ENTRY.
  Proof.
    unfold EP_owned. intros LB m p x (HC & HIN & O1 & O2 & O3 & O4 & XS) b Hb.
    unfold blocks_ENTRY in Hb. destruct Hb as [<-|Hb]; [exact HIN|].
    assert (OB : forall P o, ofield LB P o -> In b (blocks_of P o) -> In b LB).
    { intros P [[i n]|] OF K; cbn in OF, K; [| destruct K]. destruct K as [<-|[]]. destruct OF as (_ & _ & K). exact K. }
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O1 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O2 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O3 Hb)|].
    apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (OB _ _ O4 Hb)|].
    eapply EXTS_owned; [exact XS| exact Hb].
  Qed.

  Lemma ENTRYobj_frame_law : ENTRYobj_frame H.
  Proof.
    unfold ENTRYobj_frame, EP_frame. intros LB LB' m m' p x SP EO KEEP XP BEL.
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & HC) & HIN & O1 & O2 & O3 & O4 & XS).
    assert (OWN := ENTRYobj_owned_law LB m p x EO).
    unfold ENTRYobj. split.
    { exists pad1, pad2, pad3, pad4. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
      eapply (xpres_rw_cells' H); [exact XP| exact HC| | constructor].
      right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [apply KEEP; left; reflexivity|]. unfold entry_cells.
      cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    split; [apply KEEP; left; reflexivity|].
    unfold blocks_ENTRY in KEEP.
    split; [apply (ofield_keep _ _ _ _ O1); intros b Hb; apply KEEP; right; apply in_or_app; left; exact Hb|].
    split; [apply (ofield_keep _ _ _ _ O2); intros b Hb; apply KEEP; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
    split; [apply (ofield_keep _ _ _ _ O3); intros b Hb; apply KEEP; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    split; [apply (ofield_keep _ _ _ _ O4); intros b Hb; apply KEEP; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    eapply (EXTS_keep H); [exact XS| intros b Hb; apply KEEP; right; do 4 (apply in_or_app; right); exact Hb| exact XP|].
    intros b Hb. apply BEL. unfold blocks_ENTRY. right. do 4 (apply in_or_app; right). exact Hb.
  Qed.

  Lemma ENTRY_shad_frame_law : ENTRY_shad_frame H.
  Proof.
    unfold ENTRY_shad_frame, eshad_frame. intros LB' m m' p x SP (TOP & SH & S1 & S2 & S3 & S4 & XSH) KEEP XP BEL.
    unfold blocks_ENTRY in KEEP, BEL.
    split; [exact TOP|]. split.
    { eapply (addressable_xpres_blk H); [apply KEEP; left; reflexivity| exact TOP| exact SH| exact XP]. }
    assert (OS : forall P o, oshad m P o -> (forall b, In b (blocks_of P o) -> In b LB') -> oshad m' P o).
    { intros P o OSH K. eapply (oshad_xpres H); [| exact OSH| exact XP]. destruct o as [[i n]|]; [| exact I]. apply K. left. reflexivity. }
    split; [apply (OS _ _ S1); intros b Hb; apply KEEP; right; apply in_or_app; left; exact Hb|].
    split; [apply (OS _ _ S2); intros b Hb; apply KEEP; right; apply in_or_app; right; apply in_or_app; left; exact Hb|].
    split; [apply (OS _ _ S3); intros b Hb; apply KEEP; right; do 2 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    split; [apply (OS _ _ S4); intros b Hb; apply KEEP; right; do 3 (apply in_or_app; right); apply in_or_app; left; exact Hb|].
    eapply (EXTS_shad_keep H); [exact XSH| intros b Hb; apply KEEP; right; do 4 (apply in_or_app; right); exact Hb| exact XP|].
    intros b Hb. apply BEL. right. do 4 (apply in_or_app; right). exact Hb.
  Qed.

  Lemma exts_cost_pos : forall xs, 0 <= exts_cost H xs.
  Proof.
    intros [[K es]|]; cbn [exts_cost]; [| lia].
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    assert (E0 : 0 <= ecost_sum extrep (ext_cost H) es).
    { induction es as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (ext_cost_pos H HH e). unfold ecost_sum in IH. lia. }
    pose proof (CF0 SK_SIZE ltac:(unfold SK_SIZE; lia)). pose proof (CF0 (Z.max (8 * sk_cap K) 0) ltac:(lia)). lia.
  Qed.
  Lemma entry_cost_pos : ecost_pos entrep (entry_cost H).
  Proof.
    unfold ecost_pos, entry_cost. intros x.
    pose proof (ocost_pos H HH (en_pname_o x)). pose proof (ocost_pos H HH (en_pub_o x)). pose proof (ocost_pos H HH (en_encoded_o x)). pose proof (ocost_pos H HH (en_suites_o x)).
    pose proof (exts_cost_pos (en_exts_o x)). pose proof (proj1 (proj2 (proj2 (ah_costs H HH))) ENTRY_SIZE ltac:(unfold ENTRY_SIZE; lia)). lia.
  Qed.
End LAWS.

(* [comment removed for export] *)
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  Section E.
    (* [comment removed for export] *)
    Variables (E : entrep) (pad1 pad2 pad3 pad4 : list byte).
    Let EC := entry_cells E pad1 pad2 pad3 pad4.
    Hypothesis L1 : length pad1 = 6%nat. Hypothesis L2 : length pad2 = 4%nat. Hypothesis L3 : length pad3 = 6%nat. Hypothesis L4 : length pad4 = 4%nat.
    Hypothesis RPN : 0 <= en_pname E < 2^64. Hypothesis RPB : 0 <= en_pub E < 2^64. Hypothesis RSU : 0 <= en_suites E < 2^64.
    Hypothesis REN : 0 <= en_encoded E < 2^64. Hypothesis RXS : 0 <= en_exts E < 2^64.

    Local Ltac prep HDR := unfold EC, entry_cells, wz, b8 in HDR.

    (* [comment removed for export] *)
    Lemma ae_seg1 :
      forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z),
        rw_cells asegs m a EC -> 0 < a -> a mod 16 = 0 -> a + ENTRY_SIZE <= lo -> accessible m a ENTRY_SIZE ->
        rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
        stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv asegs m ->
        evt asegs (fun ms' => exists m1,
            ms' = MS (mkR (Z_to_bv 64 AEF_R1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                         (Z_to_bv 64 (en_pname E)) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 87) a3 a4 a5 a6 a7
                         (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
            /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
            /\ stk asegs m1 lo (bv_unsigned sp + -32)
            /\ rw_cells asegs m1 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)
            /\ rw_cells asegs m1 a EC)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 P_ossl_echstore_entry_free) fc None m (seg_rom asegs)).
    Proof.
      intros until lo. intros HDR POS AL16 BL ACC0 GSB SHB0 ST CEIL LO MI. unfold P_ossl_echstore_entry_free, P_CRYPTO_free, AEF_R1, R_ossl_echstore_entry_free_CRYPTO_free, AECHS_FILE, ASHB13.
      unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
      prep HDR. unfold ENTRY_SIZE in *.
      pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add length] in HB.
      acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
      pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 104)) in ACC'.
      carve_frame 32%nat ST.
      do 6 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        assert (ACC : accessible mx a 104) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; constructor; [cbn; unfold AHI_LO in *; lia| constructor]) end.
      clear ACC'.
      (* [comment removed for export] *)
      step. step. ubal_by AL16. step. if_lit. step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 8).
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      finish.
      all: unfold EC, entry_cells, wz, b8; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma ae_segF :
      forall (RA RA' line ofs fld : Z) (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
        (RA = AEF_R1 /\ RA' = AEF_R2 /\ ofs = 24 /\ fld = en_pub E /\ line = 88)
        \/ (RA = AEF_RK /\ RA' = AEF_R3 /\ ofs = 96 /\ fld = en_encoded E /\ line = 90)
        \/ (RA = AEF_R3 /\ RA' = AEF_R4 /\ ofs = 40 /\ fld = en_suites E /\ line = 91) ->
        rw_cells asegs m a EC -> 0 < a -> a + ENTRY_SIZE < 2^64 -> accessible m a ENTRY_SIZE -> mem_inv asegs m ->
        evt asegs (fun ms' => exists a1x : word,
            ms' = MS (mkR (Z_to_bv 64 RA') (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 fld) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 line) a3 a4 a5 a6 a7
                         (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) /\ a1x = Z_to_bv 64 AECHS_FILE)
          (MS (mkR (Z_to_bv 64 RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 RA)) fc None m (seg_rom asegs)).
    Proof.
      intros until a. intros CASES HDR POS AB ACC MI. unfold P_CRYPTO_free, AECHS_FILE, ASHB13.
      prep HDR. unfold ENTRY_SIZE in *. pose proof (aword_range sp) as SPR. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
      destruct CASES as [(-> & -> & -> & -> & ->)|[(-> & -> & -> & -> & ->)|(-> & -> & -> & -> & ->)]];
        unfold AEF_R1, AEF_R2, AEF_RK, AEF_R3, AEF_R4, R_ossl_echstore_entry_free_CRYPTO_free, R_ossl_echstore_entry_free_CRYPTO_free_2,
               R_ossl_echstore_entry_free_EVP_PKEY_free, R_ossl_echstore_entry_free_CRYPTO_free_3, R_ossl_echstore_entry_free_CRYPTO_free_4.
      - replace (ret_pc (Z_to_bv 64 0x552704)) with (Z_to_bv 64 0x552704) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zstep. zstep. zstep. ck8_check ACC (a + 24). step. do 5 step. apply evt_done. eexists. split; reflexivity.
      - replace (ret_pc (Z_to_bv 64 0x552750)) with (Z_to_bv 64 0x552750) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zstep. zstep. zstep. ck8_check ACC (a + 96). step. do 5 step. apply evt_done. eexists. split; reflexivity.
      - replace (ret_pc (Z_to_bv 64 0x55277c)) with (Z_to_bv 64 0x55277c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zstep. zstep. zstep. ck8_check ACC (a + 40). step. do 5 step. apply evt_done. eexists. split; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma ae_segK :
      forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
        rw_cells asegs m a EC -> 0 < a -> a + ENTRY_SIZE < 2^64 -> accessible m a ENTRY_SIZE -> mem_inv asegs m ->
        evt asegs (fun ms' => exists a1x : word,
            ms' = MS (mkR (Z_to_bv 64 AEF_RK) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 0) a1x a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_EVP_PKEY_free) fc None m (seg_rom asegs))
          (MS (mkR (Z_to_bv 64 AEF_R2) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 AEF_R2)) fc None m (seg_rom asegs)).
    Proof.
      intros until a. intros HDR POS AB ACC MI. unfold P_EVP_PKEY_free, ASHB13, AEF_R2, AEF_RK, R_ossl_echstore_entry_free_CRYPTO_free_2, R_ossl_echstore_entry_free_EVP_PKEY_free.
      prep HDR. unfold ENTRY_SIZE in *. pose proof (aword_range sp) as SPR. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
      replace (ret_pc (Z_to_bv 64 0x552730)) with (Z_to_bv 64 0x552730) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep. ck8_check ACC (a + 72). step. step. step. apply evt_done. eexists. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma ae_seg6 :
      forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
        rw_cells asegs m a EC -> 0 < a -> a + ENTRY_SIZE < 2^64 -> accessible m a ENTRY_SIZE -> mem_inv asegs m ->
        evt asegs (fun ms' => exists ra',
            ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                         (Z_to_bv 64 (en_exts E)) (Z_to_bv 64 P_sk_OSSL_ECHEXT_freefunc_thunk) a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 P_OPENSSL_sk_set_thunks) fc None m (seg_rom asegs) /\ ra' = Z_to_bv 64 AEF_RS)
          (MS (mkR (Z_to_bv 64 AEF_R4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc (Z_to_bv 64 AEF_R4)) fc None m (seg_rom asegs)).
    Proof.
      intros until a. intros HDR POS AB ACC MI. unfold AEF_R4, AEF_RS, P_OPENSSL_sk_set_thunks, P_sk_OSSL_ECHEXT_freefunc_thunk, ASHB13,
        R_ossl_echstore_entry_free_CRYPTO_free_4, R_ossl_echstore_entry_free_sk_set_thunks.
      prep HDR. unfold ENTRY_SIZE in *. pose proof (aword_range sp) as SPR. pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
      replace (ret_pc (Z_to_bv 64 0x5527a8)) with (Z_to_bv 64 0x5527a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zstep. zstep. zstep. ck8_check ACC (a + 56). step. do 4 step. apply evt_done. eexists. split; reflexivity.
    Qed.
  End E.

  (* [comment removed for export] *)
  Lemma ae_seg7 :
    forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem),
      GOT_echfree m -> mem_inv asegs m ->
      evt asegs (fun ms' => exists ra',
          ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 P_ossl_echext_free) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs) /\ ra' = Z_to_bv 64 AEF_RP)
        (MS (mkR (Z_to_bv 64 AEF_RS) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEF_RS)) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros GG MI. unfold AEF_RS, AEF_RP, R_ossl_echstore_entry_free_sk_set_thunks, R_ossl_echstore_entry_free_sk_pop_free, P_OPENSSL_sk_pop_free.
    unfold GOT_echfree, A_got_ossl_echext_free, P_ossl_echext_free, P_ossl_echstore_entry_free, wz in GG |- *.
    replace (ret_pc (Z_to_bv 64 0x5527d0)) with (Z_to_bv 64 0x5527d0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    step. step. step. step. apply evt_done. eexists. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ae_seg8 :
    forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s2x : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u1,
          ms' = MS (mkR ra sp gp tp t0 u1 t2 s0 s1
                       (Z_to_bv 64 a) (Z_to_bv 64 AECHS_FILE) (Z_to_bv 64 93) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 AEF_RP) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 AEF_RP)) fc None m (seg_rom asegs)).
  Proof.
    intros until a. intros FR MI. unfold AEF_RP, R_ossl_echstore_entry_free_sk_pop_free, AECHS_FILE, P_CRYPTO_free. unfold aef_frame in FR.
    replace (ret_pc (Z_to_bv 64 0x5527e0)) with (Z_to_bv 64 0x5527e0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR.
    step. step. step. step. do 4 step. step. step. step. apply evt_done. eexists. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma alisted_outside : forall s LB m0 q A n SP a,
    as_RHEAP H s LB m0 -> In (q, A, n) LB -> aceil <= SP ->
    aclient_addr H (as_lb_remove H q LB) SP a -> A <= a < A + n -> False.
  Proof.
    intros s LB m0 q A n SP a RH HIN CE HC Ha. acb.
    pose proof (ah_blocks H HH _ _ _ _ RH HIN) as (B1 & B2 & B3 & B4 & B5 & B6 & B7). cbn [blk_addr blk_size fst snd] in *.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof (alb_remove_exact H HH q A n LB (ah_nodup H HH _ _ _ RH) HIN) as (_ & _ & RM).
    assert (QC : 0 <= aceil < AAPP_HI) by (unfold AAPP_HI; lia). pose proof (sh_below_aceil aceil QC) as SHC.
    assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_app (as_FSB H + AFS_SIZE) QB) as SB.
    assert (SH0 : forall x, 0 <= x -> ASHADOW_BASE <= sh x) by (intros x Hx; unfold sh; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
    unfold aapp, aapp_lo, aapp_hi in B7. unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
    unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *. rewrite ASHADOW_BASE_val in SH0.
    destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]].
    - lia.
    - lia.
    - destruct (proj1 (RM b) Hb) as [HbL NE].
      pose proof (ah_disj H HH _ _ _ b (q, A, n) RH HbL HIN NE) as D. cbn [blk_addr blk_size fst snd] in D. lia.
    - destruct (proj1 (RM b) Hb) as [HbL NE].
      pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
      pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). pose proof (SH0 (blk_addr b) ltac:(lia)).
      unfold AHI_LO in S4. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - lia.
    - pose proof (SH0 (as_FSB H) ltac:(unfold AIMG_TOP in F1; lia)). unfold AHI_LO in SB. destruct B7 as [[P1 P2]|[P1 P2]]; lia.
    - assert (QA : 0 <= aceil) by lia. pose proof (SH0 aceil QA). destruct B7 as [[P1 P2]|[P1 P2]]; lia.
  Qed.

  Lemma xpres_of_munch_listed : forall s LB m0 m m' q A n SP X W,
    as_RHEAP H s LB m0 -> In (q, A, n) LB -> aceil <= SP ->
    munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (aceil <= fst iv /\ snd iv <= SP) \/ (A <= fst iv /\ snd iv <= A + n)
                              \/ (forall a, fst iv <= a < snd iv -> rin_ivs X a)) W ->
    xpres H (as_lb_remove H q LB) SP X m m'.
  Proof.
    intros s LB m0 m m' q A n SP X W RH HIN CE MU WM FW.
    assert (SUBL : forall b, In b (as_lb_remove H q LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    eapply xpres_of_munch_gen; [exact MU| exact WM|].
    intros a Ha [HC HX].
    clear MU WM. induction W as [|[lo hi] W IH]; [exact I|]. cbn.
    pose proof (Forall_inv FW) as K1. cbn in K1.
    split; [| apply IH; apply (Forall_inv_tail FW)].
    destruct K1 as [[K1 K2]|[[K1 K2]|K1]].
    - intros K. acb. pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
      assert (QB : 0 <= as_FSB H + AFS_SIZE < AAPP_HI) by (unfold AAPP_HI, AFS_SIZE, AIMG_TOP in *; lia). pose proof (sh_below_aceil (as_FSB H + AFS_SIZE) QB) as SB.
      unfold aclient_addr, aimg_client, in_block, in_block_sh in HC.
      destruct HC as [HC|[HC|[(b & Hb & Hr)|[(b & Hb & Hr)|[HC|[HC|HC]]]]]]; unfold AIMG_TOP, AHI_LO, AAPP_HI, ALOWSH_LO in *.
      + lia.
      + lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH (SUBL _ Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7). lia.
      + pose proof (ah_blocks H HH _ _ _ _ RH (SUBL _ Hb)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
        pose proof (sh_aapp_range _ _ C7 C3) as (S2 & S3 & S4). unfold AHI_LO in S4. lia.
      + lia.
      + lia.
      + lia.
    - intros K. exact (alisted_outside s LB m0 q A n SP a RH HIN CE HC ltac:(lia)).
    - intros R. apply HX. apply K1. exact R.
  Qed.

  Lemma perm_rest_sub_remove : forall s m (Fr L' L : list block) q A n,
    as_RHEAP H s L m -> Permutation (Fr ++ L') L -> In (q, A, n) Fr ->
    forall b, In b L' -> In b (as_lb_remove H q L).
  Proof.
    intros s m Fr L' L q A n HP P Hq b Hb.
    pose proof (ah_nodup H HH _ _ _ HP) as ND.
    assert (HIN : In (q, A, n) L) by (eapply Permutation_in; [exact P| apply in_or_app; left; exact Hq]).
    apply (proj2 (proj2 (proj2 (alb_remove_exact H HH q A n L ND HIN)) b)).
    split; [eapply Permutation_in; [exact P| apply in_or_app; right; exact Hb]|].
    assert (ND' : List.NoDup (map blk_id (Fr ++ L'))).
    { eapply Permutation_NoDup; [| exact ND]. apply Permutation_map. apply Permutation_sym. exact P. }
    intros E. eapply (nodup_ids_app_ne Fr L' (q, A, n) b ND' Hq Hb). symmetry. exact E.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aentryfree_spec : entryfree_stmt H.
  Proof.
    unfold entryfree_stmt, efree_stmt_at. intros until CH.
    intros VIS A0 EO ESH ND HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM GG RAE. subst a0.
    unfold ENTRYFREE_STACK, FR_ossl_echstore_entry_free, SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free,
      CFREE_STACK, AFREE_STACK, FR_EVP_PKEY_free in LO.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -32) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    assert (SUBL : forall q L b, In b (as_lb_remove H q L) -> In b L) by (intros q L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    pose proof EO as ((pad1 & pad2 & pad3 & pad4 & L1 & L2 & L3 & L4 & EC) & EIN & O1 & O2 & O3 & O4 & XS).
    pose proof ESH as (TOP & SH & OS1 & OS2 & OS3 & OS4 & XSH).
    pose proof (ah_blocks H HH _ _ _ _ HP EIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. unfold ENTRY_SIZE in K3, K5, K7, TOP. unfold AAPP_HI in TOP. clear K6.
    pose proof (aapp_bounds p 104 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    pose proof (sh_aapp_range p 104 K7 ltac:(lia)) as (SR1 & SR2 & SR3). unfold AHI_LO in SR3. pose proof aceil_range as ACR.
    assert (HB : forall b, In b LB -> blk_addr b + blk_size b <= aceil).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). exact Q5. }
    assert (OWN := ENTRYobj_owned_law LB m p x EO).
    assert (BELx : forall b, In b (blocks_ENTRY p x) -> blk_addr b + blk_size b <= aceil) by (intros b Hb; apply HB; apply OWN; exact Hb).
    assert (FRNG : forall P o, ofield LB P o -> 0 <= P < 2^64).
    { intros P [[i n]|] OF; cbn in OF; [| lia]. destruct OF as (F1 & F2 & F3). pose proof (ah_blocks H HH _ _ _ _ HP F3) as (Q1 & _ & Q3 & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q1, Q3, Q5. lia. }
    pose proof (FRNG _ _ O1) as RPN. pose proof (FRNG _ _ O2) as RPB. pose proof (FRNG _ _ O3) as RSU. pose proof (FRNG _ _ O4) as REN.
    assert (RXS : 0 <= en_exts x < 2^64).
    { revert XS. unfold EXTS. destruct (en_exts_o x) as [[K es]|]; intros XS; [| lia].
      destruct XS as (X1 & SO & _). destruct SO as (_ & _ & KIN & _). pose proof (ah_blocks H HH _ _ _ _ HP KIN) as (Q1 & _ & Q3 & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q1, Q3, Q5. unfold SK_SIZE in *. lia. }
    assert (ACC0 : accessible m p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SH| lia| unfold ENTRY_SIZE; lia| unfold ENTRY_SIZE, AAPP_HI; lia]).
    (* [comment removed for export] *)
    pose proof (proj1 (proj2 (proj2 (ah_costs H HH)))) as CF0.
    pose proof (ocost_pos H HH (en_pname_o x)) as CP1. pose proof (ocost_pos H HH (en_pub_o x)) as CP2.
    pose proof (ocost_pos H HH (en_suites_o x)) as CP3. pose proof (ocost_pos H HH (en_encoded_o x)) as CP4.
    pose proof (exts_cost_pos H HH (en_exts_o x)) as CPX. pose proof (CF0 104 ltac:(lia)) as CF104.
    unfold entry_cost, ENTRY_SIZE in HAL.
    (* [comment removed for export] *)
    unfold blocks_ENTRY in ND.
    set (Bpn := blocks_of (en_pname x) (en_pname_o x)) in *. set (Bpub := blocks_of (en_pub x) (en_pub_o x)) in *.
    set (Bsu := blocks_of (en_suites x) (en_suites_o x)) in *. set (Benc := blocks_of (en_encoded x) (en_encoded_o x)) in *.
    set (BX := blocks_EXTS (en_exts x) (en_exts_o x)) in *.
    pose proof ND as ND0. cbn [map] in ND0. inversion ND0 as [|i0 l0 NI NDt]; subst i0 l0. clear ND0.
    assert (NOTHD : forall Fr, (forall b, In b Fr -> In b (Bpn ++ Bpub ++ Bsu ++ Benc ++ BX)) -> ~ In (en_id x, p, ENTRY_SIZE) Fr).
    { intros Fr SUB K. apply NI. rewrite in_map_iff. exists (en_id x, p, ENTRY_SIZE). split; [reflexivity| apply SUB; exact K]. }
    pose proof (nd_tail _ _ NDt) as NDt2. pose proof (nd_tail _ _ NDt2) as NDt3. pose proof (nd_tail _ _ NDt3) as NDt4.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply (ae_seg1 x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (lo := lo);
      [exact EC| exact K1| exact K2| unfold ENTRY_SIZE; lia| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & EC1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -32, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -32, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (GG1 : GOT_echfree m1) by (eapply GOT_echfree_across; [exact MU1| exact WM1| unfold A_got_ossl_echext_free; cbn; lia| exact GG]).
    assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold aef_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    assert (SHH1 : addressable m1 p 104).
    { unfold ENTRY_SIZE in SH. eapply addressable_transport; [exact SH| exact MU1| exact WM1|]. cbn. lia. }
    assert (OS1a : oshad m1 (en_pname x) (en_pname_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O1)| exact OS1| exact XP1]).
    assert (OS2a : oshad m1 (en_pub x) (en_pub_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O2)| exact OS2| exact XP1]).
    assert (OS3a : oshad m1 (en_suites x) (en_suites_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O3)| exact OS3| exact XP1]).
    assert (OS4a : oshad m1 (en_encoded x) (en_encoded_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O4)| exact OS4| exact XP1]).
    assert (BELX : forall b, In b BX -> blk_addr b + blk_size b <= bv_unsigned sp + -32).
    { intros b Hb. pose proof (BELx b ltac:(unfold blocks_ENTRY; right; do 4 (apply in_or_app; right); exact Hb)). lia. }
    assert (XS1 : EXTS LB m1 (en_exts x) (en_exts_o x)).
    { eapply (EXTS_keep H); [exact XS| intros b Hb; eapply EXTS_owned; [exact XS| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }
    assert (XSH1 : EXTS_shad m1 (en_exts x) (en_exts_o x)).
    { eapply (EXTS_shad_keep H); [exact XSH| intros b Hb; eapply EXTS_owned; [exact XS| exact Hb]| exact XP1| intros b Hb; specialize (BELX b Hb); lia]. }
    pose proof MP1 as MPA1.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (lo := lo) (B := B) (LB := LB) (s := s) (P := en_pname x) (o := en_pname_o x) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| exact (ofield_match _ _ _ O1)| ..]; rewrite ?unsigned_lit by (unfold AEF_R1, R_ossl_echstore_entry_free_CRYPTO_free; lia).
      all: first [exact HP1| exact KREL1| exact OS1a| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                 | exact IM1| exact GM1| unfold CFREE_STACK, AFREE_STACK; lia
                 | unfold AEF_R1; eapply pf_ok_call; [exact PF|]; unfold PF_entryfree; intros y Hy; apply in_app_iff; left; exact Hy
                 | lia | match goal with |- ?G => idtac "LEFT1:" G end]. }
    intros [msF2 mo2] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r02 & r12 & r22 & q02 & q12 & q22 & q32 & q42 & q52 & q62 & q72 & r32 & r42 & r52 & r62 & m2 & st2 & LB2 &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PERM2 & SUB2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia.
    assert (MPA2 := ah_mpres_trans H HH _ _ _ MPA1 MP2). clear MPA1 MP2.
    assert (KEEP2 : forall b, In b LB -> ~ In b Bpn -> In b LB2) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM2| exact Hb| exact Nb]).
    assert (EIN2 : In (en_id x, p, ENTRY_SIZE) LB2).
    { apply KEEP2; [exact EIN|]. apply NOTHD. intros b Hb. apply in_or_app. left. exact Hb. }
    assert (NX2 : forall b, In b (Bpub ++ Bsu ++ Benc ++ BX) -> ~ In b Bpn) by (intros b Hb; exact (ndx_l _ _ _ NDt Hb)).
    assert (O2b : ofield LB2 (en_pub x) (en_pub_o x)).
    { eapply ofield_keep; [exact O2|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O2| exact Hb]|]. apply NX2. apply in_or_app. left. exact Hb. }
    assert (O3b : ofield LB2 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O3| exact Hb]|]. apply NX2. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (O4b : ofield LB2 (en_encoded x) (en_encoded_o x)).
    { eapply ofield_keep; [exact O4|]. intros b Hb. apply KEEP2; [eapply ofield_owned; [exact O4| exact Hb]|]. apply NX2. do 2 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (KX2 : forall b, In b BX -> In b LB2).
    { intros b Hb. apply KEEP2; [eapply EXTS_owned; [exact XS| exact Hb]|]. apply NX2. do 3 (apply in_or_app; right). exact Hb. }
    assert (XS2 : EXTS LB2 m2 (en_exts x) (en_exts_o x)) by (eapply (EXTS_keep H); [exact XS1| exact KX2| exact XP2| exact BELX]).
    assert (XSH2 : EXTS_shad m2 (en_exts x) (en_exts_o x)) by (eapply (EXTS_shad_keep H); [exact XSH1| exact KX2| exact XP2| exact BELX]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP2| exact FR1| left; cbn; lia| constructor]).
    assert (EC2 : rw_cells asegs m2 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP2| exact EC1| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN2|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG2 : GOT_echfree m2) by (eapply (GOT_echfree_xpres H); [exact XP2| exact CSP| constructor| exact GG1]).
    assert (SHH2 : addressable m2 p 104) by (eapply (addressable_xpres_blk H); [exact EIN2| unfold AAPP_HI; lia| exact SHH1| exact XP2]).
    assert (ACC2 : accessible m2 p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SHH2| lia| lia| unfold AAPP_HI; lia]).
    assert (OS2c : oshad m2 (en_pub x) (en_pub_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O2b)| exact OS2a| exact XP2]).
    assert (OS3c : oshad m2 (en_suites x) (en_suites_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O3b)| exact OS3a| exact XP2]).
    assert (OS4c : oshad m2 (en_encoded x) (en_encoded_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O4b)| exact OS4a| exact XP2]).
    assert (CH2 : as_chain H m2 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XP2| exact CHS1]).
    assert (XPA2 : xpres H LB2 (bv_unsigned sp) [] m m2).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XP1| lia| exact SUB2| auto]| eapply (xpres_weaken H); [exact XP2| lia| auto| auto]]. }
    clear XP1 XP2 OS1a OS2a OS3a OS4a XS1 XSH1 FR1 EC1 SHH1 GG1 CH1 HP1 AUX1 AC1 ERR1 IM1 GM1 MI1 ST1 KREL1 VIS1.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply (ae_segF x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (RA := AEF_R1);
      [left; repeat split; reflexivity| exact EC2| exact K1| unfold ENTRY_SIZE; lia| exact ACC2| exact MI2]|].
    intros msF2b mo2b KREL2b MP2b (a1x2 & VIS2b & ->).
    assert (MPA2b := ah_mpres_trans H HH _ _ _ MPA2 MP2b). clear MPA2 MP2b.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (lo := lo) (B := B) (LB := LB2) (s := st2) (P := en_pub x) (o := en_pub_o x) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS2b| reflexivity| exact (ofield_match _ _ _ O2b)| ..]; rewrite ?unsigned_lit by (unfold AEF_R2, R_ossl_echstore_entry_free_CRYPTO_free_2; lia).
      all: first [exact HEAP2| exact KREL2b| exact OS2c| exact AUX2| exact ST2| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16'| exact AC2| exact CH2| exact CHS1
                 | exact IM2| exact GM2| unfold CFREE_STACK, AFREE_STACK; lia
                 | unfold AEF_R2; eapply pf_ok_call; [exact PF|]; unfold PF_entryfree; intros y Hy; apply in_app_iff; right; apply in_app_iff; left; exact Hy
                 | lia | match goal with |- ?G => idtac "LEFT2:" G end]. }
    intros [msF3 mo3] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r03 & r13 & r23 & q03 & q13 & q23 & q33 & q43 & q53 & q63 & q73 & r33 & r43 & r53 & r63 & m3 & st3 & LB3 &
                    VIS3 & KREL3 & MP3 & MI3 & AC3 & ST3 & ERR3 & AUX3 & PERM3 & SUB3 & XP3 & HEAP3 & IM3 & GM3 & AL3).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST3, XP3 by lia.
    assert (MPA3 := ah_mpres_trans H HH _ _ _ MPA2b MP3). clear MPA2b MP3.
    assert (KEEP3 : forall b, In b LB2 -> ~ In b Bpub -> In b LB3) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM3| exact Hb| exact Nb]).
    assert (EIN3 : In (en_id x, p, ENTRY_SIZE) LB3).
    { apply KEEP3; [exact EIN2|]. apply NOTHD. intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (NX3 : forall b, In b (Bsu ++ Benc ++ BX) -> ~ In b Bpub) by (intros b Hb; exact (ndx_l _ _ _ NDt2 Hb)).
    assert (O3c : ofield LB3 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3b|]. intros b Hb. apply KEEP3; [eapply ofield_owned; [exact O3b| exact Hb]|]. apply NX3. apply in_or_app. left. exact Hb. }
    assert (O4c : ofield LB3 (en_encoded x) (en_encoded_o x)).
    { eapply ofield_keep; [exact O4b|]. intros b Hb. apply KEEP3; [eapply ofield_owned; [exact O4b| exact Hb]|]. apply NX3. apply in_or_app. right. apply in_or_app. left. exact Hb. }
    assert (KX3 : forall b, In b BX -> In b LB3).
    { intros b Hb. apply KEEP3; [exact (KX2 b Hb)|]. apply NX3. do 2 (apply in_or_app; right). exact Hb. }
    assert (XS3 : EXTS LB3 m3 (en_exts x) (en_exts_o x)) by (eapply (EXTS_keep H); [exact XS2| exact KX3| exact XP3| exact BELX]).
    assert (XSH3 : EXTS_shad m3 (en_exts x) (en_exts_o x)) by (eapply (EXTS_shad_keep H); [exact XSH2| exact KX3| exact XP3| exact BELX]).
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP3| exact FR2| left; cbn; lia| constructor]).
    assert (EC3 : rw_cells asegs m3 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP3| exact EC2| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN3|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG3 : GOT_echfree m3) by (eapply (GOT_echfree_xpres H); [exact XP3| exact CSP| constructor| exact GG2]).
    assert (SHH3 : addressable m3 p 104) by (eapply (addressable_xpres_blk H); [exact EIN3| unfold AAPP_HI; lia| exact SHH2| exact XP3]).
    assert (ACC3 : accessible m3 p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SHH3| lia| lia| unfold AAPP_HI; lia]).
    assert (OS3d : oshad m3 (en_suites x) (en_suites_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O3c)| exact OS3c| exact XP3]).
    assert (OS4d : oshad m3 (en_encoded x) (en_encoded_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O4c)| exact OS4c| exact XP3]).
    assert (CH3 : as_chain H m3 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH2| apply (xpres_nil_apres H); exact XP3| exact CHS1]).
    assert (XPA3 : xpres H LB3 (bv_unsigned sp) [] m m3).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPA2| lia| exact SUB3| auto]| eapply (xpres_weaken H); [exact XP3| lia| auto| auto]]. }
    clear XP3 XPA2 OS2c OS3c OS4c XS2 XSH2 FR2 EC2 SHH2 ACC2 GG2 CH2 HEAP2 AUX2 AC2 ERR2 IM2 GM2 MI2 ST2 KREL2 KREL2b VIS2 VIS2b KX2 KEEP2 NX2.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3| exact VIS3| eapply (ae_segK x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS);
      [exact EC3| exact K1| unfold ENTRY_SIZE; lia| exact ACC3| exact MI3]|].
    intros msF3a mo3a KREL3a MP3a (a1x3 & VIS3a).
    assert (MPA3a := ah_mpres_trans H HH _ _ _ MPA3 MP3a). clear MPA3 MP3a.
    eapply (ahh_evt_then H HH); [exact KREL3a| exact VIS3a| eapply apkeyfree_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
      [exact ST3| exact CEIL| unfold FR_EVP_PKEY_free; lia| exact MI3| exact AC3]|].
    intros msF3k mo3k KREL3k MP3k PO. unfold sknull_post in PO.
    destruct PO as (w0 & w1 & w2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3b & VIS3k & MU3b & WM3b & MI3b & AC3b & ST3b).
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU3b, ST3b by lia.
    assert (MPA3k := ah_mpres_trans H HH _ _ _ MPA3a MP3k). clear MPA3a MP3k.
    assert (CW3 : Forall (aclient_write_ok H LB3) [(lo, bv_unsigned sp + -32)]) by (constructor; [left; cbn; lia| constructor]).
    assert (HP3b : as_RHEAP H st3 LB3 m3b) by (eapply (ah_RHEAP_frame H HH); [exact HEAP3| exact MU3b| exact WM3b| exact CW3]).
    assert (AUX3b : as_rauxv_ok H m3b B) by (eapply (ah_rauxv_frame H HH); [exact AUX3| exact MU3b| exact WM3b| exact CW3]).
    assert (ERR3b : rw_cells asegs m3b (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR3| exact MU3b| exact WM3b| unfold ATP; cbn; lia]).
    assert (IM3b : IMPL_mem m3b) by (eapply IMPL_across; [exact MU3b| exact WM3b| unfold A_malloc_impl; cbn; lia| exact IM3]).
    assert (GM3b : GOT_mem m3b) by (eapply GOT_across; [exact MU3b| exact WM3b| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM3]).
    assert (GG3b : GOT_echfree m3b) by (eapply GOT_echfree_across; [exact MU3b| exact WM3b| unfold A_got_ossl_echext_free; cbn; lia| exact GG3]).
    assert (FR3b : rw_cells asegs m3b (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR3| exact MU3b| exact WM3b| cbn; lia]).
    assert (EC3b : rw_cells asegs m3b p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply rw_cells_transport; [exact EC3| exact MU3b| exact WM3b|]. unfold entry_cells. cbn [cells_size csize Nat.add length]. cbn. lia. }
    assert (XP3b : xpres H LB3 (bv_unsigned sp + -32) [] m3 m3b)
      by (eapply (xpres_of_munch H st3 LB3 _ [] _ m3 m3 m3b); [exact HH| exact HEAP3| exact MU3b| exact WM3b|]; constructor; [left; cbn; lia| constructor]).
    assert (SHH3b : addressable m3b p 104) by (eapply addressable_transport; [exact SHH3| exact MU3b| exact WM3b|]; cbn; lia).
    assert (ACC3b : accessible m3b p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SHH3b| lia| lia| unfold AAPP_HI; lia]).
    assert (OS3e : oshad m3b (en_suites x) (en_suites_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O3c)| exact OS3d| exact XP3b]).
    assert (OS4e : oshad m3b (en_encoded x) (en_encoded_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O4c)| exact OS4d| exact XP3b]).
    assert (XS3b : EXTS LB3 m3b (en_exts x) (en_exts_o x)) by (eapply (EXTS_keep H); [exact XS3| exact KX3| exact XP3b| exact BELX]).
    assert (XSH3b : EXTS_shad m3b (en_exts x) (en_exts_o x)) by (eapply (EXTS_shad_keep H); [exact XSH3| exact KX3| exact XP3b| exact BELX]).
    assert (CH3b : as_chain H m3b (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH3| apply (xpres_nil_apres H); exact XP3b| exact CHS1]).
    assert (XPA3b : xpres H LB3 (bv_unsigned sp) [] m m3b).
    { eapply xpres_trans; [exact XPA3| eapply (xpres_weaken H); [exact XP3b| lia| auto| auto]]. }
    clear XP3b XPA3 OS3d OS4d XS3 XSH3 FR3 EC3 SHH3 ACC3 GG3 CH3 HEAP3 AUX3 AC3 ERR3 IM3 GM3 MI3 ST3 KREL3 KREL3a VIS3 VIS3a CW3 MU3b WM3b.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL3k| exact VIS3k| eapply (ae_segF x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (RA := AEF_RK);
      [right; left; repeat split; reflexivity| exact EC3b| exact K1| unfold ENTRY_SIZE; lia| exact ACC3b| exact MI3b]|].
    intros msF3c mo3c KREL3c MP3c (a1x3c & VIS3c & ->).
    assert (MPA3c := ah_mpres_trans H HH _ _ _ MPA3k MP3c). clear MPA3k MP3c.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (lo := lo) (B := B) (LB := LB3) (s := st3) (P := en_encoded x) (o := en_encoded_o x) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS3c| reflexivity| exact (ofield_match _ _ _ O4c)| ..]; rewrite ?unsigned_lit by (unfold AEF_R3, R_ossl_echstore_entry_free_CRYPTO_free_3; lia).
      all: first [exact HP3b| exact KREL3c| exact OS4e| exact AUX3b| exact ST3b| exact CEIL| exact ERR3b| exact MI3b| reflexivity| exact SP16'| exact AC3b| exact CH3b| exact CHS1
                 | exact IM3b| exact GM3b| unfold CFREE_STACK, AFREE_STACK; lia
                 | unfold AEF_R3; eapply pf_ok_call; [exact PF|]; unfold PF_entryfree; intros y Hy; do 2 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
                 | lia | match goal with |- ?G => idtac "LEFT3:" G end]. }
    intros [msF4 mo4] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r04 & r14 & r24 & q04 & q14 & q24 & q34 & q44 & q54 & q64 & q74 & r34 & r44 & r54 & r64 & m4 & st4 & LB4 &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & PERM4 & SUB4 & XP4 & HEAP4 & IM4 & GM4 & AL4).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST4, XP4 by lia.
    assert (MPA4 := ah_mpres_trans H HH _ _ _ MPA3c MP4). clear MPA3c MP4.
    assert (KEEP4 : forall b, In b LB3 -> ~ In b Benc -> In b LB4) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM4| exact Hb| exact Nb]).
    assert (EIN4 : In (en_id x, p, ENTRY_SIZE) LB4).
    { apply KEEP4; [exact EIN3|]. apply NOTHD. intros b Hb. do 3 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (O3f : ofield LB4 (en_suites x) (en_suites_o x)).
    { eapply ofield_keep; [exact O3c|]. intros b Hb. apply KEEP4; [eapply ofield_owned; [exact O3c| exact Hb]|].
      intros Kb. exact (ndx_r _ _ _ NDt3 Hb (in_or_app _ _ _ (or_introl Kb))). }
    assert (KX4 : forall b, In b BX -> In b LB4).
    { intros b Hb. apply KEEP4; [exact (KX3 b Hb)|]. exact (ndx_l _ _ _ NDt4 Hb). }
    assert (XS4 : EXTS LB4 m4 (en_exts x) (en_exts_o x)) by (eapply (EXTS_keep H); [exact XS3b| exact KX4| exact XP4| exact BELX]).
    assert (XSH4 : EXTS_shad m4 (en_exts x) (en_exts_o x)) by (eapply (EXTS_shad_keep H); [exact XSH3b| exact KX4| exact XP4| exact BELX]).
    assert (FR4 : rw_cells asegs m4 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP4| exact FR3b| left; cbn; lia| constructor]).
    assert (EC4 : rw_cells asegs m4 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP4| exact EC3b| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN4|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG4 : GOT_echfree m4) by (eapply (GOT_echfree_xpres H); [exact XP4| exact CSP| constructor| exact GG3b]).
    assert (SHH4 : addressable m4 p 104) by (eapply (addressable_xpres_blk H); [exact EIN4| unfold AAPP_HI; lia| exact SHH3b| exact XP4]).
    assert (ACC4 : accessible m4 p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SHH4| lia| lia| unfold AAPP_HI; lia]).
    assert (OS3g : oshad m4 (en_suites x) (en_suites_o x)) by (eapply (oshad_xpres H); [exact (ofield_inm _ _ _ O3f)| exact OS3e| exact XP4]).
    assert (CH4 : as_chain H m4 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH3b| apply (xpres_nil_apres H); exact XP4| exact CHS1]).
    assert (XPA4 : xpres H LB4 (bv_unsigned sp) [] m m4).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPA3b| lia| exact SUB4| auto]| eapply (xpres_weaken H); [exact XP4| lia| auto| auto]]. }
    clear XP4 XPA3b OS3e OS4e XS3b XSH3b FR3b EC3b SHH3b ACC3b GG3b CH3b HP3b AUX3b AC3b ERR3b IM3b GM3b MI3b ST3b KREL3k KREL3c VIS3k VIS3c KX3 KEEP3 NX3.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL4| exact VIS4| eapply (ae_segF x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS) with (RA := AEF_R3);
      [right; right; repeat split; reflexivity| exact EC4| exact K1| unfold ENTRY_SIZE; lia| exact ACC4| exact MI4]|].
    intros msF4b mo4b KREL4b MP4b (a1x4 & VIS4b & ->).
    assert (MPA4b := ah_mpres_trans H HH _ _ _ MPA4 MP4b). clear MPA4 MP4b.
    (* [comment removed for export] *)
    eapply (ah_seq H HH).
    { eapply (acfree_opt_spec H HH) with (lo := lo) (B := B) (LB := LB4) (s := st4) (P := en_suites x) (o := en_suites_o x) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS4b| reflexivity| exact (ofield_match _ _ _ O3f)| ..]; rewrite ?unsigned_lit by (unfold AEF_R4, R_ossl_echstore_entry_free_CRYPTO_free_4; lia).
      all: first [exact HEAP4| exact KREL4b| exact OS3g| exact AUX4| exact ST4| exact CEIL| exact ERR4| exact MI4| reflexivity| exact SP16'| exact AC4| exact CH4| exact CHS1
                 | exact IM4| exact GM4| unfold CFREE_STACK, AFREE_STACK; lia
                 | unfold AEF_R4; eapply pf_ok_call; [exact PF|]; unfold PF_entryfree; intros y Hy; do 3 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
                 | lia | match goal with |- ?G => idtac "LEFT4:" G end]. }
    intros [msF5 mo5] PO. unfold acfree_opt_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (r05 & r15 & r25 & q05 & q15 & q25 & q35 & q45 & q55 & q65 & q75 & r35 & r45 & r55 & r65 & m5 & st5 & LB5 &
                    VIS5 & KREL5 & MP5 & MI5 & AC5 & ST5 & ERR5 & AUX5 & PERM5 & SUB5 & XP5 & HEAP5 & IM5 & GM5 & AL5).
    rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST5, XP5 by lia.
    assert (MPA5 := ah_mpres_trans H HH _ _ _ MPA4b MP5). clear MPA4b MP5.
    assert (KEEP5 : forall b, In b LB4 -> ~ In b Bsu -> In b LB5) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM5| exact Hb| exact Nb]).
    assert (EIN5 : In (en_id x, p, ENTRY_SIZE) LB5).
    { apply KEEP5; [exact EIN4|]. apply NOTHD. intros b Hb. do 2 (apply in_or_app; right). apply in_or_app. left. exact Hb. }
    assert (KX5 : forall b, In b BX -> In b LB5).
    { intros b Hb. apply KEEP5; [exact (KX4 b Hb)|]. exact (ndx_l _ _ _ NDt3 (in_or_app _ _ _ (or_intror Hb))). }
    assert (XS5 : EXTS LB5 m5 (en_exts x) (en_exts_o x)) by (eapply (EXTS_keep H); [exact XS4| exact KX5| exact XP5| exact BELX]).
    assert (XSH5 : EXTS_shad m5 (en_exts x) (en_exts_o x)) by (eapply (EXTS_shad_keep H); [exact XSH4| exact KX5| exact XP5| exact BELX]).
    assert (FR5 : rw_cells asegs m5 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply (xpres_rw_cells' H); [exact XP5| exact FR4| left; cbn; lia| constructor]).
    assert (EC5 : rw_cells asegs m5 p (entry_cells x pad1 pad2 pad3 pad4)).
    { eapply (xpres_rw_cells' H); [exact XP5| exact EC4| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN5|].
      unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
    assert (GG5 : GOT_echfree m5) by (eapply (GOT_echfree_xpres H); [exact XP5| exact CSP| constructor| exact GG4]).
    assert (SHH5 : addressable m5 p 104) by (eapply (addressable_xpres_blk H); [exact EIN5| unfold AAPP_HI; lia| exact SHH4| exact XP5]).
    assert (ACC5 : accessible m5 p ENTRY_SIZE) by (unfold ENTRY_SIZE; eapply addressable_accessible; [exact SHH5| lia| lia| unfold AAPP_HI; lia]).
    assert (CH5 : as_chain H m5 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
      by (eapply (chain_via_apres H HH); [exact CH4| apply (xpres_nil_apres H); exact XP5| exact CHS1]).
    assert (XPA5 : xpres H LB5 (bv_unsigned sp) [] m m5).
    { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPA4| lia| exact SUB5| auto]| eapply (xpres_weaken H); [exact XP5| lia| auto| auto]]. }
    clear XP5 XPA4 OS3g XS4 XSH4 FR4 EC4 SHH4 ACC4 GG4 CH4 HEAP4 AUX4 AC4 ERR4 IM4 GM4 MI4 ST4 KREL4 KREL4b VIS4 VIS4b KX4 KEEP4.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL5| exact VIS5| eapply (ae_seg6 x pad1 pad2 pad3 pad4 L1 L2 L3 L4 RPN RPB RSU REN RXS);
      [exact EC5| exact K1| unfold ENTRY_SIZE; lia| exact ACC5| exact MI5]|].
    intros msF5b mo5b KREL5b MP5b (rax & VIS5b & ->).
    assert (MPA5b := ah_mpres_trans H HH _ _ _ MPA5 MP5b). clear MPA5 MP5b.
    (* [comment removed for export] *)
    assert (MID : as_SR H (fun c => exists (w0 w1 w2 c0 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 : word) m6 (st6 : as_St H) LB6,
                 as_VIS H st6 (cfg_ms c) = MS (mkR (Z_to_bv 64 AEF_RP) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 ATP) w0 w1 w2 sp (Z_to_bv 64 p)
                                    c0 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 ASHB13) s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6)
                               F (ret_pc (Z_to_bv 64 AEF_RP)) fc None m6 (seg_rom asegs)
                 /\ as_AKREL H st6 c /\ as_MPRES H mo5b (cfg_model c) /\ mem_inv asegs m6 /\ ACONST m6 /\ stk asegs m6 lo (bv_unsigned sp + -32)
                 /\ rw_cells asegs m6 (ATP + -164) [C4 errv] /\ as_rauxv_ok H m6 B
                 /\ as_RHEAP H st6 LB6 m6 /\ In (en_id x, p, ENTRY_SIZE) LB6
                 /\ Permutation (BX ++ LB6) LB5 /\ (forall b, In b LB6 -> In b LB5)
                 /\ xpres H LB6 (bv_unsigned sp) [] m m6 /\ IMPL_mem m6 /\ GOT_mem m6 /\ GOT_echfree m6
                 /\ rw_cells asegs m6 (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)
                 /\ rw_cells asegs m6 p (entry_cells x pad1 pad2 pad3 pad4) /\ addressable m6 p 104
                 /\ as_AL H st6 >= as_AL H st5 - exts_cost H (en_exts_o x))
             (mkCfg msF5b mo5b)).
    { pose proof XS5 as XS5'. unfold EXTS in XS5'. pose proof XSH5 as XSH5'. unfold EXTS_shad in XSH5'.
      assert (NDX : List.NoDup (map blk_id BX)) by (exact (nd_tail _ _ NDt4)).
      destruct (en_exts_o x) as [[K es]|] eqn:EXO.
      - (* [comment removed for export] *)
        destruct XS5' as (HPOS & SO & LEN & F2). destruct XSH5' as ((SKSH & T1 & T2) & F2SH).
        set (h := en_exts x) in *.
        set (EB := concat (map (fun px : Z * extrep => blocks_EXT (fst px) (snd px)) (combine (sk_elems K) es))) in *.
        assert (BXE : BX = blocks_SK h K ++ EB) by (unfold BX, blocks_EXTS; reflexivity).
        rewrite BXE in NDX.
        pose proof SO as SO0. destruct SO0 as (_ & _ & KIN & KNC & KCAP & _ & _ & KDAT).
        pose proof (ah_blocks H HH _ _ _ _ HEAP5 KIN) as (KB1 & KB2 & KB3 & KB4 & KB5 & KB6 & KB7). cbn [blk_addr blk_size fst snd] in KB1, KB2, KB3, KB4, KB5, KB6, KB7.
        unfold AIMG_TOP in KB4. unfold SK_SIZE in KB3, KB5, KB7. clear KB6.
        pose proof (sh_aapp_range h 56 KB7 ltac:(lia)) as (HS1 & HS2 & HS3). unfold AHI_LO in HS3.
        assert (PK : blk_id (en_id x, p, ENTRY_SIZE) <> blk_id (sk_id K, h, SK_SIZE)).
        { intros E. apply NI. rewrite in_map_iff. exists (sk_id K, h, SK_SIZE). split; [symmetry; exact E|].
          do 4 (apply in_or_app; right). rewrite BXE. apply in_or_app. left. left. reflexivity. }
        pose proof (ah_disj H HH _ _ _ _ _ HEAP5 EIN5 KIN PK) as DPK. cbn [blk_addr blk_size fst snd] in DPK. unfold ENTRY_SIZE, SK_SIZE in DPK.
        assert (DBEL : sk_cap K = 0 \/ (In (sk_did K, sk_data K, 8 * sk_cap K) LB5 /\ sk_data K + 8 * sk_cap K <= aceil /\ 4 <= sk_cap K)).
        { destruct KDAT as [[C0 _]|(C4 & _ & _ & DIN & _)]; [left; exact C0| right].
          pose proof (ah_blocks H HH _ _ _ _ HEAP5 DIN) as (_ & _ & _ & _ & Q5 & _). cbn [blk_addr blk_size fst snd] in Q5. split; [exact DIN| split; [exact Q5| exact C4]]. }
        assert (BEL : SK_below h K lo).
        { split; [unfold SK_SIZE; lia|]. destruct DBEL as [C0|(DIN & DB & _)]; [left; exact C0| right; lia]. }
        assert (SKR : SK_ranges H h K).
        { split; [exact (ah_blocks H HH _ _ _ _ HEAP5 KIN)|]. intros NC. destruct DBEL as [C0|(DIN & _ & _)]; [exfalso; exact (NC C0)|].
          exact (ah_blocks H HH _ _ _ _ HEAP5 DIN). }
        eapply (ahh_evt_then H HH); [exact KREL5b| exact VIS5b| eapply (askset_thunks_spec H) with (lo := lo) (LB := LB5) (K := K); rewrite ?unsigned_lit by lia;
          [reflexivity| reflexivity| unfold P_sk_OSSL_ECHEXT_freefunc_thunk; lia| exact SO| exact BEL| exact SKSH| exact SKR| exact AC5| exact ST5| exact CEIL| lia| exact MI5]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold skset_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a & SO6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia. unfold SK_SIZE in MU6a.
        assert (XPh : xpres H (as_lb_remove H (sk_id K) LB5) (bv_unsigned sp + -32) [] m5 m6a).
        { eapply xpres_of_munch_listed; [exact HEAP5| exact KIN| exact CSP| exact MU6a| exact WM6a|].
          apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; left; cbn; unfold SK_SIZE; lia| apply Forall_nil]. }
        assert (CW6 : Forall (aclient_write_ok H LB5) [(lo, bv_unsigned sp + -32); (h, h + 56)]).
        { apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [| apply Forall_nil].
          right; right; left. exists (sk_id K, h, SK_SIZE). split; [exact KIN| cbn; unfold SK_SIZE; lia]. }
        assert (HP6a : as_RHEAP H st5 LB5 m6a) by (eapply (ah_RHEAP_frame H HH); [exact HEAP5| exact MU6a| exact WM6a| exact CW6]).
        assert (AUX6a : as_rauxv_ok H m6a B) by (eapply (ah_rauxv_frame H HH); [exact AUX5| exact MU6a| exact WM6a| exact CW6]).
        assert (ERR6a : rw_cells asegs m6a (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR5| exact MU6a| exact WM6a| unfold ATP; cbn; lia]).
        assert (IM6a : IMPL_mem m6a) by (eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM5]).
        assert (GM6a : GOT_mem m6a) by (eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM5]).
        assert (GG6a : GOT_echfree m6a) by (eapply GOT_echfree_across; [exact MU6a| exact WM6a| unfold A_got_ossl_echext_free; cbn; lia| exact GG5]).
        assert (FR6a : rw_cells asegs m6a (bv_unsigned sp + -32) (aef_frame s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6a| exact WM6a| cbn; lia]).
        assert (EC6a : rw_cells asegs m6a p (entry_cells x pad1 pad2 pad3 pad4)).
        { eapply rw_cells_transport; [exact EC5| exact MU6a| exact WM6a|]. unfold entry_cells. cbn [cells_size csize Nat.add length]. cbn. lia. }
        assert (S0 : sh AIMG_TOP = 0x80178800) by reflexivity.
        assert (SHH6a : addressable m6a p 104).
        { eapply addressable_transport; [exact SHH5| exact MU6a| exact WM6a|]. cbn. rewrite S0 in SR1.
          destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia. }
        assert (SKSH6a : SK_shad m6a h K).
        { destruct SKSH as [SKH SKD]. split.
          - eapply addressable_transport; [exact SKH| exact MU6a| exact WM6a|]. unfold SK_SIZE. cbn. rewrite S0 in HS1.
            destruct KB7 as [[P1 P2]|[P1 P2]]; unfold ALOWSH_LO, AHI_LO in *; lia.
          - intros NC. destruct DBEL as [C0|(DIN & DB & C4)]; [exfalso; exact (NC C0)|].
            eapply (addressable_xpres_blk H); [| exact (T2 NC)| exact (SKD NC)| exact XPh].
            apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HEAP5) KIN)) _)). split; [exact DIN|].
            cbn [blk_id fst snd]. intros E.
            assert (ND2 : List.NoDup (map blk_id (blocks_SK h K))) by (rewrite map_app in NDX; apply NoDup_app_remove_r in NDX; exact NDX).
            unfold blocks_SK in ND2. replace (sk_cap K =? 0) with false in ND2 by (symmetry; apply Z.eqb_neq; exact NC).
            cbn [map blk_id fst snd] in ND2. inversion ND2 as [|i1 l1 NI1 _]; subst. apply NI1. left. exact E. }
        assert (KEB : forall b, In b EB -> In b (as_lb_remove H (sk_id K) LB5)).
        { intros b Hb. apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HEAP5) KIN)) b)).
          split; [apply KX5; rewrite BXE; apply in_or_app; right; exact Hb|].
          intros E. eapply (nodup_ids_app_ne (blocks_SK h K) EB); [exact NDX| left; reflexivity| exact Hb| symmetry; exact E]. }
        assert (BELE : forall b, In b EB -> blk_addr b + blk_size b <= bv_unsigned sp + -32) by (intros b Hb; apply BELX; rewrite BXE; apply in_or_app; right; exact Hb).
        assert (F26a : Forall2 (fun q X => EXTobj LB5 m6a q X) (sk_elems K) es).
        { eapply (EXTs_frame H LB5 (as_lb_remove H (sk_id K) LB5) LB5 (bv_unsigned sp + -32) m5 m6a); [exact F2| exact KEB| exact (SUBL _ _)| exact XPh| exact BELE]. }
        assert (F2SH6a : Forall2 (fun q X => EXT_shad m6a q X) (sk_elems K) es).
        { eapply (EXTs_shad_frame H (as_lb_remove H (sk_id K) LB5) (bv_unsigned sp + -32) m5 m6a); [exact F2SH| exact KEB| exact XPh| exact BELE]. }
        assert (CH6a : as_chain H m6a (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH))
          by (eapply (chain_via_apres H HH); [exact CH5| apply (xpres_nil_apres H); exact XPh| exact CHS1]).
        (* [comment removed for export] *)
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply ae_seg7; [exact GG6a| exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        (* [comment removed for export] *)
        pose proof (apopfree_exts_spec H HH) as PFX. unfold popfree_exts_stmt, skpopfree_stmt_gen in PFX.
        specialize (PFX (aextfree_spec H HH) (EXTobj_frame_law H) EXTobj_owned_law (GOT_echfree_frame H) (EXT_shad_frame_law H) (ext_cost_pos H HH)
                        ltac:(unfold P_ossl_echext_free; lia) ltac:(reflexivity)).
        pose proof (CF0 56 ltac:(lia)) as CF56. pose proof (CF0 (8 * sk_cap K) ltac:(lia)) as CFD.
        assert (E0 : 0 <= ecost_sum extrep (ext_cost H) es).
        { clear - HH. induction es as [|e es IH]; cbn [ecost_sum fold_right]; [lia|]. pose proof (ext_cost_pos H HH e). unfold ecost_sum in IH. lia. }
        assert (CX : exts_cost H (Some (K, es)) = ecost_sum extrep (ext_cost H) es + as_Cf H (8 * sk_cap K) + as_Cf H SK_SIZE).
        { cbn [exts_cost]. rewrite (Z.max_l (8 * sk_cap K) 0) by lia. reflexivity. }
        rewrite CX in CPX |- *. unfold SK_SIZE in CPX, CX |- *.
        eapply (ah_seq H HH).
        { eapply PFX with (a := h) (K := sk_with_thunk K O_SK_FREETH P_sk_OSSL_ECHEXT_freefunc_thunk) (xs := es) (lo := lo) (B := B) (LB := LB5) (s := st5) (errv := errv)
                          (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
            rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk, ?e_sk_free_thunk_set, ?e_sk_cap_with_thunk;
            [exact VIS6b| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by (unfold AEF_RP, R_ossl_echstore_entry_free_sk_pop_free; lia).
          all: first [exact SO6a| exact LEN| exact F26a| exact F2SH6a| exact NDX| exact HP6a| exact KREL6b| exact AUX6a| exact ST6a| exact CEIL| exact ERR6a| exact MI6a
                     | reflexivity| exact SP16'| exact AC6a| exact CH6a| exact CHS1| exact IM6a| exact GM6a| exact GG6a
                     | unfold SK_shad; rewrite ?e_sk_cap_with_thunk, ?e_sk_data_with_thunk; exact SKSH6a
                     | unfold is_sk_freefunc_thunk; left; reflexivity
                     | unfold SKPOPFREE_STACK, EXTFREE_STACK, FR_ossl_echext_free, FR_sk_pop_free, CFREE_STACK, AFREE_STACK; lia
                     | unfold AEF_RP; eapply pf_ok_call; [exact PF|]; unfold PF_entryfree; intros y Hy; do 4 (apply in_app_iff; right); apply in_app_iff; left; exact Hy
                     | unfold SK_SIZE; lia | match goal with |- ?G => idtac "LEFTP:" G end]. }
        clear PFX. intros [msF6 mo6] PO. unfold skpopfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & st6 & LB6 &
                        VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & PERM6 & HP6 & XP6 & IM6 & GM6 & GG6 & AL6).
        rewrite ?e_blocks_SK_with_thunk, ?e_sk_elems_with_thunk in PERM6. fold EB in PERM6. cbn [sk_cap sk_with_thunk] in AL6.
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST6, XP6 by lia.
        pose proof PERM6 as P6. rewrite app_assoc in P6.
        assert (SUB65 : forall b, In b LB6 -> In b LB5) by (intros b Hb; eapply Permutation_in; [exact P6| apply in_or_app; right; exact Hb]).
        assert (EIN6 : In (en_id x, p, ENTRY_SIZE) LB6).
        { eapply perm_in_rest; [exact P6| exact EIN5|]. apply NOTHD. intros b Hb. do 4 (apply in_or_app; right). rewrite BXE. exact Hb. }
        assert (SUBR : forall b, In b LB6 -> In b (as_lb_remove H (sk_id K) LB5)).
        { eapply perm_rest_sub_remove; [exact HEAP5| exact P6|]. apply in_or_app. left. left. reflexivity. }
        apply (ah_done H HH). cbn [cfg_ms cfg_model].
        exists v0, v1, v2, e0, e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, st6, LB6.
        split; [exact VIS6|]. split; [exact KREL6|]. split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|]. split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [rewrite unsigned_lit in ERR6 by (unfold ATP; lia); exact ERR6|]. split; [exact AUX6|]. split; [exact HP6|]. split; [exact EIN6|].
        split; [rewrite BXE; first [exact P6| rewrite app_assoc; exact P6| rewrite <- app_assoc; exact P6]|]. split; [exact SUB65|].
        split.
        { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPA5| lia| exact SUB65| auto]|].
          eapply xpres_trans; [eapply (xpres_weaken H); [exact XPh| lia| exact SUBR| auto]|].
          eapply (xpres_weaken H); [exact XP6| lia| auto| auto]. }
        split; [exact IM6|]. split; [exact GM6|]. split; [exact GG6|].
        split; [eapply (xpres_rw_cells' H); [exact XP6| exact FR6a| left; cbn; lia| constructor]|].
        split.
        { eapply (xpres_rw_cells' H); [exact XP6| exact EC6a| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN6|].
          unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
        split; [eapply (addressable_xpres_blk H); [exact EIN6| unfold AAPP_HI; lia| exact SHH6a| exact XP6]|].
        unfold SK_SIZE in AL6. lia.
      - (* [comment removed for export] *)
        assert (BXE : BX = []) by (unfold BX, blocks_EXTS; reflexivity).
        assert (H0 : en_exts x = 0) by exact XS5'. rewrite H0 in VIS5b.
        eapply (ahh_evt_then H HH); [exact KREL5b| exact VIS5b| eapply askset_thunks_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST5| exact CEIL| lia| exact MI5| exact AC5]|].
        intros msF6a mo6a KREL6a MP6a PO. unfold sknull_post in PO.
        destruct PO as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m6a & VIS6a & MU6a & WM6a & MI6a & AC6a & ST6a).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6a, ST6a by lia.
        assert (GG6a : GOT_echfree m6a) by (eapply GOT_echfree_across; [exact MU6a| exact WM6a| unfold A_got_ossl_echext_free; cbn; lia| exact GG5]).
        eapply (ahh_evt_then H HH); [exact KREL6a| exact VIS6a| eapply ae_seg7; [exact GG6a| exact MI6a]|].
        intros msF6b mo6b KREL6b MP6b (rax6 & VIS6b & ->).
        eapply (ahh_evt H HH); [exact KREL6b| exact VIS6b| eapply ask_pop_free_null_spec with (lo := lo); rewrite ?unsigned_lit by lia;
          [exact ST6a| exact CEIL| unfold FR_sk_pop_free; lia| exact MI6a| exact AC6a]|].
        intros msF6 mo6 KREL6 MP6 PO. unfold sknull_post in PO.
        destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & m6 & VIS6 & MU6 & WM6 & MI6 & AC6 & ST6).
        rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in MU6, ST6 by lia.
        assert (CW6 : Forall (aclient_write_ok H LB5) [(lo, bv_unsigned sp + -32)]) by (constructor; [left; cbn; lia| constructor]).
        assert (XPa : xpres H LB5 (bv_unsigned sp + -32) [] m5 m6a)
          by (eapply (xpres_of_munch H st5 LB5 _ [] _ m5 m5 m6a); [exact HH| exact HEAP5| exact MU6a| exact WM6a|]; constructor; [left; cbn; lia| constructor]).
        assert (HP6a : as_RHEAP H st5 LB5 m6a) by (eapply (ah_RHEAP_frame H HH); [exact HEAP5| exact MU6a| exact WM6a| exact CW6]).
        assert (XPb : xpres H LB5 (bv_unsigned sp + -32) [] m6a m6)
          by (eapply (xpres_of_munch H st5 LB5 _ [] _ m6a m6a m6); [exact HH| exact HP6a| exact MU6| exact WM6|]; constructor; [left; cbn; lia| constructor]).
        assert (XPab : xpres H LB5 (bv_unsigned sp + -32) [] m5 m6) by (eapply xpres_trans; [exact XPa| exact XPb]).
        cbn [cfg_ms cfg_model].
        exists v0, v1, v2, (Z_to_bv 64 0), e1, e2, e3, e4, e5, e6, e7, v3, v4, v5, v6, m6, st5, LB5.
        split; [exact VIS6|]. split; [exact KREL6|].
        split; [eapply (ah_mpres_trans H HH); [| exact MP6]; eapply (ah_mpres_trans H HH); [exact MP6a| exact MP6b]|].
        split; [exact MI6|]. split; [exact AC6|]. split; [exact ST6|].
        split; [eapply rw_cells_transport; [| exact MU6| exact WM6| unfold ATP; cbn; lia]; eapply rw_cells_transport; [exact ERR5| exact MU6a| exact WM6a| unfold ATP; cbn; lia]|].
        split. { eapply (ah_rauxv_frame H HH); [| exact MU6| exact WM6| exact CW6]. eapply (ah_rauxv_frame H HH); [exact AUX5| exact MU6a| exact WM6a| exact CW6]. }
        split. { eapply (ah_RHEAP_frame H HH); [exact HP6a| exact MU6| exact WM6| exact CW6]. }
        split; [exact EIN5|]. rewrite BXE. cbn [app]. split; [apply Permutation_refl|]. split; [auto|].
        split. { eapply xpres_trans; [exact XPA5|]. eapply (xpres_weaken H); [exact XPab| lia| auto| auto]. }
        split; [eapply IMPL_across; [exact MU6| exact WM6| unfold A_malloc_impl; cbn; lia|]; eapply IMPL_across; [exact MU6a| exact WM6a| unfold A_malloc_impl; cbn; lia| exact IM5]|].
        split; [eapply GOT_across; [exact MU6| exact WM6| unfold A_got_CRYPTO_malloc; cbn; lia|]; eapply GOT_across; [exact MU6a| exact WM6a| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM5]|].
        split; [eapply GOT_echfree_across; [exact MU6| exact WM6| unfold A_got_ossl_echext_free; cbn; lia| exact GG6a]|].
        split; [eapply (xpres_rw_cells' H); [exact XPab| exact FR5| left; cbn; lia| constructor]|].
        split.
        { eapply (xpres_rw_cells' H); [exact XPab| exact EC5| | constructor]. right; right; left. exists (en_id x, p, ENTRY_SIZE). split; [exact EIN5|].
          unfold entry_cells. cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold ENTRY_SIZE. lia. }
        split; [eapply (addressable_xpres_blk H); [exact EIN5| unfold AAPP_HI; lia| exact SHH5| exact XPab]|].
        cbn [exts_cost]. lia. }
    (* [comment removed for export] *)
    eapply (ah_seq H HH); [exact MID|]. clear MID.
    intros [msF6 mo6] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (k0 & k1 & k2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & k3 & k4 & k5 & k6 & m6 & st6 & LB6 &
                    VIS6 & KREL6 & MP6 & MI6 & AC6 & ST6 & ERR6 & AUX6 & HP6 & EIN6 & PERMX & SUB65 & XPM & IM6 & GM6 & GG6 & FR6 & EC6 & SHH6 & AL6).
    assert (MPA6 := ah_mpres_trans H HH _ _ _ MPA5b MP6). clear MPA5b MP6.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL6| exact VIS6| eapply ae_seg8; [exact FR6| exact MI6]|].
    intros msF7 mo7 KREL7 MP7 (u1x & VIS7).
    assert (MPA7 := ah_mpres_trans H HH _ _ _ MPA6 MP7). clear MPA6 MP7.
    unfold aef_frame in FR6. release_frame FR6 ST6 (bv_unsigned sp). rename ST6 into ST7.
    pose proof (rw_cells_flatten _ _ _ _ EC6) as ECB. unfold entry_cells in ECB. cbn [cells_size csize Nat.add] in ECB.
    assert (CH7 : as_chain H m6 (bv_unsigned s0) CH).
    { eapply (chain_via_apres H HH); [exact CHN| apply (xpres_nil_apres H); exact XPM| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. }
    (* [comment removed for export] *)
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB6) (s := st6) (p := en_id x) (n := ENTRY_SIZE) (errv := errv) (CH := CH);
        [exact VIS7| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: first [exact HP6| exact KREL7| exact EIN6| exact AUX6| exact SPB| exact ST7| exact CEIL| exact ERR6| exact MI6| reflexivity| exact SP16| exact AC6| exact CH7| exact CHS
                 | unfold ENTRY_SIZE; exact ECB| unfold ENTRY_SIZE; exact SHH6| exact IM6| exact GM6| exact RAE| unfold CFREE_STACK, AFREE_STACK; lia
                 | eapply pf_ok_incl; [exact PF|]; unfold PF_entryfree; intros y Hy; do 5 (apply in_app_iff; right); exact Hy
                 | unfold ENTRY_SIZE; lia | match goal with |- ?G => idtac "LEFTT:" G end]. }
    intros [msF8 mo8] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (z0 & z1 & z2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & z3 & z4 & z5 & z6 & m8 & st8 &
                    VIS8 & KREL8 & MP8 & MI8 & AC8 & ST8 & ERR8 & AUX8 & XP8 & HEAP8 & IM8 & GM8 & AL8).
    unfold efree_post. cbn [cfg_ms cfg_model].
    exists z0, z1, z2, e0, e1, e2, e3, e4, e5, e6, e7, z3, z4, z5, z6, m8, st8, (as_lb_remove H (en_id x) LB6).
    split; [exact VIS8|]. split; [exact KREL8|]. split; [eapply (ah_mpres_trans H HH); [exact MPA7| exact MP8]|].
    split; [exact MI8|]. split; [exact AC8|]. split; [exact ST8|].
    split; [rewrite unsigned_lit by (unfold ATP; lia); rewrite unsigned_lit in ERR8 by (unfold ATP; lia); exact ERR8|]. split; [exact AUX8|].
    split.
    { unfold blocks_ENTRY. fold Bpn Bpub Bsu Benc BX.
      apply (perm_chain5 (en_id x, p, ENTRY_SIZE) Bpn Bpub Bsu Benc BX LB LB2 LB3 LB4 LB5 LB6);
        [exact PERM2| exact PERM3| exact PERM4| exact PERM5| exact PERMX| eapply (alb_remove_perm H HH); [exact HP6| exact EIN6]]. }
    split; [exact HEAP8|].
    split. { eapply xpres_trans; [eapply (xpres_weaken H); [exact XPM| lia| exact (SUBL _ _)| auto]| exact XP8]. }
    split; [exact IM8|]. split; [exact GM8|].
    split; [eapply (GOT_echfree_xpres H); [exact XP8| exact CSP0| constructor| exact GG6]|].
    unfold entry_cost, ENTRY_SIZE. unfold ENTRY_SIZE in AL8. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma apopfree_entries_spec : popfree_entries_stmt H.
  Proof. unfold popfree_entries_stmt. apply (askpopfree_spec H HH). Qed.
End W.
