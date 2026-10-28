(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec TacX ZBridge.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition NF (k : Z) : Z := 2 ^ (14 - k).                        (* [comment removed for export] *)
Definition KMAX : Z := 6.                                          (* [comment removed for export] *)
Definition slot_ok (k pos : Z) : Prop := 0 <= k <= KMAX /\ 0 <= pos < NF k.
Definition flag_addr (fsb k pos : Z) : Z := fsb + AFS_HDR - 2 ^ (15 - k) + pos.
Definition frame_addr (fsb k pos : Z) : Z := fsb + AFS_HDR + k * 2 ^ 20 + pos * fsz k.

Lemma AFS_SIZE_val : AFS_SIZE = AFS_HDR + 11 * 2 ^ 20. Proof. reflexivity. Qed.

Lemma class_cases : forall k, 0 <= k <= KMAX ->
  (k = 0 /\ NF k = 16384 /\ 2 ^ (15 - k) = 32768 /\ fsz k = 64 /\ fshn k = 8)
  \/ (k = 1 /\ NF k = 8192 /\ 2 ^ (15 - k) = 16384 /\ fsz k = 128 /\ fshn k = 16)
  \/ (k = 2 /\ NF k = 4096 /\ 2 ^ (15 - k) = 8192 /\ fsz k = 256 /\ fshn k = 32)
  \/ (k = 3 /\ NF k = 2048 /\ 2 ^ (15 - k) = 4096 /\ fsz k = 512 /\ fshn k = 64)
  \/ (k = 4 /\ NF k = 1024 /\ 2 ^ (15 - k) = 2048 /\ fsz k = 1024 /\ fshn k = 128)
  \/ (k = 5 /\ NF k = 512 /\ 2 ^ (15 - k) = 1024 /\ fsz k = 2048 /\ fshn k = 256)
  \/ (k = 6 /\ NF k = 256 /\ 2 ^ (15 - k) = 512 /\ fsz k = 4096 /\ fshn k = 512).
Proof.
  intros k Hk. unfold KMAX in Hk.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
  unfold NF, fsz, fshn.
  destruct E as [->|[->|[->|[->|[->|[->| ->]]]]]]; cbn;
    [left|right;left|do 2 right;left|do 3 right;left|do 4 right;left|do 5 right;left|do 6 right]; repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma class_facts : forall k, 0 <= k <= KMAX ->
  16 <= NF k <= 16384 /\ 2 ^ (15 - k) = 2 * NF k /\ 64 <= fsz k <= 4096 /\ NF k * fsz k = 2 ^ 20
  /\ fshn k * 8 = fsz k /\ (fsz k = 64 \/ fsz k = 128 \/ fsz k = 256 \/ fsz k = 512 \/ fsz k = 1024 \/ fsz k = 2048 \/ fsz k = 4096).
Proof.
  intros k Hk. destruct (class_cases k Hk) as [C|[C|[C|[C|[C|[C|C]]]]]]; destruct C as (-> & -> & -> & -> & ->); cbn; lia.
Qed.

Lemma flag_addr_range : forall fsb k pos, slot_ok k pos ->
  fsb + AFS_FLAGS <= flag_addr fsb k pos < fsb + AFS_HDR.
Proof.
  intros fsb k pos [Hk Hp]. pose proof (class_facts k Hk) as (A & B & _). unfold flag_addr, AFS_FLAGS, AFS_HDR in *. lia.
Qed.

Lemma frame_addr_range : forall fsb k pos, slot_ok k pos ->
  fsb + AFS_HDR <= frame_addr fsb k pos /\ frame_addr fsb k pos + fsz k <= fsb + AFS_SIZE.
Proof.
  intros fsb k pos [Hk Hp]. pose proof (class_facts k Hk) as (A & B & C & D & _). unfold frame_addr, KMAX in *. rewrite AFS_SIZE_val.
  split; [nia|]. assert (pos * fsz k + fsz k <= NF k * fsz k) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma frame_addr_band : forall fsb k pos, slot_ok k pos ->
  fsb + AFS_HDR + k * 2 ^ 20 <= frame_addr fsb k pos /\ frame_addr fsb k pos + fsz k <= fsb + AFS_HDR + (k + 1) * 2 ^ 20.
Proof.
  intros fsb k pos [Hk Hp]. pose proof (class_facts k Hk) as (A & B & C & D & _). unfold frame_addr in *.
  split; [nia|]. assert (pos * fsz k + fsz k <= NF k * fsz k) by nia. nia.
Qed.

(* [comment removed for export] *)
Lemma flag_addr_band : forall fsb k pos, slot_ok k pos ->
  fsb + AFS_HDR - 2 * NF k <= flag_addr fsb k pos < fsb + AFS_HDR - NF k.
Proof.
  intros fsb k pos [Hk Hp]. pose proof (class_facts k Hk) as (A & B & _). unfold flag_addr in *. lia.
Qed.

Lemma NF_mono : forall k k', 0 <= k <= KMAX -> 0 <= k' <= KMAX -> k < k' -> 2 * NF k' <= NF k.
Proof.
  intros k k' Hk Hk' Hlt.
  destruct (class_cases k Hk) as [C|[C|[C|[C|[C|[C|C]]]]]]; destruct C as (-> & -> & _);
  destruct (class_cases k' Hk') as [C'|[C'|[C'|[C'|[C'|[C'|C']]]]]]; destruct C' as (-> & -> & _); lia.
Qed.

Lemma flag_addr_inj : forall fsb k pos k' pos', slot_ok k pos -> slot_ok k' pos' ->
  flag_addr fsb k pos = flag_addr fsb k' pos' -> k = k' /\ pos = pos'.
Proof.
  intros fsb k pos k' pos' S S' E.
  pose proof (flag_addr_band fsb k pos S) as B. pose proof (flag_addr_band fsb k' pos' S') as B'.
  destruct S as [Hk Hp], S' as [Hk' Hp'].
  destruct (Z.lt_trichotomy k k') as [L|[->|L]].
  - pose proof (NF_mono k k' Hk Hk' L). lia.
  - split; [reflexivity|]. unfold flag_addr in E. lia.
  - pose proof (NF_mono k' k Hk' Hk L). lia.
Qed.

Lemma frame_addr_disj : forall fsb k pos k' pos', slot_ok k pos -> slot_ok k' pos' ->
  (k <> k' \/ pos <> pos') ->
  frame_addr fsb k pos + fsz k <= frame_addr fsb k' pos' \/ frame_addr fsb k' pos' + fsz k' <= frame_addr fsb k pos.
Proof.
  intros fsb k pos k' pos' S S' NE.
  pose proof (frame_addr_band fsb k pos S) as B. pose proof (frame_addr_band fsb k' pos' S') as B'.
  destruct S as [Hk Hp], S' as [Hk' Hp'].
  destruct (Z.lt_trichotomy k k') as [L|[->|L]].
  - left. nia.
  - destruct NE as [NE|NE]; [lia|]. pose proof (class_facts k' Hk') as (A & _ & C & _). unfold frame_addr.
    destruct (Z.lt_trichotomy pos pos') as [L|[->|L]]; [left; nia| lia| right; nia].
  - right. nia.
Qed.

Lemma frame_addr_inj : forall fsb k pos k' pos', slot_ok k pos -> slot_ok k' pos' ->
  frame_addr fsb k pos = frame_addr fsb k' pos' -> k = k' /\ pos = pos'.
Proof.
  intros fsb k pos k' pos' S S' E.
  destruct (Z.eq_dec k k') as [EK|NK]; [destruct (Z.eq_dec pos pos') as [EP|NP]; [auto|]|].
  - exfalso. pose proof (frame_addr_disj fsb k pos k' pos' S S' (or_intror NP)). pose proof (class_facts k (proj1 S)). pose proof (class_facts k' (proj1 S')). lia.
  - exfalso. pose proof (frame_addr_disj fsb k pos k' pos' S S' (or_introl NK)). pose proof (class_facts k (proj1 S)). pose proof (class_facts k' (proj1 S')). lia.
Qed.

Lemma frame_addr_aligned : forall fsb k pos, slot_ok k pos -> fsb mod 4096 = 0 -> frame_addr fsb k pos mod fsz k = 0.
Proof.
  intros fsb k pos [Hk Hp] HA. pose proof (class_facts k Hk) as (A & B & C & D & E & CS). unfold frame_addr, AFS_HDR.
  destruct CS as [F|[F|[F|[F|[F|[F|F]]]]]]; rewrite F in *; Z.div_mod_to_equations; nia.
Qed.

Lemma frame_addr_mod64 : forall fsb k pos, slot_ok k pos -> fsb mod 4096 = 0 -> frame_addr fsb k pos mod 64 = 0 /\ fsz k mod 64 = 0.
Proof.
  intros fsb k pos [Hk Hp] HA. pose proof (class_facts k Hk) as (A & B & C & D & E & CS). unfold frame_addr, AFS_HDR.
  destruct CS as [F|[F|[F|[F|[F|[F|F]]]]]]; rewrite F in *; Z.div_mod_to_equations; nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition liveb (LF : list fframe) (fp : Z) : bool := existsb (fun f => ff_flag f =? fp) LF.
Definition flagv (LF : list fframe) (fp : Z) : Z := if liveb LF fp then 1 else 0.

(* [comment removed for export] *)
Definition hdr (h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : word) : list cell :=
  [C8 h0; C8 h1; C8 h2; C8 h3; C8 h4; C8 h5; C8 h6; C8 h7; C8 h8; C8 h9; C8 h10; C8 (wz 20); C1 (b8 0)].

Definition RFSI (fsb : Z) (LF : list fframe) (m : mem) : Prop :=
     (AIMG_TOP <= fsb /\ fsb + AFS_SIZE <= aceil /\ fsb mod 4096 = 0 /\ aapp fsb AFS_SIZE)   (* [comment removed for export] *)
  /\ rw_cells asegs m ATP [C8 (wz fsb)]
  /\ (exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, rw_cells asegs m fsb (hdr h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10))
  /\ (forall f, In f LF -> exists pos, slot_ok (ff_class f) pos
        /\ ff_addr f = frame_addr fsb (ff_class f) pos /\ ff_flag f = flag_addr fsb (ff_class f) pos)
  /\ List.NoDup (map ff_addr LF)
  /\ (forall k pos, slot_ok k pos -> rw_cells asegs m (flag_addr fsb k pos) [C1 (b8 (flagv LF (flag_addr fsb k pos)))])
  /\ stk asegs m (fsb + AFS_HDR) (fsb + AFS_SIZE)
  /\ stk asegs m (sh fsb) (sh (fsb + AFS_SIZE)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma find_segment_asegs : forall (x : Z),
  find_segment asegs x 1 =
    if ((0x10000 <=? x) && (x + 1 <=? 0x195000))%Z then Some AsanUbsan.AsanUbsan_segment_000
    else if ((0x195000 <=? x) && (x + 1 <=? 0x571000))%Z then Some AsanUbsan.AsanUbsan_segment_001
    else if ((0x571000 <=? x) && (x + 1 <=? 0x5ea000))%Z then Some AsanUbsan.AsanUbsan_segment_002
    else if ((0x5ea000 <=? x) && (x + 1 <=? 0xc04000))%Z then Some AsanUbsan.AsanUbsan_segment_003
    else None.
Proof. intros x. reflexivity. Qed.

Lemma wview_high : forall m (a : word), AIMG_TOP <= bv_unsigned a -> wview asegs m a = m a.
Proof.
  intros m a Ha. unfold wview. destruct (m a) as [b|]; [reflexivity|].
  rewrite find_segment_asegs. unfold AIMG_TOP in Ha.
  repeat (lazymatch goal with
          | |- context [((?lo <=? bv_unsigned a) && (bv_unsigned a + 1 <=? ?hi))%bool] =>
              replace (bv_unsigned a + 1 <=? hi) with false by (symmetry; apply Z.leb_gt; lia); rewrite andb_false_r
          end).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma stk_high_transport : forall m m' lo hi,
  stk asegs m lo hi -> wmono asegs m m' -> AIMG_TOP <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) WM Hlo. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  rewrite wview_high in W' by (rewrite wa_unsigned by lia; lia).
  unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity| congruence].
Qed.

Lemma stk_ext : forall m m' lo hi,
  stk asegs m lo hi ->
  (forall a, lo <= a < hi -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
  stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) E. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [W (b & B)]. destruct (E a Ha) as [E1 E2]. split; [apply E2; exact W|].
  exists b. unfold mrd in *. rewrite E1. exact B.
Qed.

Lemma rw_cells_ext : forall m m' A cs,
  rw_cells asegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)) ->
  rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[WF (B0 & B1 & BB)] (W0 & W1 & WW)] E.
  rewrite cells_bytes_length in B1, BB by exact WF.
  split; [split; [exact WF|]|].
  - split; [exact B0|]. split; [rewrite cells_bytes_length by exact WF; exact B1|].
    intros i Hi. rewrite cells_bytes_length in Hi by exact WF.
    destruct (E (A + Z.of_nat i) ltac:(lia)) as [E1 _]. unfold mrd in *. rewrite E1. apply BB. lia.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. destruct (E (A + i) ltac:(lia)) as [_ E2]. apply E2. apply WW. exact Hi.
Qed.

Lemma disjoint_from_of_Forall : forall (P : Z * Z -> Prop) W A n,
  Forall P W -> (forall lo hi, P (lo, hi) -> A + n <= lo \/ hi <= A) -> disjoint_from W A n.
Proof.
  intros P W A n F HP. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split.
  - apply HP. exact (Forall_inv F).
  - apply IH. exact (Forall_inv_tail F).
Qed.

Lemma rw_cells_out : forall (P : Z * Z -> Prop) W m m' A cs,
  rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' -> Forall P W ->
  (forall lo hi, P (lo, hi) -> A + Z.of_nat (cells_size cs) <= lo \/ hi <= A) ->
  rw_cells asegs m' A cs.
Proof.
  intros P W m m' A cs RC MU WM F HP. eapply rw_cells_transport; [exact RC| exact MU| exact WM|].
  eapply disjoint_from_of_Forall; [exact F| exact HP].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_C1_intro : forall m a b,
  0 <= a -> a + 1 <= 2^64 -> mrd asegs m (wa a) = Some b -> wview asegs m (wa a) <> None -> rw_cells asegs m a [C1 b].
Proof.
  intros m a b H0 H1 RD WV. split; [split; [cbn; exact (conj I I)|]|].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. assert (i = 0%nat) by lia. subst i.
    cbn. rewrite Z.add_0_r. exact RD.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace (a + i) with a by lia. exact WV.
Qed.

Lemma rw_cells_C1_wview : forall m a b, rw_cells asegs m a [C1 b] -> wview asegs m (wa a) <> None.
Proof. intros m a b [_ (_ & _ & W)]. replace a with (a + 0) by lia. apply W. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma liveb_cons : forall f LF q, liveb (f :: LF) q = ((ff_flag f =? q) || liveb LF q)%bool.
Proof. reflexivity. Qed.

Lemma liveb_true : forall LF q, liveb LF q = true <-> exists f, In f LF /\ ff_flag f = q.
Proof.
  intros LF q. unfold liveb. rewrite existsb_exists. split.
  - intros (f & IN & E). exists f. split; [exact IN| lia].
  - intros (f & IN & E). exists f. split; [exact IN| lia].
Qed.

Lemma liveb_false : forall LF q, liveb LF q = false <-> forall f, In f LF -> ff_flag f <> q.
Proof.
  intros LF q. split.
  - intros H f IN E. assert (T : liveb LF q = true) by (apply liveb_true; eauto). congruence.
  - intros H. destruct (liveb LF q) eqn:E; [|reflexivity]. apply liveb_true in E. destruct E as (f & IN & EQ). exfalso. exact (H f IN EQ).
Qed.

Lemma NoDup_map_inj_In : forall (g : fframe -> Z) l x y, List.NoDup (map g l) -> In x l -> In y l -> g x = g y -> x = y.
Proof.
  intros g l x y ND. induction l as [|a l IH]; intros INx INy E; [destruct INx|].
  cbn in ND. inversion ND as [|a' l' NI ND']; subst.
  destruct INx as [<-|INx], INy as [<-|INy]; [reflexivity| | |].
  - exfalso. apply NI. rewrite E. apply in_map. exact INy.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact INx.
  - apply IH; assumption.
Qed.

Lemma lf_remove_notin : forall ff LF, ~ In ff (map ff_addr LF) -> lf_remove ff LF = LF.
Proof.
  intros ff LF. induction LF as [|f LF IH]; intros NI; [reflexivity|]. cbn.
  destruct (Z.eqb_spec (ff_addr f) ff) as [E|NE].
  - exfalso. apply NI. left. exact E.
  - f_equal. apply IH. intros IN. apply NI. right. exact IN.
Qed.

(* [comment removed for export] *)
Lemma lf_remove_spec : forall ff LF, List.NoDup (map ff_addr LF) ->
  (forall f, In f (lf_remove ff LF) <-> In f LF /\ ff_addr f <> ff) /\ List.NoDup (map ff_addr (lf_remove ff LF)).
Proof.
  intros ff LF. induction LF as [|f0 LF IH]; intros ND.
  - cbn. split; [intros f; tauto| constructor].
  - cbn in ND. inversion ND as [|a l NI ND']; subst. destruct (IH ND') as [IH1 IH2]. cbn.
    destruct (Z.eqb_spec (ff_addr f0) ff) as [E|NE].
    + split; [| exact ND']. intros f. split.
      * intros IN. split; [right; exact IN|]. intros E'. apply NI. rewrite E, <- E'. apply in_map. exact IN.
      * intros [[<-|IN] NE']; [congruence| exact IN].
    + split.
      * intros f. cbn. rewrite IH1. split; [intros [<-|[IN NE']]; [split; [left; reflexivity| exact NE]| split; [right; exact IN| exact NE']]|].
        intros [[<-|IN] NE']; [left; reflexivity| right; split; assumption].
      * cbn. constructor; [| exact IH2]. intros IN. apply in_map_iff in IN. destruct IN as (f & E' & IN).
        apply IH1 in IN. destruct IN as [IN _]. apply NI. rewrite <- E'. apply in_map. exact IN.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Laws.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Lemma RFSI_range : RFS_range H.
  Proof.
    intros LF m R. apply RFS_is in R. destruct R as (G & _ & _ & SL & _).
    split; [exact G|]. intros f IN. destruct (SL f IN) as (pos & S & E1 & E2).
    pose proof (frame_addr_range (as_FSB H) _ _ S) as [A B]. pose proof (flag_addr_range (as_FSB H) _ _ S) as C.
    pose proof (frame_addr_aligned (as_FSB H) _ _ S ltac:(lia)) as D.
    unfold aframe_range. rewrite E1, E2. destruct S as [[K1 K2] _]. unfold KMAX in K2. repeat (split; try lia).
  Qed.

  Lemma RFSI_nodup : RFS_nodup H.
  Proof. intros LF m R. apply RFS_is in R. destruct R as (_ & _ & _ & _ & ND & _). exact ND. Qed.

  Lemma RFSI_disjoint : RFS_disjoint H.
  Proof.
    intros LF m f1 f2 R IN1 IN2 NE. apply RFS_is in R. destruct R as (G & _ & _ & SL & _).
    destruct (SL f1 IN1) as (p1 & S1 & A1 & F1). destruct (SL f2 IN2) as (p2 & S2 & A2 & F2).
    assert (DS : ff_class f1 <> ff_class f2 \/ p1 <> p2).
    { destruct (Z.eq_dec (ff_class f1) (ff_class f2)) as [EK|NK]; [|left; exact NK].
      destruct (Z.eq_dec p1 p2) as [EP|NP]; [|right; exact NP]. exfalso. apply NE. rewrite A1, A2, EK, EP. reflexivity. }
    split.
    - rewrite A1, A2. apply frame_addr_disj; assumption.
    - rewrite F1, F2. intros E. destruct (flag_addr_inj (as_FSB H) _ _ _ _ S1 S2 E) as [EK EP]. destruct DS; congruence.
  Qed.

  Lemma RFSI_shvis : RFS_shvis H.
  Proof.
    intros LF m f R IN. apply RFS_is in R. destruct R as (G & _ & _ & SL & _ & _ & _ & SH).
    destruct (SL f IN) as (pos & S & E1 & _). unfold shvis. rewrite E1.
    pose proof (frame_addr_range (as_FSB H) _ _ S) as [A B]. pose proof (frame_addr_mod64 (as_FSB H) _ _ S ltac:(lia)) as [M1 M2].
    destruct G as (G1 & G2 & G3 & G4). unfold AIMG_TOP, AFS_HDR in *.
    set (ff := frame_addr (as_FSB H) (ff_class f) pos) in *.
    replace (hull_lo ff) with ff. 2:{ unfold hull_lo. lia. }
    replace (hull_hi (ff + fsz (ff_class f))) with (ff + fsz (ff_class f)). 2:{ unfold hull_hi. Z.div_mod_to_equations. nia. }
    assert (L1 : sh (as_FSB H) <= sh ff) by (apply sh_mono; lia).
    assert (L2 : sh (ff + fsz (ff_class f)) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    pose proof (class_facts _ (proj1 S)) as (_ & _ & FZ & _).
    assert (L3 : sh ff <= sh (ff + fsz (ff_class f))) by (apply sh_mono; lia).
    destruct (stk_split asegs m _ (sh ff) _ SH ltac:(lia)) as [_ SH2].
    destruct (stk_split asegs m _ (sh (ff + fsz (ff_class f))) _ SH2 ltac:(lia)) as [SH3 _]. exact SH3.
  Qed.

  (* [comment removed for export] *)
  Lemma afs_window_low : forall LF m lo hi, RFSI (as_FSB H) LF m -> afs_write_ok H LF (lo, hi) ->
    (hi <= as_FSB H \/ as_FSB H + AFS_HDR <= lo) /\ (hi <= ATP \/ ATP + 8 <= lo).
  Proof.
    intros LF m lo hi (G & _ & _ & SL & _) [[A B]|(f & IN & A & B)]; cbn in *.
    - unfold ATLS_PRIV_LO, ATLS_PRIV_HI in B. unfold AFS_HDR, AFS_SIZE in *. lia.
    - destruct (SL f IN) as (pos & S & E1 & _). pose proof (frame_addr_range (as_FSB H) _ _ S) as [R1 R2].
      rewrite E1 in A. destruct G as (G1 & _). unfold AIMG_TOP, ATP, AFS_HDR in *. lia.
  Qed.

  Lemma RFSI_frame : RFS_frame H.
  Proof.
    intros LF m m' W R MU WM FW. apply RFS_is in R. apply RFS_is. pose proof R as R0.
    destruct R as (G & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS).
    pose proof (fun lo hi => afs_window_low LF m lo hi R0) as WIN.
    split; [exact G|]. split.
    { eapply rw_cells_out; [exact TLS| exact MU| exact WM| exact FW|]. intros lo hi P. cbn. destruct (WIN lo hi P). lia. }
    split.
    { exists h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10. eapply rw_cells_out; [exact HDR| exact MU| exact WM| exact FW|]. intros lo hi P. cbn. destruct (WIN lo hi P). unfold AFS_HDR in *. lia. }
    split; [exact SL|]. split; [exact ND|]. split.
    { intros k pos S. eapply rw_cells_out; [exact (FL k pos S)| exact MU| exact WM| exact FW|]. intros lo hi P. cbn.
      destruct (WIN lo hi P). pose proof (flag_addr_range (as_FSB H) k pos S). unfold AFS_FLAGS in *. lia. }
    destruct G as (G1 & G2 & G3 & G4). split.
    { eapply stk_high_transport; [exact STF| exact WM|]. unfold AIMG_TOP, AIMG_TOP, AFS_HDR in *. lia. }
    eapply stk_high_transport; [exact STS| exact WM|]. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val. lia.
  Qed.

  Lemma RFSI_ext : RFS_ext H.
  Proof.
    intros LF m m' R E. apply RFS_is in R. apply RFS_is.
    destruct R as (G & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS). destruct G as (G1 & G2 & G3 & G4).
    acb; unfold AIMG_TOP in G1, G2.
    assert (EM : forall a, as_FSB H <= a < as_FSB H + AFS_SIZE ->
              m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None)).
    { intros a Ha. apply E; [lia| left; exact Ha]. }
    split; [repeat split; try assumption; lia|]. split.
    { eapply rw_cells_ext; [exact TLS|]. intros a Ha. cbn in Ha.
      apply E; [unfold ATP in *; lia| right; left; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *; lia]. }
    split. { exists h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10. eapply rw_cells_ext; [exact HDR|]. intros a Ha. cbn in Ha. apply EM. unfold AFS_SIZE; lia. }
    split; [exact SL|]. split; [exact ND|]. split.
    { intros k pos S. eapply rw_cells_ext; [exact (FL k pos S)|]. intros a Ha. cbn in Ha. pose proof (flag_addr_range (as_FSB H) k pos S).
      apply EM. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia. }
    split. { eapply stk_ext; [exact STF|]. intros a Ha. apply EM. unfold AFS_HDR in *; lia. }
    eapply stk_ext; [exact STS|]. intros a Ha. apply E; [| right; right; exact Ha].
    unfold sh in *. rewrite ASHADOW_BASE_val in *. lia.
  Qed.

  Lemma RFSI_release : frame_release_law H.
  Proof.
    intros LF m m' W k ff fp R IN MU WM FW RD. apply RFS_is in R. apply RFS_is. pose proof R as R0.
    destruct R as (G & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS). destruct G as (G1 & G2 & G3 & G4).
    destruct (SL _ IN) as (pos & S & E1 & E2). cbn in S, E1, E2.
    pose proof (lf_remove_spec ff LF ND) as [RM ND'].
    pose proof (flag_addr_range (as_FSB H) k pos S) as FR. rewrite <- E2 in FR.
    set (P := fun iv : Z * Z => afs_write_ok H LF iv \/ (fst iv = fp /\ snd iv = fp + 1)) in FW.
    assert (WIN : forall lo hi, P (lo, hi) ->
              ((hi <= as_FSB H \/ as_FSB H + AFS_HDR <= lo) /\ (hi <= ATP \/ ATP + 8 <= lo)) \/ (lo = fp /\ hi = fp + 1)).
    { intros lo hi [Q|Q]; [left; exact (afs_window_low LF m lo hi R0 Q)| right; cbn in Q; exact Q]. }
    split; [repeat split; assumption|]. split.
    { eapply rw_cells_out; [exact TLS| exact MU| exact WM| exact FW|]. intros lo hi Q. cbn. destruct (WIN lo hi Q); [lia|].
      unfold AIMG_TOP, ATP, AFS_FLAGS in *. lia. }
    split.
    { exists h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10. eapply rw_cells_out; [exact HDR| exact MU| exact WM| exact FW|]. intros lo hi Q. cbn. destruct (WIN lo hi Q); unfold AFS_HDR, AFS_FLAGS in *; lia. }
    split. { intros f INf. apply RM in INf. destruct INf as [INf _]. exact (SL f INf). }
    split; [exact ND'|].
    (* [comment removed for export] *)
    assert (OWN : forall f', In f' LF -> ff_flag f' = fp -> f' = (k, ff, fp)).
    { intros f' IN' EF. destruct (SL f' IN') as (p' & S' & A' & F').
      rewrite F', E2 in EF.
      destruct (flag_addr_inj (as_FSB H) _ _ _ _ S' S EF) as [EK EP].
      eapply (NoDup_map_inj_In ff_addr); [exact ND| exact IN'| exact IN|]. cbn. rewrite A', EK, EP. symmetry. exact E1. }
    split.
    { intros k' pos' S'. destruct (Z.eq_dec (flag_addr (as_FSB H) k' pos') fp) as [EQ|NE].
      - rewrite EQ. replace (flagv (lf_remove ff LF) fp) with 0.
        2:{ unfold flagv. replace (liveb (lf_remove ff LF) fp) with false; [reflexivity|]. symmetry. apply (proj2 (liveb_false _ _)).
            intros f' IN' EF. apply RM in IN'. destruct IN' as [IN' NA]. pose proof (OWN f' IN' EF). subst f'. cbn in NA. congruence. }
        pose proof (FL k pos S) as C. rewrite <- E2 in C.
        apply rw_cells_C1_intro; [unfold AIMG_TOP, AFS_FLAGS in *; lia| acb; unfold AFS_HDR, AFS_SIZE in *; lia| exact RD|].
        apply WM. exact (rw_cells_C1_wview _ _ _ C).
      - replace (flagv (lf_remove ff LF) (flag_addr (as_FSB H) k' pos')) with (flagv LF (flag_addr (as_FSB H) k' pos')).
        2:{ unfold flagv. set (q := flag_addr (as_FSB H) k' pos') in *.
            destruct (liveb LF q) eqn:L1; destruct (liveb (lf_remove ff LF) q) eqn:L2; try reflexivity; exfalso.
            + apply liveb_true in L1. destruct L1 as (f' & IN' & EF). pose proof (proj1 (liveb_false _ _) L2) as L2'. apply (L2' f'); [| exact EF].
              apply RM. split; [exact IN'|]. intros EA.
              assert (f' = (k, ff, fp)).
              { eapply (NoDup_map_inj_In ff_addr); [exact ND| exact IN'| exact IN|]. cbn. exact EA. }
              subst f'. cbn in EF. congruence.
            + apply liveb_true in L2. destruct L2 as (f' & IN' & EF). apply RM in IN'. destruct IN' as [IN' _].
              pose proof (proj1 (liveb_false _ _) L1) as L1'. exact (L1' f' IN' EF). }
        eapply rw_cells_out; [exact (FL k' pos' S')| exact MU| exact WM| exact FW|]. intros lo hi Q. cbn.
        pose proof (flag_addr_range (as_FSB H) k' pos' S'). destruct (WIN lo hi Q); unfold AFS_FLAGS in *; lia. }
    split.
    { eapply stk_high_transport; [exact STF| exact WM|]. unfold AIMG_TOP, AIMG_TOP, AFS_HDR in *. lia. }
    eapply stk_high_transport; [exact STS| exact WM|]. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val. lia.
  Qed.
End Laws.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma RFSI_frame_win : forall fsb LF m m' W,
  RFSI fsb LF m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (snd iv <= fsb \/ fsb + AFS_HDR <= fst iv) /\ (snd iv <= ATP \/ ATP + 8 <= fst iv)) W ->
  RFSI fsb LF m'.
Proof.
  intros fsb LF m m' W R MU WM FW.
  destruct R as (G & TLS & (h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & HDR) & SL & ND & FL & STF & STS).
  split; [exact G|]. split.
  { eapply rw_cells_out; [exact TLS| exact MU| exact WM| exact FW|]. intros lo hi [P Q]. cbn in *. lia. }
  split.
  { exists h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10. eapply rw_cells_out; [exact HDR| exact MU| exact WM| exact FW|].
    intros lo hi [P Q]. cbn in *. unfold AFS_HDR in *. lia. }
  split; [exact SL|]. split; [exact ND|]. split.
  { intros k pos S. eapply rw_cells_out; [exact (FL k pos S)| exact MU| exact WM| exact FW|]. intros lo hi [P Q]. cbn in *.
    pose proof (flag_addr_range fsb k pos S). unfold AFS_FLAGS in *. lia. }
  destruct G as (G1 & G2 & G3 & G4). split.
  { eapply stk_high_transport; [exact STF| exact WM|]. unfold AIMG_TOP, AIMG_TOP, AFS_HDR in *. lia. }
  eapply stk_high_transport; [exact STS| exact WM|]. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val. lia.
Qed.

Lemma RFSI_stack_frame : forall fsb LF m m' slo shi,
  RFSI fsb LF m -> munch [(slo, shi)] m m' -> wmono asegs m m' -> aceil <= slo -> RFSI fsb LF m'.
Proof.
  intros fsb LF m m' slo shi R MU WM LO. eapply RFSI_frame_win; [exact R| exact MU| exact WM|].
  destruct R as ((G1 & G2 & G3 & G4) & _). constructor; [| constructor]. cbn. acb; unfold AFS_HDR, AFS_SIZE, ATP in *. lia.
Qed.

Lemma RFSI_geom : forall fsb LF m, RFSI fsb LF m -> AIMG_TOP <= fsb /\ fsb + AFS_SIZE <= aceil /\ fsb mod 4096 = 0 /\ aapp fsb AFS_SIZE.
Proof. intros fsb LF m (G & _). exact G. Qed.
Lemma RFSI_tls : forall fsb LF m, RFSI fsb LF m -> rw_cells asegs m ATP [C8 (wz fsb)].
Proof. intros fsb LF m (_ & T & _). exact T. Qed.
Lemma RFSI_hdr : forall fsb LF m, RFSI fsb LF m ->
  exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, rw_cells asegs m fsb (hdr h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).
Proof. intros fsb LF m (_ & _ & HD & _). exact HD. Qed.
Lemma RFSI_frames : forall fsb LF m, RFSI fsb LF m -> stk asegs m (fsb + AFS_HDR) (fsb + AFS_SIZE).
Proof. intros fsb LF m (_ & _ & _ & _ & _ & _ & S & _). exact S. Qed.
Lemma RFSI_shadow : forall fsb LF m, RFSI fsb LF m -> stk asegs m (sh fsb) (sh (fsb + AFS_SIZE)).
Proof. intros fsb LF m (_ & _ & _ & _ & _ & _ & _ & S). exact S. Qed.

Lemma flagv_01 : forall LF q, flagv LF q = 0 \/ flagv LF q = 1.
Proof. intros LF q. unfold flagv. destruct (liveb LF q); [right|left]; reflexivity. Qed.

(* [comment removed for export] *)
Definition flagbytes (fsb : Z) (LF : list fframe) (k : Z) : list byte :=
  map (fun i => b8 (flagv LF (flag_addr fsb k (Z.of_nat i)))) (seq 0 (Z.to_nat (NF k))).

Lemma flagbytes_length : forall fsb LF k, 0 <= k <= KMAX -> Z.of_nat (length (flagbytes fsb LF k)) = NF k.
Proof. intros fsb LF k Hk. unfold flagbytes. rewrite length_map, length_seq. pose proof (class_facts k Hk). lia. Qed.

Lemma flagbytes_nth : forall fsb LF k p, 0 <= k <= KMAX -> 0 <= p < NF k ->
  nth_error (flagbytes fsb LF k) (Z.to_nat p) = Some (b8 (flagv LF (flag_addr fsb k p))).
Proof.
  intros fsb LF k p Hk Hp. unfold flagbytes. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec (Z.to_nat p) (Z.to_nat (NF k))); [|lia]. cbn. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma RFSI_flags_arr : forall fsb LF m k, RFSI fsb LF m -> 0 <= k <= KMAX ->
  u8arr asegs m (flag_addr fsb k 0) (flagbytes fsb LF k).
Proof.
  intros fsb LF m k R Hk. pose proof R as ((G1 & G2 & G3 & G4) & _ & _ & _ & _ & FL & _).
  pose proof (class_facts k Hk) as (A & _).
  pose proof (flagbytes_length fsb LF k Hk) as LEN.
  assert (B0 : slot_ok k 0) by (split; lia). pose proof (flag_addr_range fsb k 0 B0) as R0.
  acb; unfold AFS_FLAGS, AFS_HDR, AIMG_TOP, AFS_SIZE in *.
  assert (EA : forall i, flag_addr fsb k 0 + i = flag_addr fsb k i) by (intros; unfold flag_addr; lia).
  split.
  - split; [lia|]. split; [unfold flag_addr in *; lia|].
    intros i Hi. assert (SI : slot_ok k (Z.of_nat i)) by (split; lia).
    pose proof (FL k (Z.of_nat i) SI) as [[_ (_ & _ & BB)] _].
    specialize (BB 0%nat ltac:(cbn; lia)). cbn in BB. rewrite Z.add_0_r in BB.
    rewrite EA, BB, <- (Nat2Z.id i), flagbytes_nth by lia. rewrite Nat2Z.id. reflexivity.
  - split; [lia|]. split; [unfold flag_addr in *; lia|].
    intros i Hi. assert (SI : slot_ok k i) by (split; lia).
    rewrite EA. exact (rw_cells_C1_wview _ _ _ (FL k i SI)).
Qed.

(* [comment removed for export] *)
Lemma u8arr_cell : forall m A bs (i : Z) b,
  u8arr asegs m A bs -> 0 <= i -> nth_error bs (Z.to_nat i) = Some b -> rw_cells asegs m (A + i) [C1 b].
Proof.
  intros m A bs i b [(B0 & B1 & BB) (W0 & W1 & WW)] Hi NTH. pose proof (nth_error_lt _ _ _ NTH).
  apply rw_cells_C1_intro; [lia| lia| |].
  - specialize (BB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in BB by lia. rewrite BB. exact NTH.
  - apply WW. lia.
Qed.


Lemma filter_length_le : forall {A} (g : A -> bool) l, (length (List.filter g l) <= length l)%nat.
Proof. intros A g l. induction l as [|x l IH]; cbn; [lia|]. destruct (g x); cbn; lia. Qed.

(* [comment removed for export] *)
Lemma filter_neq_length : forall (ps : list Z) (p0 : Z), List.NoDup ps ->
  (length ps <= S (length (List.filter (fun p => negb (Z.eqb p0 p)) ps)))%nat.
Proof.
  intros ps p0 ND. induction ps as [|p ps IH]; [cbn; lia|].
  inversion ND as [|p' ps' NI ND']; subst. cbn. destruct (Z.eqb_spec p0 p) as [->|NE]; cbn.
  - enough (E : List.filter (fun p1 => negb (Z.eqb p p1)) ps = ps) by (rewrite E; lia).
    clear IH ND. induction ps as [|q ps IH]; [reflexivity|]. cbn. destruct (Z.eqb_spec p q) as [->|NQ]; cbn.
    + exfalso. apply NI. left. reflexivity.
    + f_equal. apply IH; [intros IN; apply NI; right; exact IN| inversion ND'; assumption].
  - specialize (IH ND'). lia.
Qed.

Lemma live_positions_bound : forall fsb k LF ps,
  0 <= k <= KMAX ->
  (forall f, In f LF -> exists pos, slot_ok (ff_class f) pos /\ ff_flag f = flag_addr fsb (ff_class f) pos) ->
  List.NoDup ps -> (forall p, In p ps -> 0 <= p < NF k /\ liveb LF (flag_addr fsb k p) = true) ->
  (length ps <= length LF)%nat.
Proof.
  intros fsb k LF. induction LF as [|f LF IH]; intros ps Hk SL ND LIVE.
  - destruct ps as [|p ps]; [cbn; lia|]. destruct (LIVE p (or_introl eq_refl)) as [_ L]. cbn in L. discriminate.
  - cbn. destruct (SL f (or_introl eq_refl)) as (pf & Sf & Ef).
    (* [comment removed for export] *)
    destruct (Z.eq_dec (ff_class f) k) as [EK|NK].
    + set (ps' := List.filter (fun p => negb (Z.eqb pf p)) ps).
      pose proof (filter_neq_length ps pf ND) as L1. fold ps' in L1.
      assert (L' : (length ps' <= length LF)%nat); [|lia].
      apply IH; [exact Hk| intros f' IN'; apply SL; right; exact IN'| apply NoDup_filter; exact ND|].
      intros p IN. apply filter_In in IN. destruct IN as [IN NEQ]. destruct (LIVE p IN) as [RP L]. split; [exact RP|].
      rewrite liveb_cons in L. destruct (Z.eqb_spec (ff_flag f) (flag_addr fsb k p)) as [E|NE]; [|exact L].
      exfalso. rewrite Ef, EK in E. destruct (flag_addr_inj fsb k pf k p ltac:(rewrite <- EK; exact Sf) ltac:(split; lia) E) as [_ ->].
      rewrite Z.eqb_refl in NEQ. discriminate.
    + (* [comment removed for export] *)
      enough (length ps <= length LF)%nat by lia.
      apply IH; [exact Hk| intros f' IN'; apply SL; right; exact IN'| exact ND|].
      intros p IN. destruct (LIVE p IN) as [RP L]. split; [exact RP|].
      rewrite liveb_cons in L. destruct (Z.eqb_spec (ff_flag f) (flag_addr fsb k p)) as [E|NE]; [|exact L].
      exfalso. rewrite Ef in E. destruct (flag_addr_inj fsb _ pf k p Sf ltac:(split; lia) E) as [EK' _]. exact (NK EK').
Qed.

Lemma seqZ_facts : forall n, List.NoDup (map Z.of_nat (seq 0 n)) /\ (forall p, In p (map Z.of_nat (seq 0 n)) <-> 0 <= p < Z.of_nat n)
  /\ length (map Z.of_nat (seq 0 n)) = n.
Proof.
  intros n. split; [|split].
  - apply (NoDup_map_NoDup_ForallPairs Z.of_nat); [| apply seq_NoDup]. intros x y _ _ E. lia.
  - intros p. rewrite in_map_iff. split.
    + intros (x & <- & IN). apply in_seq in IN. lia.
    + intros Hp. exists (Z.to_nat p). split; [lia|]. apply in_seq. lia.
  - rewrite length_map, length_seq. reflexivity.
Qed.

Lemma RFSI_free_slot : forall fsb LF m k h, RFSI fsb LF m -> 0 <= k <= 4 -> (length LF < AFS_MAXLIVE)%nat ->
  exists j, 0 <= j < NF k /\ flagv LF (flag_addr fsb k ((h + j) mod NF k)) = 0.
Proof.
  intros fsb LF m k h R Hk LEN. pose proof R as (_ & _ & _ & SL & _).
  assert (HK : 0 <= k <= KMAX) by (unfold KMAX; lia). pose proof (class_facts k HK) as (A & _).
  assert (NFK : 1024 <= NF k).
  { destruct (class_cases k HK) as [C|[C|[C|[C|[C|[C|C]]]]]]; destruct C as (-> & -> & _); lia. }
  destruct (seqZ_facts (Z.to_nat (NF k))) as (ND & INS & LENS).
  destruct (existsb (fun p => negb (liveb LF (flag_addr fsb k p))) (map Z.of_nat (seq 0 (Z.to_nat (NF k))))) eqn:EX.
  - apply existsb_exists in EX. destruct EX as (p & IN & NL). apply INS in IN.
    exists ((p - h) mod NF k). split; [Z.div_mod_to_equations; lia|].
    replace ((h + (p - h) mod NF k) mod NF k) with p.
    2:{ rewrite Zplus_mod_idemp_r. replace (h + (p - h)) with p by lia. symmetry. apply Z.mod_small. lia. }
    unfold flagv. destruct (liveb LF (flag_addr fsb k p)); [cbn in NL; discriminate| reflexivity].
  - exfalso.
    assert (ALL : forall p, In p (map Z.of_nat (seq 0 (Z.to_nat (NF k)))) -> 0 <= p < NF k /\ liveb LF (flag_addr fsb k p) = true).
    { intros p IN. pose proof (proj1 (INS p) IN) as RP. split; [lia|].
      destruct (liveb LF (flag_addr fsb k p)) eqn:L; [reflexivity|]. exfalso.
      assert (T : existsb (fun p => negb (liveb LF (flag_addr fsb k p))) (map Z.of_nat (seq 0 (Z.to_nat (NF k)))) = true).
      { apply existsb_exists. exists p. split; [exact IN|]. rewrite L. reflexivity. }
      rewrite T in EX. discriminate. }
    assert (SL' : forall f, In f LF -> exists pos, slot_ok (ff_class f) pos /\ ff_flag f = flag_addr fsb (ff_class f) pos).
    { intros f IN. destruct (SL f IN) as (pos & S & _ & E). exists pos. split; assumption. }
    pose proof (live_positions_bound fsb k LF _ HK SL' ND ALL) as B.
    rewrite LENS in B. unfold AFS_MAXLIVE in LEN. lia.
Qed.

(* [comment removed for export] *)
Lemma RFSI_alloc : forall fsb LF m1 m' k pos slo shi ff fp,
  RFSI fsb LF m1 -> slot_ok k pos -> flagv LF (flag_addr fsb k pos) = 0 ->
  ff = frame_addr fsb k pos -> fp = flag_addr fsb k pos ->
  munch [(slo, shi); (fsb, fsb + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz k); (sh ff, sh ff + fshn k)] m1 m' ->
  wmono asegs m1 m' -> aceil <= slo ->
  rw_cells asegs m' ATP [C8 (wz fsb)] ->
  (exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, rw_cells asegs m' fsb (hdr h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)) ->
  rw_cells asegs m' fp [C1 (b8 1)] ->
  RFSI fsb ((k, ff, fp) :: LF) m'.
Proof.
  intros fsb LF m1 m' k pos slo shi ff fp R S FREE Eff Efp MU WM LO TLS HDR FLAG. subst ff fp.
  set (ff := frame_addr fsb k pos) in *. set (fp := flag_addr fsb k pos) in *.
  destruct R as ((G1 & G2 & G3 & G4) & _ & _ & SL & ND & FL & STF & STS).
  pose proof (flag_addr_range fsb k pos S) as FR. pose proof (frame_addr_range fsb k pos S) as [AR1 AR2].
  pose proof (class_facts k (proj1 S)) as (CF1 & CF2 & CF3 & CF4 & CF5 & _).
  split; [repeat split; assumption|]. split; [exact TLS|]. split; [exact HDR|]. split.
  { intros f [<-|IN]; [| exact (SL f IN)]. exists pos. cbn. split; [exact S|]. split; reflexivity. }
  split.
  { cbn. constructor; [| exact ND]. intros IN. apply in_map_iff in IN. destruct IN as (f & EA & IN).
    destruct (SL f IN) as (p' & S' & A' & F'). rewrite A' in EA.
    destruct (frame_addr_inj fsb _ _ _ _ S' S EA) as [EK EP].
    assert (L : liveb LF fp = true).
    { apply liveb_true. exists f. split; [exact IN|]. rewrite F', EK, EP. reflexivity. }
    unfold flagv in FREE. fold fp in FREE. rewrite L in FREE. discriminate. }
  split.
  { intros k' pos' S'. unfold flagv. rewrite liveb_cons. cbn [ff_flag snd].
    destruct (Z.eqb_spec fp (flag_addr fsb k' pos')) as [EQ|NE].
    - rewrite <- EQ. cbn. exact FLAG.
    - cbn [orb]. fold (flagv LF (flag_addr fsb k' pos')).
      eapply rw_cells_transport; [exact (FL k' pos' S')| exact MU| exact WM|].
      pose proof (flag_addr_range fsb k' pos' S') as FR'. cbn.
      acb; unfold AIMG_TOP, AFS_FLAGS, AFS_HDR, AFS_SIZE, sh in *. rewrite ASHADOW_BASE_val in *.
      destruct G4 as [[G4a G4b]|[G4a G4b]]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO in G4a, G4b;
      repeat split; lia. }
  split.
  { eapply stk_high_transport; [exact STF| exact WM|]. unfold AIMG_TOP, AIMG_TOP, AFS_HDR in *. lia. }
  eapply stk_high_transport; [exact STS| exact WM|]. unfold sh, AIMG_TOP in *. rewrite ASHADOW_BASE_val. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RFSI_init : forall fsb m,
  AIMG_TOP <= fsb -> fsb + AFS_SIZE <= aceil -> fsb mod 4096 = 0 -> aapp fsb AFS_SIZE ->
  rw_cells asegs m ATP [C8 (wz fsb)] ->                                              (* [comment removed for export] *)
  (exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, rw_cells asegs m fsb (hdr h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)) ->   (* [comment removed for export] *)
  (forall a, fsb + AFS_FLAGS <= a < fsb + AFS_HDR -> rw_cells asegs m a [C1 (b8 0)]) ->  (* [comment removed for export] *)
  stk asegs m (fsb + AFS_HDR) (fsb + AFS_SIZE) ->                                    (* [comment removed for export] *)
  stk asegs m (sh fsb) (sh (fsb + AFS_SIZE)) ->                                     (* [comment removed for export] *)
  RFSI fsb [] m.
Proof.
  intros fsb m G1 G2 G3 G4 TLS HDR FL STF STS.
  split; [repeat split; assumption|]. split; [exact TLS|]. split; [exact HDR|].
  split; [intros f IN; destruct IN|]. split; [constructor|]. split; [| split; [exact STF| exact STS]].
  intros k pos S. unfold flagv. cbn. apply FL. exact (flag_addr_range fsb k pos S).
Qed.

(* [comment removed for export] *)
Lemma hdr_zero : forall m fsb,
  rw_cells asegs m fsb (hdr (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0) (wz 0)) ->
  exists h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10, rw_cells asegs m fsb (hdr h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).
Proof. intros m fsb R. do 11 eexists. exact R. Qed.

End HCW.

