(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AProg_kit AHarness_iface
     AFake_iface Stdio_kit ADriver_iface AD_kit MonadF AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_dctx_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition acell (a : Z) : Prop := APDCTX <= a < APDCTX + 8.

(* [comment removed for export] *)
Definition kimg (a : Z) : Prop := 0 <= a < AIMG_HI.
Definition kshd (a : Z) : Prop := exists a', (0 <= a' < AIMG_HI \/ ATOP <= a' < 2^47) /\ a = shad a'.

Lemma kshd_range : forall a, kshd a -> ASHOFF <= a < shad AIMG_HI \/ shad ATOP <= a < ASHOFF + 2^44.
Proof.
  intros a (a' & Ha' & ->). pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  rewrite !shad_div. unfold ASHOFF, AIMG_HI in *. destruct Ha' as [H|H]; [left| right]; Z.div_mod_to_equations; lia.
Qed.

Lemma kshd_intro : forall lo hi a, (0 <= lo /\ hi <= AIMG_HI) \/ (ATOP <= lo /\ hi <= 2^47) -> lo mod 8 = 0 ->
  shad lo <= a < shad hi -> kshd a.
Proof.
  intros lo hi a H L8 Ha. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
  rewrite !shad_div in Ha. unfold ASHOFF in *. destruct H as [H|H]; [left| right]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition kept (K : list ablock) (SPX : Z) (a : Z) : Prop :=
  kimg a \/ SPX <= a < 2^47 \/ in_block K a \/ kshd a.

(* [comment removed for export] *)
Definition wok (K LB' : list ablock) (L : alayout) (SPX : Z) (iv : Z * Z) : Prop :=
     (ATOP <= fst iv /\ snd iv <= SPX)
  \/ (exists p A n, In (HB p A n) LB' /\ ~ In (HB p A n) K /\ A <= fst iv /\ snd iv <= A + n)
  \/ In iv (fake_area L)
  \/ snd iv <= fst iv.

Lemma wok_antimono : forall K K0 LB' L SPX iv, (forall b, In b K0 -> In b K) -> wok K LB' L SPX iv -> wok K0 LB' L SPX iv.
Proof.
  intros K K0 LB' L SPX iv HI [H|[(p & A & n & Hin & HNK & H1 & H2)|[H|H]]]; [left; exact H| | right; right; left; exact H| do 3 right; exact H].
  right; left. exists p, A, n. split; [exact Hin|]. split; [intros X; apply HNK; apply HI; exact X| lia].
Qed.

Lemma nodup_hd : forall {A} (a : A) l, List.NoDup (a :: l) -> ~ In a l.
Proof. intros A a l ND. inversion ND; assumption. Qed.
Lemma nodup_3 : forall {A} (a b : A) l, List.NoDup (a :: b :: l) -> ~ In a (b :: l) /\ ~ In b l /\ b <> a.
Proof.
  intros A a b l ND. inversion ND as [|x l' N1 ND1]; subst. split; [exact N1|]. split; [exact (nodup_hd b l ND1)|].
  intros E. apply N1. left. exact E.
Qed.

(* [comment removed for export] *)
Definition hcl (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (a : Z) : Prop :=
  (aclient_addr CI LB SP a /\ ~ acell a) \/ (shad ATOP <= a < shad SP).

Section HK.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Hypothesis FHEAP : fake_heap_law AI.

  Lemma hcl_post : forall LB SP m m', SP <= 2^47 -> magree bsegs (hcl CI LB SP) m m' ->
    harness_presA AI LB SP m m' /\ AHarness_iface.astk_shadow_pres SP m m'.
  Proof.
    intros LB SP m m' H47 AG. split.
    - intros a Ha Hc Hn. exact (AG a Ha (or_introl (conj Hc Hn))).
    - intros a Ha. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      assert (R : 0 <= a < 2^64) by (rewrite !shad_div in Ha; unfold ASHOFF in Ha; Z.div_mod_to_equations; lia).
      exact (proj1 (AG a R (or_intror Ha))).
  Qed.


  Lemma block_geom : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    ablk A (A + n) /\ 1 <= n /\ A + n <= ATOP /\ A mod 16 = 0 /\ AIMG_HI <= A.
  Proof.
    intros L RNG st LB m p A n AH Hin. destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (N & (BR & B2 & B3 & B4) & _).
    pose proof (ablk_lin _ _ BR) as (X1 & _). repeat split; try lia; exact BR.
  Qed.

  (* [comment removed for export] *)
  Lemma fake_area_apart : forall L RNG st K LB' m a, AHEAP AI L RNG st LB' m -> hb_heap K -> (forall b, In b K -> In b LB') ->
    (kimg a \/ ATOP <= a < 2^47 \/ in_block K a \/ kshd a) -> outside (fake_area L) a.
  Proof.
    intros L RNG st K LB' m a AH HH HI Ha. destruct (FHEAP _ _ _ _ _ AH) as [FB FD].
    pose proof (ablk_lin _ _ FB) as (F1 & F2 & F3 & F4). pose proof (ablk_disj_band _ _ FB) as FBD.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (FA : al_fake L mod 8 = 0) by (unfold al_fake; Z.div_mod_to_equations; lia).
    unfold fake_area. cbn [outside]. rewrite !shad_div. unfold FAKESZ in *. unfold ASHOFF, KLS, AIMG_HI in *.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    - unfold kimg, AIMG_HI in Ha. split; [lia| split; [Z.div_mod_to_equations; lia| exact I]].
    - split; [lia| split; [Z.div_mod_to_equations; lia| exact I]].
    - destruct (HH b Hb) as (p & A & n & ->). cbn [ab_addr ab_size] in Hr.
      pose proof (FD p A n (HI _ Hb)) as DJ. destruct (block_geom _ _ _ _ _ _ _ _ AH (HI _ Hb)) as (BR & _ & _ & _ & _).
      pose proof (ablk_disj_band _ _ BR) as BB. unfold KLS in BB.
      split; [lia| split; [Z.div_mod_to_equations; lia| exact I]].
    - destruct Ha as (a' & Ha' & ->). unfold AIMG_HI in Ha'. rewrite shad_div. unfold ASHOFF.
      split; [Z.div_mod_to_equations; lia| split; [| exact I]].
      destruct Ha' as [H|H]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_win_apart : forall L RNG st K LB' m a x y, AHEAP AI L RNG st LB' m -> (forall b, In b K -> In b LB') -> ATOP <= x ->
    (kimg a \/ y <= a < 2^47 \/ in_block K a \/ kshd a) -> ~ (x <= a < y).
  Proof.
    intros L RNG st K LB' m a x y AH HI HX Ha. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    - unfold kimg, AIMG_HI in Ha. lia.
    - lia.
    - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH (HI _ Hb)) as BB. lia.
    - apply kshd_range in Ha. rewrite !shad_div in Ha. unfold ASHOFF, AIMG_HI in Ha. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma block_apart : forall L RNG st K LB' m p A n a, AHEAP AI L RNG st LB' m -> (forall b, In b K -> In b LB') ->
    In (HB p A n) LB' -> ~ In (HB p A n) K ->
    (kimg a \/ ATOP <= a < 2^47 \/ in_block K a \/ kshd a) -> ~ (A <= a < A + n).
  Proof.
    intros L RNG st K LB' m p A n a AH HI Hin HNK Ha. destruct (block_geom _ _ _ _ _ _ _ _ AH Hin) as (BR & B1 & B2 & B3 & B4).
    pose proof (ablk_disj_band _ _ BR) as BB. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct Ha as [Ha|[Ha|[(b & Hb & Hr)|Ha]]].
    - unfold kimg in Ha. lia.
    - lia.
    - assert (NE : b <> HB p A n) by (intros E; apply HNK; rewrite <- E; exact Hb).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (HI _ Hb) Hin NE) as DJ. cbn [ab_addr ab_size] in DJ. lia.
    - apply kshd_range in Ha. rewrite !shad_div in Ha. unfold ASHOFF, AIMG_HI, KLS in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kept_outside : forall L RNG st K LB' m W SPX a, AHEAP AI L RNG st LB' m -> hb_heap K -> (forall b, In b K -> In b LB') ->
    ATOP <= SPX -> Forall (wok K LB' L SPX) W -> kept K SPX a -> outside W a.
  Proof.
    intros L RNG st K LB' m W SPX a AH HH HI HS FW Ha.
    assert (Hc : kimg a \/ ATOP <= a < 2^47 \/ in_block K a \/ kshd a).
    { destruct Ha as [Ha'|[Ha'|[Ha'|Ha']]]; [left; exact Ha'| right; left; lia| right; right; left; exact Ha'| do 3 right; exact Ha']. }
    induction FW as [|[x y] W Hxy FW IH]; cbn [outside]; [exact I|]. split; [| exact IH].
    destruct Hxy as [[H1 H2]|[(p & A & n & Hin & HNK & H1 & H2)|[Hf|E]]]; cbn [fst snd] in *; [| | | lia].
    - apply (stack_win_apart L RNG st K LB' m a x y AH HI H1).
      destruct Ha as [Ha'|[Ha'|[Ha'|Ha']]]; [left; exact Ha'| right; left; lia| right; right; left; exact Ha'| do 3 right; exact Ha'].
    - enough (~ (A <= a < A + n)) by lia. exact (block_apart L RNG st K LB' m p A n a AH HI Hin HNK Hc).
    - pose proof (fake_area_apart L RNG st K LB' m a AH HH HI Hc) as OF.
      unfold fake_area in Hf, OF. cbn [outside] in OF. destruct OF as (O1 & O2 & _).
      destruct Hf as [E|[E|[]]]; injection E as E1 E2; subst x y; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma kept_of_munch : forall L RNG st K LB' m W SPX m1 m2, AHEAP AI L RNG st LB' m -> hb_heap K -> (forall b, In b K -> In b LB') ->
    ATOP <= SPX -> Forall (wok K LB' L SPX) W -> munch W m1 m2 -> wmono bsegs m1 m2 -> magree bsegs (kept K SPX) m1 m2.
  Proof.
    intros L RNG st K LB' m W SPX m1 m2 AH HH HI HS FW MU WM.
    eapply magree_mono; [exact (magree_of_munch bsegs W m1 m2 MU WM)|]. cbv beta. intros a Ha.
    exact (kept_outside L RNG st K LB' m W SPX a AH HH HI HS FW Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma aclient_kept : forall K SP SPX a, hb_heap K -> SPX <= SP -> aclient_addr CI K SP a -> kept K SPX a.
  Proof.
    intros K SP SPX a HH HS Ha.
    destruct Ha as [Ha|[(iv & Hiv & Hr)|[Ha|(a' & Ha' & ->)]]].
    - right; left; lia.
    - left. pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). unfold kimg. lia.
    - right; right; left; exact Ha.
    - right; right; right. exists a'. split; [| reflexivity].
      destruct Ha' as [X|[(iv & Hiv & Hr)|(c & F & n & Hin & Hr)]].
      + right; exact X.
      + left. pose proof (AI_aci_img AI iv Hiv). pose proof (AI_aci_lo AI iv Hiv). lia.
      + destruct (HH _ Hin) as (p & A & k & E). discriminate E.
  Qed.

  Lemma hcl_kept : forall K SP SPX a, hb_heap K -> SPX <= SP -> SP <= 2^47 -> hcl CI K SP a -> kept K SPX a.
  Proof.
    intros K SP SPX a HH HS H47 [[Ha _]|Ha]; [exact (aclient_kept K SP SPX a HH HS Ha)|].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    right; right; right. apply (kshd_intro ATOP SP); [right; lia| pose proof ATOP_al16; Z.div_mod_to_equations; lia| exact Ha].
  Qed.

  (* [comment removed for export] *)
  Lemma hcl_of_munch : forall L RNG st K LB' m W SPX SP m1 m2, AHEAP AI L RNG st LB' m -> hb_heap K -> (forall b, In b K -> In b LB') ->
    ATOP <= SPX -> SPX <= SP -> SP <= 2^47 -> Forall (wok K LB' L SPX) W -> munch W m1 m2 -> wmono bsegs m1 m2 ->
    magree bsegs (hcl CI K SP) m1 m2.
  Proof.
    intros L RNG st K LB' m W SPX SP m1 m2 AH HH HI HS HSP H47 FW MU WM.
    eapply magree_mono; [exact (kept_of_munch L RNG st K LB' m W SPX m1 m2 AH HH HI HS FW MU WM)|]. cbv beta.
    intros a Ha. exact (hcl_kept K SP SPX a HH HSP H47 Ha).
  Qed.

  (* [comment removed for export] *)
  Lemma hcl_of_cell : forall K SP m1 m2,
    munch [(APDCTX, APDCTX + 8)] m1 m2 -> wmono bsegs m1 m2 -> magree bsegs (hcl CI K SP) m1 m2.
  Proof.
    intros K SP m1 m2 MU WM. eapply magree_mono; [exact (magree_of_munch bsegs _ m1 m2 MU WM)|]. cbv beta.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    intros a [[_ NC]|Ha]; cbn [outside]; (split; [| exact I]); unfold acell, APDCTX in *; [exact NC|].
    rewrite !shad_div in Ha. unfold ASHOFF in Ha. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hcl_of_aheap_pres : forall K LB' SP SP' m1 m2, aheap_pres CI LB' SP' m1 m2 -> (forall b, In b K -> In b LB') ->
    SP' <= SP -> SP <= 2^47 -> magree bsegs (hcl CI K SP) m1 m2.
  Proof.
    intros K LB' SP SP' m1 m2 HP HI HS H47 a Ha Hc. apply (aheap_pres_weaken CI LB' K SP' SP m1 m2 HP HS HI a Ha).
    destruct Hc as [[Hc _]|Hc]; [exact Hc|].
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. pose proof ATOP_al16 as A16.
    right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
    rewrite !shad_div in Hc. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fresh_not_in : forall L RNG st LB m b, AHEAP AI L RNG st (b :: LB) m -> ~ In b LB.
  Proof.
    intros L RNG st LB m b AH. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND. inversion ND; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma areg_block : forall L RNG st LB m p A n A' n', AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    A <= A' -> 0 <= n' -> A' + n' <= A + n -> areg RNG m A' n'.
  Proof.
    intros L RNG st LB m p A n A' n' AH Hin H1 H2 H3 Hpos.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (N & (BR & B2 & B3 & B4) & RA & RS & SHB & WR & _ & _).
    split; [eapply ablk_sub; [exact BR| lia| lia]|].
    assert (A8 : A mod 8 = 0) by (clear - B4; Z.div_mod_to_equations; lia).
    pose proof (ablk_lin _ _ BR) as (X1 & X2 & X3 & X4).
    assert (UA : unpoisoned m A (A + n)) by (apply ablock_unpoisoned; [exact SHB| exact A8| lia| lia| lia]).
    split; [eapply unpoisoned_sub; [exact UA| lia| lia]|].
    split; [eapply rng_sub'; [exact RA| lia]|].
    eapply rng_sub'; [exact RS|]. rewrite shlenE. rewrite !shad_div. unfold shspan. Z.div_mod_to_equations. lia.
  Qed.

  Lemma aro_block : forall L RNG st LB m p A n A' n', AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    A <= A' -> 0 < n' -> A' + n' <= A + n -> aro RNG m A' n'.
  Proof.
    intros L RNG st LB m p A n A' n' AH Hin H1 H2 H3.
    exact (aregU_aro _ _ _ _ (areg_block L RNG st LB m p A n A' n' AH Hin H1 ltac:(lia) H3 H2)).
  Qed.

  Lemma ahull_block : forall L RNG st LB m p A n A' n', AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    A <= A' -> 0 <= n' -> A' + n' <= A + n -> ahull RNG m A' n'.
  Proof.
    intros L RNG st LB m p A n A' n' AH Hin H1 H2 H3.
    destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hin) as (N & (BR & B2 & B3 & B4) & RA & RS & SHB & WR & _ & RLO & RHI & L1 & L2 & L3 & L4 & R5 & W6).
    pose proof (ablk_lin _ _ BR) as (X1 & X2 & X3 & X4). unfold AIMG_HI in X1.
    destruct (block_hull RNG m A n RLO RHI ltac:(lia) L1 L2 L3 L4 ltac:(lia) R5 W6) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    pose proof (hull_props A n ltac:(lia)) as (_ & _ & _ & _ & _ & P6).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    exists (hull_lo A), (hull_hi A n). unfold KEND.
    split; [lia|]. split; [lia|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [lia|].
    split; [exact Q2| exact Q1].
  Qed.

  Lemma ainblk_block : forall LB p A n A' n', In (HB p A n) LB -> A <= A' -> A' + n' <= A + n -> ainblk LB A' n'.
  Proof. intros LB p A n A' n' Hin H1 H2. exists (HB p A n). split; [exact Hin| cbn; lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma art_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> art m.
  Proof.
    intros L RNG st LB m AH. pose proof (AI_rtcells AI _ _ _ _ _ AH) as (_ & A & B & C & D & E & F & G & _).
    unfold art. split; [exact A|]. split; [exact B|]. split; [exact D|]. split; [exact F|]. split; [exact G| exact C].
  Qed.

  (* [comment removed for export] *)
  Lemma got_trace_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m ->
    rw_cells bsegs m 0xc7fd0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Proof.
    intros L RNG st LB m AH.
    pose proof (relro_C8 AI L RNG st LB m 0xc7fd0 0 AH ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C1.
    pose proof (relro_C8 AI L RNG st LB m 0xc7fd8 0 AH ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as C2.
    apply (proj2 (rw_cells_app bsegs m 0xc7fd0 [C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 0)])). split; [exact C1|].
    cbn [cells_size csize Nat.add]. replace (0xc7fd0 + Z.of_nat 8) with 0xc7fd8 by lia. exact C2.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma payload_newblock : forall L RNG st LB LB' m D pl p A n, AHEAP AI L RNG st LB' m -> (forall b, In b LB -> In b LB') ->
    payload_atA LB D pl -> In (HB p A n) LB' -> ~ In (HB p A n) LB -> (D + zlength pl <= A \/ A + n <= D).
  Proof.
    intros L RNG st LB LB' m D pl p A n AH HI PAY Hin HNK.
    destruct (block_geom _ _ _ _ _ _ _ _ AH Hin) as (BR & B1 & B2 & B3 & B4).
    destruct PAY as [(q & Hq & POS)|(-> & ->)].
    - assert (NE : HB q D (zlength pl) <> HB p A n) by (intros E; apply HNK; rewrite <- E; exact Hq).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH (HI _ Hq) Hin NE) as DJ. cbn [ab_addr ab_size] in DJ. lia.
    - replace (zlength (@nil Z)) with 0 by reflexivity. unfold AEMPTY, AIMG_HI in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma payload_facts : forall L RNG st LB LB' m D pl, AHEAP AI L RNG st LB' m -> (forall b, In b LB -> In b LB') ->
    payload_atA LB D pl -> rng_aimg RNG -> rng RNG 0x7fffa000 0xc2a00 ->
    4096 <= D /\ D + zlength pl <= ATOP /\ D mod 8 = 0 /\
    aro RNG m D (zlength pl) /\ areg RNG m D (zlength pl) /\ (0 < zlength pl -> ainimg LB' D (zlength pl)) /\
    (kimg D /\ zlength pl = 0 \/ in_block LB D).
  Proof.
    intros L RNG st LB LB' m D pl AH HI PAY RI RS. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct PAY as [(q & Hq & POS)|(PE & DE)].
    - destruct (block_geom _ _ _ _ _ _ _ _ AH (HI _ Hq)) as (BR & B1 & B2 & B3 & B4). unfold AIMG_HI in B4.
      pose proof (areg_block L RNG st LB' m q D (zlength pl) D (zlength pl) AH (HI _ Hq) ltac:(lia) ltac:(lia) ltac:(lia)) as AR.
      split; [lia|]. split; [lia|]. split; [clear - B3; Z.div_mod_to_equations; lia|].
      split; [exact (aregU_aro _ _ _ _ (AR POS))|]. split; [exact AR|].
      split; [intros _; left; exact (ainblk_block LB' q D (zlength pl) D (zlength pl) (HI _ Hq) ltac:(lia) ltac:(lia))|].
      right. exists (HB q D (zlength pl)). split; [exact Hq| cbn; lia].
    - subst pl D. replace (zlength (@nil Z)) with 0 by reflexivity. unfold AEMPTY. rewrite ?Z.add_0_r.
      split; [lia|]. split; [lia|]. split; [reflexivity|].
      split.
      { split; [apply unpoisoned_nil; lia|]. split; [eapply rng_sub; [exact RI| lia| lia]|].
        unfold shspan. rewrite shad_div. unfold ASHOFF. eapply rng_sub; [exact RS| |]; cbn; lia. }
      split; [apply areg_empty|]. split; [intros H; lia|]. left. unfold kimg, AIMG_HI. split; [lia| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma payload_ahull : forall L RNG st LB LB' m D pl, AHEAP AI L RNG st LB' m -> (forall b, In b LB -> In b LB') ->
    payload_atA LB D pl -> 0 < zlength pl -> ahull RNG m D (zlength pl).
  Proof.
    intros L RNG st LB LB' m D pl AH HI PAY POS. destruct PAY as [(q & Hq & _)|(PE & DE)].
    - exact (ahull_block L RNG st LB' m q D (zlength pl) D (zlength pl) AH (HI _ Hq) ltac:(lia) ltac:(lia) ltac:(lia)).
    - exfalso. subst pl. unfold zlength in POS. cbn in POS. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma payload_kept : forall K SPX m1 m2 D pl, magree bsegs (kept K SPX) m1 m2 -> payload_atA K D pl ->
    bytes_at bsegs m1 D (map (Z_to_bv 8) pl) -> bytes_at bsegs m2 D (map (Z_to_bv 8) pl).
  Proof.
    intros K SPX m1 m2 D pl AG PAY B. destruct PAY as [(q & Hq & POS)|(PE & DE)].
    - eapply bytes_at_magree; [exact AG| exact B|]. rewrite length_map. intros a Ha.
      right; right; left. exists (HB q D (zlength pl)). split; [exact Hq| cbn; unfold zlength; lia].
    - subst. cbn. apply bytes_at_nil. unfold AEMPTY. lia.
  Qed.

  Lemma payload_apres : forall K LB' SP' m1 m2 D pl, aheap_pres CI LB' SP' m1 m2 -> (forall b, In b K -> In b LB') ->
    payload_atA K D pl -> bytes_at bsegs m1 D (map (Z_to_bv 8) pl) -> bytes_at bsegs m2 D (map (Z_to_bv 8) pl).
  Proof.
    intros K LB' SP' m1 m2 D pl HP HI PAY B. destruct PAY as [(q & Hq & POS)|(PE & DE)].
    - eapply aheap_pres_bytes_at; [exact HP| exact B|]. rewrite length_map.
      right; left. exists (HB q D (zlength pl)). split; [exact (HI _ Hq)| cbn; unfold zlength; lia].
    - subst. cbn. apply bytes_at_nil. unfold AEMPTY. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma frame_apres : forall LB' SP' SPX m1 m2 cs, aheap_pres CI LB' SP' m1 m2 -> SP' <= SPX ->
    SPX + Z.of_nat (cells_size cs) <= 2^47 -> rw_cells bsegs m1 SPX cs -> rw_cells bsegs m2 SPX cs.
  Proof. intros LB' SP' SPX m1 m2 cs HP HS H47 FR. eapply aheap_pres_rw_cells; [exact HP| exact FR| left; left; lia]. Qed.

  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv CI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv CI.

  Lemma cell_apres : forall LB' SP' m1 m2 v, aheap_pres CI LB' SP' m1 m2 ->
    rw_cells bsegs m1 APDCTX [C8 v] -> rw_cells bsegs m2 APDCTX [C8 v].
  Proof.
    intros LB' SP' m1 m2 v HP C. eapply aheap_pres_rw_cells; [exact HP| exact C|].
    left; right; left. exists (0x602380, 0x6023a0). split; [apply CLI_CI; unfold cli_img_ranges; left; reflexivity| unfold APDCTX; cbn; lia].
  Qed.

  Lemma aroM_apres : forall LB' SP' m1 m2, aheap_pres CI LB' SP' m1 m2 -> aro_clientM m1 -> aro_clientM m2.
  Proof.
    intros LB' SP' m1 m2 HP H. eapply (aro_clientM_magree (aclient_addr CI LB' SP')); [exact HP| | exact H].
    intros a Ha. right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
    rewrite !shad_div in Ha. unfold ASHOFF in *.
    destruct (Z_lt_le_dec (8 * (a - 2147450880)) 0x229a0) as [LT|GE].
    - right; left. exists (0x21100, 0x229a0). split; [apply DRV_CI; unfold drv_img_ranges; cbn; tauto|]. cbn [fst snd]. Z.div_mod_to_equations. lia.
    - right; left. exists (0x229a0, 0x229c0). split; [apply CLI_CI; unfold cli_img_ranges; cbn; tauto|]. cbn [fst snd]. Z.div_mod_to_equations. lia.
  Qed.

  Lemma rclean_apres : forall LB' SP' m1 m2 r, aheap_pres CI LB' SP' m1 m2 -> ATOP <= r_rlo r -> rclean m1 r -> rclean m2 r.
  Proof.
    intros LB' SP' m1 m2 r HP HR RC. eapply (rclean_magree (aclient_addr CI LB' SP')); [exact HP| | exact RC].
    intros a Ha. destruct RC as [(_ & HL & _) _]. unfold hull64, KEND in HL.
    right; right; right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad]. left.
    rewrite !shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dctx_any_magree : forall (P : Z -> Prop) m1 m2 DCTX, magree bsegs P m1 m2 -> (forall a, DCTX <= a < DCTX + 95992 -> P a) ->
    dctx_any m1 DCTX -> dctx_any m2 DCTX.
  Proof.
    intros P m1 m2 DCTX AG HP (llt & mlt & oft & huf & pde & pfx & vst & dend & expd & fp & pcs & dsz & bt & stg & le & fe & xs & ws & jhb & ovd & dcb & dce & trace &
                   PT & H1 & [FPC FPSZ] & H3 & [XSC XSSZ] & [H5C H5L] & H5OK & TX & [OWE OWX]).
    assert (TR : forall A cs, rw_cells bsegs m1 A cs -> DCTX <= A -> A + Z.of_nat (cells_size cs) <= DCTX + 95992 -> rw_cells bsegs m2 A cs).
    { intros A cs RC L1 L2. eapply rw_cells_magree; [exact AG | exact RC |]. intros a Ha. apply HP. lia. }
    assert (TS : forall a b, stk bsegs m1 a b -> DCTX <= a -> a <= b -> b <= DCTX + 95992 -> stk bsegs m2 a b).
    { intros a b SK L1 L2 L3. eapply stk_magree; [exact AG | exact SK |]. intros x Hx. apply HP. lia. }
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
    exists llt, mlt, oft, huf, pde, pfx, vst, dend, expd, fp, pcs, dsz, bt, stg, le, fe, xs, ws, jhb, ovd, dcb, dce, trace.
    split; [apply TR; [exact PT | lia | cbn; lia]|].
    split; [apply TR; [exact H1 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact FPC | lia | rewrite FPSZ; lia]| exact FPSZ]|].
    split; [apply TR; [exact H3 | lia | cbn; lia]|].
    split; [split; [apply TR; [exact XSC | lia | rewrite XSSZ; lia]| exact XSSZ]|].
    split; [split; [apply TR; [exact H5C | lia | rewrite (h5_cells_size _ H5L); lia]| exact H5L]|].
    split; [exact H5OK|].
    split; [apply TR; [exact TX | lia | cbn; lia]|].
    split; apply TS; try assumption; lia.
  Qed.

  Lemma dctx_apres : forall LB' SP' m1 m2 p DC, aheap_pres CI LB' SP' m1 m2 -> In (HB p DC DCTX_SIZE) LB' ->
    dctx_any m1 DC -> dctx_any m2 DC.
  Proof.
    intros LB' SP' m1 m2 p DC HP Hin DA. eapply (dctx_any_magree (aclient_addr CI LB' SP')); [exact HP| | exact DA].
    intros a Ha. right; right; left. exists (HB p DC DCTX_SIZE). split; [exact Hin| cbn; unfold DCTX_SIZE; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma frame_kept : forall K SPX m1 m2 cs, magree bsegs (kept K SPX) m1 m2 -> SPX + Z.of_nat (cells_size cs) <= 2^47 ->
    rw_cells bsegs m1 SPX cs -> rw_cells bsegs m2 SPX cs.
  Proof. intros K SPX m1 m2 cs AG H47 FR. eapply rw_cells_magree; [exact AG| exact FR| intros a Ha; right; left; lia]. Qed.

  Lemma cell_kept : forall K SPX m1 m2 v, magree bsegs (kept K SPX) m1 m2 ->
    rw_cells bsegs m1 APDCTX [C8 v] -> rw_cells bsegs m2 APDCTX [C8 v].
  Proof.
    intros K SPX m1 m2 v AG C. eapply rw_cells_magree; [exact AG| exact C|]. intros a Ha. left. unfold kimg, APDCTX, AIMG_HI in *. cbn in Ha. lia.
  Qed.

  Lemma got_kept : forall K SPX m1 m2 cs, magree bsegs (kept K SPX) m1 m2 ->
    rw_cells bsegs m1 0xc7fd0 cs -> Z.of_nat (cells_size cs) <= 16 -> rw_cells bsegs m2 0xc7fd0 cs.
  Proof.
    intros K SPX m1 m2 cs AG C HS. eapply rw_cells_magree; [exact AG| exact C|]. intros a Ha. left. unfold kimg, AIMG_HI in *. lia.
  Qed.

  Lemma aroM_kept : forall K SPX m1 m2, magree bsegs (kept K SPX) m1 m2 -> aro_clientM m1 -> aro_clientM m2.
  Proof.
    intros K SPX m1 m2 AG H. eapply aro_clientM_magree; [exact AG| | exact H].
    intros a Ha. right; right; right. apply (kshd_intro 0x21100 0x229c0); [left; unfold AIMG_HI; lia| reflexivity| exact Ha].
  Qed.

  Lemma rclean_kept : forall K SPX m1 m2 r, magree bsegs (kept K SPX) m1 m2 -> ATOP <= r_rlo r -> rclean m1 r -> rclean m2 r.
  Proof.
    intros K SPX m1 m2 r AG HR RC. eapply rclean_magree; [exact AG| | exact RC].
    intros a Ha. destruct RC as [(_ & HL & _) _]. unfold hull64, KEND in HL.
    right; right; right. apply (kshd_intro (r_rlo r) (r_rhi r)); [right; lia| clear - HL; Z.div_mod_to_equations; lia| exact Ha].
  Qed.

  Lemma dctx_kept : forall K SPX m1 m2 p DC, magree bsegs (kept K SPX) m1 m2 -> In (HB p DC DCTX_SIZE) K ->
    dctx_any m1 DC -> dctx_any m2 DC.
  Proof.
    intros K SPX m1 m2 p DC AG Hin DA. eapply dctx_any_magree; [exact AG| | exact DA].
    intros a Ha. right; right; left. exists (HB p DC DCTX_SIZE). split; [exact Hin| cbn; unfold DCTX_SIZE; lia].
  Qed.

  Lemma prod_kept : forall K SPX m1 m2 p P cs, magree bsegs (kept K SPX) m1 m2 -> In (HB p P PRODUCER_SIZE) K ->
    rw_cells bsegs m1 P cs -> Z.of_nat (cells_size cs) <= 16 -> rw_cells bsegs m2 P cs.
  Proof.
    intros K SPX m1 m2 p P cs AG Hin C HS. eapply rw_cells_magree; [exact AG| exact C|].
    intros a Ha. right; right; left. exists (HB p P PRODUCER_SIZE). split; [exact Hin| cbn; unfold PRODUCER_SIZE; lia].
  Qed.

  Lemma prod_apres : forall LB' SP' m1 m2 p P cs, aheap_pres CI LB' SP' m1 m2 -> In (HB p P PRODUCER_SIZE) LB' ->
    rw_cells bsegs m1 P cs -> Z.of_nat (cells_size cs) <= 16 -> rw_cells bsegs m2 P cs.
  Proof.
    intros LB' SP' m1 m2 p P cs HP Hin C HS. eapply aheap_pres_rw_cells; [exact HP| exact C|].
    right; left. exists (HB p P PRODUCER_SIZE). split; [exact Hin| cbn; unfold PRODUCER_SIZE; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma azstk_of_rclean : forall RNG m r lo hi, rclean m r -> rrng RNG r -> r_lo r <= lo -> lo <= hi -> hi <= r_hi r ->
    azstk RNG m lo hi.
  Proof.
    intros RNG m r lo hi [(U & HL & W & AB) LT] RR H1 H2 H3. unfold hull64 in HL. exists (r_rlo r), (r_rhi r).
    split; [eapply unpoisoned_sub; [exact U| lia| lia]|]. split; [lia|]. split; [exact W|].
    split; [eapply app_blk_sub; [exact AB| lia| lia| lia]| exact RR].
  Qed.
End HK.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implMA_retbH : forall {X Y} RNG (a : X) (f : X -> @Monad.M APS Y) (s : APS) Q ms,
  implMA RNG (f a) s Q ms -> implMA RNG (Monad.mbind (Monad.mret a) f) s Q ms.
Proof. intros X Y RNG a f s Q ms H. exact H. Qed.

Lemma implMA_bind_assocH : forall {X Y W} RNG (ma : @Monad.M APS X) (g : X -> @Monad.M APS Y) (f : Y -> @Monad.M APS W) s Q ms,
  implMA RNG (Monad.mbind ma (fun a => Monad.mbind (g a) f)) s Q ms -> implMA RNG (Monad.mbind (Monad.mbind ma g) f) s Q ms.
Proof.
  intros X Y W RNG ma g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
  apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
  intros [|[a s']] RNG' ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
Qed.
End CANSEC1.
