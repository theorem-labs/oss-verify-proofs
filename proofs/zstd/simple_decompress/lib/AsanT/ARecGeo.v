(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ABytes AQConst AModelFacts ARep ARepKit ARepFrame ALayout AHeapP
     AMalloc_iface ARepQ ARepQP AFreeRep AFreeGeo AFreeRead AFrameD ASecFacts ARefillP F_arefill F_acdealloc F_arecyc1 ASecRecycle_iface ARecyc1P.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma outside_of_In : forall W x, (forall iv, In iv W -> ~ (fst iv <= x < snd iv)) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn; [exact I|]. split; [exact (H (lo, hi) (or_introl eq_refl))|].
  apply IH. intros iv Hiv. apply H. right. exact Hiv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Geo.
Variables (L : alayout) (st : astate) (X : aconc).
Hypothesis ALO : alayout_ok L.
Hypothesis WF : awf L st X.

(* [comment removed for export] *)
Lemma busy_slot_geo : forall b, In b (x_busy X) ->
     1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b)
  /\ aregion L (xb_class b) <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= aregion L (xb_class b) + c_allocated_user (get_cls st (xb_class b))
  /\ (al_space_beg L <= aregion L (xb_class b) /\ c_allocated_user (get_cls st (xb_class b)) <= c_mapped_user (get_cls st (xb_class b)) <= K_FREEARR_OFF
      /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE)
  /\ 0x10007fff8000 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= ATOP
  /\ al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104.
Proof.
  intros b Hb. pose proof WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & _).
  destruct (BUSY b Hb) as [CLB _]. destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
  pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
  assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
  { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
    apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
  pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF CLB KB) as (S1 & S2 & AL & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof (ao_space L ALO) as RSP.
  assert (RS : al_space_beg L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize CLB. clear. unfold aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold xb_alloc. split; [exact CLB|]. split; [exact KB|]. split; [exact G1|]. split; [exact G2|]. split; [split; [exact (proj1 RS)| split; [clear -G3 G4; lia| exact (proj2 RS)]]|].
  split; [exact G7|]. split; [exact G8|]. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. split; lia.
Qed.
End Geo.

Lemma in_ic_W : forall L i d iv, In iv (ic_W L i d) -> exists j, i <= j /\ j < i + Z.of_nat d /\ iv = (acache_addr L j + 4, acache_addr L j + 16).
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i iv Hin; cbn [ic_W] in Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists i; split; [lia| split; [lia| reflexivity]]|].
  destruct (IH (i + 1) iv Hin) as (j & A & B & E). exists j. split; [lia| split; [lia| exact E]].
Qed.

(* [comment removed for export] *)
Definition lowpiece (L : alayout) (c : Z) (iv : Z * Z) : Prop :=
  0 <= fst iv /\ snd iv <= ATOP /\ ((shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
                                    \/ al_t L <= fst iv /\ snd iv <= al_t L + 4096
                     \/ aregion L c + K_FREEARR_OFF <= fst iv /\ snd iv <= aregion L c + K_REGION
                     \/ al_space_beg L + K_SPACE_SIZE <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

Lemma cd_W_cases : forall L sp c nf mfa mfa' iv,
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (cd_W L sp c nf mfa mfa') -> iv = (sp - 688, sp) \/ lowpiece L c iv.
Proof.
  intros L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin. unfold lowpiece.
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & _).   (* [comment removed for export] *)
  assert (FAS : shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000 /\ 0x10007fff8000 <= afreearr L c /\ afreearr L c + mfa' <= aregion L c + K_REGION
                /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                /\ shad (al_space_beg L) <= shad (afreearr L c + mfa) /\ shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= shad (al_space_beg L + K_SPACE_SIZE)).
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE, K_SPACE_EXTRA, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
    rewrite !shad_div, shlen_div. unfold ASHOFF. clear -HC SP1 SP2 NF0 NF4 MFA. Z.div_mod_to_equations. lia. }
  destruct FAS as (FA1 & FA2 & FA3 & FA4 & FA5 & FA6).
  unfold cd_W in Hin. cbv zeta in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  assert (CAB : forall j, 1 <= j -> j <= 32 -> al_t L <= acache_addr L j /\ acache_addr L j + 80 <= al_t L + 4096) by (intros j A B; unfold acache_addr; clear -A B; lia).
  assert (RIB : al_space_beg L + 137438953472 <= aregion_info L c /\ aregion_info L c + 128 <= al_space_beg L + 137438953472 + 4096).
  { unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. unfold K_NUM_CLASSES in HC. clear -HC. lia. }
  destruct Hin as [[E|F] | [Hic | H9]]; try (destruct F); try subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. apply in_ic_W in Hic. destruct Hic as (j & J1 & J2 & ->). cbn [fst snd]. destruct (CAB j ltac:(clear -J1; lia) ltac:(clear -J2; cbn in J2; lia)) as [C1 C2].
    split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
  - destruct H9 as [E|[E|[E|[E|[E|[E|[E|[E|[E|F]]]]]]]]]; try (destruct F); subst iv; cbn [fst snd]; right.
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + destruct (CAB c ltac:(clear -HC; lia) ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [C1 C2]. split; [clear -C1 TL1; lia|]. split; [clear -C2 TL2; lia| right; left; clear -C1 C2; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
    + split; [unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA2; lia|]. split; [clear -FA3 FA4 SP2; lia| right; right; left; unfold afreearr, K_FREEARR_OFF in *; clear -NF0 FA3; lia].
    + split; [rewrite shad_div; unfold ASHOFF; clear -FA2 NF0 NF4; Z.div_mod_to_equations; lia|]. split; [clear -FA1; lia| left; clear -FA1 FA5 FA6; unfold K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; repeat split; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
    + split; [clear -RIB SP1; lia|]. split; [clear -RIB SP2; lia| right; right; right; clear -RIB; lia].
Qed.

(* [comment removed for export] *)
Lemma rec_W_cases : forall L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  In iv (rec_W L sp c kk n nf mfa mfa') ->
  let AB := aslot_addr L c kk in let S := size_of_class c in
  iv = (sp - 688, sp) \/ (AB <= fst iv /\ snd iv <= AB + S) \/ lowpiece L c iv.
Proof.
  intros L st X sp c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin. cbv zeta.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & _).
  pose proof (chunk_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as (_ & _ & G3 & G4 & _ & G6 & G7 & _).
  pose proof (chunk_shadow_geo L st X c kk n ALO WF HC KR (proj1 N0) FIT0) as (SE & _ & GE & SG0 & SGF & SHLO & SHHI & _).
  pose proof (alayout_t_lin L ALO) as (TL1 & TL2). pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].   (* [comment removed for export] *)
  unfold rec_W in Hin. cbv zeta in Hin. apply in_app_iff in Hin.
  destruct Hin as [Hin|Hin]; [| destruct (cd_W_cases L sp c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hin) as [E|P]; [left; exact E| right; right; exact P]].
  unfold lowpiece in *. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|F]]]]]; try (destruct F); subst iv; cbn [fst snd].
  - left. reflexivity.
  - right. left. clear -RZ1 G6 N0; unfold rup in *; split; lia.
  - right. left. clear -RZ1 G3 G6 N0; unfold rup in *; split; lia.
  - pose proof (slot_geo L st X c kk ALO WF HC KR) as (_ & _ & _ & _ & _ & _ & _ & Q5 & Q6 & _).
    assert (SB : shad (al_space_beg L) <= shad (aslot_addr L c kk) /\ shad (aslot_addr L c kk) + shlen (size_of_class c) <= shad (al_space_beg L + K_SPACE_SIZE)).
    { rewrite !shad_div, shlen_div. clear -Q5 Q6. Z.div_mod_to_equations. lia. }
    right. right. split; [clear -SE SHLO SG0 GE RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); lia|].
    split; [clear -SE SGF SHHI SG0 GE TL1 TL2; lia| left; clear -SE SGF SHHI SG0 GE SB RZ1; pose proof (shlen_nonneg (rz_size n) ltac:(lia)); repeat split; lia].
  - right. right. split; [clear -TL1; lia|]. split; [clear -TL2; lia| right; left; clear; lia].
Qed.

(* [comment removed for export] *)
Lemma lowpiece_vs_slot : forall L st X c b iv, alayout_ok L -> awf L st X -> 1 <= c < K_NUM_CLASSES -> In b (x_busy X) ->
  lowpiece L c iv -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b.
Proof.
  intros L st X c b iv ALO WF HC Hb (Pz & P0 & P).
  pose proof (busy_slot_geo L st X ALO WF b Hb) as (CLB & KB & G1 & G2 & (G3a & G3 & G3b) & G4 & G5 & G6 & G7).
  pose proof (ad_t_res L ALO) as DTR. pose proof (ao_space L ALO) as RSP. unfold adisj in DTR.
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [(_ & _ & P)|[P|[P|P]]].
  - right. clear -P G4. lia.
  - clear -P DTR RSP G6 G7. lia.
  - destruct (Z.eq_dec (xb_class b) c) as [<-|NC].
    + left. clear -P G2 G3. lia.
    + pose proof (region_other_geo L c (xb_class b) ALO ltac:(unfold K_NUM_CLASSES in HC; exact HC) ltac:(unfold K_NUM_CLASSES in CLB; exact CLB) NC) as (_ & RD & _).
      clear -P G1 G2 G3 RD. lia.
  - left. clear -P G2 G3 G3b. lia.
Qed.

(* [comment removed for export] *)
Definition wpiece (L : alayout) (lo SP : Z) (iv : Z * Z) : Prop :=
     (lo <= fst iv /\ snd iv <= SP)
  \/ (shad (al_space_beg L) <= fst iv /\ snd iv <= shad (al_space_beg L + K_SPACE_SIZE) /\ snd iv <= 0x10007fff8000)
  \/ (al_t L <= fst iv /\ snd iv <= al_t L + 4096)
  \/ (al_space_beg L <= fst iv /\ snd iv <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA).

Lemma lowpiece_wpiece : forall L lo SP c iv, 1 <= c < K_NUM_CLASSES -> lowpiece L c iv -> wpiece L lo SP iv.
Proof.
  intros L lo SP c iv HC (_ & _ & P). unfold wpiece.
  assert (RS : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^32) with 4294967296 in *. change (2^37) with 137438953472 in *.
  destruct P as [P|[P|[P|P]]]; [right; left; exact P| right; right; left; exact P| right; right; right; clear -P RS; lia| right; right; right; clear -P; lia].
Qed.

Lemma wpiece_fake : forall L lo SP iv, alayout_ok L -> ATOP <= lo -> wpiece L lo SP iv ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xc90f0 \/ 0xc90f0 + 8 <= fst iv) /\ (snd iv <= 0x602ca8 \/ 0x602ca8 + 16 <= fst iv)
  /\ (snd iv <= 0x602cb8 \/ 0x602cb8 + 8 <= fst iv) /\ (snd iv <= 0x602cd8 \/ 0x602cd8 + 8 <= fst iv)
  /\ (snd iv <= 0x1618b1 \/ 0x1618b1 + 1 <= fst iv) /\ (snd iv <= 0x15f798 \/ 0x15f798 + 4 <= fst iv).
Proof.
  intros L lo SP iv ALO CEIL P. unfold wpiece in P.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_space L ALO) as RSP. pose proof (ao_space_al L ALO) as SAL.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj in OF, OD, OT, ORS. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OD, OT.   (* [comment removed for export] *)
  unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (SHF : shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L) \/ shad (al_space_beg L + 137438953472) <= shad (al_fake L)).
  { rewrite !shad_div, shlen_div. clear -DFR RSP OF SAL. Z.div_mod_to_equations. lia. }
  assert (SHB : 2201439137792 <= shad (al_space_beg L) /\ 2147450880 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF. clear -RSP ORS RHI OF AR. Z.div_mod_to_equations. lia. }
  destruct P as [P|[P|[P|P]]]; clear -P OF OD OT ORS RHI AR RSP DFR DDR DTF DTD CEIL SHF SHB; repeat split; lia.
Qed.

Lemma fake_untouched_of : forall L W,
  (forall iv, In iv W ->
     (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
  /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
  /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
  /\ (snd iv <= 0xc90f0 \/ 0xc90f0 + 8 <= fst iv) /\ (snd iv <= 0x602ca8 \/ 0x602ca8 + 16 <= fst iv)
  /\ (snd iv <= 0x602cb8 \/ 0x602cb8 + 8 <= fst iv) /\ (snd iv <= 0x602cd8 \/ 0x602cd8 + 8 <= fst iv)
  /\ (snd iv <= 0x1618b1 \/ 0x1618b1 + 1 <= fst iv) /\ (snd iv <= 0x15f798 \/ 0x15f798 + 4 <= fst iv)) ->
  fake_untouched L W.
Proof. intros L W H. unfold fake_untouched. apply Forall_forall. exact H. Qed.

Lemma rec_W_wpiece : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> lo <= SP - 688 ->
  In iv (rec_W L SP c kk n nf mfa mfa') -> wpiece L lo SP iv.
Proof.
  intros L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA LO Hin.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hin) as [E|[SL|LP]].
  - left. subst iv. cbn. lia.
  - right. right. right. pose proof (slot_geo L st X c kk ALO WF HC KR) as (_ & _ & _ & _ & _ & _ & _ & G5 & G6 & _). unfold K_SPACE_EXTRA. clear -SL G5 G6. lia.
  - eapply lowpiece_wpiece; [exact HC| exact LP].
Qed.

Lemma rec_W_fake : forall L st X lo SP c kk n b1 ctx l1 l2 nf mfa mfa',
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros. apply fake_untouched_of. intros iv Hiv. eapply wpiece_fake; [eassumption| eassumption|]. eapply rec_W_wpiece; eassumption.
Qed.

Lemma cd_W_fake : forall L lo SP c nf mfa mfa',
  alayout_ok L -> 1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX -> ATOP <= lo -> lo <= SP - 688 ->
  fake_untouched L (cd_W L SP c nf mfa mfa').
Proof.
  intros L lo SP c nf mfa mfa' ALO HC NF0 NF4 MFA CEIL LO. apply fake_untouched_of. intros iv Hiv. eapply (wpiece_fake L lo SP); [exact ALO| exact CEIL|].
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P]; [left; cbn [fst snd]; clear -LO; lia| eapply lowpiece_wpiece; [exact HC| exact P]].
Qed.

(* [comment removed for export] *)
Lemma srec_W_pieces : forall L st X lo SP mb ms n nres hl iv,
  alayout_ok L -> awf L st X -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) ->
     ((lo <= fst iv /\ snd iv <= SP)
      \/ (forall b, In b (x_busy X) -> xb_alloc L b + size_of_class (xb_class b) <= fst iv \/ snd iv <= xb_alloc L b) /\ 0 <= fst iv /\ snd iv <= ATOP)
  /\ ((snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
      /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
      /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
      /\ (snd iv <= 0xc90f0 \/ 0xc90f0 + 8 <= fst iv) /\ (snd iv <= 0x602ca8 \/ 0x602ca8 + 16 <= fst iv)
      /\ (snd iv <= 0x602cb8 \/ 0x602cb8 + 8 <= fst iv) /\ (snd iv <= 0x602cd8 \/ 0x602cd8 + 8 <= fst iv)
      /\ (snd iv <= 0x1618b1 \/ 0x1618b1 + 1 <= fst iv) /\ (snd iv <= 0x15f798 \/ 0x15f798 + 4 <= fst iv)).
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO WF SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_dtls L ALO) as OD. pose proof (ao_t L ALO) as OT. pose proof (ao_res L ALO) as ORS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_dtls_res L ALO) as DDR. pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_t_dtls L ALO) as DTD.
  pose proof (ad_t_res L ALO) as DTR. pose proof (ad_ptr_res L ALO) as DPR. pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_dtls_ptr L ALO) as DDP.
  destruct SW as (MB & KH & MCE & _ & _ & _ & SC). destruct SC as (SCt & SCc & SCr & SCp & SCn & SCs & SCf & SCd).
  destruct HLOK as (HK & HC8 & (HCt & HCc & HCr & HCp & HCn & HCs & HCf & HCd)).
  pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold aobj, sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI, adisj, K_HIGH_MEM, AINSTANCE in *.
  assert (SHB : shad (al_fake L) + shlen 11571200 <= 17594332446720 /\ 0 <= shad mb /\ shad mb + shlen ms <= shad (mb + ms) /\ shad (mb + ms) <= 17594332446720
                /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb) /\ 2148256256 <= shad mb /\ 2148256256 <= shad (al_fake L)).   (* [comment removed for export] *)
  { rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -OF MCE KH SCf AR. Z.div_mod_to_equations. lia. }
  destruct SHB as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7).
  assert (BB : forall b, In b (x_busy X) -> al_res L + 4096 <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104 /\ 17594333495296 <= xb_alloc L b).
  { intros b Hb. pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & G4 & _ & G6 & G7). unfold K_HIGH_MEM in *. clear -G4 G6 G7. lia. }
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd].
  - split; [left; clear -LO; lia|]. clear -OF OD CEIL LO SH1 SH7 AR. repeat split; lia.
  - split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B1 B2 DTR; lia| clear -OT; lia]|]. clear -OF OD OT DTF DTD SH1 SH7. repeat split; lia.
  - unfold AINSTANCE. split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B3; lia| clear -AR; lia]|]. clear -OF OD SH1 SH7. repeat split; lia.
  - split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B1 B2 DPR NR0 NR1; lia| clear -OP NR0 NR1; lia]|]. clear -OF OD OP DFP DDP SH1 SH7 NR0 NR1. repeat split; lia.
  - split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B1 B2 SCr; lia| clear -KH MCE; lia]|]. clear -OF OD KH MCE SCf SCd SH1 SH7. repeat split; lia.
  - split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B3 SH3 SH4; lia| clear -SH2 SH3 SH4 AR; lia]|]. clear -OF OD SH1 SH2 SH3 SH4 SH5 SH6. repeat split; lia.
  - split; [right; split; [intros b Hb; destruct (BB b Hb) as (B1 & B2 & B3); clear -B1 B2 HCr; lia| clear -HK HC8; lia]|]. clear -OF OD HK HC8 HCf HCd SH1 SH7. repeat split; lia.
Qed.


(* [comment removed for export] *)
Lemma srec_W_t48 : forall L (st : astate) (X : aconc) lo SP mb ms n nres hl iv,
  alayout_ok L -> sec_wf1 L (CSec mb ms n) -> srec_hl_ok L hl -> 0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 ->
  In iv (srec_W L SP mb ms nres ++ [(hl, hl + 8)]) -> snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv.
Proof.
  intros L st X lo SP mb ms n nres hl iv ALO SW HLOK NR0 NR1 CEIL LO Hin.
  unfold srec_W in Hin. rewrite in_app_iff in Hin. cbn [In] in Hin.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ptr L ALO) as OP. pose proof (ad_t_ptr L ALO) as DTP. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OT, OP, DTP.   (* [comment removed for export] *)
  destruct SW as (MAL & MLO & MCE & _ & _ & _ & (SCt & _)). destruct HLOK as (HK & HC8 & (HCt & _)). unfold ablk, AIMG_HI, KLS in MLO.
  assert (SHB : 2148256256 <= shad mb /\ shad mb + shlen ms <= 17594332446720) by (pose proof atop_range as AR; rewrite shad_div, shlen_div; unfold ASHOFF in *; clear -MLO MCE AR; Z.div_mod_to_equations; lia).
  unfold K_HIGH_MEM, AINSTANCE in *.
  destruct Hin as [[E|[E|[E|[E|[E|[E|F]]]]]] | [E|F]]; try (destruct F); subst iv; cbn [fst snd];
    first [clear -CEIL LO OT; lia| clear -OT; lia| clear -OT OP DTP NR0 NR1; lia| clear -SCt; lia| clear -SHB OT; lia| clear -HCt; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition astatic (a : Z) : Prop :=
  a < 0x10000 \/ (AINSTANCE <= a < 0xcca30) \/ (0x1a1bc8 <= a < 0x5f1c10) \/ (0xd0f00 <= a < 0x151f30) \/ (0x15f788 <= a < 0x15f78c).

(* [comment removed for export] *)
Definition cprot (L : alayout) (HI : Z) (LB : list ablock) (a : Z) : Prop :=
     HI <= a
  \/ (a < AIMG_HI /\ ~ astatic a)
  \/ in_block LB a
  \/ (al_fake L <= a < al_fake L + 11571200)
  \/ (shad ATOP <= a < shad (2^47))
  \/ (ASHOFF <= a < shad AIMG_HI)
  \/ (shad (al_fake L) <= a < shad (al_fake L + 11571200)).

Definition cpres (L : alayout) (HI : Z) (LB : list ablock) (m m' : amem) : Prop :=
  forall x : word, cprot L HI LB (bv_unsigned x) -> m' x = m x.

Lemma cpres_refl : forall L HI LB m, cpres L HI LB m m.
Proof. intros L HI LB m x _. reflexivity. Qed.
Lemma cpres_trans : forall L HI LB m1 m2 m3, cpres L HI LB m1 m2 -> cpres L HI LB m2 m3 -> cpres L HI LB m1 m3.
Proof. intros L HI LB m1 m2 m3 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.

(* [comment removed for export] *)
Definition np_fp (L : alayout) (HI : Z) (LB : list ablock) (W : list (Z * Z)) : Prop :=
  forall iv, In iv W -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.

Lemma cpres_of_munch : forall L HI LB W m m', munch W m m' -> np_fp L HI LB W -> cpres L HI LB m m'.
Proof.
  intros L HI LB W m m' MU NP x Hx. apply MU. apply outside_of_In. intros iv Hiv R. exact (NP iv Hiv _ R Hx).
Qed.
Lemma np_fp_app : forall L HI LB W1 W2, np_fp L HI LB W1 -> np_fp L HI LB W2 -> np_fp L HI LB (W1 ++ W2).
Proof. intros L HI LB W1 W2 H1 H2 iv Hiv. apply in_app_iff in Hiv. destruct Hiv as [H|H]; [exact (H1 iv H)| exact (H2 iv H)]. Qed.
Lemma np_fp_cons : forall L HI LB iv W, (forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a) -> np_fp L HI LB W -> np_fp L HI LB (iv :: W).
Proof. intros L HI LB iv W H1 H2 iv' [<-|H]; [exact H1| exact (H2 iv' H)]. Qed.
Lemma np_fp_nil : forall L HI LB, np_fp L HI LB [].
Proof. intros L HI LB iv []. Qed.

(* [comment removed for export] *)
Lemma shad_consts : (17594064011264 <= shad ATOP <= 17594332446720) /\ shad (2^47) = 17594333495296 /\ shad AIMG_HI = 2148256256 /\ ASHOFF = 2147450880.
Proof. split; [pose proof atop_range as AR; rewrite shad_div; unfold ASHOFF; lia|]. repeat split; reflexivity. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lb_geo : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  match ab_kind blk with
  | ABHeap p =>
         (exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_alloc L b <= ab_addr blk /\ ab_addr blk + ab_size blk <= xb_alloc L b + size_of_class (xb_class b))
      \/ (exists mb ms n, (a_live st) !! p = Some (CSec mb ms n) /\ sec_wf1 L (CSec mb ms n) /\ mb + SEC_UOFF <= ab_addr blk /\ ab_addr blk + ab_size blk <= mb + ms)
  | ABFake _ => al_fake L <= ab_addr blk /\ ab_addr blk + ab_size blk <= al_fake L + 11571200
  end.
Proof.
  intros L st X LB [[p|cls] A n] ALO WF (B1 & B2 & _) Hin; cbn [ab_kind ab_addr ab_size].
  - destruct (B1 p A n Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EA & G)].
    + left. exists b. split; [exact Hb|]. split; [exact Sb|].
      pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n.
      clear -FIT. lia.
    + right. exists mb, ms, n. split; [exact Lp|]. split; [exact G|]. subst A.
      destruct G as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
      pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as (_ & RZ & _ & RS1 & _ & NS & _ & MSB & _). rewrite <- MSE in MSB.
      unfold SEC_UOFF. clear -RS1 NS MSB. lia.
  - exact (conj (proj1 (B2 cls A n Hin)) (proj2 (proj2 (B2 cls A n Hin)))).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lb_high : forall L st X LB blk, alayout_ok L -> awf L st X -> ablocks L st X LB -> In blk LB ->
  ab_addr blk < ab_addr blk + ab_size blk ->
  AIMG_HI <= ab_addr blk /\ ab_addr blk + ab_size blk <= ATOP /\ (ab_addr blk + ab_size blk <= KLS \/ K_HIGH_MEM <= ab_addr blk).
Proof.
  intros L st X LB blk ALO WF BL Hin NE. pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A n]; cbn [ab_kind ab_addr ab_size] in G |- *.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n' & _ & SW & G1 & G2)].
    + pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & Q4 & Q5 & _). unfold K_HIGH_MEM, AIMG_HI, KLS. clear -G1 G2 Q4 Q5. lia.
    + destruct SW as (_ & MLO & MCE & _). unfold ablk, K_HIGH_MEM, AIMG_HI, KLS in *. unfold SEC_UOFF in G1. clear -G1 G2 MLO MCE. lia.
  - pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, K_HIGH_MEM, AIMG_LO, AIMG_HI, KLS in *. clear -G OF NE. lia.
Qed.

(* [comment removed for export] *)
Lemma np_high : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  ATOP <= A -> B <= HI -> forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HA HB a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4). pose proof atop_range as AR.   (* [comment removed for export] *)
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF.
  assert (SF : shad (al_fake L + 11571200) <= shad ATOP) by (apply shad_mono; clear -OF; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha HA HB OF S1 S2 S3 S4 SF AR; lia).
  destruct C as (blk & Hin & R). pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as (_ & G & _). clear -R G Ha HA. lia.
Qed.

(* [comment removed for export] *)
Lemma np_low : forall L st X LB HI c iv, alayout_ok L -> awf L st X -> ablocks L st X LB -> 1 <= c < K_NUM_CLASSES -> ATOP <= HI ->
  lowpiece L c iv -> forall a, fst iv <= a < snd iv -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI c iv ALO WF BL HC HHI (Pz & P0 & P) a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS, OT.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as DTF. pose proof (ad_fake_res L ALO) as DFR. pose proof (ad_t_res L ALO) as DTR. unfold adisj in DTF, DFR, DTR.
  pose proof (ao_space L ALO) as RSP. pose proof (alayout_space L ALO) as (SP1 & SP2 & _).
  assert (RR : al_space_beg L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE).
  { generalize HC. clear. unfold aregion, K_REGION, K_SPACE_SIZE, K_NUM_CLASSES. change (2^37) with 137438953472. change (2^32) with 4294967296. intros. lia. }
  assert (SHB : shad AIMG_HI <= shad (al_space_beg L) /\ shad (al_space_beg L + K_SPACE_SIZE) <= shad ATOP
                /\ (shad (al_fake L + 11571200) <= shad (al_space_beg L) \/ shad (al_space_beg L + K_SPACE_SIZE) <= shad (al_fake L))).
  { rewrite !shad_div. unfold AIMG_HI, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -OF ORS RSP DFR SP1 SP2. Z.div_mod_to_equations. lia. }
  destruct SHB as (SB1 & SB2 & SB3).
  unfold cprot, astatic, AINSTANCE, AIMG_HI, K_HIGH_MEM, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha P0 HHI. lia.
  - destruct P as [P|[P|[P|P]]]; clear -C Ha P S1 S2 S3 S4 SB1 OT RR SP1; lia.
  - destruct C as (blk & Hin & R). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
      * pose proof (lowpiece_vs_slot L st X c b iv ALO WF HC Hb (conj Pz (conj P0 P))) as D. clear -D G1 G2 R Ha. lia.
      * destruct SW as (_ & MLO & MCE & _ & _ & _ & (SCt & _ & SCr & _)). unfold ablk, AIMG_HI, KLS, K_HIGH_MEM, SEC_UOFF in *.
        destruct P as [P|[P|[P|P]]]; clear -P R Ha G1 G2 MLO MCE SCt SCr S2 S3 SB1 SB2 RR RSP ORS; lia.
    + destruct P as [P|[P|[P|P]]]; clear -P R Ha G OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha OF S1 S3 SB1 SB2 DTF DFR RR RSP ORS; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S1 S2 SB2 OT RR SP1; lia.
  - destruct P as [P|[P|[P|P]]]; clear -P C Ha S3 S4 SB1 OT RR SP1 S2; lia.
  - assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720)
      by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct P as [P|[P|[P|P]]]; clear -P C Ha SF SB3 OT RR SP1 S2; lia.
Qed.

(* [comment removed for export] *)
Lemma np_slot : forall L st X LB HI stt c k n b1 ctx l1 l2 A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  x_busy X = l1 ++ bany stt c k n b1 ctx :: l2 -> (forall p, stt <> BLive p) ->
  aslot_addr L c k <= A -> B <= aslot_addr L c k + size_of_class c ->
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI stt c k n b1 ctx l1 l2 A B ALO WF BL HHI XB NL HA HB a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4).
  assert (IN0 : In (bany stt c k n b1 ctx) (x_busy X)) by (rewrite XB; apply in_app_iff; right; left; reflexivity).
  pose proof (busy_slot_geo L st X ALO WF _ IN0) as (HC & KR & G1 & G2 & (G3a & G3 & G3b) & G4 & G5 & G6 & G7).
  unfold xb_alloc in *. cbn [xb_class xb_slot bany] in *.
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof (ad_fake_res L ALO) as DFR. unfold adisj in DFR.   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]].
  - clear -C Ha HB G5 HHI. lia.
  - clear -C Ha HA G4. lia.
  - destruct C as (blk & Hin & R). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
    destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
    + destruct G as [(b & Hb & Sb & Q1 & Q2)|(mb & ms & n0 & _ & SW & Q1 & Q2)].
      * assert (NEQ : c <> xb_class b \/ k <> xb_slot b).
        { destruct (Z.eq_dec c (xb_class b)) as [EC|NC]; [right| left; exact NC]. intros EK.
          destruct (proj1 (In_X_g X stt c k n b1 ctx l1 l2 XB b) Hb) as [Hl| ->]; [| cbn in Sb; exact (NL p Sb)].
          exact (key_fresh_g L st X stt c k n b1 ctx l1 l2 XB WF b Hl (eq_sym EC) (eq_sym EK)). }
        destruct (busy_slot_geo L st X ALO WF b Hb) as (CLB & KB & _).
        pose proof (slots_sep_any L st X c k (xb_class b) (xb_slot b) ALO WF HC CLB KR KB NEQ) as D.
        unfold xb_alloc in Q1, Q2. clear -D Q1 Q2 R Ha HA HB. lia.
      * destruct SW as (_ & MLO & MCE & _ & _ & _ & (_ & _ & SCr & _)). unfold SEC_UOFF in *. clear -R Ha HA HB Q1 Q2 SCr G6 G7. lia.
    + clear -R Ha HA HB G G6 G7 DFR. lia.
  - clear -C Ha HA HB G6 G7 DFR. lia.
  - clear -C Ha HA G4 S2. lia.
  - clear -C Ha HA G4 S3. lia.
  - assert (SF : shad (al_fake L + 11571200) <= 17594332446720) by (pose proof atop_range as AR; rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    clear -C Ha HA G4 SF. lia.
Qed.

(* [comment removed for export] *)
Lemma np_static : forall L st X LB HI A B, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  (forall a, A <= a < B -> astatic a) -> 0 <= A -> B <= AIMG_HI ->
  forall a, A <= a < B -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI A B ALO WF BL HHI ST A0 BH a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4). pose proof (ST a Ha) as SA.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. pose proof atop_range as AR.   (* [comment removed for export] *)
  unfold cprot, astatic, AIMG_HI, AINSTANCE, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha SA HHI BH OF S1 S2 S3 S4 AR; lia).
  - destruct C as (blk & Hin & R). pose proof (lb_high L st X LB blk ALO WF BL Hin ltac:(clear -R; lia)) as (G & _ & _). unfold AIMG_HI in G. clear -R G Ha BH. lia.
  - assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia). clear -C Ha BH SF. lia.
Qed.

(* [comment removed for export] *)
Lemma np_ptrarr : forall L st X LB HI nres, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  0 <= nres -> 8 * nres <= 8388608 ->
  forall a, al_ptr_array L <= a < al_ptr_array L + 8 * nres -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI nres ALO WF BL HHI N0 N1 a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_ptr L ALO) as OP. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, OP, ORS.   (* [comment removed for export] *)
  pose proof (ad_fake_ptr L ALO) as DFP. pose proof (ad_ptr_res L ALO) as DPR. unfold adisj in DFP, DPR. pose proof atop_range as AR.
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha N0 N1 HHI OF OP DFP S1 S2 S3 S4 SF AR; lia).
  destruct C as (blk & Hin & R). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb & ms & n0 & _ & SW & G1 & G2)].
    + pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & _ & _ & Q6 & Q7). clear -R Ha N0 N1 G1 G2 Q6 Q7 DPR. lia.
    + destruct SW as (_ & MLO & MCE & _ & _ & _ & (_ & _ & _ & SCp & _)). unfold SEC_UOFF in *. clear -R Ha N0 N1 G1 G2 SCp. lia.
  - clear -R Ha N0 N1 G DFP. lia.
Qed.

(* [comment removed for export] *)
Lemma np_secmap : forall L st X LB HI mb ms n, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  forall a, (mb <= a < mb + ms \/ shad mb <= a < shad mb + shlen ms) -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI mb ms n ALO WF BL HHI SW DJ a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4).
  pose proof (ao_fake L ALO) as OF. pose proof (ao_res L ALO) as ORS. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF, ORS. pose proof atop_range as AR.   (* [comment removed for export] *)
  destruct SW as (MAL & MLO & MCE & MSE & NB & NPR & SCL). pose proof SCL as (_ & _ & SCr & _ & _ & _ & SCf & _). unfold ablk, AIMG_HI, KLS in MLO.
  pose proof (sec_facts n ltac:(unfold AREQMAX in *; lia) NPR) as (_ & _ & _ & _ & _ & _ & _ & _ & MSAL & _). rewrite <- MSE in MSAL.
  assert (SH : shad mb + shlen ms = shad (mb + ms) /\ shad (mb + ms) <= shad ATOP /\ 2148256256 <= shad mb
               /\ ((mb + ms <= 2147446784 /\ shad (mb + ms) <= 2415881728) \/ (K_HIGH_MEM <= mb /\ 2201439137792 <= shad mb))
               /\ (shad (mb + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb) /\ shad (al_fake L + 11571200) <= shad ATOP).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_HIGH_MEM in *. clear -MAL MLO MCE MSAL SCf OF. Z.div_mod_to_equations. lia. }
  destruct SH as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
  assert (SF : 2147450880 <= shad (al_fake L)) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha MLO MCE HHI OF SCf S1 S2 S3 S4 SH1 SH2 SH3 SH4 SH5 SH6 SF AR; lia).
  destruct C as (blk & Hin & R). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & Q4 & _ & Q6 & Q7). clear -R Ha G1 G2 Q4 Q6 Q7 SCr MLO S1 SH1 SH2 AR. lia.
    + destruct SW' as (_ & MLO' & _). unfold ablk, AIMG_HI, KLS in MLO'. specialize (DJ _ _ _ _ Lp). unfold SEC_UOFF, K_HIGH_MEM in *. clear -R Ha G1 G2 DJ MLO MLO' S1 SH1 SH2 SH3 AR. lia.
  - clear -R Ha G SCf OF MLO S1 SH1 SH2 SH3 SF AR. lia.
Qed.

(* [comment removed for export] *)
Lemma np_hl : forall L st X LB HI hl, alayout_ok L -> awf L st X -> ablocks L st X LB -> ATOP <= HI ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  forall a, hl <= a < hl + 8 -> ~ cprot L HI LB a.
Proof.
  intros L st X LB HI hl ALO WF BL HHI K1 K2 SCL HLS a Ha C. pose proof shad_consts as (S1 & S2 & S3 & S4). unfold ablk, AIMG_HI, KLS in K1. pose proof atop_range as AR.
  pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF. pose proof SCL as (_ & _ & SCr & _ & _ & _ & SCf & _).
  assert (SF : 2147450880 <= shad (al_fake L) /\ shad (al_fake L + 11571200) <= 17594332446720) by (rewrite !shad_div; unfold ASHOFF in *; clear -OF AR; Z.div_mod_to_equations; lia).
  unfold cprot, AIMG_HI, K_HIGH_MEM in *.
  destruct C as [C|[C|[C|[C|[C|[C|C]]]]]]; try (clear -C Ha K1 K2 HHI OF SCf S1 S2 S3 S4 SF AR; lia).
  destruct C as (blk & Hin & R). pose proof (lb_geo L st X LB blk ALO WF BL Hin) as G.
  destruct blk as [[p|cls] A' n']; cbn [ab_kind ab_addr ab_size] in G, R.
  - destruct G as [(b & Hb & _ & G1 & G2)|(mb' & ms' & n0 & Lp & SW' & G1 & G2)].
    + pose proof (busy_slot_geo L st X ALO WF b Hb) as (_ & _ & _ & _ & _ & _ & _ & Q6 & Q7). clear -R Ha G1 G2 Q6 Q7 SCr. lia.
    + specialize (HLS _ _ _ _ Lp). clear -R Ha G1 G2 HLS. lia.
  - clear -R Ha G SCf. lia.
Qed.

(* [comment removed for export] *)
Lemma np_cd_W : forall L st X LB HI lo SP c nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  1 <= c < K_NUM_CLASSES -> 0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (cd_W L SP c nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c nf mfa mfa' ALO WF BL HC NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (cd_W_cases L SP c nf mfa mfa' iv ALO HC NF0 NF4 MFA Hiv) as [->|P].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

Lemma np_rec_W : forall L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa', alayout_ok L -> awf L st X -> ablocks L st X LB ->
  x_busy X = l1 ++ bany BQuar c kk n b1 ctx :: l2 ->
  0 <= nf -> 4 * nf <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  ATOP <= lo -> lo <= SP - 688 -> SP <= HI ->
  np_fp L HI LB (rec_W L SP c kk n nf mfa mfa').
Proof.
  intros L st X LB HI lo SP c kk n b1 ctx l1 l2 nf mfa mfa' ALO WF BL XB NF0 NF4 MFA CEIL LO SPH iv Hiv.
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (rec_W_cases L st X SP c kk n b1 ctx l1 l2 nf mfa mfa' iv ALO WF XB NF0 NF4 MFA Hiv) as [->|[SL|P]].
  - cbn [fst snd]. eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - intros a Ha. eapply (np_slot L st X LB HI BQuar c kk n b1 ctx l1 l2 (fst iv) (snd iv));
      [exact ALO| exact WF| exact BL| clear -CEIL LO SPH; lia| exact XB| intros p; discriminate| exact (proj1 SL)| exact (proj2 SL)| exact Ha].
  - eapply (np_low L st X LB HI c iv); [exact ALO| exact WF| exact BL| exact HC| clear -CEIL LO SPH; lia| exact P].
Qed.

Lemma np_srec_W : forall L st X LB HI lo SP mb ms n nres hl, alayout_ok L -> awf L st X -> ablocks L st X LB ->
  sec_wf1 L (CSec mb ms n) ->
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> mb' + ms' <= mb \/ mb + ms <= mb') ->
  ablk hl (hl + 8) -> hl + 8 <= ATOP -> sec_clear L hl 8 ->      (* [comment removed for export] *)
  (forall p mb' ms' n', (a_live st) !! p = Some (CSec mb' ms' n') -> hl + 8 <= mb' + SEC_UOFF \/ mb' + ms' <= hl) ->
  0 <= nres -> 8 * nres <= 8388608 ->
  ATOP <= lo -> lo <= SP - 1024 -> SP <= HI ->
  np_fp L HI LB (srec_W L SP mb ms nres ++ [(hl, hl + 8)]).
Proof.
  intros L st X LB HI lo SP mb ms n nres hl ALO WF BL SW DJ K1 K2 SCL HLS N0 N1 CEIL LO SPH.
  assert (HHI : ATOP <= HI) by (clear -CEIL LO SPH; lia).
  pose proof (alayout_t_lin L ALO) as OT.
  unfold srec_W. cbn [app].
  apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_cons; [| apply np_fp_nil]]]]]]]; cbn [fst snd].
  - eapply (np_high L st X LB HI); [exact ALO| exact WF| exact BL| clear -CEIL LO; lia| exact SPH].
  - eapply (np_low L st X LB HI 1 (al_t L + 2800, al_t L + 3168)); [exact ALO| exact WF| exact BL| unfold K_NUM_CLASSES; clear; lia| exact HHI|].
    unfold lowpiece. cbn [fst snd]. split; [clear -OT; lia|]. split; [clear -OT; lia| right; left; clear; lia].
  - eapply (np_static L st X LB HI); [exact ALO| exact WF| exact BL| exact HHI| intros a Ha; unfold astatic, AINSTANCE in *; clear -Ha; lia| unfold AINSTANCE; clear; lia| unfold AINSTANCE, AIMG_HI; clear; lia].
  - eapply (np_ptrarr L st X LB HI nres); [exact ALO| exact WF| exact BL| exact HHI| exact N0| exact N1].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| left; exact Ha].
  - intros a Ha. eapply (np_secmap L st X LB HI mb ms n); [exact ALO| exact WF| exact BL| exact HHI| exact SW| exact DJ| right; exact Ha].
  - eapply (np_hl L st X LB HI hl); [exact ALO| exact WF| exact BL| exact HHI| exact K1| exact K2| exact SCL| exact HLS].
Qed.

(* [comment removed for export] *)
Lemma cpres_aheap_pres : forall (CI : list (Z * Z)) L HI LB SPc st X m m',
  alayout_ok L -> awf L st X -> ablocks L st X LB ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= 0x1a1bc8 \/ 0x5f1c10 <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0xcc970 \/ 0xcca30 <= fst iv) /\ (snd iv <= 0xd0f00 \/ 0x151f30 <= fst iv) /\ (snd iv <= 0x15f788 \/ 0x15f78c <= fst iv)) CI ->
  Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI ->
  HI <= SPc -> cpres L HI LB m m' -> aheap_pres CI LB SPc m m'.
Proof.
  intros CI L HI LB SPc st X m m' ALO WF BL CI_OK CI_OK2 HS CP a Ha CL. pose proof shad_consts as (S1 & S2 & S3 & S4).
  pose proof (ao_fake L ALO) as OF. unfold aobj in OF.
  assert (E : m' (wa a) = m (wa a)).
  { apply CP. rewrite wa_unsigned by exact Ha. unfold cprot.
    destruct CL as [ST | [CIa | [BLK | SHD]]].
    - left. clear -ST HS. lia.
    - right; left. destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. unfold astatic, AINSTANCE in *. clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7. lia.
    - right; right; left. exact BLK.
    - destruct SHD as (a' & Ha' & ->). right; right; right; right.
      destruct Ha' as [STa | [CIa | FK]].
      + left. rewrite !shad_div. unfold ASHOFF in *. clear -STa. Z.div_mod_to_equations. lia.
      + right; left. destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & _ & Q3 & _).
        rewrite !shad_div. unfold AIMG_HI, ASHOFF in *. clear -R Q1 Q3. Z.div_mod_to_equations. lia.
      + right; right. destruct FK as (cls & FA & sz & Hin & R). destruct (proj1 (proj2 BL) cls FA sz Hin) as (F1 & F2 & F3).
        rewrite !shad_div. unfold ASHOFF in *. clear -R F1 F3 OF. Z.div_mod_to_equations. lia. }
  split; [exact E|]. intros Hw. rewrite (wview_agree bsegs m m' (wa a) E). exact Hw.
Qed.
End CANSEC1.
(* [comment removed for export] *)
