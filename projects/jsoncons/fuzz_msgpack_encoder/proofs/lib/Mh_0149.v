(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool Permutation. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module PnEncKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.L5CoreKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module NEKT.
Import NEM. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & EQ). apply Nat.eqb_eq in EQ. subst x. exact Hx.
Qed.
Lemma ecap_nonneg k : 0 <= ecap k.
Proof. unfold ecap. destruct (k =? 0); [lia| apply Z.pow_nonneg; lia]. Qed.
Lemma al8_item eb n : eb mod 8 = 0 -> (eb + 24 * n) mod 8 = 0.
Proof. intros H. rewrite Z.add_mod, H by lia. replace (24 * n) with ((3 * n) * 8) by lia. rewrite Z.mod_mul by lia. reflexivity. Qed.
Lemma m8_of16 fb c : fb mod 16 = 0 -> c mod 8 = 0 -> (fb + c) mod 8 = 0.
Proof. intros H1 H2. rewrite Z.add_mod, H2, Z.add_0_r, Z.mod_mod by lia. apply PMPK.m16_8. exact H1. Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation enc_at := (NEM.enc_at segs E L T3 T4).
Abbreviation sink_at := (NESK.sink_at segs L T3 T4).
Abbreviation ec_state := (NEM.ec_state segs A).

(* [comment removed for export] *)
Lemma heap_perm (HIok : heap_iface_ok L SCFG HI) l1 l2 cr M VM : Permutation l1 l2 -> hi_heap HI l1 cr M VM -> hi_heap HI l2 cr M VM.
Proof.
  intros PERM HH. apply (hio_perm L SCFG HI HIok _ _ cr M VM HH).
  - intros b0. split; apply Permutation_in; [exact PERM| apply Permutation_sym; exact PERM].
  - apply NoDup_ListNoDup. apply (Permutation_NoDup (Permutation_map fst PERM)). apply NoDup_ListNoDup. exact (PMPK.heap_nodup L HI HIok _ cr M _ HH).
Qed.

(* [comment removed for export] *)
Lemma own_not_client (HIok : heap_iface_ok L SCFG HI) OWN LB cr M VM B m a sp scr :
  hi_heap HI (OWN ++ LB) cr M VM -> In (B, m) OWN -> B <= a < B + m -> ~ client_addr L LB sp scr a.
Proof.
  intros HH Hin Ha. assert (BR : PMFR.brange L (OWN ++ LB)) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M _ HH); apply incl_refl).
  destruct (BR B m (in_or_app _ _ _ (or_introl Hin))) as (Z0 & Z1 & Z4).
  intros [((B' & m') & Hb & Hr)|[[S1 _]|[IM _]]]; [|lia|lia]. cbn in Hr.
  assert (NE : B <> B') by (apply (PMPK.fst_neq_app OWN LB B m B' m' (PMPK.heap_nodup L HI HIok _ _ _ _ HH) Hin Hb)).
  destruct (PMPK.blocks_apart_heap L HI HIok _ cr M _ B m B' m' HH (in_or_app _ _ _ (or_introl Hin)) (in_or_app _ _ _ (or_intror Hb)) NE); lia.
Qed.

(* [comment removed for export] *)
Lemma ek_piece_own (HIok : heap_iface_ok L SCFG HI) OWN LB cr M0 VM sp scr W M M' (Pf : Z -> Prop) B m :
  hi_heap HI (OWN ++ LB) cr M0 VM -> In (B, m) OWN ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Pf a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  hl_ceil L <= sp - scr -> 0x7fff80000000 <= hl_sptop L ->
  (forall a, Pf a -> (sp - scr <= a < sp) \/ PMK.inW W a \/ (B <= a < B + m)) -> PMK.ek L LB sp scr W M M'.
Proof.
  intros HH Hin FRZ Hc Hw FP. pose proof (PMK.kl_img segs L KL) as KI. unfold hl_ceil in Hc.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ _ _ M0 _ HH); apply incl_appr; apply incl_refl).
  apply (PMK.ek_piece L LB sp scr W M M' Pf FRZ). intros a Ha CA NE OW Pa. destruct (FP a Pa) as [S|[I|Bk]].
  - destruct CA as [((b & m') & Hb & Hr)|[[S1 S2]|[IM _]]]; [pose proof (PMFR.brange_hi L LB BR _ Hb) as X; cbn in X, Hr; lia| exact (S2 S)| lia].
  - exact (PMK.inW_not_outside W a I OW).
  - exact (own_not_client HIok OWN LB cr M0 VM B m a sp scr HH Hin Bk CA).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Agree.
Variables M M' : word -> option byte.
Abbreviation ag := (L5C.agree_on M M').

(* [comment removed for export] *)
Lemma sink_at_agree P o k :
  0 <= o -> o + 24 <= 2 ^ 64 -> ag o 24 ->
  (0 < NESK.sk_c k -> 0 <= NESK.sk_b k /\ NESK.sk_b k + NESK.sk_c k <= 2 ^ 64 /\ ag (NESK.sk_b k) (NESK.sk_c k)) ->
  sink_at P M o k -> sink_at P M' o k.
Proof.
  intros Ho Ho' AG AGB (V0 & V8 & V16 & D & _ & Hz & Hc & Hc0 & HB).
  assert (SUB : forall a n, o <= a -> a + n <= o + 24 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
  split; [exact Hz|]. split; [exact Hc|]. split; [exact Hc0|].
  intros Hp. destruct (HB Hp) as (DB & _ & _ & BR & CAP & NM). destruct (AGB Hp) as (B0 & B1 & AB).
  split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split; [exact I|]. split; [exact I|]. split; [exact BR|]. split; [exact CAP| exact NM].
Qed.

(* [comment removed for export] *)
Lemma enc_at_agree ov osk en :
  0 <= ov -> ov + 56 <= 2 ^ 64 -> ag ov 56 ->
  (0 < en_k en -> 0 <= en_b en /\ en_b en + NEM.ESZ * ecap (en_k en) <= 2 ^ 64 /\ ag (en_b en) (NEM.ESZ * ecap (en_k en))) ->
  enc_at M ov osk en -> enc_at M' ov osk en.
Proof.
  intros Ho Ho' AG AGB (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hd & Hn & Hk0 & HB).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [apply (L5C.defined_agree M M' ov 56 AG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hd|]. split; [exact Hn|]. split; [exact Hk0|].
  intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _). destruct (AGB Hp) as (B0 & B1 & AB).
  split; [exact AL|]. split; [exact (L5C.defined_agree M M' _ _ AB DB)|]. split; [exact BR|]. split; exact I.
Qed.

(* [comment removed for export] *)
Lemma ec_state_agree oec b cat :
  0 <= oec -> oec + 16 <= 2 ^ 64 -> ag oec 16 -> ec_state M oec b cat -> ec_state M' oec b cat.
Proof.
  intros Ho Ho' AG.
  assert (EC : forall v c, PMSP.ec_at segs M oec v c -> PMSP.ec_at segs M' oec v c).
  { intros v c (E0 & E8 & ED). split; [|split].
    - apply (PMF.u32_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E0].
    - apply (L5C.u64_at_agree segs M M'); [eapply L5C.agree_on_sub; [exact AG|lia|lia] |lia|lia| exact E8].
    - exact (L5C.defined_agree M M' _ _ AG ED). }
  unfold NEM.ec_state. destruct b.
  - intros (v & Hv & EC0). exists v. split; [exact Hv| apply EC; exact EC0].
  - apply EC.
Qed.

(* [comment removed for export] *)
Lemma enc_at_inner ov osk en lo hi :
  mem_grows M M' -> (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0 <= ov -> ov + 56 <= 2 ^ 64 -> (hi <= ov \/ ov + 56 <= lo) ->
  enc_at M ov osk en -> enc_at M' ov osk en.
Proof.
  intros MG FRZ Ho Ho' AP (V0 & V8 & V16 & V24 & V32 & V40 & V48 & D & _ & Hk & Hd & Hn & Hk0 & HB).
  assert (AG : ag ov 56) by (intros i Hi; apply FRZ; lia).
  assert (SUB : forall a n, ov <= a -> a + n <= ov + 56 -> ag a n) by (intros a n X1 X2; eapply L5C.agree_on_sub; [exact AG|lia|lia]).
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V8]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V16]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V24]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V32]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V40]|].
  split; [apply (PMF.u32_at_agree segs M M'); [apply SUB; lia|lia|lia| exact V48]|].
  split; [exact (L5.defined_grows M M' ov 56 MG D)|]. split; [exact I|].
  split; [exact Hk|]. split; [exact Hd|]. split; [exact Hn|]. split; [exact Hk0|].
  intros Hp. destruct (HB Hp) as (AL & DB & BR & _ & _).
  split; [exact AL|]. split; [exact (L5.defined_grows M M' _ _ MG DB)|]. split; [exact BR|]. split; exact I.
Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis EK : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.
Hypothesis WHI : forall a, PMK.inW W' a -> sp' <= a \/ hl_img_lo L <= a < hl_img_hi L.

Let ag_hi := PMFR.ag_hi segs L KL LBc sp' scr' W' M M' EK STKc SCR0.
Let ag_block := PMFR.ag_block segs L KL LBc sp' scr' W' M M' EK STKc SCR0 BR WHI.

Lemma enc_keep ov osk en :
  sp' <= ov -> ov + 56 <= 2 ^ 64 -> (forall i, ov <= i < ov + 56 -> ~ PMK.inW W' i) -> incl (enc_own en) LBc ->
  enc_at M ov osk en -> enc_at M' ov osk en.
Proof.
  intros H1 H2 N INC EN. pose proof STKc as (_ & SLO & _ & STOP & _). pose proof EN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hk & _ & _ & _ & HB).
  apply (enc_at_agree M M' ov osk en); [lia|lia| apply ag_hi; assumption| |exact EN].
  intros Hp. destruct (HB Hp) as (_ & _ & BRK & _ & _).
  assert (IN : In (en_b en, NEM.ESZ * ecap (en_k en)) LBc).
  { apply INC. unfold enc_own. replace (en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ IN) as (B0 & B1 & B4). pose proof (PMFR.brange_hi L LBc BR _ IN) as BH. cbn [fst snd] in BH.
  split; [lia|]. split; [unfold hl_ceil in BH; lia|]. apply ag_block. exact IN.
Qed.

Lemma sink_keep P o k :
  sp' <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> ~ PMK.inW W' i) -> incl (NESK.sink_own k) LBc ->
  sink_at P M o k -> sink_at P M' o k.
Proof.
  intros H1 H2 N INC SK. pose proof STKc as (_ & SLO & _ & STOP & _).
  apply (sink_at_agree M M' P o k); [lia|lia| apply ag_hi; assumption| |exact SK].
  intros Hp.
  assert (IN : In (NESK.sk_b k, NESK.sk_c k) LBc).
  { apply INC. unfold NESK.sink_own. replace (NESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  destruct (BR _ _ IN) as (B0 & B1 & B4). pose proof (PMFR.brange_hi L LBc BR _ IN) as BH. cbn [fst snd] in BH.
  split; [lia|]. split; [unfold hl_ceil in BH; lia|]. apply ag_block. exact IN.
Qed.

Lemma ec_state_keep oec b cat :
  sp' <= oec -> oec + 16 <= 2 ^ 64 -> (forall i, oec <= i < oec + 16 -> ~ PMK.inW W' i) ->
  ec_state M oec b cat -> ec_state M' oec b cat.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & SLO & _ & STOP & _). apply (ec_state_agree M M' oec b cat); [lia|lia| apply ag_hi; assumption].
Qed.
End Along.
End Kit.
End NEKT.

End PnEncKit.
From Stdlib Require ZArith List Lia Bool. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require UbjRef.
Module PnMpKitN.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PmLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmStatics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmStep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmFrame OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0135.PmParKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PgSrc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnV8 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.PnLayoutQ OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnQModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.PnMpModelFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0124.PnMpKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0018.NemLayout OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemSink OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0149.PnEncKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Spec Require Import UbjRef.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNMK.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable E : ne_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis KL : PMK.klayout segs L.
Variable vpa : Z.

Abbreviation T3 := PMSP.T3.
Abbreviation T4 := PMSP.T4.
Abbreviation ae_at := (NEM.ae_at segs A E L T3 T4 vpa).
Abbreviation enc_at := (NEM.enc_at segs E L T3 T4).
Abbreviation sink_at := (NESK.sink_at segs L T3 T4 NESK.PME).
Abbreviation ec_state := (NEM.ec_state segs A).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Agree.
Variables Ma Mb : word -> option byte.
Abbreviation agn := (L5C.agree_on Ma Mb).

Lemma kcontent_agree o x bs : 0 <= o -> o + 24 <= 2 ^ 64 -> agn o 24 ->
  (forall c n p, x = PM.VLong c n p -> 0 <= p /\ p + c <= 2 ^ 64 /\ agn p c) ->
  PQM.kstr_at segs T3 Ma o x -> NEM.kcontent segs Ma o x bs -> NEM.kcontent segs Mb o x bs.
Proof.
  intros Ho Ho' AG AGB KS ((BA & BOK) & LEN). split; [split; [|exact BOK]|exact LEN].
  destruct x as [n|c n p]; cbn [PM.vs_data PM.vs_size] in *.
  - destruct KS as (_ & _ & Hn & _). apply (L5C.bytes_at_agree segs Ma Mb); [|lia|lia|exact BA]. eapply L5C.agree_on_sub; [exact AG|lia|lia].
  - destruct KS as (_ & _ & _ & _ & _ & Hnc & Hc & _). destruct (AGB c n p eq_refl) as (P0 & P1 & AGP).
    apply (L5C.bytes_at_agree segs Ma Mb); [|lia|lia|exact BA]. eapply L5C.agree_on_sub; [exact AGP|lia|lia].
Qed.

Lemma ae_at_agree oa ov osk st :
  0 <= oa -> oa + PQM.ASIZE <= 2 ^ 64 -> agn oa PQM.ASIZE -> 0 <= ov -> ov + 56 <= 2 ^ 64 -> agn ov 56 -> 0 <= osk -> osk + 24 <= 2 ^ 64 -> agn osk 24 ->
  (forall B m, In (B, m) (NEM.aeown st) -> 0 <= B /\ B + m <= 2 ^ 64 /\ agn B m) ->
  ae_at Ma oa ov osk st -> ae_at Mb oa ov osk st.
Proof.
  intros Ho Ho' AG Hv Hv' AGV Hk Hk' AGK BL (AT & KC & EN & SK).
  assert (BLa : forall B m, In (B, m) (PQM.aown (NEM.ae_a st)) -> 0 <= B /\ B + m <= 2 ^ 64 /\ agn B m).
  { intros B m Hin. apply BL. unfold NEM.aeown. apply in_or_app. left. exact Hin. }
  split.
  { assert (Bl : In (PQM.a_lb (NEM.ae_a st), PQM.LSZ * 2 ^ PQM.a_lk (NEM.ae_a st)) (PQM.aown (NEM.ae_a st))) by (unfold PQM.aown, PQM.lvec_own; cbn; auto).
    destruct (BLa _ _ Bl) as (L0 & L1 & AL).
    eapply (PQMF.adaptor_at_frame segs A vpa Ma Mb oa ov (NEM.ae_a st)).
    - exact Ho.
    - exact Ho'.
    - apply PQMF.dkr_agree. exact AG.
    - unfold PQM.ASIZE in *. eapply PMF.ag_sub; [exact AG| lia| lia].
    - unfold PQM.ASIZE, PQM.AOFF_KEY in *. destruct (PQM.a_key (NEM.ae_a st)); cbn [PQMF.vs_cells fst snd]; (eapply PMF.ag_sub; [exact AG| lia| lia]).
    - intros c n p Et. apply PQMF.dkr_agree. assert (Bt : In (p, c) (PQM.aown (NEM.ae_a st))).
      { unfold PQM.aown. apply in_or_app. right. apply in_or_app. left. rewrite Et. cbn. auto. }
      destruct (BLa _ _ Bt) as (_ & _ & X). exact X.
    - unfold PQM.ASIZE, PQM.AOFF_KB in *. destruct (PQM.a_kb (NEM.ae_a st)); cbn [PQMF.vs_cells fst snd]; (eapply PMF.ag_sub; [exact AG| lia| lia]).
    - intros c n p Et. apply PQMF.dkr_agree. assert (Bt : In (p, c) (PQM.aown (NEM.ae_a st))).
      { unfold PQM.aown. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto. }
      destruct (BLa _ _ Bt) as (_ & _ & X). exact X.
    - unfold PQM.ASIZE, PQM.AOFF_LV in *. eapply PMF.ag_sub; [exact AG| lia| lia].
    - exact L0.
    - exact L1.
    - exact AL.
    - exact AT. }
  split.
  { pose proof AT as (_ & _ & _ & _ & _ & _ & KSB & _).
    apply (kcontent_agree (oa + PQM.AOFF_KB) (PQM.a_kb (NEM.ae_a st)) (NEM.ae_kbb st)); [unfold PQM.AOFF_KB; lia| unfold PQM.AOFF_KB, PQM.ASIZE in *; lia| | |exact KSB|exact KC].
    - unfold PQM.AOFF_KB, PQM.ASIZE in *. eapply L5C.agree_on_sub; [exact AG|lia|lia].
    - intros c n p Et. apply BLa. unfold PQM.aown. apply in_or_app. right. apply in_or_app. right. rewrite Et. cbn. auto. }
  split.
  { apply (NEKT.enc_at_agree segs E L Ma Mb ov osk (NEM.ae_e st) Hv Hv' AGV); [|exact EN].
    intros Hp. apply BL. unfold NEM.aeown, NEM.enc_own. apply in_or_app. right. apply in_or_app. left.
    replace (NEM.en_k (NEM.ae_e st) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. auto. }
  apply (NEKT.sink_at_agree segs L Ma Mb NESK.PME osk (NEM.ae_s st) Hk Hk' AGK); [|exact SK].
  intros Hp. apply BL. unfold NEM.aeown, NESK.sink_own. apply in_or_app. right. apply in_or_app. right.
  replace (NESK.sk_c (NEM.ae_s st) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn. auto.
Qed.
End Agree.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis EK : PMK.ek L LBc sp' scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M sp' scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : PMFR.brange L LBc.

Let ag_hi := PMPK.ag_hi segs L KL LBc sp' scr' W' M M' EK STKc SCR0.
Let ag_blk := PMPK.ag_blk segs L KL LBc sp' scr' W' M M' EK STKc BR.

(* [comment removed for export] *)
Lemma ae_keep oa ov osk st :
  sp' <= oa -> oa + PQM.ASIZE <= 2 ^ 64 -> sp' <= ov -> ov + 56 <= 2 ^ 64 -> sp' <= osk -> osk + 24 <= 2 ^ 64 ->
  (forall i, oa <= i < oa + PQM.ASIZE -> ~ PMK.inW W' i) -> (forall i, ov <= i < ov + 56 -> ~ PMK.inW W' i) -> (forall i, osk <= i < osk + 24 -> ~ PMK.inW W' i) ->
  incl (NEM.aeown st) LBc -> (forall B m, In (B, m) (NEM.aeown st) -> PQMK.untouched W' B m) ->
  ae_at M oa ov osk st -> ae_at M' oa ov osk st.
Proof.
  intros H1 H2 H3 H4 H5 H6 Na Nv Nk INC NB AT. pose proof STKc as (_ & SLO & SHI & STOP & _).
  apply (ae_at_agree M M' oa ov osk st); [lia|exact H2| apply ag_hi; [lia|exact H2|exact Na] |lia|exact H4| apply ag_hi; [lia|exact H4|exact Nv]
     |lia|exact H6| apply ag_hi; [lia|exact H6|exact Nk] | |exact AT].
  intros B m Hin. pose proof (INC _ Hin) as HinC. destruct (BR _ _ HinC) as (Q0 & Q1 & Q4). pose proof (PMFR.brange_hi L LBc BR _ HinC) as BH. cbn [fst snd] in BH.
  split; [lia|]. split; [unfold hl_ceil in BH; lia|]. apply ag_blk; [exact HinC| exact (NB _ _ Hin)].
Qed.

(* [comment removed for export] *)
Lemma ec_state_keep oec b cat :
  sp' <= oec -> oec + 16 <= 2 ^ 64 -> (forall i, oec <= i < oec + 16 -> ~ PMK.inW W' i) -> ec_state M oec b cat -> ec_state M' oec b cat.
Proof. intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). apply (NEKT.ec_state_agree segs A M M' oec b cat); [lia|lia| apply ag_hi; assumption]. Qed.
End Along.
End Kit.
End PNMK.

End PnMpKitN.
