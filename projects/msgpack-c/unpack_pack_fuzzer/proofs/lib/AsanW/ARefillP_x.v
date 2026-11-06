(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARefill_iface RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aensure F_apopulate. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface AEmbRep AFrameD ARepFrameD AEmbFrame. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_agetfrom. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ARefill_iface_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AExh AC6Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.
Notation AREFILL_STACK_X := 2048 (only parsing).

Definition sec_untouchedD (L : alayout) (RESV : list (Z * Z)) (st : astate) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (forall a, fst iv <= a < snd iv -> aknown L a)
                 \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true)) W.
Record ahole_lawsD (H : aholes) : Prop := mkAHLD {
  hqD : forall L st st' X X' m m' W,
      ah_quar H L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> ah_quar H L st' X' m';

  hx_get : forall L st X m, ah_sec H L st X m -> AEXH L st m;

  hsD : forall L RESV st st' X X' m m' W,
      aresv_ok L RESV -> ah_sec H L st X m -> munch W m m' -> sec_untouchedD L RESV st W -> sec_sameX st st' -> AEXH L st' m' -> ah_sec H L st' X' m';
  hdD : forall L m m' W,
      ah_depot H L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1ab988 <= a < 0x5fb9d0) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      ah_depot H L m';

  hfD : forall L LB m m' W,
      ah_fake H L LB m -> munch W m m' -> disjoint_from W (al_t L + 72) 8 -> fake_untouched L W ->
      Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> ah_fake H L LB m'
}.

Definition nz (d cap : Z) : Z * Z := if 0 <? cap then (d, d + cap) else (0, 0).
Lemma outside_cons : forall (iv : Z * Z) W x, outside (iv :: W) x <-> ~ (fst iv <= x < snd iv) /\ outside W x.
Proof. intros [lo hi] W x. cbn [outside fst snd]. tauto. Qed.
Lemma nz_outside : forall d cap x, ~ (fst (nz d cap) <= x < snd (nz d cap)) -> ~ (d <= x < d + cap).
Proof. intros d cap x. unfold nz. destruct (0 <? cap) eqn:Q; cbn [fst snd]; [tauto|]. apply Z.ltb_ge in Q. intros _. lia. Qed.
Lemma ic_W_in_t : forall L i d, 1 <= i -> i + Z.of_nat d <= 32 ->
  Forall (fun iv : Z * Z => al_t L + 288 <= fst iv /\ snd iv <= al_t L + 2768 /\ fst iv <= snd iv) (ic_W L i d).
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i Hi Hd; cbn [ic_W]; [constructor|].
  constructor; [cbn [fst snd]; unfold acache_addr; lia| apply IH; lia].
Qed.

Section RefillPX.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Hypothesis HLD : ahole_lawsD H.

Lemma quar_same_x : forall st X l e, quar_same st (set_emb e (set_exh l st)) X X.
Proof. intros st X l e. destruct st. unfold quar_same. cbn. repeat split; try reflexivity; intros b Hb; destruct (xb_st b); auto. Qed.

Lemma sec_sameX_x : forall st st' l e, sec_sameX st st' -> sec_sameX st (set_emb e (set_exh l st')).
Proof. intros st st' l e S. destruct st'. exact S. Qed.

Lemma AREPns_x_indep : forall L st X m l e, AREPns H L st X m -> AREPns H L (set_emb e (set_exh l st)) X m.
Proof.
  intros L st X m l e (WF & RT & INST & THR & CLS & HQ & HD & HRO & RT2 & AVL & RT3).
  pose proof (quar_same_x st X l e) as QS.
  assert (HQ' : ah_quar H L (set_emb e (set_exh l st)) X m)
    by (eapply (hq_frame H HL L st _ X X m m []); [exact HQ| apply munch_refl| apply wmono_refl| constructor| exact QS]).
  clear QS HQ. destruct st.
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact HQ'|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.
Lemma arng_x_indep : forall L RNG st l e, arng L RNG st -> arng L RNG (set_emb e (set_exh l st)).
Proof. intros L RNG st l e A. destruct st. exact A. Qed.

Lemma set_x_eta : forall st, set_emb (a_emb st) (set_exh (a_exh st) st) = st.
Proof. intros st. destruct st. reflexivity. Qed.
Lemma put_cls_set_x : forall c r l e st, put_cls c r (set_emb e (set_exh l st)) = set_emb e (set_exh l (put_cls c r st)).
Proof. intros. destruct st. reflexivity. Qed.
Lemma exh_clear_as_set : forall c st, exh_clear c st = set_emb (a_emb st) (set_exh (a_exh (exh_clear c st)) st).
Proof. intros c st. destruct st. reflexivity. Qed.

Lemma set_x_fields : forall l e st,
  let s' := set_emb e (set_exh l st) in
  a_cinit s' = a_cinit st /\ (forall c, get_cls s' c = get_cls st c) /\ (forall c, max_count s' c = max_count st c)
  /\ a_live s' = a_live st /\ a_next s' = a_next st /\ a_qloc s' = a_qloc st /\ a_qloc_bytes s' = a_qloc_bytes st
  /\ a_qglob s' = a_qglob st /\ a_qglob_bytes s' = a_qglob_bytes st /\ a_nsec s' = a_nsec st /\ a_nres s' = a_nres st
  /\ a_emb s' = e /\ a_exh s' = l.
Proof. intros l e st. destruct st. cbv zeta. repeat split; reflexivity. Qed.

Lemma refill_ret_x_old : forall L RNG sp st c lo fl chunks0 cnt m st2 RNG' m',
  c <> K_BATCH_CLASS ->
  F_arefill.F_arefill_x.refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
  exists st2o l, st2 = set_emb (a_emb st2o) (set_exh l st2o) /\ get_cls st2o c = get_cls st2 c
    /\ (l = a_exh (init_cache st) \/ l = a_exh (exh_clear c (init_cache st)))
    /\ a_emb st2o = a_emb (init_cache st)
    /\ F_arefill.F_arefill.refill_ret L RNG sp st c lo fl chunks0 cnt m st2o RNG' m'.
Proof.
  intros L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' NC RR.
  destruct RR as (m1 & MU1 & WM1 & TR & RECS).
  unfold refill_tail_ret_x in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & EXH' & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  set (st1 := init_cache st) in *.
  assert (PICK : exists st2o l, st2 = set_emb (a_emb st2o) (set_exh l st2o) /\ get_cls st2o c = get_cls st2 c
                   /\ (l = a_exh st1 \/ l = a_exh (exh_clear c st1)) /\ a_emb st2o = a_emb st1
                   /\ (st2o = st1 \/ st2o = put_cls c (get_cls st2o c) st1)).
  { destruct ST2E as [E|E].
    - exists st1, (a_exh st1). rewrite E. split; [symmetry; apply set_x_eta|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity| left; reflexivity].
    - set (R2 := get_cls st2 c) in *. exists (put_cls c R2 st1), (a_exh (exh_clear c st1)).
      pose proof (get_cls_put_cls_eq c R2 st1) as G.
      split. { rewrite E. rewrite (exh_clear_as_set c (put_cls c R2 st1)). destruct st1; reflexivity. }
      split; [exact G|]. split; [right; reflexivity|]. split; [destruct st1; reflexivity|]. right. rewrite G. reflexivity. }
  destruct PICK as (st2o & l & ES & GC & LL & EE & SO).
  exists st2o, l. split; [exact ES|]. split; [exact GC|]. split; [exact LL|]. split; [exact EE|].
  exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [| exact RECS].
  unfold F_arefill.F_arefill.refill_tail_ret. cbv zeta. fold st1.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split; [exact UD|]. split; [exact MUB|]. split; [exact MUM'|]. split; [exact NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split; [exact FD|]. split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|]. split; [exact AR2|]. split; [exact JR|].
  split; [rewrite GC; exact GC2|]. split; [exact SO|].
  split; [exact MUT|]. split; [exact WMT|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MTX'|]. split; [exact REG'|].
  split. { eexists. split; [exact EXH'|]. intros X. exfalso. exact (NC X). }
  split; [exact STN'|]. split; [exact STATS'|]. split; [exact LSJ'|]. split; [exact STM'|]. split; [exact REC'|]. split; [exact CH'|].
  split; [exact AZU'|]. split; [exact AZF'|]. exact MC'.
Qed.

Lemma init_cache_exh_list : forall st, a_exh (init_cache st) = a_exh st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma exh_clear_init_cache : forall c st, a_exh (exh_clear c (init_cache st)) = a_exh (exh_clear c st).
Proof. intros c st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma refill_store_x : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr asegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  F_arefill.F_arefill_x.refill_ret_x L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', (AEXH L st_r m' -> AREP H L st_r X' m')
    /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m'
    /\ a_emb st_r = a_emb st /\ (a_exh st_r = a_exh st \/ a_exh st_r = a_exh (exh_clear c st)).
Proof.
  intros L RESV RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH RR. cbv zeta.
  destruct (refill_ret_x_old _ _ _ _ _ _ _ _ _ _ _ _ _ NC RR) as (st2o & l & ES & GC & LL & EE & RRo).
  pose proof (refill_store_ns H HL L RNG RNG' sp m m' st st2o X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RRo) as S0. cbv zeta in S0.
  set (n := max_cached c / 2) in *.
  set (st_ro := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2o c) - n) (get_cls st2o c))) st2o) in *.
  assert (ESR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = set_emb (a_emb st2o) (set_exh l st_ro)).
  { rewrite <- GC. rewrite ES at 1. subst st_ro. apply put_cls_set_x. }
  rewrite ESR.
  destruct S0 as (X' & WH & ARNS & MUH & SU & _ & SSo & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GCo & MU & WM).
  destruct (set_x_fields l (a_emb st2o) st_ro) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13). cbv zeta in *.
  exists X'. split.
  { intros AX. apply AREP_split. split; [apply AREPns_x_indep; exact ARNS|].
    destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
    eapply (hsD H HLD L RESV st _ X X' m m' WH ARV HS MUH); [| apply sec_sameX_x; exact (sec_same_X _ _ SSo)| exact AX].
    unfold sec_untouchedD. eapply Forall_impl; [| exact SU]. intros iv K. left. exact K. }
  split; [apply arng_x_indep; exact ARNG'|].
  split; [rewrite F1; exact CIN|]. split; [rewrite F2, F3; exact CCNT|]. split; [rewrite F3; exact NPOS|].
  split; [exact XB|]. split; [exact XC|].
  split; [rewrite F4; exact L1|]. split; [rewrite F5; exact L2|]. split; [rewrite F6; exact L3|]. split; [rewrite F7; exact L4|].
  split; [rewrite F8; exact L5|]. split; [rewrite F9; exact L6|]. split; [rewrite F10; exact L7|]. split; [rewrite F11; exact L8|].
  split; [intros c' NE; rewrite F2; exact (GCo c' NE)|]. split; [exact MU|]. split; [exact WM|].
  split; [rewrite F12, EE; apply init_cache_emb|].
  rewrite F13. destruct LL as [-> | ->]; [left; apply init_cache_exh_list| right; apply exh_clear_init_cache].
Qed.

Lemma dj_cons : forall (iv : Z * Z) W A k, (A + k <= fst iv \/ snd iv <= A) -> disjoint_from W A k -> disjoint_from (iv :: W) A k.
Proof. intros [lo hi] W A k H1 H2. cbn [disjoint_from fst snd] in *. split; assumption. Qed.

Section FalseKinds.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (sp XS c d0 cap0 d1 cap1 d2 cap2 : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis ARV : aresv_ok L RESV.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis SPLO : ATOP <= sp - XS.
Definition bufok (d cap : Z) : Prop := cap <= 0 \/ (d + cap <= ATOP /\ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true).
Hypotheses (B0 : bufok d0 cap0) (B1 : bufok d1 cap1) (B2 : bufok d2 cap2).
Notation RI := (aregion_info L c).
Definition Wn : list (Z * Z) :=
  ((sp - XS, sp) :: ic_W L 1 31) ++ [(RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56); nz d0 cap0; nz d1 cap1; nz d2 cap2].

Lemma nz_clear : forall d cap lo hi A n, bufok d cap -> pcov RESV lo hi -> lo < hi -> 0 <= lo -> lo <= A -> A + n <= hi ->
  A + n <= fst (nz d cap) \/ snd (nz d cap) <= A.
Proof.
  intros d cap lo hi A n B PC LH L0 HA HN. unfold nz. destruct (0 <? cap) eqn:Q; cbn [fst snd]; [| right; lia].
  apply Z.ltb_lt in Q. destruct B as [B|[_ AV]]; [lia|].
  unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (pcov_clear _ _ _ _ _ PC AV LH Q) as [X|X]; [right; lia| left; lia].
Qed.

Lemma Wn_obj : forall lo hi A k, pcov RESV lo hi -> lo < hi -> 0 <= lo -> hi <= ATOP -> lo <= A -> A + k <= hi ->
  disjoint_from (ic_W L 1 31) A k -> (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= AEMB \/ AEMB + 56 <= A) ->
  disjoint_from Wn A k.
Proof.
  intros lo hi A k PC LH L0 HT HA HK DIC R1 R2 EM. unfold Wn. apply dj_app.
  - cbn [disjoint_from]. split; [left; lia| exact DIC].
  - apply dj_cons; [exact R1|]. apply dj_cons; [exact R2|]. apply dj_cons; [exact EM|].
    apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B0 PC LH L0 HA HK)|]. apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B1 PC LH L0 HA HK)|].
    apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B2 PC LH L0 HA HK)| exact I].
Qed.

Lemma fk_geo : RI = al_space_beg L + 137438953472 + c * 128
  /\ al_res L + 4096 <= al_space_beg L <= al_res L + 65536 /\ 0x10007fff8000 <= al_res L /\ al_res L + 137439023104 <= ATOP
  /\ al_res L + 137438957568 <= RI /\ RI + 128 <= al_res L + 137439023104.
Proof.
  pose proof (ao_space L ALO) as SB. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & RT & _).
  assert (E : RI = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold K_NUM_CLASSES in HC. split; [exact E|]. rewrite E. clear E. lia.
Qed.
Lemma ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k.
Proof. intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. Qed.
Lemma ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k.
Proof. intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. Qed.

Lemma K_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI -> (A + k <= AEMB \/ AEMB + 56 <= A) -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct ARV as (PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & _).
  pose proof (ao_t L ALO) as (_ & _ & _ & _ & TI). unfold iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  eapply (Wn_obj 0x10000 0x62f000); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| exact Y4].
Qed.
Lemma K_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from (ic_W L 1 31) A k -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct ARV as (_ & _ & _ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & G6).
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_t_res L ALO) as D. unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *.
  eapply (Wn_obj (al_t L) (al_t L + 4096)); [exact PC| lia| lia| lia| lia| lia| exact Y4| lia| lia| unfold AEMB; lia].
Qed.
Lemma K_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3. destruct ARV as (_ & _ & _ & _ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & G6).
  pose proof (ao_ctx L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_ctx_res L ALO) as D. pose proof (ad_t_ctx L ALO) as D2.
  unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *.
  eapply (Wn_obj (al_ctx L) (al_ctx L + 65536)); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| unfold AEMB; lia].
Qed.
Lemma K_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4 Y5. destruct ARV as (_ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & G4 & _).
  pose proof (ad_t_res L ALO) as D. unfold adisj, AEMB in *. fold (al_res L) in PC.
  eapply (Wn_obj (al_res L) (al_res L + 137439023104)); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| exact Y4| exact Y5| unfold AEMB; lia].
Qed.
Lemma K_sh : forall A k, 0x7fff7000 <= A -> 0 <= k -> A + k <= 0x10007fff8000 -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3. destruct ARV as (_ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & _).
  pose proof (ao_t L ALO) as (_ & _ & _ & TS & _). unfold sclr, KLS, AEMB in *. pose proof atop_range as AT.
  eapply (Wn_obj 0x7fff7000 0x10007fff8000); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| unfold AEMB; lia].
Qed.

Definition piece_ok (iv : Z * Z) : Prop :=
     ATOP <= fst iv
  \/ (al_t L + 288 <= fst iv /\ snd iv <= al_t L + 2768)
  \/ (RI <= fst iv /\ snd iv <= RI + 128)
  \/ (AEMB <= fst iv /\ snd iv <= AEMB + 56)
  \/ iv = (0, 0)
  \/ (0 < snd iv - fst iv /\ snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true).
Lemma nz_piece : forall d cap, bufok d cap -> piece_ok (nz d cap).
Proof.
  intros d cap B. unfold nz, piece_ok. destruct (0 <? cap) eqn:Q; [| right; right; right; right; left; reflexivity].
  apply Z.ltb_lt in Q. destruct B as [B|[B1' B2']]; [lia|]. do 5 right. cbn [fst snd]. replace (d + cap - d) with cap by lia. repeat split; [lia| exact B1'| exact B2'].
Qed.
Lemma Wn_pieces : Forall piece_ok Wn.
Proof.
  unfold Wn. apply Forall_app. split.
  - constructor; [left; cbn [fst]; exact SPLO|]. eapply Forall_impl; [| apply (ic_W_in_t L 1 31); [lia| cbn; lia]].
    intros iv (I1 & I2 & _). right; left. split; assumption.
  - repeat (apply Forall_cons); try apply Forall_nil; try (apply nz_piece; assumption).
    + right; right; left. cbn [fst snd]. lia.
    + right; right; left. cbn [fst snd]. lia.
    + right; right; right; left. cbn [fst snd]. lia.
Qed.

Lemma Wn_buf : forall (iv : Z * Z) lo hi A n, pcov RESV lo hi -> lo < hi -> lo <= A -> A + n <= hi ->
  0 < snd iv - fst iv -> avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true -> snd iv <= A \/ A + n <= fst iv.
Proof.
  intros iv lo hi A n PC LH HA HN POS AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (pcov_clear _ _ _ _ _ PC AV LH POS) as [Q|Q]; lia.
Qed.
Lemma Wn_quar : forall X,
  (forall b, In b (x_busy X) -> al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472) ->
  quar_untouched L X Wn.
Proof.
  intros X BB. unfold quar_untouched. eapply Forall_impl; [| exact Wn_pieces]. intros iv PK. unfold piece_ok in PK.
  destruct ARV as (PCI & _ & PCR & _ & PCT & _). fold (al_res L) in PCR.
  destruct fk_geo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof HC as HC'. unfold K_NUM_CLASSES in HC'.
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_t_res L ALO) as D. unfold adisj, iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  unfold AINSTANCE, AEMB in *.
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  1-4: (split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|]; split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|];
        split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|]; split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|];
        intros b Hb; destruct (BB b Hb) as [Q1 Q2]; destruct (xb_st b); [exact I| clear -K G1 HC' G2 G3 G4 G5 G6 T1 T2 TI D AT Q1 Q2; lia| clear -K G1 HC' G2 G3 G4 G5 G6 T1 T2 TI D AT Q1 Q2; lia]).
  - subst iv. cbn [fst snd]. split; [clear -T1; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
    intros b Hb. destruct (BB b Hb) as [Q1 Q2]. destruct (xb_st b); [exact I| clear -Q1 G2 G3; lia| clear -Q1 G2 G3; lia].
  - pose proof (Wn_buf iv _ _ (al_t L + 80) 128 PCT ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q1.
    pose proof (Wn_buf iv _ _ (877656 + 728) 256 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q2.
    pose proof (Wn_buf iv _ _ 896192 528432 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q3.
    pose proof (Wn_buf iv _ _ 1480008 4 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q4.
    split; [clear -Q1; lia|]. split; [clear -Q2; lia|]. split; [clear -Q3; lia|]. split; [clear -Q4; lia|].
    intros b Hb. destruct (BB b Hb) as [Q5 Q6].
    pose proof (Wn_buf iv _ _ (xb_alloc L b) (size_of_class (xb_class b)) PCR ltac:(clear; lia) ltac:(clear -Q5 G2; lia) ltac:(clear -Q6 G2; lia) K1 K3) as Q7.
    destruct (xb_st b); [exact I| exact Q7| exact Q7].
Qed.
Lemma Wn_sec : sec_untouchedD L RESV st Wn.
Proof.
  unfold sec_untouchedD. eapply Forall_impl; [| exact Wn_pieces]. intros iv PK. unfold piece_ok in PK.
  destruct fk_geo as (_ & G2 & G3 & G4 & G5 & G6).
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  - left. intros a Ha. unfold aknown. do 4 right. left. lia.
  - left. intros a Ha. unfold aknown. do 5 right. left. lia.
  - left. intros a Ha. unfold aknown. do 7 right. left. lia.
  - left. intros a Ha. unfold aknown. left. left. unfold AIMG_HI, AINSTANCE, AEMB in *. lia.
  - left. subst iv. cbn [fst snd]. intros a Ha. lia.
  - right. split; [exact K2| exact K3].
Qed.
Lemma Wn_depot : Forall (fun iv : Z * Z => forall a, fst iv <= a < snd iv ->
     ~ (0x1ab988 <= a < 0x5fb9d0) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) Wn.
Proof.
  eapply Forall_impl; [| exact Wn_pieces]. intros iv PK a Ha. unfold piece_ok in PK.
  destruct ARV as (PCI & _ & _ & _ & _ & _ & PCN & PCS & _).
  destruct fk_geo as (_ & G2 & G3 & G4 & G5 & G6).
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ao_nodes L ALO) as NO. pose proof (ao_store L ALO) as SO.
  pose proof (aobj_img _ _ NO ltac:(lia)) as NI. pose proof (aobj_img _ _ SO ltac:(lia)) as SI. destruct NO as (_ & N1 & N2 & _). destruct SO as (_ & S1 & S2 & _).
  pose proof (ad_t_nodes L ALO) as D1. pose proof (ad_t_store L ALO) as D2. pose proof (ad_nodes_res L ALO) as D3. pose proof (ad_store_res L ALO) as D4.
  unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *. pose proof atop_range as AT.
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  1-4: lia.
  - subst iv. cbn [fst snd] in Ha. lia.
  - pose proof (Wn_buf iv 0x10000 0x62f000 0x10000 (0x62f000 - 0x10000) PCI ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q1.
    pose proof (Wn_buf iv _ _ (al_nodes L) 1048576 PCN ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q2.
    pose proof (Wn_buf iv _ _ (al_store L) 8388608 PCS ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q3. lia.
Qed.
End FalseKinds.

Lemma achunks_init_cache : forall st, achunks (init_cache st) = achunks st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma max_count_ic : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite init_cache_cinit. reflexivity. Qed.
Lemma awf_init_cache : forall L st X, awf L st X -> awf L (init_cache st) X.
Proof.
  intros L st X WF. unfold init_cache. destruct (a_cinit st) eqn:CI; [exact WF|].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split; [| split; [exact OUTC|]; split; [exact BUSY|]; split; [exact LIVE|]; split; [exact FRESH| exact UNIQ]].
  intros c Hc. destruct (PERC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  cbv zeta in *. repeat (split; [assumption|]). split; [| split; [exact ND| exact RANGE]].
  unfold max_count in *. rewrite CI in CNTB. cbn [a_cinit set_cinit].
  pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in Hc; lia)) as [MR _]. change (get_cls (set_cinit true st) c) with (get_cls st c). lia.
Qed.
Lemma arng_init_cache : forall L RNG st, arng L RNG st -> arng L RNG (init_cache st).
Proof. intros L RNG st A. unfold init_cache. destruct (a_cinit st); [exact A|]. destruct st. exact A. Qed.
Lemma quar_same_ic : forall st X, quar_same st (init_cache st) X X.
Proof. intros st X. unfold init_cache. destruct (a_cinit st); destruct st; unfold quar_same; cbn; repeat split; try reflexivity; intros b Hb; destruct (xb_st b); auto. Qed.
Lemma sec_same_ic : forall st, sec_same st (init_cache st).
Proof. intros st. unfold init_cache. destruct (a_cinit st); [apply sec_same_refl|]. destruct st. unfold sec_same. cbn. repeat split; try reflexivity; try (intros Q; exact Q); try apply Permutation_refl. Qed.

Lemma refill_store_false : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  emb_cells st m -> emb_clr RESV st ->
  F_arefill.F_arefill_x.refill_ret_false L RESV RNG sp st c lo (c_count (get_cls st c)) (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  AREP H L st2 X m' /\ arng L RNG' st2 /\ axflag L st2 m' c /\ axg RESV RNG' st2 m'.
Proof.
  intros L RESV RNG RNG' sp m m' st st2 X c lo ALO ARV ARNG AR HC NC CEIL LO EC ECL RR.
  destruct RR as (m1 & MU1 & XF & HDRc & HDRS).
  unfold xfalse_ret in XF. rewrite init_cache_emb in XF.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct XF as (FPLE & STEQ & EC2 & ER2 & XC2 & MTX' & FLG' & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI' & STK').
  unfold emb_prov in PV1, PV2. rewrite achunks_init_cache in PV1, PV2.
  set (st1 := init_cache st) in *.

  assert (B0 : bufok RESV st d0 cap0).
  { unfold bufok. unfold emb_cells in EC. rewrite EA in EC. unfold emb_clr in ECL. rewrite EA in ECL.
    destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
    destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECL as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
  assert (B1 : bufok RESV st d1 cap1).
  { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
    right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
  assert (B2 : bufok RESV st d2 cap2).
  { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
    unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
    destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }
  assert (SPLO : ATOP <= bv_unsigned sp - REFILL_STACK_X) by (clear -CEIL LO; lia).
  set (W := Wn L (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2).
  assert (MUALL : munch W m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; subst W; unfold Wn; intros x Hx;
      apply outside_app in Hx; destruct Hx as [H1 H2]; [exact H1|].
    cbn [outside] in H1. destruct H1 as [H1 _]. apply outside_cons in H2 as [R1 H2]. apply outside_cons in H2 as [R2 H2]. apply outside_cons in H2 as [R3 H2]. cbn [fst snd] in R1, R2, R3.
    apply outside_cons in H2 as [N0 H2]. apply outside_cons in H2 as [N1 H2]. apply outside_cons in H2 as [N2 _].
    apply nz_outside in N0, N1, N2. cbn [outside]. repeat split; assumption. }
  pose proof (K_img L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kimg.
  pose proof (K_t L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kt.
  pose proof (K_ctx L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kctx.
  pose proof (K_res L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kres.
  pose proof (K_sh L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Ksh.
  fold W in Kimg, Kt, Kctx, Kres, Ksh.
  assert (Kt' : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from W A k)
    by (intros A k Y1 Y2 Y3 Y4; apply Kt; [exact Y1| exact Y2| exact Y3| apply ICW_t; exact Y4]).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6).
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11). fold st1 in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11.
  assert (GCI : forall j, get_cls st1 j = get_cls st j) by (intros j; subst st1; apply init_cache_cls).
  assert (NDI : forall j, ndist st1 j = ndist st j) by (intros j; unfold ndist; rewrite GCI; reflexivity).

  assert (RAL8 : al_res L mod 8 = 0) by (pose proof (ao_res L ALO) as (R8 & _); clear -R8; Z.div_mod_to_equations; lia).
  assert (RSH : 0x7fff7000 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= 0x10007fff8000).
  { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as AT. clear -G3 G4 AT. Z.div_mod_to_equations. lia. }
  destruct RSH as [SR1 SR3].
  assert (Kshres : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k)
    by (intros A k Y1 Y2 Y3; apply Ksh; [clear -Y1 SR1; lia| exact Y2| clear -Y3 SR3; lia]).
  assert (BB : forall b, In b (x_busy X) -> al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -P5 P4 Q1 Q2 CLB. lia. }
  assert (AR1 : AREPns H L st1 X m').
  { split; [apply awf_init_cache; exact WF|].
    split. { eapply arep_rt_frameD; [exact MUALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AEMB; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. { eapply (ainstance_frameD L W m m' MUALL st st1); [exact INST| exact E8| exact E7| | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI, AEMB; lia. }
    split. { unfold athread.
             split; [eapply cells_frameD; [exact T0c| exact MUALL| apply Kt'; clear; cbn; lia]|].
             split; [eapply cells_frameD; [exact T40| exact MUALL| apply Kt'; clear; cbn; lia]|].
             split. { intros j Hj. destruct (CACHES j Hj) as [tail (REC & ARR & LEN)]. exists tail. unfold K_NUM_CLASSES in Hj.
                      split; [| split; [| exact LEN]].
                      - rewrite GCI. subst st1. rewrite max_count_ic, init_cache_cinit.
                        destruct (Z.eq_dec j c) as [->|NE]; [exact HDRc|]. exact (HDRS j ltac:(clear -Hj; lia) NE).
                      - eapply u32arr_frameD; [exact ARR| exact MUALL|]. rewrite length_app, length_map.
                        replace (4 * Z.of_nat (length (xc_cache (x_cls X j)) + length tail)) with 64 by (clear -LEN; lia).
                        apply Kt; [unfold acache_addr; clear -Hj; lia| clear; lia| unfold acache_addr; clear -Hj; lia| apply ic_W_disjoint_chunks]. }
             split; [eapply junk_frameD; [exact CSTATS| exact MUALL| intros _; apply Kt'; clear; lia]|].
             split; [exists sj; split; [eapply u64arr_frameD; [exact STATS| exact MUALL| rewrite LSJ; apply Kt'; clear; unfold ASTATS_WORDS; lia]| exact LSJ]|].
             eapply cells_frameD; [exact UNW| exact MUALL| apply Kt'; clear; cbn; lia]. }
    split.
    {
      intros c' Hc'. destruct (CLS c' Hc') as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c' Hc') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c' Hc') as [QS QS16]. pose proof (aregion_mod L c' SAL) as RM. unfold K_NUM_CLASSES in Hc'.
      assert (RGc : al_res L <= aregion L c' /\ aregion L c' + K_REGION <= al_space_beg L + 137438953472
                   /\ al_space_beg L + 137438953472 <= aregion_info L c).
      { unfold aregion, K_REGION. change (2^32) with 4294967296. pose proof HC as HC'. unfold K_NUM_CLASSES in HC'. clear -Hc' G2 RIE HC'. lia. }
      destruct RGc as (RI1 & RI2 & RI3). unfold K_REGION in RI2. change (2^32) with 4294967296 in RI2.
      assert (Kreg : forall A k, aregion L c' <= A -> 0 <= k -> A + k <= aregion L c' + 4294967296 -> disjoint_from W A k).
      { intros A k Y1 Y2 Y3. apply Kres; [clear -Y1 RI1; lia| exact Y2| clear -Y3 RI2 RI3 G6; lia| left; clear -Y3 RI2 RI3; lia| left; clear -Y3 RI2 RI3; lia]. }
      assert (Kshreg : forall A k, shad (aregion L c') <= A -> 0 <= k -> A + k <= shad (aregion L c' + 4294967296) -> disjoint_from W A k).
      { intros A k Y1 Y2 Y3. apply Kshres; [pose proof (shad_mono _ _ RI1) as Q; clear -Y1 Q; lia| exact Y2|].
        assert (Q : shad (aregion L c' + 4294967296) <= shad (al_res L + 137439023104)) by (apply shad_mono; clear -RI2 RI3 G6; lia). clear -Y3 Q. lia. }
      split; [| split; [| split]].
      - destruct (Z.eq_dec c' c) as [->|NE].
        +
          destruct REG as (MTX16 & REGc & RJ4 & EXHc & RJ56). unfold aregion_cells. cbv zeta. rewrite GCI.
          assert (Kri : forall A k, aregion_info L c + 8 <= A -> 0 <= k -> A + k <= aregion_info L c + 128 ->
                          (A + k <= aregion_info L c + 68 \/ aregion_info L c + 69 <= A) -> disjoint_from W A k).
          { intros A k Y1 Y2 Y3 Y4. apply Kres; [clear -Y1 G5; lia| exact Y2| clear -Y3 G6; lia| right; clear -Y1; lia| exact Y4]. }
          pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
          eapply cells_frameD in M2b; [| exact MUALL| cbn [cells_size csize Nat.add]; apply Kri; clear; lia].
          split. { rw_join MTX' M2b M16. exact M16. }
          split; [eapply cells_frameD; [exact REGc| exact MUALL| cbn [cells_size csize Nat.add]; apply Kri; clear; lia]|].
          split; [eapply junk_frameD; [exact RJ4| exact MUALL| intros _; apply Kri; clear; lia]|].
          split; [unfold aflag_cell; replace (c =? K_BATCH_CLASS) with false by (symmetry; apply Z.eqb_neq; exact NC); exact (junk_of_cells m' _ _ FLG')|].
          eapply junk_frameD; [exact RJ56| exact MUALL| intros _; apply Kri; clear; lia].
        + eapply aregion_cells_frameD; [exact MUALL| exact REG| rewrite GCI; reflexivity| rewrite GCI; reflexivity| rewrite GCI; reflexivity| rewrite GCI; reflexivity|].
          apply Kres; [unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -Hc' G2; lia| clear; lia
                      | unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -Hc' G2; lia
                      | rewrite RIE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -NE; lia
                      | rewrite RIE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -NE; lia].
      - eapply afreearray_frameD; [exact MUALL| exact FARR| rewrite GCI; reflexivity| rewrite GCI; reflexivity| reflexivity| exact QLENF| exact Q5| | clear -Q6; lia|].
        + apply Kreg; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear; lia| clear -Q5 Q6; lia| clear -Q6; lia].
        + apply Kshreg; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear; lia| apply shlen_nonneg; clear -Q5 Q6; lia|].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -Q6. lia.
      - eapply (aslots_updateD L W m m' MUALL st st1 X X c' (-1)); [exact SLOTS| apply NDI| rewrite GCI; reflexivity| rewrite GCI; reflexivity| | | intros Hk; exfalso; clear -Hk; lia].
        + intros kq Hk _. pose proof (slot_in_region L st c' kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kreg; [exact P5| clear -QS; lia| clear -P4 Q1 Q2; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kreg; [clear -Q1; lia| clear -POS; lia| clear -Q1 Q2; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_updateD L W m m' MUALL st st1 X X c' (-1)); [exact SHADOW| apply NDI| rewrite GCI; reflexivity| rewrite GCI; reflexivity| | | intros Hk; exfalso; clear -Hk; lia| apply shlen_nonneg; clear -QS; lia].
        + intros kq Hk _. pose proof (slot_in_region L st c' kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c' kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc'; lia)) as AL.
          split; [reflexivity|]. apply Kshreg; [apply shad_mono; exact P5| apply shlen_nonneg; clear -QS; lia|].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kshreg; [apply shad_mono; clear -Q1; lia| clear -POS; lia|].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2. unfold K_FREEARR_OFF in *. lia. }

    split. { eapply (hqD H HLD L st st1 X X m m' W); [exact HQ| exact MUALL| | apply quar_same_ic].
             exact (Wn_quar L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2 X BB). }
    split. { eapply (hdD H HLD L m m' W); [exact HD| exact MUALL|].
             exact (Wn_depot L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2). }

    split; [eapply (ARepFrameD.arelro_frameD W m m' MUALL); [exact HRO| apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AEMB; lia]|].
    split; [eapply arep_rt2_frameD; [exact MUALL| exact RT2| | |]; apply Kimg; clear; unfold AIMG_HI, AEMB; lia|].
    split; [| eapply arep_rt3_frameD; [exact MUALL| exact RT3|]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AEMB; lia|]); apply Forall_nil].
    intros c' Hc'. destruct (PERC c' Hc') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc'.
    assert (RGc : al_res L <= aregion L c' /\ aregion L c' + 4294967296 <= al_res L + 137439023104).
    { unfold aregion, K_REGION. change (2^32) with 4294967296. clear -Hc' G2. lia. }
    destruct RGc as (RI1 & RI2). pose proof (aregion_mod L c' SAL) as RM.
    eapply (ashadow_avail_frameD L W m m' MUALL st st1); [exact (AVL c' ltac:(unfold K_NUM_CLASSES; clear -Hc'; lia))| rewrite GCI; reflexivity| rewrite GCI; reflexivity| |].
    - intros POS. apply Kshres; [apply shad_mono; clear -Q1 RI1; lia| clear -POS; lia|].
      rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF in *. clear -Q1 Q2 RI2. lia.
    - intros POS. apply Kshres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF in *; clear -Q5 Q6 RI1; lia| clear -POS; lia|].
      rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -Q5 Q6 RI2. lia. }

  assert (ST2 : exists l e, st2 = set_emb e (set_exh l st1) /\ exh_mem c st2 = true).
  { destruct STEQ as [[EM E]|[EM [e2 E]]].
    - exists (a_exh st1), (a_emb st1). split; [rewrite E; symmetry; apply set_x_eta| rewrite E; exact EM].
    - exists (c :: a_exh st1), e2. split; [exact E|]. rewrite E. unfold exh_mem, exh_set. destruct st1. cbn. rewrite Z.eqb_refl. reflexivity. }
  destruct ST2 as (l & e & ES & EM2).

  assert (ECL2 : emb_clr RESV st2).
  { unfold emb_clr. rewrite EA2.
    assert (ACH : achunks st2 = achunks st) by (rewrite ES; destruct st1 eqn:Q; cbn; rewrite <- (achunks_init_cache st); fold st1; rewrite Q; reflexivity).
    rewrite ACH. destruct B2 as [LE|[_ AV]]; [| right; exact AV].
    pose proof EC2 as EC2'. unfold emb_cells in EC2'. rewrite EA2 in EC2'. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; exact E0|].
    destruct EC2' as (_ & _ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -LE P2. lia. }
  assert (AXF2 : axflags L st2 m').
  { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [unfold axflag; rewrite EM2; exact FLG'|].
    pose proof (hx_get H HLD L st X m HS) as (_ & _ & AXFm & _). pose proof (AXFm c' Hc' NC') as F0. unfold axflag in *.
    assert (EXE : exh_mem c' st2 = exh_mem c' st).
    { assert (SE : forall e0 s, exh_mem c' (set_emb e0 s) = exh_mem c' s) by (intros e0 []; reflexivity).
      destruct STEQ as [[_ E]|[_ [e2 E]]]; rewrite E; [apply init_cache_exh|]. rewrite SE, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
    rewrite EXE. eapply cells_frameD; [exact F0| exact MUALL|]. cbn [cells_size csize Nat.add].
    destruct (fk_geo L c' ALO Hc') as (RIE' & _ & _ & _ & G5' & G6'). unfold K_NUM_CLASSES in *.
    apply Kres; [clear -G5'; lia| clear; lia| clear -G6'; lia| rewrite RIE, RIE'; clear -NE Hc' HC; lia| rewrite RIE, RIE'; clear -NE Hc' HC; lia]. }
  assert (AEX2 : AEXH L st2 m').
  { split; [exact XC2|]. split; [exact EC2|]. split; [exact AXF2|]. split; [exact (emb_clrK_of L RESV st2 m' ALO ARV EC2 ECL2)| exact (emb_clrS_of RESV st2 ECL2)]. }
  split.
  { apply AREP_split. split; [rewrite ES; apply AREPns_x_indep; exact AR1|].
    eapply (hsD H HLD L RESV st st2 X X m m' W ARV HS MUALL); [| | exact AEX2].
    - exact (Wn_sec L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO HC SPLO B0 B1 B2).
    - rewrite ES. apply sec_sameX_x. exact (sec_same_X _ _ (sec_same_ic st)). }
  split; [rewrite ES; apply arng_x_indep; apply (arng_mono L RNG RNG'); [exact FPLE| apply arng_init_cache; exact ARNG]|].
  split; [unfold axflag; rewrite EM2; exact FLG'|].
  unfold axg. split; [exact XC2|]. split; [exact EC2|]. split; [exact ER2| exact ECL2].
Qed.

Lemma exh_cells_frameK : forall m m' (W : list (Z * Z)), exh_cells m -> munch W m m' ->
  (forall A k, 0 <= k -> AIMG_LO <= A -> A + k <= AIMG_HI -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from W A k) -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU K. destruct RC as (R1 & R2 & R3 & R4 & R5).
  assert (T : forall A cs, rw_cells asegs m A cs -> (AIMG_LO <=? A) = true -> (A + Z.of_nat (cells_size cs) <=? AIMG_HI) = true ->
                ((A + Z.of_nat (cells_size cs) <=? AINSTANCE) || (AINSTANCE + 728 <=? A)) = true -> rw_cells asegs m' A cs).
  { intros A cs Hc H1 H2 H3. eapply cells_frameD; [exact Hc| exact MU|]. apply K; [lia| apply Z.leb_le; exact H1| apply Z.leb_le; exact H2|].
    apply orb_prop in H3. destruct H3 as [H3|H3]; apply Z.leb_le in H3; [left| right]; exact H3. }
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T; [eassumption| reflexivity| reflexivity| reflexivity]).
Qed.

Section TrueKinds.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (c sp lo : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= sp - 1536.
Hypothesis MU0 : 0 <= c_mapped_user (get_cls st c).
Lemma tk_geo : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439019008 /\ aregion L c mod 8 = 0
  /\ 0x10007fff8000 <= al_res L /\ al_res L + 137439023104 <= ATOP /\ al_res L mod 8 = 0.
Proof.
  pose proof (ao_space L ALO) as SB. pose proof (ao_space_al L ALO) as SAL. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (R8 & _ & RT & _).
  unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296. repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.
Lemma arefillW_img : forall A k, 0 <= k -> AIMG_LO <= A -> A + k <= AIMG_HI -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) ->
  disjoint_from (arefill_W L st c sp) A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct (fk_geo L c ALO HC) as (_ & _ & G3 & _ & G5 & _). destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (ao_t L ALO) as (_ & _ & _ & _ & TI). unfold iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  assert (SHL : 0x7fff8000 <= shad (aregion L c + c_mapped_user (get_cls st c))) by (rewrite shad_div; unfold ASHOFF; clear -T1 T4 MU0; Z.div_mod_to_equations; lia).
  cbn [disjoint_from]. repeat split; try exact I; clear -Y1 Y2 Y3 Y4 G3 G5 T1 T4 TI AT SHL CEIL LO MU0; lia.
Qed.

Lemma arefillW_flag : forall c', 1 <= c' < K_NUM_CLASSES -> c' <> c -> disjoint_from (arefill_W L st c sp) (aregion_info L c' + 68) 1.
Proof.
  intros c' Hc' NE. destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6). destruct (fk_geo L c' ALO Hc') as (RIE' & _ & _ & _ & G5' & G6').
  destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (ao_t L ALO) as (_ & _ & OT2 & _ & TI). pose proof (ad_t_res L ALO) as DTR. unfold adisj, iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  assert (SHH : shad (aregion L c) + shlen K_REGION <= 0x10007fff8000).
  { rewrite shad_div, shlen_div. unfold ASHOFF, K_REGION in *. change (2^32) with 4294967296 in *. clear -T2 T5 AT. Z.div_mod_to_equations. lia. }
  unfold K_NUM_CLASSES, aregion, K_REGION, AINSTANCE in *. change (2^32) with 4294967296 in *.
  cbn [disjoint_from]. rewrite RIE, RIE'. repeat split; try exact I; clear -NE Hc' HC G2 G3 G4 G5' G6' T1 T2 T4 T5 OT2 TI DTR AT SHH CEIL LO MU0; lia.
Qed.
Lemma arefillW_buf : forall d cap, aresv_ok L RESV -> c_mapped_user (get_cls st c) <= K_REGION ->
  0 < cap -> AIMG_HI <= d -> d + cap <= ATOP -> avoids_all d cap RESV = true -> disjoint_from (arefill_W L st c sp) d cap.
Proof.
  intros d cap ARV MUK POS DI DT AV. destruct ARV as (_ & PCS & PCR & _ & PCT & _). fold (al_res L) in PCR.
  destruct (fk_geo L c ALO HC) as (_ & _ & G3 & _ & G5 & G6). destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) POS) as Q1. pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) POS) as Q2.
  pose proof (pcov_clear _ _ _ _ _ PCS AV ltac:(lia) POS) as Q3.
  assert (SHB : 0x7fff7000 <= shad (aregion L c + c_mapped_user (get_cls st c)) /\ shad (aregion L c) + shlen K_REGION <= 0x10007fff8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION in *. change (2^32) with 4294967296 in *. pose proof atop_range as AT. clear -T1 T2 T3 T4 T5 MU0 AT. Z.div_mod_to_equations. lia. }
  destruct SHB as [SH1 SH2]. unfold AIMG_HI, AINSTANCE, K_REGION in *. change (2^32) with 4294967296 in *.
  cbn [disjoint_from]. repeat split; try exact I; clear -POS DI DT Q1 Q2 Q3 G5 G6 T1 T2 SH1 SH2 CEIL LO MU0 MUK; lia.
Qed.
End TrueKinds.

Lemma pcov_sub : forall RESV lo hi lo' hi', pcov RESV lo hi -> lo <= lo' -> hi' <= hi -> pcov RESV lo' hi'.
Proof. intros RESV lo hi lo' hi' PC H1 H2 x Hx. apply PC. lia. Qed.
Lemma rng_fp_le : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

Lemma refill_xf_of_false : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z)
    (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  emb_cells st m -> emb_clr RESV st ->
  F_arefill.F_arefill_x.refill_ret_false L RESV RNG sp st c lo (c_count (get_cls st c)) (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  refill_ret_xf H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG'
    (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc ra) fc None m' (seg_rom asegs)).
Proof.
  intros L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
         ALO ARV ARNG AR HC NC CEIL LO EC ECL RF.
  pose proof (refill_store_false L RESV RNG RNG' sp m m' st st2 X c lo ALO ARV ARNG AR HC NC CEIL LO EC ECL RF) as (AR2 & ARNG2 & AXF2 & AXG2).
  destruct RF as (m1 & MU1 & XF & _ & _). unfold xfalse_ret in XF. rewrite init_cache_emb in XF.
  unfold refill_ret_xf, aret_xf. cbv zeta.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct XF as (FPLE & STEQ & _ & _ & _ & _ & _ & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI' & STK').
  split; [exact FPLE|]. do 15 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
  split; [rewrite init_cache_exh in STEQ; exact STEQ|].
  split; [exact AR2|]. split; [exact ARNG2|]. split; [exact AXF2|]. split; [exact AXG2|].
  unfold emb_prov in PV1, PV2 |- *. rewrite achunks_init_cache in PV1, PV2.
  exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *.
  - destruct Hx as (X1 & X2 & _). split; [clear -X1; lia|]. apply ic_W_outside; [unfold acache_addr; clear -X2; lia| clear; cbn; lia| clear; lia].
  - destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). split; [clear -X1; lia|]. repeat (split; [assumption|]). exact I.
Qed.

Lemma refill_xt_of_true : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z)
    (chunks0 : list word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  u32arr asegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  axg RESV RNG st m ->
  F_arefill.F_arefill_x.refill_ret_x L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', refill_ret_xt H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG'
    (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc ra) fc None m' (seg_rom asegs)).
Proof.
  intros L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo chunks0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
         ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH AXG RR. cbv zeta.
  destruct AXG as (XC & EC & ER & ECL).
  assert (LO' : lo <= bv_unsigned sp - 1536) by (clear -LO; lia).
  pose proof AR as (_ & _ & _ & _ & _ & _ & HS0 & _).
  destruct (refill_store_x L RESV RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARV ARNG AR HC NC CNT0 CEIL LO' CH LCH RR)
    as (X' & ARI & ARNG' & CIN & CCNT & NPOS & XB & XCL & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM & EMB' & EXHL).
  destruct RR as (m1 & _ & _ & TR & _). unfold refill_tail_ret_x in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _ & _ & EXH' & _).
  set (st_r := put_cls c (cls_set_count (max_cached c / 2) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_cached c / 2) (get_cls st2 c))) st2) in *.
  assert (EXM : exh_mem c st_r = exh_mem c st2) by reflexivity.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c HC) as (A1 & A2 & _).

  assert (MU0 : 0 <= c_mapped_user (get_cls st c)) by (clear -A1; lia).
  assert (MUK : c_mapped_user (get_cls st c) <= K_REGION) by (unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; clear -A2; lia).
  pose proof (arefillW_img L st c (bv_unsigned sp) lo ALO HC CEIL LO' MU0) as KI.
  assert (AXFc : axflag L st_r m' c) by (unfold axflag; rewrite EXM; exact EXH').
  assert (XC' : exh_cells m') by (eapply exh_cells_frameK; [exact XC| exact MU| exact KI]).
  assert (EC' : emb_cells st_r m').
  { assert (EC0 : emb_cells st m').
    { destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
      eapply emb_cells_frameD; [exact EC| exact MU| apply KI; clear; unfold AEMB, AIMG_LO, AIMG_HI, AINSTANCE; lia|]. rewrite EA.
      destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; exact E0| right].
      pose proof EC as EC1. unfold emb_cells in EC1. rewrite EA in EC1. replace (cap0 =? 0) with false in EC1 by (symmetry; apply Z.eqb_neq; exact NZ).
      destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _).
      unfold emb_clr in ECL. rewrite EA in ECL. destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      apply (arefillW_buf L RESV st c (bv_unsigned sp) lo ALO HC CEIL LO' MU0 d0 cap0 ARV MUK); [unfold EMB_INIT in P2; clear -P2; lia| exact P5| exact P6| exact AV]. }
    unfold emb_cells in EC0 |- *. rewrite EMB'. exact EC0. }
  assert (ECL' : emb_clr RESV st_r).
  { unfold emb_clr in ECL |- *. rewrite EMB'. assert (ACH : achunks st_r = achunks st) by (unfold achunks; rewrite L1, L3, L5; reflexivity). rewrite ACH. exact ECL. }
  assert (AXFS' : axflags L st_r m').
  { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFc|].
    pose proof (hx_get H HLD L st X m HS0) as (_ & _ & AXFm & _). pose proof (AXFm c' Hc' NC') as F0. unfold axflag in *.
    assert (EXE : exh_mem c' st_r = exh_mem c' st).
    { destruct EXHL as [E|E]; [apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); apply exh_mem_clear_other; exact NE]. }
    rewrite EXE. eapply cells_frameD; [exact F0| exact MU|]. cbn [cells_size csize Nat.add].
    eapply arefillW_flag; first [exact ALO| exact HC| exact CEIL| exact LO'| exact MU0| exact Hc'| exact NE]. }
  assert (AR' : AREP H L st_r X' m').
  { apply ARI. split; [exact XC'|]. split; [exact EC'|]. split; [exact AXFS'|]. split; [exact (emb_clrK_of L RESV st_r m' ALO ARV EC' ECL')| exact (emb_clrS_of RESV st_r ECL')]. }
  exists X'. unfold refill_ret_xt. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|].
  split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XCL|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  split; [exact GC|]. split; [exact EMB'|]. split; [exact EXHL|].
  split; [exact AXFc|].
  unfold axg. split; [exact XC'|]. split; [exact EC'|].
  split; [unfold emb_rng in ER |- *; rewrite EMB'; destruct (a_emb st) as [[d0 cap0] sz0]; destruct ER as [QQ|QQ]; [left; exact QQ| right; exact (rng_fp_le _ _ _ _ FPLE QQ)]|].
  exact ECL'.
Qed.

Theorem arefill_x : refill_stmt_x H.
Proof.
  unfold refill_stmt_x.
  intros R RESV k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC NC CNT0 RSTK EXHW ARV SP63 FC AXF AXG CAPB KF KT.
  pose proof AXG as AXG0. destruct AXG as (XC & EC & ER & ECL).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & _ & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }

  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
  destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6).
  pose proof ARV as ARV0. destruct ARV0 as (_ & _ & PCR & _ & PCT & _). fold (al_res L) in PCR.
  assert (PCRI : pcov RESV (aregion_info L c) (aregion_info L c + 128)) by (eapply pcov_sub; [exact PCR| clear -G5; lia| clear -G6; lia]).
  assert (CAPZ : cap0 <= 0 -> cap0 = 0).
  { intros LE. unfold emb_cells in EC. rewrite EA in EC. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [exact E0|].
    destruct EC as (_ & _ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -LE P2. lia. }
  assert (CLRI : cap0 = 0 \/ aregion_info L c + 128 <= d0 \/ d0 + cap0 <= aregion_info L c).
  { destruct (emb_clr_pcov RESV st d0 cap0 sz0 _ _ ECL EA PCRI ltac:(clear; lia)) as [QQ|[QQ|QQ]]; [left; exact (CAPZ QQ)| right; right; exact QQ| right; left; exact QQ]. }
  assert (CLT : cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L).
  { destruct (emb_clr_pcov RESV st d0 cap0 sz0 _ _ ECL EA PCT ltac:(clear; lia)) as [QQ|[QQ|QQ]]; [left; exact (CAPZ QQ)| right; right; exact QQ| right; left; exact QQ]. }
  assert (LO' : lo <= bv_unsigned sp - 1536) by (clear -LO; lia).
  eapply refill_spec_x with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                            (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail) (RESV := RESV);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- context [a_emb st] => rewrite EA; first [exact CAPB | exact CLRI | exact CLT]
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ARV
       | |- arelro _ => exact HRO
       | |- exh_cells _ => exact XC
       | |- emb_cells _ _ => exact EC
       | |- emb_rng _ _ => exact ER
       | |- pcov _ (aregion_info _ _) _ => exact PCRI
       | |- pcov _ (al_t _) _ => exact PCT
       | |- bv_unsigned _ < 2 ^ 63 => exact SP63
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ <> K_BATCH_CLASS => exact NC
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact AXF
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.
  -
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RF.
    eapply KF. eapply refill_xf_of_false; [exact ALO| exact ARV| exact ARNG| exact AR| exact HC| exact NC| exact CEIL| exact LO| exact EC| exact ECL| exact RF].
  -
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
    destruct (refill_xt_of_true L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo tail
                t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH AXG0 RR) as [X' RT'].
    unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2). eapply KT. exact RT'.
Qed.

End RefillPX.
End CANSECX.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ABytes.TwinB AModelFacts.TwinB ARep.TwinB ARepKit.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB ARefill_iface.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import F_aensure.TwinB F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP. Import AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB ARepFrameD.TwinB AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import ARefill_iface_x.TwinB.
Import AExh.TwinB AC6Frame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.
Notation AREFILL_STACK_X := 2048 (only parsing).

Definition sec_untouchedD (L : alayout) (RESV : list (Z * Z)) (st : astate) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (forall a, fst iv <= a < snd iv -> aknown L a)
                 \/ (snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true)) W.
Record ahole_lawsD (H : aholes) : Prop := mkAHLD {
  hqD : forall L st st' X X' m m' W,
      ah_quar H L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' -> ah_quar H L st' X' m';

  hx_get : forall L st X m, ah_sec H L st X m -> AEXH L st m;

  hsD : forall L RESV st st' X X' m m' W,
      aresv_ok L RESV -> ah_sec H L st X m -> munch W m m' -> sec_untouchedD L RESV st W -> sec_sameX st st' -> AEXH L st' m' -> ah_sec H L st' X' m';
  hdD : forall L m m' W,
      ah_depot H L m -> munch W m m' ->
      Forall (fun iv => forall a, fst iv <= a < snd iv ->
                           ~ (0x1adb48 <= a < 0x5fdb90) /\ ~ (al_nodes L <= a < al_nodes L + 1048576)
                           /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
      ah_depot H L m';

  hfD : forall L LB m m' W,
      ah_fake H L LB m -> munch W m m' -> disjoint_from W (al_t L + 72) 8 -> fake_untouched L W ->
      Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> ah_fake H L LB m'
}.

Definition nz (d cap : Z) : Z * Z := if 0 <? cap then (d, d + cap) else (0, 0).
Lemma outside_cons : forall (iv : Z * Z) W x, outside (iv :: W) x <-> ~ (fst iv <= x < snd iv) /\ outside W x.
Proof. intros [lo hi] W x. cbn [outside fst snd]. tauto. Qed.
Lemma nz_outside : forall d cap x, ~ (fst (nz d cap) <= x < snd (nz d cap)) -> ~ (d <= x < d + cap).
Proof. intros d cap x. unfold nz. destruct (0 <? cap) eqn:Q; cbn [fst snd]; [tauto|]. apply Z.ltb_ge in Q. intros _. lia. Qed.
Lemma ic_W_in_t : forall L i d, 1 <= i -> i + Z.of_nat d <= 32 ->
  Forall (fun iv : Z * Z => al_t L + 288 <= fst iv /\ snd iv <= al_t L + 2768 /\ fst iv <= snd iv) (ic_W L i d).
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i Hi Hd; cbn [ic_W]; [constructor|].
  constructor; [cbn [fst snd]; unfold acache_addr; lia| apply IH; lia].
Qed.

Section RefillPX.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Hypothesis HLD : ahole_lawsD H.

Lemma quar_same_x : forall st X l e, quar_same st (set_emb e (set_exh l st)) X X.
Proof. intros st X l e. destruct st. unfold quar_same. cbn. repeat split; try reflexivity; intros b Hb; destruct (xb_st b); auto. Qed.

Lemma sec_sameX_x : forall st st' l e, sec_sameX st st' -> sec_sameX st (set_emb e (set_exh l st')).
Proof. intros st st' l e S. destruct st'. exact S. Qed.

Lemma AREPns_x_indep : forall L st X m l e, AREPns H L st X m -> AREPns H L (set_emb e (set_exh l st)) X m.
Proof.
  intros L st X m l e (WF & RT & INST & THR & CLS & HQ & HD & HRO & RT2 & AVL & RT3).
  pose proof (quar_same_x st X l e) as QS.
  assert (HQ' : ah_quar H L (set_emb e (set_exh l st)) X m)
    by (eapply (hq_frame H HL L st _ X X m m []); [exact HQ| apply munch_refl| apply wmono_refl| constructor| exact QS]).
  clear QS HQ. destruct st.
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact HQ'|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.
Lemma arng_x_indep : forall L RNG st l e, arng L RNG st -> arng L RNG (set_emb e (set_exh l st)).
Proof. intros L RNG st l e A. destruct st. exact A. Qed.

Lemma set_x_eta : forall st, set_emb (a_emb st) (set_exh (a_exh st) st) = st.
Proof. intros st. destruct st. reflexivity. Qed.
Lemma put_cls_set_x : forall c r l e st, put_cls c r (set_emb e (set_exh l st)) = set_emb e (set_exh l (put_cls c r st)).
Proof. intros. destruct st. reflexivity. Qed.
Lemma exh_clear_as_set : forall c st, exh_clear c st = set_emb (a_emb st) (set_exh (a_exh (exh_clear c st)) st).
Proof. intros c st. destruct st. reflexivity. Qed.

Lemma set_x_fields : forall l e st,
  let s' := set_emb e (set_exh l st) in
  a_cinit s' = a_cinit st /\ (forall c, get_cls s' c = get_cls st c) /\ (forall c, max_count s' c = max_count st c)
  /\ a_live s' = a_live st /\ a_next s' = a_next st /\ a_qloc s' = a_qloc st /\ a_qloc_bytes s' = a_qloc_bytes st
  /\ a_qglob s' = a_qglob st /\ a_qglob_bytes s' = a_qglob_bytes st /\ a_nsec s' = a_nsec st /\ a_nres s' = a_nres st
  /\ a_emb s' = e /\ a_exh s' = l.
Proof. intros l e st. destruct st. cbv zeta. repeat split; reflexivity. Qed.

Lemma refill_ret_x_old : forall L RNG sp st c lo fl chunks0 cnt m st2 RNG' m',
  c <> K_BATCH_CLASS ->
  F_arefill.TwinB.F_arefill_x.refill_ret_x L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
  exists st2o l, st2 = set_emb (a_emb st2o) (set_exh l st2o) /\ get_cls st2o c = get_cls st2 c
    /\ (l = a_exh (init_cache st) \/ l = a_exh (exh_clear c (init_cache st)))
    /\ a_emb st2o = a_emb (init_cache st)
    /\ F_arefill.TwinB.F_arefill.refill_ret L RNG sp st c lo fl chunks0 cnt m st2o RNG' m'.
Proof.
  intros L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' NC RR.
  destruct RR as (m1 & MU1 & WM1 & TR & RECS).
  unfold refill_tail_ret_x in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & EXH' & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  set (st1 := init_cache st) in *.
  assert (PICK : exists st2o l, st2 = set_emb (a_emb st2o) (set_exh l st2o) /\ get_cls st2o c = get_cls st2 c
                   /\ (l = a_exh st1 \/ l = a_exh (exh_clear c st1)) /\ a_emb st2o = a_emb st1
                   /\ (st2o = st1 \/ st2o = put_cls c (get_cls st2o c) st1)).
  { destruct ST2E as [E|E].
    - exists st1, (a_exh st1). rewrite E. split; [symmetry; apply set_x_eta|]. split; [reflexivity|]. split; [left; reflexivity|]. split; [reflexivity| left; reflexivity].
    - set (R2 := get_cls st2 c) in *. exists (put_cls c R2 st1), (a_exh (exh_clear c st1)).
      pose proof (get_cls_put_cls_eq c R2 st1) as G.
      split. { rewrite E. rewrite (exh_clear_as_set c (put_cls c R2 st1)). destruct st1; reflexivity. }
      split; [exact G|]. split; [right; reflexivity|]. split; [destruct st1; reflexivity|]. right. rewrite G. reflexivity. }
  destruct PICK as (st2o & l & ES & GC & LL & EE & SO).
  exists st2o, l. split; [exact ES|]. split; [exact GC|]. split; [exact LL|]. split; [exact EE|].
  exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [| exact RECS].
  unfold F_arefill.TwinB.F_arefill.refill_tail_ret. cbv zeta. fold st1.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split; [exact UD|]. split; [exact MUB|]. split; [exact MUM'|]. split; [exact NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split; [exact FD|]. split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|]. split; [exact AR2|]. split; [exact JR|].
  split; [rewrite GC; exact GC2|]. split; [exact SO|].
  split; [exact MUT|]. split; [exact WMT|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MTX'|]. split; [exact REG'|].
  split. { eexists. split; [exact EXH'|]. intros X. exfalso. exact (NC X). }
  split; [exact STN'|]. split; [exact STATS'|]. split; [exact LSJ'|]. split; [exact STM'|]. split; [exact REC'|]. split; [exact CH'|].
  split; [exact AZU'|]. split; [exact AZF'|]. exact MC'.
Qed.

Lemma init_cache_exh_list : forall st, a_exh (init_cache st) = a_exh st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma exh_clear_init_cache : forall c st, a_exh (exh_clear c (init_cache st)) = a_exh (exh_clear c st).
Proof. intros c st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma refill_store_x : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  F_arefill.TwinB.F_arefill_x.refill_ret_x L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', (AEXH L st_r m' -> AREP H L st_r X' m')
    /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m'
    /\ a_emb st_r = a_emb st /\ (a_exh st_r = a_exh st \/ a_exh st_r = a_exh (exh_clear c st)).
Proof.
  intros L RESV RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH RR. cbv zeta.
  destruct (refill_ret_x_old _ _ _ _ _ _ _ _ _ _ _ _ _ NC RR) as (st2o & l & ES & GC & LL & EE & RRo).
  pose proof (refill_store_ns H HL L RNG RNG' sp m m' st st2o X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RRo) as S0. cbv zeta in S0.
  set (n := max_cached c / 2) in *.
  set (st_ro := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2o c) - n) (get_cls st2o c))) st2o) in *.
  assert (ESR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = set_emb (a_emb st2o) (set_exh l st_ro)).
  { rewrite <- GC. rewrite ES at 1. subst st_ro. apply put_cls_set_x. }
  rewrite ESR.
  destruct S0 as (X' & WH & ARNS & MUH & SU & _ & SSo & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GCo & MU & WM).
  destruct (set_x_fields l (a_emb st2o) st_ro) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13). cbv zeta in *.
  exists X'. split.
  { intros AX. apply AREP_split. split; [apply AREPns_x_indep; exact ARNS|].
    destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
    eapply (hsD H HLD L RESV st _ X X' m m' WH ARV HS MUH); [| apply sec_sameX_x; exact (sec_same_X _ _ SSo)| exact AX].
    unfold sec_untouchedD. eapply Forall_impl; [| exact SU]. intros iv K. left. exact K. }
  split; [apply arng_x_indep; exact ARNG'|].
  split; [rewrite F1; exact CIN|]. split; [rewrite F2, F3; exact CCNT|]. split; [rewrite F3; exact NPOS|].
  split; [exact XB|]. split; [exact XC|].
  split; [rewrite F4; exact L1|]. split; [rewrite F5; exact L2|]. split; [rewrite F6; exact L3|]. split; [rewrite F7; exact L4|].
  split; [rewrite F8; exact L5|]. split; [rewrite F9; exact L6|]. split; [rewrite F10; exact L7|]. split; [rewrite F11; exact L8|].
  split; [intros c' NE; rewrite F2; exact (GCo c' NE)|]. split; [exact MU|]. split; [exact WM|].
  split; [rewrite F12, EE; apply init_cache_emb|].
  rewrite F13. destruct LL as [-> | ->]; [left; apply init_cache_exh_list| right; apply exh_clear_init_cache].
Qed.

Lemma dj_cons : forall (iv : Z * Z) W A k, (A + k <= fst iv \/ snd iv <= A) -> disjoint_from W A k -> disjoint_from (iv :: W) A k.
Proof. intros [lo hi] W A k H1 H2. cbn [disjoint_from fst snd] in *. split; assumption. Qed.

Section FalseKinds.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (sp XS c d0 cap0 d1 cap1 d2 cap2 : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis ARV : aresv_ok L RESV.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis SPLO : ATOP <= sp - XS.
Definition bufok (d cap : Z) : Prop := cap <= 0 \/ (d + cap <= ATOP /\ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true).
Hypotheses (B0 : bufok d0 cap0) (B1 : bufok d1 cap1) (B2 : bufok d2 cap2).
Notation RI := (aregion_info L c).
Definition Wn : list (Z * Z) :=
  ((sp - XS, sp) :: ic_W L 1 31) ++ [(RI, RI + 8); (RI + 68, RI + 69); (AEMB, AEMB + 56); nz d0 cap0; nz d1 cap1; nz d2 cap2].

Lemma nz_clear : forall d cap lo hi A n, bufok d cap -> pcov RESV lo hi -> lo < hi -> 0 <= lo -> lo <= A -> A + n <= hi ->
  A + n <= fst (nz d cap) \/ snd (nz d cap) <= A.
Proof.
  intros d cap lo hi A n B PC LH L0 HA HN. unfold nz. destruct (0 <? cap) eqn:Q; cbn [fst snd]; [| right; lia].
  apply Z.ltb_lt in Q. destruct B as [B|[_ AV]]; [lia|].
  unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (pcov_clear _ _ _ _ _ PC AV LH Q) as [X|X]; [right; lia| left; lia].
Qed.

Lemma Wn_obj : forall lo hi A k, pcov RESV lo hi -> lo < hi -> 0 <= lo -> hi <= ATOP -> lo <= A -> A + k <= hi ->
  disjoint_from (ic_W L 1 31) A k -> (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= AEMB \/ AEMB + 56 <= A) ->
  disjoint_from Wn A k.
Proof.
  intros lo hi A k PC LH L0 HT HA HK DIC R1 R2 EM. unfold Wn. apply dj_app.
  - cbn [disjoint_from]. split; [left; lia| exact DIC].
  - apply dj_cons; [exact R1|]. apply dj_cons; [exact R2|]. apply dj_cons; [exact EM|].
    apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B0 PC LH L0 HA HK)|]. apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B1 PC LH L0 HA HK)|].
    apply dj_cons; [exact (nz_clear _ _ _ _ _ _ B2 PC LH L0 HA HK)| exact I].
Qed.

Lemma fk_geo : RI = al_space_beg L + 137438953472 + c * 128
  /\ al_res L + 4096 <= al_space_beg L <= al_res L + 65536 /\ 0x10007fff8000 <= al_res L /\ al_res L + 137439023104 <= ATOP
  /\ al_res L + 137438957568 <= RI /\ RI + 128 <= al_res L + 137439023104.
Proof.
  pose proof (ao_space L ALO) as SB. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (_ & _ & RT & _).
  assert (E : RI = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold K_NUM_CLASSES in HC. split; [exact E|]. rewrite E. clear E. lia.
Qed.
Lemma ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k.
Proof. intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. Qed.
Lemma ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k.
Proof. intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. Qed.

Lemma K_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI -> (A + k <= AEMB \/ AEMB + 56 <= A) -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct ARV as (PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & _).
  pose proof (ao_t L ALO) as (_ & _ & _ & _ & TI). unfold iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  eapply (Wn_obj 0x10000 0x631000); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| exact Y4].
Qed.
Lemma K_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from (ic_W L 1 31) A k -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct ARV as (_ & _ & _ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & G6).
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_t_res L ALO) as D. unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *.
  eapply (Wn_obj (al_t L) (al_t L + 4096)); [exact PC| lia| lia| lia| lia| lia| exact Y4| lia| lia| unfold AEMB; lia].
Qed.
Lemma K_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3. destruct ARV as (_ & _ & _ & _ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & G6).
  pose proof (ao_ctx L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_ctx_res L ALO) as D. pose proof (ad_t_ctx L ALO) as D2.
  unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *.
  eapply (Wn_obj (al_ctx L) (al_ctx L + 65536)); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| unfold AEMB; lia].
Qed.
Lemma K_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3 Y4 Y5. destruct ARV as (_ & _ & PC & _). destruct fk_geo as (_ & _ & G3 & G4 & _).
  pose proof (ad_t_res L ALO) as D. unfold adisj, AEMB in *. fold (al_res L) in PC.
  eapply (Wn_obj (al_res L) (al_res L + 137439023104)); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| exact Y4| exact Y5| unfold AEMB; lia].
Qed.
Lemma K_sh : forall A k, 0x7fff7000 <= A -> 0 <= k -> A + k <= 0x10007fff8000 -> disjoint_from Wn A k.
Proof.
  intros A k Y1 Y2 Y3. destruct ARV as (_ & PC & _). destruct fk_geo as (_ & _ & G3 & _ & G5 & _).
  pose proof (ao_t L ALO) as (_ & _ & _ & TS & _). unfold sclr, KLS, AEMB in *. pose proof atop_range as AT.
  eapply (Wn_obj 0x7fff7000 0x10007fff8000); [exact PC| lia| lia| lia| lia| lia| apply ICW_far; lia| lia| lia| unfold AEMB; lia].
Qed.

Definition piece_ok (iv : Z * Z) : Prop :=
     ATOP <= fst iv
  \/ (al_t L + 288 <= fst iv /\ snd iv <= al_t L + 2768)
  \/ (RI <= fst iv /\ snd iv <= RI + 128)
  \/ (AEMB <= fst iv /\ snd iv <= AEMB + 56)
  \/ iv = (0, 0)
  \/ (0 < snd iv - fst iv /\ snd iv <= ATOP /\ avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true).
Lemma nz_piece : forall d cap, bufok d cap -> piece_ok (nz d cap).
Proof.
  intros d cap B. unfold nz, piece_ok. destruct (0 <? cap) eqn:Q; [| right; right; right; right; left; reflexivity].
  apply Z.ltb_lt in Q. destruct B as [B|[B1' B2']]; [lia|]. do 5 right. cbn [fst snd]. replace (d + cap - d) with cap by lia. repeat split; [lia| exact B1'| exact B2'].
Qed.
Lemma Wn_pieces : Forall piece_ok Wn.
Proof.
  unfold Wn. apply Forall_app. split.
  - constructor; [left; cbn [fst]; exact SPLO|]. eapply Forall_impl; [| apply (ic_W_in_t L 1 31); [lia| cbn; lia]].
    intros iv (I1 & I2 & _). right; left. split; assumption.
  - repeat (apply Forall_cons); try apply Forall_nil; try (apply nz_piece; assumption).
    + right; right; left. cbn [fst snd]. lia.
    + right; right; left. cbn [fst snd]. lia.
    + right; right; right; left. cbn [fst snd]. lia.
Qed.

Lemma Wn_buf : forall (iv : Z * Z) lo hi A n, pcov RESV lo hi -> lo < hi -> lo <= A -> A + n <= hi ->
  0 < snd iv - fst iv -> avoids_all (fst iv) (snd iv - fst iv) (RESV ++ flat_map sec_iv (achunks st)) = true -> snd iv <= A \/ A + n <= fst iv.
Proof.
  intros iv lo hi A n PC LH HA HN POS AV. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
  destruct (pcov_clear _ _ _ _ _ PC AV LH POS) as [Q|Q]; lia.
Qed.
Lemma Wn_quar : forall X,
  (forall b, In b (x_busy X) -> al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472) ->
  quar_untouched L X Wn.
Proof.
  intros X BB. unfold quar_untouched. eapply Forall_impl; [| exact Wn_pieces]. intros iv PK. unfold piece_ok in PK.
  destruct ARV as (PCI & _ & PCR & _ & PCT & _). fold (al_res L) in PCR.
  destruct fk_geo as (G1 & G2 & G3 & G4 & G5 & G6). pose proof HC as HC'. unfold K_NUM_CLASSES in HC'.
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ad_t_res L ALO) as D. unfold adisj, iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  unfold AINSTANCE, AEMB in *.
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  1-4: (split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|]; split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|];
        split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|]; split; [clear -K G2 G3 G4 G5 G6 T1 T2 TI D AT; lia|];
        intros b Hb; destruct (BB b Hb) as [Q1 Q2]; destruct (xb_st b); [exact I| clear -K G1 HC' G2 G3 G4 G5 G6 T1 T2 TI D AT Q1 Q2; lia| clear -K G1 HC' G2 G3 G4 G5 G6 T1 T2 TI D AT Q1 Q2; lia]).
  - subst iv. cbn [fst snd]. split; [clear -T1; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|].
    intros b Hb. destruct (BB b Hb) as [Q1 Q2]. destruct (xb_st b); [exact I| clear -Q1 G2 G3; lia| clear -Q1 G2 G3; lia].
  - pose proof (Wn_buf iv _ _ (al_t L + 80) 128 PCT ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q1.
    pose proof (Wn_buf iv _ _ (886296 + 728) 256 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q2.
    pose proof (Wn_buf iv _ _ 904832 528432 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q3.
    pose proof (Wn_buf iv _ _ 1488648 4 PCI ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) K1 K3) as Q4.
    split; [clear -Q1; lia|]. split; [clear -Q2; lia|]. split; [clear -Q3; lia|]. split; [clear -Q4; lia|].
    intros b Hb. destruct (BB b Hb) as [Q5 Q6].
    pose proof (Wn_buf iv _ _ (xb_alloc L b) (size_of_class (xb_class b)) PCR ltac:(clear; lia) ltac:(clear -Q5 G2; lia) ltac:(clear -Q6 G2; lia) K1 K3) as Q7.
    destruct (xb_st b); [exact I| exact Q7| exact Q7].
Qed.
Lemma Wn_sec : sec_untouchedD L RESV st Wn.
Proof.
  unfold sec_untouchedD. eapply Forall_impl; [| exact Wn_pieces]. intros iv PK. unfold piece_ok in PK.
  destruct fk_geo as (_ & G2 & G3 & G4 & G5 & G6).
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  - left. intros a Ha. unfold aknown. do 4 right. left. lia.
  - left. intros a Ha. unfold aknown. do 5 right. left. lia.
  - left. intros a Ha. unfold aknown. do 7 right. left. lia.
  - left. intros a Ha. unfold aknown. left. left. unfold AIMG_HI, AINSTANCE, AEMB in *. lia.
  - left. subst iv. cbn [fst snd]. intros a Ha. lia.
  - right. split; [exact K2| exact K3].
Qed.
Lemma Wn_depot : Forall (fun iv : Z * Z => forall a, fst iv <= a < snd iv ->
     ~ (0x1adb48 <= a < 0x5fdb90) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) Wn.
Proof.
  eapply Forall_impl; [| exact Wn_pieces]. intros iv PK a Ha. unfold piece_ok in PK.
  destruct ARV as (PCI & _ & _ & _ & _ & _ & PCN & PCS & _).
  destruct fk_geo as (_ & G2 & G3 & G4 & G5 & G6).
  pose proof (ao_t L ALO) as (_ & T1 & T2 & _ & TI). pose proof (ao_nodes L ALO) as NO. pose proof (ao_store L ALO) as SO.
  pose proof (aobj_img _ _ NO ltac:(lia)) as NI. pose proof (aobj_img _ _ SO ltac:(lia)) as SI. destruct NO as (_ & N1 & N2 & _). destruct SO as (_ & S1 & S2 & _).
  pose proof (ad_t_nodes L ALO) as D1. pose proof (ad_t_store L ALO) as D2. pose proof (ad_nodes_res L ALO) as D3. pose proof (ad_store_res L ALO) as D4.
  unfold adisj, iclr, AIMG_LO, AIMG_HI, AEMB in *. pose proof atop_range as AT.
  destruct PK as [K|[K|[K|[K|[K|(K1 & K2 & K3)]]]]].
  1-4: lia.
  - subst iv. cbn [fst snd] in Ha. lia.
  - pose proof (Wn_buf iv 0x10000 0x631000 0x10000 (0x631000 - 0x10000) PCI ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q1.
    pose proof (Wn_buf iv _ _ (al_nodes L) 1048576 PCN ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q2.
    pose proof (Wn_buf iv _ _ (al_store L) 8388608 PCS ltac:(lia) ltac:(lia) ltac:(lia) K1 K3) as Q3. lia.
Qed.
End FalseKinds.

Lemma achunks_init_cache : forall st, achunks (init_cache st) = achunks st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma max_count_ic : forall st c, max_count (init_cache st) c = max_cached c.
Proof. intros st c. unfold max_count. rewrite init_cache_cinit. reflexivity. Qed.
Lemma awf_init_cache : forall L st X, awf L st X -> awf L (init_cache st) X.
Proof.
  intros L st X WF. unfold init_cache. destruct (a_cinit st) eqn:CI; [exact WF|].
  destruct WF as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split; [| split; [exact OUTC|]; split; [exact BUSY|]; split; [exact LIVE|]; split; [exact FRESH| exact UNIQ]].
  intros c Hc. destruct (PERC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  cbv zeta in *. repeat (split; [assumption|]). split; [| split; [exact ND| exact RANGE]].
  unfold max_count in *. rewrite CI in CNTB. cbn [a_cinit set_cinit].
  pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in Hc; lia)) as [MR _]. change (get_cls (set_cinit true st) c) with (get_cls st c). lia.
Qed.
Lemma arng_init_cache : forall L RNG st, arng L RNG st -> arng L RNG (init_cache st).
Proof. intros L RNG st A. unfold init_cache. destruct (a_cinit st); [exact A|]. destruct st. exact A. Qed.
Lemma quar_same_ic : forall st X, quar_same st (init_cache st) X X.
Proof. intros st X. unfold init_cache. destruct (a_cinit st); destruct st; unfold quar_same; cbn; repeat split; try reflexivity; intros b Hb; destruct (xb_st b); auto. Qed.
Lemma sec_same_ic : forall st, sec_same st (init_cache st).
Proof. intros st. unfold init_cache. destruct (a_cinit st); [apply sec_same_refl|]. destruct st. unfold sec_same. cbn. repeat split; try reflexivity; try (intros Q; exact Q); try apply Permutation_refl. Qed.

Lemma refill_store_false : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  emb_cells st m -> emb_clr RESV st ->
  F_arefill.TwinB.F_arefill_x.refill_ret_false L RESV RNG sp st c lo (c_count (get_cls st c)) (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  AREP H L st2 X m' /\ arng L RNG' st2 /\ axflag L st2 m' c /\ axg RESV RNG' st2 m'.
Proof.
  intros L RESV RNG RNG' sp m m' st st2 X c lo ALO ARV ARNG AR HC NC CEIL LO EC ECL RR.
  destruct RR as (m1 & MU1 & XF & HDRc & HDRS).
  unfold xfalse_ret in XF. rewrite init_cache_emb in XF.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct XF as (FPLE & STEQ & EC2 & ER2 & XC2 & MTX' & FLG' & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI' & STK').
  unfold emb_prov in PV1, PV2. rewrite achunks_init_cache in PV1, PV2.
  set (st1 := init_cache st) in *.

  assert (B0 : bufok RESV st d0 cap0).
  { unfold bufok. unfold emb_cells in EC. rewrite EA in EC. unfold emb_clr in ECL. rewrite EA in ECL.
    destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
    destruct EC as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECL as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
  assert (B1 : bufok RESV st d1 cap1).
  { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
    right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
  assert (B2 : bufok RESV st d2 cap2).
  { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
    unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
    destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }
  assert (SPLO : ATOP <= bv_unsigned sp - REFILL_STACK_X) by (clear -CEIL LO; lia).
  set (W := Wn L (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2).
  assert (MUALL : munch W m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; subst W; unfold Wn; intros x Hx;
      apply outside_app in Hx; destruct Hx as [H1 H2]; [exact H1|].
    cbn [outside] in H1. destruct H1 as [H1 _]. apply outside_cons in H2 as [R1 H2]. apply outside_cons in H2 as [R2 H2]. apply outside_cons in H2 as [R3 H2]. cbn [fst snd] in R1, R2, R3.
    apply outside_cons in H2 as [N0 H2]. apply outside_cons in H2 as [N1 H2]. apply outside_cons in H2 as [N2 _].
    apply nz_outside in N0, N1, N2. cbn [outside]. repeat split; assumption. }
  pose proof (K_img L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kimg.
  pose proof (K_t L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kt.
  pose proof (K_ctx L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kctx.
  pose proof (K_res L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Kres.
  pose proof (K_sh L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2) as Ksh.
  fold W in Kimg, Kt, Kctx, Kres, Ksh.
  assert (Kt' : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from W A k)
    by (intros A k Y1 Y2 Y3 Y4; apply Kt; [exact Y1| exact Y2| exact Y3| apply ICW_t; exact Y4]).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6).
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11). fold st1 in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11.
  assert (GCI : forall j, get_cls st1 j = get_cls st j) by (intros j; subst st1; apply init_cache_cls).
  assert (NDI : forall j, ndist st1 j = ndist st j) by (intros j; unfold ndist; rewrite GCI; reflexivity).

  assert (RAL8 : al_res L mod 8 = 0) by (pose proof (ao_res L ALO) as (R8 & _); clear -R8; Z.div_mod_to_equations; lia).
  assert (RSH : 0x7fff7000 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= 0x10007fff8000).
  { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as AT. clear -G3 G4 AT. Z.div_mod_to_equations. lia. }
  destruct RSH as [SR1 SR3].
  assert (Kshres : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W A k)
    by (intros A k Y1 Y2 Y3; apply Ksh; [clear -Y1 SR1; lia| exact Y2| clear -Y3 SR3; lia]).
  assert (BB : forall b, In b (x_busy X) -> al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -P5 P4 Q1 Q2 CLB. lia. }
  assert (AR1 : AREPns H L st1 X m').
  { split; [apply awf_init_cache; exact WF|].
    split. { eapply arep_rt_frameD; [exact MUALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AEMB; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
    split. { eapply (ainstance_frameD L W m m' MUALL st st1); [exact INST| exact E8| exact E7| | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI, AEMB; lia. }
    split. { unfold athread.
             split; [eapply cells_frameD; [exact T0c| exact MUALL| apply Kt'; clear; cbn; lia]|].
             split; [eapply cells_frameD; [exact T40| exact MUALL| apply Kt'; clear; cbn; lia]|].
             split. { intros j Hj. destruct (CACHES j Hj) as [tail (REC & ARR & LEN)]. exists tail. unfold K_NUM_CLASSES in Hj.
                      split; [| split; [| exact LEN]].
                      - rewrite GCI. subst st1. rewrite max_count_ic, init_cache_cinit.
                        destruct (Z.eq_dec j c) as [->|NE]; [exact HDRc|]. exact (HDRS j ltac:(clear -Hj; lia) NE).
                      - eapply u32arr_frameD; [exact ARR| exact MUALL|]. rewrite length_app, length_map.
                        replace (4 * Z.of_nat (length (xc_cache (x_cls X j)) + length tail)) with 64 by (clear -LEN; lia).
                        apply Kt; [unfold acache_addr; clear -Hj; lia| clear; lia| unfold acache_addr; clear -Hj; lia| apply ic_W_disjoint_chunks]. }
             split; [eapply junk_frameD; [exact CSTATS| exact MUALL| intros _; apply Kt'; clear; lia]|].
             split; [exists sj; split; [eapply u64arr_frameD; [exact STATS| exact MUALL| rewrite LSJ; apply Kt'; clear; unfold ASTATS_WORDS; lia]| exact LSJ]|].
             eapply cells_frameD; [exact UNW| exact MUALL| apply Kt'; clear; cbn; lia]. }
    split.
    {
      intros c' Hc'. destruct (CLS c' Hc') as (REG & FARR & SLOTS & SHADOW).
      destruct (PERC c' Hc') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
      pose proof (size_of_class_facts c' Hc') as [QS QS16]. pose proof (aregion_mod L c' SAL) as RM. unfold K_NUM_CLASSES in Hc'.
      assert (RGc : al_res L <= aregion L c' /\ aregion L c' + K_REGION <= al_space_beg L + 137438953472
                   /\ al_space_beg L + 137438953472 <= aregion_info L c).
      { unfold aregion, K_REGION. change (2^32) with 4294967296. pose proof HC as HC'. unfold K_NUM_CLASSES in HC'. clear -Hc' G2 RIE HC'. lia. }
      destruct RGc as (RI1 & RI2 & RI3). unfold K_REGION in RI2. change (2^32) with 4294967296 in RI2.
      assert (Kreg : forall A k, aregion L c' <= A -> 0 <= k -> A + k <= aregion L c' + 4294967296 -> disjoint_from W A k).
      { intros A k Y1 Y2 Y3. apply Kres; [clear -Y1 RI1; lia| exact Y2| clear -Y3 RI2 RI3 G6; lia| left; clear -Y3 RI2 RI3; lia| left; clear -Y3 RI2 RI3; lia]. }
      assert (Kshreg : forall A k, shad (aregion L c') <= A -> 0 <= k -> A + k <= shad (aregion L c' + 4294967296) -> disjoint_from W A k).
      { intros A k Y1 Y2 Y3. apply Kshres; [pose proof (shad_mono _ _ RI1) as Q; clear -Y1 Q; lia| exact Y2|].
        assert (Q : shad (aregion L c' + 4294967296) <= shad (al_res L + 137439023104)) by (apply shad_mono; clear -RI2 RI3 G6; lia). clear -Y3 Q. lia. }
      split; [| split; [| split]].
      - destruct (Z.eq_dec c' c) as [->|NE].
        +
          destruct REG as (MTX16 & REGc & RJ4 & EXHc & RJ56). unfold aregion_cells. cbv zeta. rewrite GCI.
          assert (Kri : forall A k, aregion_info L c + 8 <= A -> 0 <= k -> A + k <= aregion_info L c + 128 ->
                          (A + k <= aregion_info L c + 68 \/ aregion_info L c + 69 <= A) -> disjoint_from W A k).
          { intros A k Y1 Y2 Y3 Y4. apply Kres; [clear -Y1 G5; lia| exact Y2| clear -Y3 G6; lia| right; clear -Y1; lia| exact Y4]. }
          pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
          eapply cells_frameD in M2b; [| exact MUALL| cbn [cells_size csize Nat.add]; apply Kri; clear; lia].
          split. { rw_join MTX' M2b M16. exact M16. }
          split; [eapply cells_frameD; [exact REGc| exact MUALL| cbn [cells_size csize Nat.add]; apply Kri; clear; lia]|].
          split; [eapply junk_frameD; [exact RJ4| exact MUALL| intros _; apply Kri; clear; lia]|].
          split; [unfold aflag_cell; replace (c =? K_BATCH_CLASS) with false by (symmetry; apply Z.eqb_neq; exact NC); exact (junk_of_cells m' _ _ FLG')|].
          eapply junk_frameD; [exact RJ56| exact MUALL| intros _; apply Kri; clear; lia].
        + eapply aregion_cells_frameD; [exact MUALL| exact REG| rewrite GCI; reflexivity| rewrite GCI; reflexivity| rewrite GCI; reflexivity| rewrite GCI; reflexivity|].
          apply Kres; [unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -Hc' G2; lia| clear; lia
                      | unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -Hc' G2; lia
                      | rewrite RIE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -NE; lia
                      | rewrite RIE; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; clear -NE; lia].
      - eapply afreearray_frameD; [exact MUALL| exact FARR| rewrite GCI; reflexivity| rewrite GCI; reflexivity| reflexivity| exact QLENF| exact Q5| | clear -Q6; lia|].
        + apply Kreg; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear; lia| clear -Q5 Q6; lia| clear -Q6; lia].
        + apply Kshreg; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear; lia| apply shlen_nonneg; clear -Q5 Q6; lia|].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -Q6. lia.
      - eapply (aslots_updateD L W m m' MUALL st st1 X X c' (-1)); [exact SLOTS| apply NDI| rewrite GCI; reflexivity| rewrite GCI; reflexivity| | | intros Hk; exfalso; clear -Hk; lia].
        + intros kq Hk _. pose proof (slot_in_region L st c' kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          split; [reflexivity|]. split.
          * apply Kreg; [exact P5| clear -QS; lia| clear -P4 Q1 Q2; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kreg; [clear -Q1; lia| clear -POS; lia| clear -Q1 Q2; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_updateD L W m m' MUALL st st1 X X c' (-1)); [exact SHADOW| apply NDI| rewrite GCI; reflexivity| rewrite GCI; reflexivity| | | intros Hk; exfalso; clear -Hk; lia| apply shlen_nonneg; clear -QS; lia].
        + intros kq Hk _. pose proof (slot_in_region L st c' kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
          pose proof (slot_aligned L c' kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc'; lia)) as AL.
          split; [reflexivity|]. apply Kshreg; [apply shad_mono; exact P5| apply shlen_nonneg; clear -QS; lia|].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kshreg; [apply shad_mono; clear -Q1; lia| clear -POS; lia|].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2. unfold K_FREEARR_OFF in *. lia. }

    split. { eapply (hqD H HLD L st st1 X X m m' W); [exact HQ| exact MUALL| | apply quar_same_ic].
             exact (Wn_quar L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2 X BB). }
    split. { eapply (hdD H HLD L m m' W); [exact HD| exact MUALL|].
             exact (Wn_depot L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO ARV HC SPLO B0 B1 B2). }

    split; [eapply (ARepFrameD.TwinB.arelro_frameD W m m' MUALL); [exact HRO| apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AEMB; lia]|].
    split; [eapply arep_rt2_frameD; [exact MUALL| exact RT2| | |]; apply Kimg; clear; unfold AIMG_HI, AEMB; lia|].
    split; [| eapply arep_rt3_frameD; [exact MUALL| exact RT3|]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AEMB; lia|]); apply Forall_nil].
    intros c' Hc'. destruct (PERC c' Hc') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc'.
    assert (RGc : al_res L <= aregion L c' /\ aregion L c' + 4294967296 <= al_res L + 137439023104).
    { unfold aregion, K_REGION. change (2^32) with 4294967296. clear -Hc' G2. lia. }
    destruct RGc as (RI1 & RI2). pose proof (aregion_mod L c' SAL) as RM.
    eapply (ashadow_avail_frameD L W m m' MUALL st st1); [exact (AVL c' ltac:(unfold K_NUM_CLASSES; clear -Hc'; lia))| rewrite GCI; reflexivity| rewrite GCI; reflexivity| |].
    - intros POS. apply Kshres; [apply shad_mono; clear -Q1 RI1; lia| clear -POS; lia|].
      rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF in *. clear -Q1 Q2 RI2. lia.
    - intros POS. apply Kshres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF in *; clear -Q5 Q6 RI1; lia| clear -POS; lia|].
      rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -Q5 Q6 RI2. lia. }

  assert (ST2 : exists l e, st2 = set_emb e (set_exh l st1) /\ exh_mem c st2 = true).
  { destruct STEQ as [[EM E]|[EM [e2 E]]].
    - exists (a_exh st1), (a_emb st1). split; [rewrite E; symmetry; apply set_x_eta| rewrite E; exact EM].
    - exists (c :: a_exh st1), e2. split; [exact E|]. rewrite E. unfold exh_mem, exh_set. destruct st1. cbn. rewrite Z.eqb_refl. reflexivity. }
  destruct ST2 as (l & e & ES & EM2).

  assert (ECL2 : emb_clr RESV st2).
  { unfold emb_clr. rewrite EA2.
    assert (ACH : achunks st2 = achunks st) by (rewrite ES; destruct st1 eqn:Q; cbn; rewrite <- (achunks_init_cache st); fold st1; rewrite Q; reflexivity).
    rewrite ACH. destruct B2 as [LE|[_ AV]]; [| right; exact AV].
    pose proof EC2 as EC2'. unfold emb_cells in EC2'. rewrite EA2 in EC2'. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; exact E0|].
    destruct EC2' as (_ & _ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -LE P2. lia. }
  assert (AXF2 : axflags L st2 m').
  { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [unfold axflag; rewrite EM2; exact FLG'|].
    pose proof (hx_get H HLD L st X m HS) as (_ & _ & AXFm & _). pose proof (AXFm c' Hc' NC') as F0. unfold axflag in *.
    assert (EXE : exh_mem c' st2 = exh_mem c' st).
    { assert (SE : forall e0 s, exh_mem c' (set_emb e0 s) = exh_mem c' s) by (intros e0 []; reflexivity).
      destruct STEQ as [[_ E]|[_ [e2 E]]]; rewrite E; [apply init_cache_exh|]. rewrite SE, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
    rewrite EXE. eapply cells_frameD; [exact F0| exact MUALL|]. cbn [cells_size csize Nat.add].
    destruct (fk_geo L c' ALO Hc') as (RIE' & _ & _ & _ & G5' & G6'). unfold K_NUM_CLASSES in *.
    apply Kres; [clear -G5'; lia| clear; lia| clear -G6'; lia| rewrite RIE, RIE'; clear -NE Hc' HC; lia| rewrite RIE, RIE'; clear -NE Hc' HC; lia]. }
  assert (AEX2 : AEXH L st2 m').
  { split; [exact XC2|]. split; [exact EC2|]. split; [exact AXF2|]. split; [exact (emb_clrK_of L RESV st2 m' ALO ARV EC2 ECL2)| exact (emb_clrS_of RESV st2 ECL2)]. }
  split.
  { apply AREP_split. split; [rewrite ES; apply AREPns_x_indep; exact AR1|].
    eapply (hsD H HLD L RESV st st2 X X m m' W ARV HS MUALL); [| | exact AEX2].
    - exact (Wn_sec L RESV st (bv_unsigned sp) REFILL_STACK_X c d0 cap0 d1 cap1 d2 cap2 ALO HC SPLO B0 B1 B2).
    - rewrite ES. apply sec_sameX_x. exact (sec_same_X _ _ (sec_same_ic st)). }
  split; [rewrite ES; apply arng_x_indep; apply (arng_mono L RNG RNG'); [exact FPLE| apply arng_init_cache; exact ARNG]|].
  split; [unfold axflag; rewrite EM2; exact FLG'|].
  unfold axg. split; [exact XC2|]. split; [exact EC2|]. split; [exact ER2| exact ECL2].
Qed.

Lemma exh_cells_frameK : forall m m' (W : list (Z * Z)), exh_cells m -> munch W m m' ->
  (forall A k, 0 <= k -> AIMG_LO <= A -> A + k <= AIMG_HI -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from W A k) -> exh_cells m'.
Proof.
  intros m m' W (RC & TN & CF & CB) MU K. destruct RC as (R1 & R2 & R3 & R4 & R5).
  assert (T : forall A cs, rw_cells bsegs m A cs -> (AIMG_LO <=? A) = true -> (A + Z.of_nat (cells_size cs) <=? AIMG_HI) = true ->
                ((A + Z.of_nat (cells_size cs) <=? AINSTANCE) || (AINSTANCE + 728 <=? A)) = true -> rw_cells bsegs m' A cs).
  { intros A cs Hc H1 H2 H3. eapply cells_frameD; [exact Hc| exact MU|]. apply K; [lia| apply Z.leb_le; exact H1| apply Z.leb_le; exact H2|].
    apply orb_prop in H3. destruct H3 as [H3|H3]; apply Z.leb_le in H3; [left| right]; exact H3. }
  split; [unfold rmap_cells; split; [| split; [| split; [| split]]]| split; [| split]]; (eapply T; [eassumption| reflexivity| reflexivity| reflexivity]).
Qed.

Section TrueKinds.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (c sp lo : Z).
Hypothesis ALO : alayout_ok L.
Hypothesis HC : 1 <= c < K_NUM_CLASSES.
Hypothesis CEIL : ATOP <= lo.
Hypothesis LO : lo <= sp - 1536.
Hypothesis MU0 : 0 <= c_mapped_user (get_cls st c).
Lemma tk_geo : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439019008 /\ aregion L c mod 8 = 0
  /\ 0x10007fff8000 <= al_res L /\ al_res L + 137439023104 <= ATOP /\ al_res L mod 8 = 0.
Proof.
  pose proof (ao_space L ALO) as SB. pose proof (ao_space_al L ALO) as SAL. pose proof (ao_res_hi L ALO) as RH. pose proof (ao_res L ALO) as (R8 & _ & RT & _).
  unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296. repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.
Lemma arefillW_img : forall A k, 0 <= k -> AIMG_LO <= A -> A + k <= AIMG_HI -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) ->
  disjoint_from (arefill_W L st c sp) A k.
Proof.
  intros A k Y1 Y2 Y3 Y4. destruct (fk_geo L c ALO HC) as (_ & _ & G3 & _ & G5 & _). destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (ao_t L ALO) as (_ & _ & _ & _ & TI). unfold iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  assert (SHL : 0x7fff8000 <= shad (aregion L c + c_mapped_user (get_cls st c))) by (rewrite shad_div; unfold ASHOFF; clear -T1 T4 MU0; Z.div_mod_to_equations; lia).
  cbn [disjoint_from]. repeat split; try exact I; clear -Y1 Y2 Y3 Y4 G3 G5 T1 T4 TI AT SHL CEIL LO MU0; lia.
Qed.

Lemma arefillW_flag : forall c', 1 <= c' < K_NUM_CLASSES -> c' <> c -> disjoint_from (arefill_W L st c sp) (aregion_info L c' + 68) 1.
Proof.
  intros c' Hc' NE. destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6). destruct (fk_geo L c' ALO Hc') as (RIE' & _ & _ & _ & G5' & G6').
  destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (ao_t L ALO) as (_ & _ & OT2 & _ & TI). pose proof (ad_t_res L ALO) as DTR. unfold adisj, iclr, AIMG_LO, AIMG_HI in *. pose proof atop_range as AT.
  assert (SHH : shad (aregion L c) + shlen K_REGION <= 0x10007fff8000).
  { rewrite shad_div, shlen_div. unfold ASHOFF, K_REGION in *. change (2^32) with 4294967296 in *. clear -T2 T5 AT. Z.div_mod_to_equations. lia. }
  unfold K_NUM_CLASSES, aregion, K_REGION, AINSTANCE in *. change (2^32) with 4294967296 in *.
  cbn [disjoint_from]. rewrite RIE, RIE'. repeat split; try exact I; clear -NE Hc' HC G2 G3 G4 G5' G6' T1 T2 T4 T5 OT2 TI DTR AT SHH CEIL LO MU0; lia.
Qed.
Lemma arefillW_buf : forall d cap, aresv_ok L RESV -> c_mapped_user (get_cls st c) <= K_REGION ->
  0 < cap -> AIMG_HI <= d -> d + cap <= ATOP -> avoids_all d cap RESV = true -> disjoint_from (arefill_W L st c sp) d cap.
Proof.
  intros d cap ARV MUK POS DI DT AV. destruct ARV as (_ & PCS & PCR & _ & PCT & _). fold (al_res L) in PCR.
  destruct (fk_geo L c ALO HC) as (_ & _ & G3 & _ & G5 & G6). destruct tk_geo as (T1 & T2 & T3 & T4 & T5 & T6).
  pose proof (pcov_clear _ _ _ _ _ PCT AV ltac:(lia) POS) as Q1. pose proof (pcov_clear _ _ _ _ _ PCR AV ltac:(lia) POS) as Q2.
  pose proof (pcov_clear _ _ _ _ _ PCS AV ltac:(lia) POS) as Q3.
  assert (SHB : 0x7fff7000 <= shad (aregion L c + c_mapped_user (get_cls st c)) /\ shad (aregion L c) + shlen K_REGION <= 0x10007fff8000).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION in *. change (2^32) with 4294967296 in *. pose proof atop_range as AT. clear -T1 T2 T3 T4 T5 MU0 AT. Z.div_mod_to_equations. lia. }
  destruct SHB as [SH1 SH2]. unfold AIMG_HI, AINSTANCE, K_REGION in *. change (2^32) with 4294967296 in *.
  cbn [disjoint_from]. repeat split; try exact I; clear -POS DI DT Q1 Q2 Q3 G5 G6 T1 T2 SH1 SH2 CEIL LO MU0 MUK; lia.
Qed.
End TrueKinds.

Lemma pcov_sub : forall RESV lo hi lo' hi', pcov RESV lo hi -> lo <= lo' -> hi' <= hi -> pcov RESV lo' hi'.
Proof. intros RESV lo hi lo' hi' PC H1 H2 x Hx. apply PC. lia. Qed.
Lemma rng_fp_le : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

Lemma refill_xf_of_false : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z)
    (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  emb_cells st m -> emb_clr RESV st ->
  F_arefill.TwinB.F_arefill_x.refill_ret_false L RESV RNG sp st c lo (c_count (get_cls st c)) (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  refill_ret_xf H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG'
    (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc ra) fc None m' (seg_rom bsegs)).
Proof.
  intros L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
         ALO ARV ARNG AR HC NC CEIL LO EC ECL RF.
  pose proof (refill_store_false L RESV RNG RNG' sp m m' st st2 X c lo ALO ARV ARNG AR HC NC CEIL LO EC ECL RF) as (AR2 & ARNG2 & AXF2 & AXG2).
  destruct RF as (m1 & MU1 & XF & _ & _). unfold xfalse_ret in XF. rewrite init_cache_emb in XF.
  unfold refill_ret_xf, aret_xf. cbv zeta.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
  destruct XF as (FPLE & STEQ & _ & _ & _ & _ & _ & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI' & STK').
  split; [exact FPLE|]. do 15 eexists. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
  split; [rewrite init_cache_exh in STEQ; exact STEQ|].
  split; [exact AR2|]. split; [exact ARNG2|]. split; [exact AXF2|]. split; [exact AXG2|].
  unfold emb_prov in PV1, PV2 |- *. rewrite achunks_init_cache in PV1, PV2.
  exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; intros x Hx; cbn [outside] in Hx |- *.
  - destruct Hx as (X1 & X2 & _). split; [clear -X1; lia|]. apply ic_W_outside; [unfold acache_addr; clear -X2; lia| clear; cbn; lia| clear; lia].
  - destruct Hx as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). split; [clear -X1; lia|]. repeat (split; [assumption|]). exact I.
Qed.

Lemma refill_xt_of_true : forall (L : alayout) (RESV : list (Z * Z)) (RNG RNG' : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z)
    (chunks0 : list word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
  alayout_ok L -> aresv_ok L RESV -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c <> K_BATCH_CLASS -> c_count (get_cls st c) = 0 -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK_X ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  axg RESV RNG st m ->
  F_arefill.TwinB.F_arefill_x.refill_ret_x L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', refill_ret_xt H L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG'
    (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F (ret_pc ra) fc None m' (seg_rom bsegs)).
Proof.
  intros L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo chunks0 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
         ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH AXG RR. cbv zeta.
  destruct AXG as (XC & EC & ER & ECL).
  assert (LO' : lo <= bv_unsigned sp - 1536) by (clear -LO; lia).
  pose proof AR as (_ & _ & _ & _ & _ & _ & HS0 & _).
  destruct (refill_store_x L RESV RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARV ARNG AR HC NC CNT0 CEIL LO' CH LCH RR)
    as (X' & ARI & ARNG' & CIN & CCNT & NPOS & XB & XCL & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM & EMB' & EXHL).
  destruct RR as (m1 & _ & _ & TR & _). unfold refill_tail_ret_x in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _ & _ & EXH' & _).
  set (st_r := put_cls c (cls_set_count (max_cached c / 2) (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_cached c / 2) (get_cls st2 c))) st2) in *.
  assert (EXM : exh_mem c st_r = exh_mem c st2) by reflexivity.
  destruct AR as (WF & _). destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC c HC) as (A1 & A2 & _).

  assert (MU0 : 0 <= c_mapped_user (get_cls st c)) by (clear -A1; lia).
  assert (MUK : c_mapped_user (get_cls st c) <= K_REGION) by (unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; clear -A2; lia).
  pose proof (arefillW_img L st c (bv_unsigned sp) lo ALO HC CEIL LO' MU0) as KI.
  assert (AXFc : axflag L st_r m' c) by (unfold axflag; rewrite EXM; exact EXH').
  assert (XC' : exh_cells m') by (eapply exh_cells_frameK; [exact XC| exact MU| exact KI]).
  assert (EC' : emb_cells st_r m').
  { assert (EC0 : emb_cells st m').
    { destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
      eapply emb_cells_frameD; [exact EC| exact MU| apply KI; clear; unfold AEMB, AIMG_LO, AIMG_HI, AINSTANCE; lia|]. rewrite EA.
      destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; exact E0| right].
      pose proof EC as EC1. unfold emb_cells in EC1. rewrite EA in EC1. replace (cap0 =? 0) with false in EC1 by (symmetry; apply Z.eqb_neq; exact NZ).
      destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _).
      unfold emb_clr in ECL. rewrite EA in ECL. destruct ECL as [QQ|AV]; [exfalso; exact (NZ QQ)|].
      unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
      apply (arefillW_buf L RESV st c (bv_unsigned sp) lo ALO HC CEIL LO' MU0 d0 cap0 ARV MUK); [unfold EMB_INIT in P2; clear -P2; lia| exact P5| exact P6| exact AV]. }
    unfold emb_cells in EC0 |- *. rewrite EMB'. exact EC0. }
  assert (ECL' : emb_clr RESV st_r).
  { unfold emb_clr in ECL |- *. rewrite EMB'. assert (ACH : achunks st_r = achunks st) by (unfold achunks; rewrite L1, L3, L5; reflexivity). rewrite ACH. exact ECL. }
  assert (AXFS' : axflags L st_r m').
  { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFc|].
    pose proof (hx_get H HLD L st X m HS0) as (_ & _ & AXFm & _). pose proof (AXFm c' Hc' NC') as F0. unfold axflag in *.
    assert (EXE : exh_mem c' st_r = exh_mem c' st).
    { destruct EXHL as [E|E]; [apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); apply exh_mem_clear_other; exact NE]. }
    rewrite EXE. eapply cells_frameD; [exact F0| exact MU|]. cbn [cells_size csize Nat.add].
    eapply arefillW_flag; first [exact ALO| exact HC| exact CEIL| exact LO'| exact MU0| exact Hc'| exact NE]. }
  assert (AR' : AREP H L st_r X' m').
  { apply ARI. split; [exact XC'|]. split; [exact EC'|]. split; [exact AXFS'|]. split; [exact (emb_clrK_of L RESV st_r m' ALO ARV EC' ECL')| exact (emb_clrS_of RESV st_r ECL')]. }
  exists X'. unfold refill_ret_xt. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|].
  split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XCL|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  split; [exact GC|]. split; [exact EMB'|]. split; [exact EXHL|].
  split; [exact AXFc|].
  unfold axg. split; [exact XC'|]. split; [exact EC'|].
  split; [unfold emb_rng in ER |- *; rewrite EMB'; destruct (a_emb st) as [[d0 cap0] sz0]; destruct ER as [QQ|QQ]; [left; exact QQ| right; exact (rng_fp_le _ _ _ _ FPLE QQ)]|].
  exact ECL'.
Qed.

Theorem arefill_x : refill_stmt_x H.
Proof.
  unfold refill_stmt_x.
  intros R RESV k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC NC CNT0 RSTK EXHW ARV SP63 FC AXF AXG CAPB KF KT.
  pose proof AXG as AXG0. destruct AXG as (XC & EC & ER & ECL).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & _ & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }

  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
  destruct (fk_geo L c ALO HC) as (RIE & G2 & G3 & G4 & G5 & G6).
  pose proof ARV as ARV0. destruct ARV0 as (_ & _ & PCR & _ & PCT & _). fold (al_res L) in PCR.
  assert (PCRI : pcov RESV (aregion_info L c) (aregion_info L c + 128)) by (eapply pcov_sub; [exact PCR| clear -G5; lia| clear -G6; lia]).
  assert (CAPZ : cap0 <= 0 -> cap0 = 0).
  { intros LE. unfold emb_cells in EC. rewrite EA in EC. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [exact E0|].
    destruct EC as (_ & _ & _ & _ & P2 & _). unfold EMB_INIT in P2. clear -LE P2. lia. }
  assert (CLRI : cap0 = 0 \/ aregion_info L c + 128 <= d0 \/ d0 + cap0 <= aregion_info L c).
  { destruct (emb_clr_pcov RESV st d0 cap0 sz0 _ _ ECL EA PCRI ltac:(clear; lia)) as [QQ|[QQ|QQ]]; [left; exact (CAPZ QQ)| right; right; exact QQ| right; left; exact QQ]. }
  assert (CLT : cap0 = 0 \/ al_t L + 4096 <= d0 \/ d0 + cap0 <= al_t L).
  { destruct (emb_clr_pcov RESV st d0 cap0 sz0 _ _ ECL EA PCT ltac:(clear; lia)) as [QQ|[QQ|QQ]]; [left; exact (CAPZ QQ)| right; right; exact QQ| right; left; exact QQ]. }
  assert (LO' : lo <= bv_unsigned sp - 1536) by (clear -LO; lia).
  eapply refill_spec_x with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                            (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail) (RESV := RESV);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- context [a_emb st] => rewrite EA; first [exact CAPB | exact CLRI | exact CLT]
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ARV
       | |- arelro _ => exact HRO
       | |- exh_cells _ => exact XC
       | |- emb_cells _ _ => exact EC
       | |- emb_rng _ _ => exact ER
       | |- pcov _ (aregion_info _ _) _ => exact PCRI
       | |- pcov _ (al_t _) _ => exact PCT
       | |- bv_unsigned _ < 2 ^ 63 => exact SP63
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ <> K_BATCH_CLASS => exact NC
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact AXF
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.
  -
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RF.
    eapply KF. eapply refill_xf_of_false; [exact ALO| exact ARV| exact ARNG| exact AR| exact HC| exact NC| exact CEIL| exact LO| exact EC| exact ECL| exact RF].
  -
    intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
    destruct (refill_xt_of_true L RESV RNG RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' st st2 X c lo tail
                t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ALO ARV ARNG AR HC NC CNT0 CEIL LO CH LCH AXG0 RR) as [X' RT'].
    unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2). eapply KT. exact RT'.
Qed.

End RefillPX.
End CANSECX.
End TwinB.
