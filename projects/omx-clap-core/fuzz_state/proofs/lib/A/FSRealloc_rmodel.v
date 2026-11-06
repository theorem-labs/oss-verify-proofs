(* fuzz_state realloc thin: the IMAGE-FREE part of the instance of a Theorem Labs lane's realloc composition (lib/Reusable/RGtop.v,
   c5: a working branch 2bd8ae006ef): the universe [FS_Un], the trace premises [FS_U] (Allocate's / Deallocate's)
   and [FS_rU] (realloc's entry), the premises [FS_rpre] / [FS_rpreA] / [FS_rpreD], and the model obligation
   [fs_rmodel_ok] (cgif_rgb YG0f.v:23-28, 113-140 ported to fs's kit).  Moved out of lib/A/FSRealloc_inst.v (a Theorem Labs lane
   L13-RtB, 2026-10-29) so that image B's instance lib/B/FSRealloc_inst.v and image A's lib/A/FSRealloc_inst.v share one
   text.

   The trace premises (a Theorem Labs lane decision (B), 2026-10-29; FSupoisonRealloc.v @ fda61055856):
   - [FS_U tr S] = `In tr Un \/ st_nev S < EV_MAX`, fs's standard C5 form (YG0d.amalloc_realizes, FSupoisonU's
     amalloc_realizesU / afree_realizesU), taken by the Allocate call at S1 (one event after realloc's entry) and the
     Deallocate call at S2 (two events after it);
   - [FS_rU tr S] = `In tr Un \/ (length tr <= kUnwindMax /\ st_nev S + 2 < EV_MAX)`: realloc's entry premise; the
     length is call_trace_len's (YG0d.v:226), so FSupoisonRealloc.arealloc_realizesU's premise
     `In (call_trace ..) Un \/ st_nev S + 2 < EV_MAX` gives it ([fs_rU_call]).
   [fs_rmodel_ok] transports [FS_rU] at S to [FS_U] at S1 and S2 and to malloc_gen's tr_admit (YG01.v:148) at S1.

   This file names no image and no image address: it Requires only lib/Reusable files and the image-free realloc model
   lib/A/FSH_ReallocModelG.v.  It does not Require lib/A/FSH_ReallocModel.v (that file holds image A's realloc entry
   pcs).  The two model definitions it needs, [realloc_s1] (cgif_rgb YG0f.v:34) and [aregime3] (cgif_rgb
   YG0f.v:110-111), are FSH_ReallocModelG's; it exports those two names, which the instances and the top files use.

   No Axiom, no Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG03 YG06 YG07 YG08 YG0k YG0l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
(* fs's realloc model, the two definitions this file needs (cgif_rgb YG0f.v:34 and :110-111) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Export FSH_ReallocModelG(realloc_s1, aregime3).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image-free instance values (RGtop.v Section b): U, rU, rpre, rpreA, rpreD.                                    *)

(* the universe AR's Wf and fs's malloc / free contracts use *)
Definition FS_Un : list (list Z) := as_universe B.
(* Allocate's / Deallocate's trace premise (RGtop's U): fs's C5 form *)
Definition FS_U (tr : list Z) (S : astate) : Prop := In tr FS_Un \/ st_nev S < EV_MAX.
(* realloc's entry premise (RGtop's rU): room for realloc's entry event and its inner malloc's event before the
   Deallocate call *)
Definition FS_rU (tr : list Z) (S : astate) : Prop :=
  In tr FS_Un \/ ((length tr <= kUnwindMax)%nat /\ st_nev S + 2 < EV_MAX).
(* realloc's premise: FSH_ReallocModel.arealloc_realizes_all's acall_pre (whose AR gives Wf and which carries qmeter)
   and aregime3 *)
Definition FS_rpre (S : astate) (n : Z) : Prop := Wf FS_Un S /\ qmeter S /\ aregime3 S n.
(* Allocate's premise (= AllocGcgif.rpre_cgif, model-level) *)
Definition FS_rpreA (S : astate) (n : Z) : Prop := aregime S /\ qmeter S.
(* Deallocate's premise (= DeallocGcgif.rpre_dealloc_cgif) *)
Definition FS_rpreD (S : astate) (n : Z) : Prop := aregime S /\ qmeter S /\ st_internal_inited S = true.

(* the transports of the trace premises (realloc_s1 ticks st_nev once, malloc once more) *)
Lemma fs_rU_call : forall ly pc0 regs ch S,
  In (call_trace ly pc0 regs ch) FS_Un \/ st_nev S + 2 < EV_MAX -> FS_rU (call_trace ly pc0 regs ch) S.
Proof. intros ly pc0 regs ch S [H|H]; [left; exact H | right; split; [apply call_trace_len | exact H]]. Qed.
Lemma fs_rU_s1 : forall tr S, FS_rU tr S -> FS_U tr (realloc_s1 S).
Proof. intros tr S [H|(_ & H)]; [left; exact H | right; unfold realloc_s1; cbn [st_nev set_nev set_internal_inited]; lia]. Qed.
Lemma fs_rU_admit : forall tr S, FS_rU tr S -> tr_admit FS_Un (realloc_s1 S) tr.
Proof.
intros tr S [H|(L & H)]; [left; exact H|]. right. split; [exact L|].
unfold realloc_s1; cbn [st_nev set_nev set_internal_inited]; lia.
Qed.
Lemma fs_rU_s2 : forall tr S S2, FS_rU tr S -> st_nev S2 = st_nev (realloc_s1 S) + 1 -> FS_U tr S2.
Proof.
intros tr S S2 [H|(_ & H)] E; [left; exact H | right]. rewrite E. unfold realloc_s1; cbn [st_nev set_nev set_internal_inited]; lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* rmodel_ok: the model obligations, over fs's malloc / free (cgif_rgb YG0f.v:23-28, 113-140 ported to fs's kit).   *)

Lemma fs_free_null : forall tr s, YG00.free PNull tr s = IRet (tt, realloc_s1 s).
Proof.
intros tr s. unfold YG00.free, realloc_s1. cbn [YG00.bind YG00.ret YG00.tick YG00.modify ibind YG00.get YG00.put].
destruct (st_internal_inited (set_nev (st_nev s + 1) s)) eqn:E; cbn [YG00.ret YG00.modify ibind]; [|reflexivity].
f_equal. f_equal. destruct s; cbn in E |- *. subst. reflexivity.
Qed.

Lemma fs_aregime3_s0 : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> aregime s.
Proof.
intros U s n W Hn [H|(BI & QT & Bd)]; [left; lia|]. apply (aregime_intro U s W BI QT).
pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn). eapply bud_ok_mono; [exact Bd | lia | lia | lia | lia].
Qed.

Lemma fs_realloc_s1_wf : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> Wf U (realloc_s1 s).
Proof.
intros U s n W Hn R. unfold realloc_s1. apply (YG06.WfP_weaken U 1 1 1); try lia. apply YG03.WfP_set_internal_inited.
apply YG02.WfP_tick; [exact W | exact (fs_aregime3_s0 U s n W Hn R)].
Qed.

Lemma fs_aregime3_s1 : forall U s n, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> aregime (realloc_s1 s).
Proof.
intros U s n W Hn R. pose proof (fs_realloc_s1_wf U s n W Hn R) as W1. destruct R as [H|(BI & QT & (B1 & B2 & B3 & B4))].
- left. unfold realloc_s1. cbn [st_nev set_nev set_internal_inited]. lia.
- apply (aregime_intro U _ W1); [exact BI | exact (qtight_ext s _ eq_refl eq_refl eq_refl QT) |].
  pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn).
  unfold bud_ok, nrec, wpot, sec_hulls, realloc_s1 in *. cbn [st_nev st_chunks st_secs set_nev set_internal_inited]. lia.
Qed.

Lemma fs_aregime3_s2 : forall U s n s2, Wf U s -> 0 <= n < MALLOC_MAX -> aregime3 s n -> qtight s ->
  Wf U s2 -> st_nev s2 = st_nev (realloc_s1 s) + 1 -> (qtight (realloc_s1 s) -> qtight s2) ->
  (BigInv (realloc_s1 s) -> BigInv s2) -> mgrow (realloc_s1 s) n s2 -> aregime s2.
Proof.
intros U s n s2 W Hn R QT W2 NE QT2 BG G.
destruct R as [H|(BI & _ & (B1 & B2 & B3 & B4))].
- left. rewrite NE. unfold realloc_s1. cbn [st_nev set_nev set_internal_inited]. lia.
- apply (aregime_intro U s2 W2 (BG BI) (QT2 (qtight_ext s _ eq_refl eq_refl eq_refl QT))).
  pose proof (bud_malloc _ n s2 ltac:(lia) G NE) as (C1 & C2 & C3 & C4).
  pose proof (wcost_range n ltac:(lia)). pose proof (hcost_range n Hn).
  unfold bud_ok, bud_le, nrec, wpot, sec_hulls, realloc_s1 in *.
  cbn [st_nev st_chunks st_secs set_nev set_internal_inited] in *. lia.
Qed.

(* malloc never writes st_internal_inited (only free's entry step does): along every path of the malloc tree the
   flag is the entry state's.  The proof follows YG0k.v's frame lemmas (ensure_free_array_frame .. malloc_sec_sameq). *)
Definition IK (s s' : astate) : Prop := st_internal_inited s' = st_internal_inited s.
Lemma IK_trans : forall s1 s2 s3, IK s1 s2 -> IK s2 s3 -> IK s1 s3.
Proof. unfold IK. intros s1 s2 s3 H1 H2. rewrite H2. exact H1. Qed.

Lemma ik_efa : forall c need b s, apost (ensure_free_array c need b s) (fun r => IK s (snd r)).
Proof.
intros c need b s. unfold ensure_free_array.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; reflexivity|].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _.
- apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. reflexivity.
- apply apost_bind.
  apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd];
  (apply apost_if; intros _; [apply apost_spin | apply apost_ret]); reflexivity.
Qed.

Lemma ik_mmu : forall c need s, apost (map_more_user c need s) (fun r => IK s (snd r)).
Proof.
intros c need s. unfold map_more_user.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [|apply apost_ret; reflexivity].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _.
- apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. reflexivity.
- apply apost_bind. apply apost_if; intros _; [apply apost_set_region | apply apost_ret]; cbn [fst snd]; apply apost_ret;
  reflexivity.
Qed.

Lemma ik_populate : forall c need s, apost (populate c need s) (fun r => IK s (snd r)).
Proof.
intros c need s. unfold populate.
apply apost_bind. eapply apost_mono; [|apply ik_mmu]. intros [ok s1] F1. cbn [fst snd] in *.
apply apost_if; intros _; [apply apost_ret; exact F1|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind. eapply apost_mono; [|apply ik_efa]. intros [ok2 s2] F2. cbn [fst snd] in *.
apply apost_if; intros _; [apply apost_ret; exact (IK_trans _ _ _ F1 F2)|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. exact (IK_trans _ _ _ F1 F2).
Qed.

Lemma ik_gfa : forall c n s, apost (get_from_allocator c n s) (fun r => IK s (snd r)).
Proof.
intros c n s. unfold get_from_allocator.
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_bind.
match goal with |- apost (?m ?sx) _ => assert (P : apost (m sx) (fun r => IK s (snd r))) end.
{ apply apost_if; intros _; [apply ik_populate | apply apost_ret; reflexivity]. }
eapply apost_mono; [|exact P]. intros [ok s1] F1. cbn [fst snd] in *.
apply apost_if; intros _; [apply apost_ret; exact F1|].
apply apost_bind. apply apost_get_region. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; exact F1|].
destruct (fa_pop_n _ _ _ _ _) as [[tops rest]|]; [|apply apost_fail].
apply apost_bind. apply apost_set_region. cbn [fst snd]. apply apost_ret. exact F1.
Qed.

Lemma ik_cache_alloc : forall c s, apost (cache_alloc c s) (fun r => IK s (snd r)).
Proof.
intros c s. unfold cache_alloc, init_cache_if_needed, refill_if_empty.
apply apost_bind. apply apost_bind. apply apost_get. cbn [fst snd].
match goal with |- apost (?m ?sx) _ => assert (I : apost (m sx) (fun r => IK s (snd r))) end.
{ apply apost_if; intros _; [apply apost_ret; reflexivity | apply apost_put; reflexivity]. }
eapply apost_mono; [|exact I]. intros [[] s1] F1. cbn [fst snd] in *.
apply apost_bind. apply apost_bind. apply apost_get_pc. cbn [fst snd].
match goal with |- apost (?m ?sx) _ => assert (R : apost (m sx) (fun r => IK s (snd r))) end.
{ destruct (pc_chunks (cache s1 c)).
  - apply apost_bind. eapply apost_mono; [|apply ik_gfa]. intros [got s2] F2. cbn [fst snd] in *.
    destruct got as [tops|]; [apply apost_set_pc | apply apost_ret]; cbn [snd]; exact (IK_trans _ _ _ F1 F2).
  - apply apost_ret. exact F1. }
eapply apost_mono; [|exact R]. intros [[] s2] F2. cbn [fst snd] in *.
apply apost_bind. apply apost_get_pc. cbn [fst snd].
destruct (pc_chunks (cache s2 c)); [apply apost_ret; exact F2|].
apply apost_bind. apply apost_set_pc. cbn [fst snd]. apply apost_ret. exact F2.
Qed.

Lemma ik_sec_alloc : forall n s, apost (sec_alloc n s) (fun r => IK s (snd r)).
Proof.
intros n s. unfold sec_alloc.
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; reflexivity|].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_put. cbn [fst snd].
apply apost_bind.
match goal with |- apost (?m ?sx) _ => assert (X : apost (m sx) (fun r => IK s (snd r))) end.
{ apply apost_if; intros _.
  - apply apost_bind. apply apost_askz. intros z2 _. cbn [fst snd].
    apply apost_if; intros _; [apply apost_modify; reflexivity | apply apost_spin].
  - apply apost_ret. reflexivity. }
eapply apost_mono; [|exact X]. intros [[] s3] H3. cbn [fst snd] in *.
apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret. exact H3.
Qed.

Lemma ik_depot_put : forall trc s, apost (depot_put trc s) (fun r => IK s (snd r)).
Proof.
intros trc s. unfold depot_put.
apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
apply apost_if; intros _; [apply apost_ret; reflexivity|].
apply apost_bind. apply apost_get. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_put. reflexivity.
Qed.

Lemma ik_malloc : forall n trc S, apost (YG00.malloc n trc S) (fun r => IK S (snd r)).
Proof.
intros n trc S. unfold YG00.malloc.
apply apost_bind. apply apost_tick. cbn [fst snd].
apply apost_bind. apply apost_mcheck. intros _. cbn [fst snd].
apply apost_bind.
match goal with |- apost (?m ?sx) _ => assert (OB : apost (m sx) (fun r => IK S (snd r))) end.
{ apply apost_if; intros _.
  - apply apost_bind. eapply apost_mono; [|apply ik_cache_alloc]. intros [o s1] F1. cbn [fst snd] in *.
    apply apost_ret. exact F1.
  - eapply apost_mono; [|apply ik_sec_alloc]. intros [ob s1] F1. exact F1. }
eapply apost_mono; [|exact OB]. intros [ob s1] H1. cbn [fst snd] in *.
destruct ob as [beg|]; [|apply apost_ret; exact H1].
apply apost_bind. eapply apost_mono; [|apply ik_depot_put]. intros [[] s2] H2. cbn [fst snd] in *.
apply apost_bind.
match goal with |- apost (?m ?sx) _ => assert (X : apost (m sx) (fun r => IK S (snd r))) end.
{ apply apost_if; intros _.
  - apply apost_bind. apply apost_askz. intros z _. cbn [fst snd].
    apply apost_if; intros _; [apply apost_ret | apply apost_spin]. exact (IK_trans _ _ _ H1 H2).
  - apply apost_ret. exact (IK_trans _ _ _ H1 H2). }
eapply apost_mono; [|exact X]. intros [[] s3] H3. cbn [fst snd] in *.
apply apost_bind. apply apost_modify. cbn [fst snd]. apply apost_ret. exact H3.
Qed.

Theorem fs_rmodel_ok : universe_ok FS_Un ->
  rmodel_ok FS_U YG00.malloc YG00.free (aowned B) FS_rpre MALLOC_MAX LIVE_MAX FS_rU FS_rpreA FS_rpreD.
Proof.
intros HU. split.
- intros S n tr trc S1 (W0 & QM & R3) Hn Hl Htr Hp _.
  rewrite fs_free_null in Hp. destruct trc as [|e trc']; cbn [apath] in Hp; [|destruct Hp].
  injection Hp as E1. subst S1.
  assert (Hn' : 0 <= n < MALLOC_MAX) by lia.
  pose proof (fs_realloc_s1_wf FS_Un S n W0 Hn' R3) as W1. pose proof (fs_aregime3_s1 FS_Un S n W0 Hn' R3) as R1.
  pose proof (qtight_ext S (realloc_s1 S) eq_refl eq_refl eq_refl (qmeter_tight S QM)) as QT1.
  split; [exact (fs_rU_s1 tr S Htr)|].
  split; [split; [exact R1 | split; [exact QT1 | exact (mroom_of_regime _ _ W1 (aregime_to_mid _ R1) (qtight_qloose _ QT1))]]|].
  split; [exact Hl|]. split; [reflexivity|]. split; [exact (Nat.le_refl _)|].
  intros ly a Ha. exact Ha.
- intros S n tr trc1 S1 trc2 q S2 (W0 & QM & R3) Hn Hl Htr Hp1 _ Hp2 _.
  rewrite fs_free_null in Hp1. destruct trc1 as [|e trc']; cbn [apath] in Hp1; [|destruct Hp1].
  injection Hp1 as E1. subst S1.
  assert (Hn' : 0 <= n < MALLOC_MAX) by lia.
  pose proof (fs_realloc_s1_wf FS_Un S n W0 Hn' R3) as W1. pose proof (fs_aregime3_s1 FS_Un S n W0 Hn' R3) as R1.
  pose proof (qtight_ext S (realloc_s1 S) eq_refl eq_refl eq_refl (qmeter_tight S QM)) as QT1.
  (* malloc_gen takes tr_admit (YG01.v:148) at the inner malloc's entry state realloc_s1 S *)
  pose proof (malloc_gen FS_Un (realloc_s1 S) n tr HU W1 (aregime_ok _ R1) ltac:(lia) Hl (fs_rU_admit tr S Htr)) as AT.
  destruct (atok_apath _ _ _ _ _ AT Hp2) as (ns & MP & BG & MG). cbn [snd] in BG, MG.
  destruct MP as (W2 & NE & _ & _ & BL & QTI).
  pose proof (apost_apath _ _ _ _ (ik_malloc n tr (realloc_s1 S)) Hp2) as INI. unfold IK in INI. cbn [snd] in INI.
  pose proof (QTI QT1) as QT2.
  pose proof (fs_aregime3_s2 FS_Un S n S2 W0 Hn' R3 (qmeter_tight S QM) W2 NE QTI BG MG) as R2.
  pose proof (conj QT2 (mroom_of_regime _ _ W2 (aregime_to_mid _ R2) (qtight_qloose _ QT2)) : qmeter S2) as QM2.
  assert (BLK : (q = PNull /\ blocks S2 = blocks S) \/
                (q <> PNull /\ blocks S2 = blocks S ++ [(q, n)] /\ ~ In q (map fst (blocks S)))).
  { destruct q as [|o|r o|c o]; [left; split; [reflexivity | exact BL] | right; split; [discriminate | exact BL] ..]. }
  split; [intros _; exact (fs_rU_s2 tr S S2 Htr NE)|].
  split.
  + intros HQ. destruct BLK as [(E & _) | (_ & E & _)]; [exfalso; exact (HQ E)|].
    rewrite E. apply in_or_app. right. left. reflexivity.
  + intros p n_old Hin. split.
    { destruct BLK as [(_ & E) | (_ & E & _)]; rewrite E; [exact Hin | apply in_or_app; left; exact Hin]. }
    split; [intros _; exact (conj R2 (conj QM2 INI))|].
    intros HQ Eqp. destruct BLK as [(E & _) | (_ & _ & NI)]; [exfalso; exact (HQ E)|].
    apply NI. rewrite Eqp. exact (in_map fst _ (p, n_old) Hin).
Qed.

End r.
