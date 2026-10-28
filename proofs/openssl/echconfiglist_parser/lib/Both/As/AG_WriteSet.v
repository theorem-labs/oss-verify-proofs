(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsDepotInv.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition astatw (a : Z) : Prop :=
    AINST + 112 <= a < AINST + 920 \/ 0x77c7c8 <= a < 0xb8c7f0 \/ AIAINIT <= a < AIAINIT + 4 \/ AIAINST <= a < AIAINST + 0x81030.
  (* [comment removed for export] *)
  Definition awrit (s s' : ast) (d : depot) (lo SP a : Z) : Prop :=
       lo <= a < SP
    \/ a_thr s + 64 <= a < a_thr s + kPageSize
    \/ a_sb s <= a < a_sb s + kSpaceSize + kPageSize
    \/ sh (a_sb s) <= a < sh (a_sb s + kSpaceSize + kPageSize)
    \/ a_pa s <= a < a_pa s + kPtrArrayReserve
    \/ (exists sc, (In sc (as_sec (a_st s)) \/ In sc (as_sec (a_st s')))
          /\ (sc_map_beg sc <= a < sc_map_beg sc + sc_map_size sc \/ sh (sc_map_beg sc) <= a < sh (sc_map_beg sc) + sc_map_size sc / 8))
    \/ astatw a
    \/ d_nb d <= a < d_nb d + 16 * 65536 \/ d_sb d <= a < d_sb d + 8 * 131072.

  Definition acompl (s s' : ast) (d : depot) (lo SP : Z) (m m' : mem) : Prop :=
    forall a, 0 <= a < 2 ^ 64 -> ~ awrit s s' d lo SP a -> m' (wa a) = m (wa a).

  (* [comment removed for export] *)
  Definition avmx (s s' : ast) (mo mo' : Model) : Prop :=
    forall x : word, in_rangesb x (vm_maps (m_vmmaps mo)) = true ->
         (in_rangesb x (vm_maps (m_vmmaps mo')) = true
          \/ exists sc, In sc (as_sec (a_st s)) /\ ~ In sc (as_sec (a_st s')) /\ sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc)
      /\ forall sc, In sc (as_sec (a_st s')) -> ~ In sc (as_sec (a_st s)) -> ~ (sc_map_beg sc <= bv_unsigned x < sc_map_beg sc + sc_map_size sc).

  (* [comment removed for export] *)
  Lemma acompl_of_munch : forall s s' d lo SP W m m',
    munch W m m' -> (forall iv a, In iv W -> fst iv <= a < snd iv -> awrit s s' d lo SP a) -> acompl s s' d lo SP m m'.
  Proof.
    intros s s' d lo SP W m m' MU SUB a Ha NW. pose proof (MU (wa a)) as E. rewrite wa_unsigned in E by exact Ha. apply E. clear E MU.
    induction W as [|[x y] W IH]; [exact I|]. cbn. split.
    - intros R. apply NW. apply (SUB (x, y) a); [left; reflexivity| exact R].
    - apply IH. intros iv b Hiv Hb. apply (SUB iv b); [right; exact Hiv| exact Hb].
  Qed.
  Lemma acompl_of_munchF : forall s s' d lo SP W m m',
    munch W m m' -> Forall (fun iv => forall a, fst iv <= a < snd iv -> awrit s s' d lo SP a) W -> acompl s s' d lo SP m m'.
  Proof.
    intros s s' d lo SP W m m' MU FA. apply (acompl_of_munch s s' d lo SP W m m' MU).
    intros iv a Hiv Ha. exact (proj1 (Forall_forall _ _) FA iv Hiv a Ha).
  Qed.
  (* [comment removed for export] *)
  Lemma awrit_mono : forall s s1 s2 d lo SP a,
    (forall sc, In sc (as_sec (a_st s1)) -> In sc (as_sec (a_st s2)) \/ In sc (as_sec (a_st s))) ->
    awrit s s1 d lo SP a -> awrit s s2 d lo SP a.
  Proof.
    intros s s1 s2 d lo SP a SUB W. unfold awrit in *.
    destruct W as [H|[H|[H|[H|[H|[H|H]]]]]]; [tauto|tauto|tauto|tauto|tauto| |tauto].
    right; right; right; right; right; left. destruct H as (sc & I & R). exists sc. split; [| exact R].
    destruct I as [I|I]; [left; exact I|]. destruct (SUB sc I); [right| left]; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma acompl_refl : forall s s' d lo SP m, acompl s s' d lo SP m m.
  Proof. intros s s' d lo SP m a _ _. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma avmx_same : forall s s' mo mo',
    vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> as_sec (a_st s') = as_sec (a_st s) -> avmx s s' mo mo'.
  Proof. intros s s' mo mo' EV ES x Hx. rewrite EV, ES. split; [left; exact Hx|]. intros sc A B. exact (False_ind _ (B A)). Qed.
  Lemma avmx_mat_l : forall s s' mo mo1 mo', same_but_materialized mo mo1 -> avmx s s' mo1 mo' -> avmx s s' mo mo'.
  Proof. intros s s' mo mo1 mo' SB A x Hx. apply A. rewrite (same_but_materialized_vmmaps mo mo1 SB). exact Hx. Qed.
  Lemma avmx_mat_r : forall s s' mo mo1 mo', avmx s s' mo mo1 -> same_but_materialized mo1 mo' -> avmx s s' mo mo'.
  Proof. intros s s' mo mo1 mo' A SB x Hx. rewrite (same_but_materialized_vmmaps mo1 mo' SB). exact (A x Hx). Qed.
  (* [comment removed for export] *)
  Lemma avmx_remove : forall s s' mo mo' sc0,
    In sc0 (as_sec (a_st s)) -> ~ In sc0 (as_sec (a_st s')) ->
    (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s))) ->
    (forall x : word, in_rangesb x (vm_maps (m_vmmaps mo)) = true ->
       in_rangesb x (vm_maps (m_vmmaps mo')) = true \/ sc_map_beg sc0 <= bv_unsigned x < sc_map_beg sc0 + sc_map_size sc0) ->
    avmx s s' mo mo'.
  Proof.
    intros s s' mo mo' sc0 IN OUT SUB COV x Hx. split.
    - destruct (COV x Hx) as [C|C]; [left; exact C| right; exists sc0; split; [exact IN| split; [exact OUT| exact C]]].
    - intros sc A B. exact (False_ind _ (B (SUB sc A))).
  Qed.
  (* [comment removed for export] *)
  Lemma avmx_cons : forall s s' mo mo' (a msz z : Z),
    0 <= a -> 0 < msz -> a + msz < 2 ^ 64 ->
    region_free (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true ->
    (forall x : word, in_rangesb x (vm_maps (m_vmmaps mo)) = true -> in_rangesb x (vm_maps (m_vmmaps mo')) = true) ->
    (forall sc, In sc (as_sec (a_st s')) -> In sc (as_sec (a_st s)) \/ sc = mkSC a msz z) ->
    avmx s s' mo mo'.
  Proof.
    intros s s' mo mo' a msz z Ha Hm Ham FR INCL SEC x Hx. split; [left; exact (INCL x Hx)|].
    intros sc Hin Hnot R. destruct (SEC sc Hin) as [Old| ->]; [exact (Hnot Old)|]. cbn [sc_map_beg sc_map_size] in R.
    pose proof (region_free_not_in _ _ _ x FR) as NI. unfold wz in NI. rewrite !unsigned_lit in NI by lia.
    rewrite (NI R) in Hx. discriminate Hx.
  Qed.
End HCW.
