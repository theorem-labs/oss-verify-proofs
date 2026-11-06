From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT.
Import ListNotations.
Local Open Scope Z_scope.

(* RelayRunT's traces over a ResFormT: the model pointers are sptr, the null pointer SP 0 0 stands for an address
   list too short. *)
Abbreviation trF := (list (rev sptr)).
Abbreviation adrF := (addr sptr).
Abbreviation nretF tr := (nret sptr tr).
Abbreviation resolveF qs a := (resolve sptr (SP 0 0) qs a).
(* The default of a list of addresses. *)
Abbreviation adr0 := (@Known sptr (SP 0 0)).

Section RunF.
Variable F : ResFormT.

(* The resource state after the requests tr from b, the i-th returned address being nth i qs. *)
Definition runF (qs : list sptr) (b : rt_R F) (tr : trF) : rt_R F :=
  run_tr (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) qs b tr.

(* Each request of tr that takes memory finds room in the state the earlier requests left. *)
Definition roomF (qs : list sptr) (b : rt_R F) (tr : trF) : Prop :=
  room_run (rt_R F) sptr (SP 0 0) (rt_malloc F) (rt_free F) (rt_realloc F) (rt_room F) qs b tr.
End RunF.

(* The model pointer of the live block at address a (SP 0 0 when there is none). *)
Definition sptr_of (L : layout) (A : astate) (a : Z) : sptr :=
  match find (fun pb => ptr_addr L (fst pb) =? a) (user_blocks A) with
  | Some pb => fst pb
  | None => SP 0 0
  end.

(* A start-state block in a trace: Known (its model pointer). *)
Definition known_at (L : layout) (A : astate) (a : Z) : adrF := Known (sptr_of L A a).

(* p is the live block of n bytes at address a: what a post states of a trace address resolved by its qs. *)
Definition live_at (L : layout) (A : astate) (p : sptr) (a n : Z) : Prop := In (p, n) (user_blocks A) /\ ptr_addr L p = a.

Lemma nodup_fst_eq : forall (l : list (Z * Z)) x y y', List.NoDup (map fst l) -> In (x, y) l -> In (x, y') l -> y = y'.
Proof.
  induction l as [|[u v] l IH]; intros x y y' HN H1 H2; [destruct H1|].
  cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Hu HN].
  destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
  - congruence.
  - exfalso. apply Hu. injection E1 as -> ->. exact (in_map fst l (x, y') H2).
  - exfalso. apply Hu. injection E2 as -> ->. exact (in_map fst l (x, y) H1).
  - exact (IH x y y' HN H1 H2).
Qed.

(* With the block addresses distinct, sptr_of names the block at a. *)
Lemma sptr_of_spec : forall L A a n,
    NoDup (map fst (blocks L A)) -> In (a, n) (blocks L A) ->
    In (sptr_of L A a, n) (user_blocks A) /\ ptr_addr L (sptr_of L A a) = a.
Proof.
  intros L A a n HN Hin. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN. unfold blocks in HN, Hin.
  apply in_map_iff in Hin as [[p k] [Hpk Hb]]. cbn [fst snd] in Hpk. injection Hpk as Hp Hk. subst k.
  unfold sptr_of.
  destruct (find (fun pb => ptr_addr L (fst pb) =? a) (user_blocks A)) as [[q m]|] eqn:Hf.
  - apply find_some in Hf as [Hq Hqa]. cbn [fst snd] in Hqa |- *. apply Z.eqb_eq in Hqa.
    assert (m = n) as ->.
    { apply (nodup_fst_eq _ a m n HN).
      - rewrite <- Hqa. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q, m) Hq).
      - rewrite <- Hp. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hb). }
    split; [exact Hq | exact Hqa].
  - exfalso. apply (find_none _ _ Hf) in Hb. cbn [fst] in Hb. rewrite Hp, Z.eqb_refl in Hb. discriminate.
Qed.
