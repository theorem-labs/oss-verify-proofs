From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF TrNames HarnessRep ListTr.
Import ListNotations.
Local Open Scope Z_scope.

Definition sh_real (L : layout) (qs : list sptr) (s : shl) (l : hlist) : Prop :=
  hl_cap l = sh_cap s /\ (sh_cap s <> 0 -> hl_v l = ptr_addr L (resolveF qs (sh_v s))) /\
  map (fun r => bzs (snd r)) (hl_recs l) = sh_keys s /\
  map fst (hl_recs l) = map (fun r => ptr_addr L (resolveF qs (fst r))) (sh_recs s).

Definition sh_live (A : astate) (qs : list sptr) (s : shl) : Prop :=
  (sh_cap s <> 0 -> exists n, In (resolveF qs (sh_v s), n) (user_blocks A)) /\
  (forall r, In r (sh_recs s) -> exists n, In (resolveF qs (fst r), n) (user_blocks A)).

Lemma sh_real_of : forall L A qs l,
    NoDup (map fst (blocks L A)) ->
    (hl_cap l <> 0 -> exists n, In (hl_v l, n) (blocks L A)) ->
    (forall r, In r (hl_recs l) -> exists n, In (fst r, n) (blocks L A)) ->
    sh_real L qs (sh_of (known_at L A) l) l.
Proof.
  intros L A qs l HN Hv Hr. unfold sh_real, sh_of, known_at, sh_keys. cbn [sh_cap sh_v sh_recs]. split; [reflexivity|].
  split.
  - intros Hc. destruct (Hv Hc) as [n Hn]. simpl. symmetry. exact (proj2 (sptr_of_spec L A _ n HN Hn)).
  - split.
    + rewrite map_map. reflexivity.
    + rewrite map_map. apply map_ext_in. intros r Hin. destruct (Hr r Hin) as [n Hn]. simpl.
      symmetry. exact (proj2 (sptr_of_spec L A _ n HN Hn)).
Qed.

Lemma nodup_map_inj : forall (X : Type) (f : X -> Z) (l : list X) x y,
    List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros X f l. induction l as [|z l IH]; intros x y HN Hx Hy Hf; [destruct Hx|].
  cbn [map] in HN. apply NoDup_cons_iff in HN as [Hz HN].
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hz. rewrite Hf. apply in_map, Hy.
  - exfalso. apply Hz. rewrite <- Hf. apply in_map, Hx.
  - exact (IH x y HN Hx Hy Hf).
Qed.

Lemma sptr_of_eq : forall L A p n,
    NoDup (map fst (blocks L A)) -> In (p, n) (user_blocks A) -> sptr_of L A (ptr_addr L p) = p.
Proof.
  intros L A p n HN Hin. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in HN.
  unfold blocks in HN. rewrite map_map in HN. cbn [fst] in HN. unfold sptr_of.
  destruct (find (fun pb => ptr_addr L (fst pb) =? ptr_addr L p) (user_blocks A)) as [[q m]|] eqn:Hf.
  - apply find_some in Hf as [Hq Hqa]. cbn [fst] in Hqa |- *. apply Z.eqb_eq in Hqa.
    pose proof (nodup_map_inj _ (fun b => ptr_addr L (fst b)) _ (q, m) (p, n) HN Hq Hin Hqa) as E.
    injection E as -> _. reflexivity.
  - exfalso. apply (find_none _ _ Hf) in Hin. cbn [fst] in Hin. rewrite Z.eqb_refl in Hin. discriminate.
Qed.

Lemma sh_rel_real : forall L qs1 qs2 s1 s2 l,
    sh_rel qs1 qs2 s1 s2 -> sh_real L qs2 s2 l -> sh_real L qs1 s1 l.
Proof.
  intros L qs1 qs2 s1 s2 l (Ec & Ev & Hr) (Rc & Rv & Rk & Ra). unfold sh_real.
  split; [rewrite Rc; symmetry; exact Ec|]. split.
  - intros Hc. rewrite Ec in Hc. rewrite (Rv Hc). pose proof (Ev Hc) as E. unfold ad_eq, pdefT in E. rewrite E. reflexivity.
  - split.
    + rewrite Rk. symmetry. exact (sh_rel_keys qs1 qs2 s1 s2 (conj Ec (conj Ev Hr))).
    + rewrite Ra. clear -Hr. induction Hr as [|r1 r2 l1 l2 [_ Ha] _ IH]; [reflexivity|].
      simpl. rewrite IH. unfold ad_eq, pdefT in Ha. rewrite Ha. reflexivity.
Qed.
