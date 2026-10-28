(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio HexModel Target Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Exit Printf_wfile Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dec_op (o : Z * Z * Z) : lop :=
  match o with
  | (c, a, b) => if c =? 0 then OpMalloc a else if c =? 1 then OpFree (Z.to_nat a) else if c =? 2 then OpRealloc (Z.to_nat a) b
                 else OpAligned b a   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Fixpoint live_blocks (rho : valuation) (tl : list int) (env : lenv) : list block :=
  match tl, env with
  | t :: tl', e :: env' =>
      match e with
      | Some (p, n) => (p, rho t, n) :: live_blocks rho tl' env'
      | None => live_blocks rho tl' env'
      end
  | _, _ => []
  end.

Lemma live_blocks_in (rho : valuation) : forall (tl : list int) (env : lenv) (k : nat) (t : int) (p : bptr) (n : Z),
  nth_error tl k = Some t -> nth_error env k = Some (Some (p, n)) -> In (p, rho t, n) (live_blocks rho tl env).
Proof.
  induction tl as [|t0 tl IH]; intros env k t p n Ht He; [destruct k; discriminate|].
  destruct env as [|e env]; [destruct k; discriminate|]. destruct k as [|k]; cbn in Ht, He |- *.
  - injection Ht as ->. injection He as ->. left. reflexivity.
  - destruct e as [[p0 n0]|]; [right|]; exact (IH env k t p n Ht He).
Qed.

Lemma live_blocks_inv (rho : valuation) : forall (tl : list int) (env : lenv) (b : block),
  In b (live_blocks rho tl env) ->
  exists k t p n, nth_error tl k = Some t /\ nth_error env k = Some (Some (p, n)) /\ b = (p, rho t, n).
Proof.
  induction tl as [|t0 tl IH]; intros env b Hb; [destruct Hb|]. destruct env as [|e env]; [destruct Hb|]. cbn in Hb.
  destruct e as [[p0 n0]|].
  - destruct Hb as [<-|Hb]; [exists 0%nat, t0, p0, n0; auto|].
    destruct (IH env b Hb) as (k & t & p & n & H1 & H2 & H3). exists (Datatypes.S k), t, p, n. auto.
  - destruct (IH env b Hb) as (k & t & p & n & H1 & H2 & H3). exists (Datatypes.S k), t, p, n. auto.
Qed.

Lemma live_blocks_agree (rho rho' : valuation) : forall (tl : list int) (env : lenv),
  (forall t, In t tl -> rho' t = rho t) -> live_blocks rho' tl env = live_blocks rho tl env.
Proof.
  induction tl as [|t0 tl IH]; intros env H; [reflexivity|]. destruct env as [|e env]; [reflexivity|]. cbn.
  rewrite (IH env) by (intros t Ht; apply H; right; exact Ht). rewrite (H t0) by (left; reflexivity). reflexivity.
Qed.

Lemma live_blocks_snoc (rho : valuation) : forall (tl : list int) (env : lenv) (t : int) (e : option (bptr * Z)),
  length env = length tl ->
  live_blocks rho (tl ++ [t]) (env ++ [e]) = live_blocks rho tl env ++ match e with Some (p, n) => [(p, rho t, n)] | None => [] end.
Proof.
  induction tl as [|t0 tl IH]; intros env t e Hl; destruct env as [|e0 env]; try discriminate.
  - cbn. destruct e as [[p n]|]; reflexivity.
  - cbn. injection Hl as Hl. rewrite (IH env t e Hl). destruct e0 as [[p0 n0]|]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_cons_ne (p : bptr) (b : block) (L : list block) : blk_id b <> p -> lb_remove p (b :: L) = b :: lb_remove p L.
Proof.
  intros Hne. unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N]; [reflexivity|].
  exfalso. apply N. destruct (bptr_eqb (blk_id b) p) eqn:E; [apply bptr_eqb_eq in E; contradiction | exact I].
Qed.

Lemma lb_remove_app (p : bptr) (L1 L2 : list block) : lb_remove p (L1 ++ L2) = lb_remove p L1 ++ lb_remove p L2.
Proof. unfold lb_remove. apply list.filter_app. Qed.

Lemma set_nth_length {A : Type} (x : A) : forall (k : nat) (l : list A), length (set_nth k x l) = length l.
Proof. induction k as [|k IH]; intros [|y l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma nth_error_set_nth_ne {A : Type} (x : A) : forall (k k' : nat) (l : list A), k <> k' -> nth_error (set_nth k x l) k' = nth_error l k'.
Proof.
  induction k as [|k IH]; intros k' [|y l] Hne; cbn; try reflexivity.
  - destruct k'; [contradiction | reflexivity].
  - destruct k'; [reflexivity | cbn; apply IH; lia].
Qed.

Lemma nth_error_set_nth_same {A : Type} (x : A) : forall (k : nat) (l : list A) (y : A), nth_error l k = Some y -> nth_error (set_nth k x l) k = Some x.
Proof. induction k as [|k IH]; intros [|z l] y H; cbn in *; try discriminate; [reflexivity | exact (IH l y H)]. Qed.

Lemma lb_remove_live (rho : valuation) : forall (tl : list int) (env : lenv) (k : nat) (t : int) (p : bptr) (n0 : Z),
  List.NoDup (map blk_id (live_blocks rho tl env)) -> nth_error tl k = Some t -> nth_error env k = Some (Some (p, n0)) ->
  lb_remove p (live_blocks rho tl env) = live_blocks rho tl (set_nth k None env).
Proof.
  induction tl as [|t0 tl IH]; intros env k t p n0 ND Ht He; [destruct k; discriminate|].
  destruct env as [|e env]; [destruct k; discriminate|]. destruct k as [|k]; cbn in Ht, He.
  - injection Ht as ->. injection He as ->. cbn [live_blocks set_nth] in ND |- *. exact (lb_remove_hd p (rho t) n0 _ ND).
  - cbn [live_blocks set_nth] in ND |- *. destruct e as [[p1 n1]|]; [|exact (IH env k t p n0 ND Ht He)].
    cbn [map] in ND. apply List.NoDup_cons_iff in ND as [Hni ND]. rewrite lb_remove_cons_ne.
    + f_equal. exact (IH env k t p n0 ND Ht He).
    + cbn [blk_id fst]. intros ->. apply Hni. pose proof (live_blocks_in rho tl env k t p n0 Ht He) as Hin.
      exact (in_map blk_id _ _ Hin).
Qed.

(* [comment removed for export] *)
Lemma tag_of_nth (cd : acd) (k : Z) (t' : int) :
  a_n cd = Z.of_nat (length (a_tags cd)) -> tag_of cd k = Some t' -> (Z.to_nat k < length (a_tags cd))%nat ->
  0 <= k /\ nth_error (rev (a_tags cd)) (Z.to_nat k) = Some t'.
Proof.
  intros Hn Ht Hk. unfold tag_of in Ht. rewrite Hn in Ht.
  assert (H0 : 0 <= k).
  { destruct (Z_lt_le_dec k 0) as [L|L]; [|exact L]. exfalso.
    assert (X : nth_error (a_tags cd) (Z.to_nat (Z.of_nat (length (a_tags cd)) - 1 - k)) = None) by (apply nth_error_None; lia). congruence. }
  split; [exact H0|]. rewrite nth_error_rev. replace (Z.to_nat k <? length (a_tags cd))%nat with true by (symmetry; apply Nat.ltb_lt; exact Hk).
  rewrite <- Ht. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition static_ok (a b : Z) (wr : bool) : Prop := In (a, b, wr) STATICS.

(* [comment removed for export] *)
Lemma static_facts : forall a b wr, static_ok a b wr ->
  0x10000 <= a /\ a < b /\ b <= 0x355000
  /\ (wr = true -> 0x2c2000 <= a /\ (b <= RMallocRep.RLIBC \/ RMallocRep.RCTX + 936 <= a) /\ (b <= RMallocRep.RSSP_GUARD \/ RMallocRep.RSSP_GUARD + 8 <= a)
                   /\ (b <= RMallocRep.RGOT_SSP \/ RMallocRep.RGOT_SSP + 8 <= a) /\ (b <= 0x354990 \/ 0x354990 + 4 <= a)
                   /\ (forall x, a <= x < b -> rin_ivs LIBW_HX x \/ ralloc_static x))
  /\ ((a = RMallocRep.RERRNO /\ b = RMallocRep.RERRNO + 4) \/ (b <= 0xe1000 /\ wr = false) \/ ((a = got_ssp \/ a = ssp_guard) /\ b = a + 8 /\ wr = false)
      \/ (0x2c2000 <= a /\ forall x, a <= x < b -> ~ ralloc_static x)).
Proof.
  intros a b wr H. unfold static_ok, STATICS in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <- <-|]); try contradiction;
    unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, RMallocRep.RERRNO, got_ssp, ssp_guard;
    (split; [lia|]); (split; [lia|]); (split; [lia|]);
    (split; [first [ discriminate
                   | intros _; repeat (split; [lia|]); intros x Hx; cbn [rin_ivs LIBW_HX fst snd]; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, RMallocRep.RERRNO; lia ]|]);
    first [ left; split; reflexivity
          | right; left; split; [lia | reflexivity]
          | right; right; left; split; [first [left; reflexivity | right; reflexivity] | split; reflexivity]
          | right; right; right; split; [lia|]; intros x Hx; unfold ralloc_static, RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP, RMallocRep.RERRNO; lia ].
Qed.

Lemma nodup_map_app {A B : Type} (f : A -> B) : forall (l1 l2 : list A) (x y : A),
  List.NoDup (map f (l1 ++ l2)) -> In x l1 -> In y l2 -> f x <> f y.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x y ND Hx Hy; [destruct Hx|]. cbn in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Hx as [->|Hx]; [|exact (IH l2 x y ND' Hx Hy)].
  intros E. apply Hn. rewrite E. apply in_map. apply in_or_app. right. exact Hy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Inv.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.

(* [comment removed for export] *)
Variables (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState).
Variable ls0 : LS.
Variable POST : LS -> PState -> machine_state -> Prop.

Hypothesis H_LIBW : LIBW = LIBW_HX.
Hypothesis H_lo1 : alloc_ceiling <= lo.
Hypothesis H_lo2 : GLOBALS_TOP <= lo.
Hypothesis H_lo3 : lo <= sp0 - to_Z STK.
Hypothesis H_sp0B : sp0 <= B.
Hypothesis H_sp064 : sp0 < 2 ^ 64.

Record ghost : Type := GH { g_s : PState; g_env : lenv; g_ops : list lop }.

(* [comment removed for export] *)
Definition J (g : ghost) (ms : machine_state) : Prop :=
  implM ctusegs (interp (lbind (run_ops (g_ops g) (g_env g)) (fun _ => LRet ls0))) (g_s g) POST ms.

Lemma J_evt : forall g ms, evt ctusegs (J g) ms -> J g ms.
Proof. intros g ms H. unfold J. eapply implM_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Definition region_class (M : HxMem.mem) (tl : list int) (env : lenv) : Prop :=
  forall t rg, mget M t = Some rg ->
    match rg_abs rg with
    | Some a => (to_Z a = 0 /\ to_Z (rg_size rg) = 0 /\ rg_wr rg = false) \/ static_ok (to_Z a) (to_Z a + to_Z (rg_size rg)) (rg_wr rg)
    | None => (t = 1%uint63 /\ rg_size rg = STK)
              \/ (exists k p n, nth_error tl k = Some t /\ nth_error env k = Some (Some (p, n)) /\ to_Z (rg_size rg) = n)
    end.

(* [comment removed for export] *)
Definition live_link (M : HxMem.mem) (tl : list int) (env : lenv) : Prop :=
  forall k t p n, nth_error tl k = Some t -> nth_error env k = Some (Some (p, n)) ->
    exists rg, mget M t = Some rg /\ rg_abs rg = None /\ to_Z (rg_size rg) = n /\ rg_wr rg = true.

(* [comment removed for export] *)
Definition FMem (g : ghost) (rho : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m : word -> option byte) : Prop :=
  let tl := rev (a_tags cd) in
  g_ops g = map dec_op (a_ops cd)
  /\ length (g_env g) = length tl /\ a_n cd = Z.of_nat (length tl) /\ List.NoDup tl
  /\ (forall t, In t tl -> to_Z NEXT0 <= to_Z t < to_Z nx)
  /\ (forall t rg, mget M t = Some rg -> to_Z t < to_Z nx)
  /\ to_Z NEXT0 <= to_Z nx /\ to_Z nx + Z.of_nat (length (a_ops cd)) < 2 ^ 20
  /\ region_class M tl (g_env g) /\ live_link M tl (g_env g)
  /\ RHEAP (g_s g) (live_blocks rho tl (g_env g) ++ LB) m
  /\ rho 1%uint63 = sp0 - to_Z STK
  /\ mem_inv ctusegs m /\ stk ctusegs m lo sp0 /\ rauxv_ok m B
  /\ agree_on (lx_client LB sp0 LIBW) m0 m.

Definition FInv (g : ghost) (rho : valuation) (cd : acd) (S : sstate) (ms : machine_state) : Prop :=
  FMem g rho cd (s_mem S) (s_next S) (ms_mem ms)
  /\ ms_fregs ms = F0 /\ ms_fcsr ms = fc0 /\ ms_rom ms = seg_rom ctusegs /\ regs_nf (ms_regs ms)
  /\ (ps_fa (g_s g) = ps_fa s0 /\ ps_so (g_s g) = ps_so s0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma STK_Z : to_Z STK = 65536. Proof. reflexivity. Qed.

Lemma wr_facts (g : ghost) (rho : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m : word -> option byte)
    (t : int) (rg : region) (A A' : Z) :
  FMem g rho cd M nx m -> mget M t = Some rg -> rg_wr rg = true ->
  rbase rho t rg <= A -> A <= A' -> A' <= rbase rho t rg + to_Z (rg_size rg) ->
  rclient_write_ok (live_blocks rho (rev (a_tags cd)) (g_env g) ++ LB) (A, A')
  /\ A' <= sp0
  /\ (A < A' -> forall a, A <= a < A' -> ~ lx_client LB sp0 LIBW a)
  /\ (A' <= RMallocRep.RAUXV_CELL \/ RMallocRep.RAUXV_CELL + 8 <= A).
Proof.
  intros (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr) Eg Hw HA HAA HA'.
  pose proof (Hcls t rg Eg) as C. unfold rbase in HA, HA'. pose proof STK_Z as ES.
  assert (BLK : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. eapply RMalloc_ifaceP.RHEAP_block_range_proof; [exact Hheap|]. apply in_or_app. right. exact Hb. }
  assert (HALL : forall b, In b (live_blocks rho (rev (a_tags cd)) (g_env g) ++ LB) -> rblock_range (blk_addr b) (blk_size b)).
  { intros b Hb. eapply RMalloc_ifaceP.RHEAP_block_range_proof; [exact Hheap| exact Hb]. }
  unfold GLOBALS_TOP in H_lo2. unfold RMallocRep.RAUXV_CELL.
  destruct (rg_abs rg) as [a|] eqn:Ea.
  - (* [comment removed for export] *)
    destruct C as [(_ & _ & C)|C]; [congruence|]. rewrite Hw in C.
    destruct (static_facts _ _ _ C) as (S1 & S2 & S3 & S4 & _). specialize (S4 eq_refl).
    destruct S4 as (W1 & W2 & W3 & W4 & W5 & W6). unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP in *.
    split; [right; left; cbn [fst snd]; unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP; lia|].
    split; [lia|]. split; [|lia].
    intros _ x Hx [Hnx' Hc]. destruct (W6 x ltac:(lia)) as [Hl|Hs]; [apply Hnx'; rewrite H_LIBW; exact Hl|].
    destruct Hc as [Hc|[(b & Hb & Hr)|[_ Hc]]]; [lia| | exact (Hc Hs)].
    destruct (BLK b Hb) as (_ & _ & _ & _ & Hout). lia.
  - destruct C as [[-> Es]|(k & p & n & Hk & He & Es)].
    + (* [comment removed for export] *)
      rewrite Es in HA'. rewrite Hrho1 in HA, HA'.
      split; [left; cbn [fst]; lia|]. split; [lia|]. split; [|lia].
      intros _ x Hx [_ Hc]. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| | lia].
      destruct (BLK b Hb) as (_ & _ & _ & Hce & _). lia.
    + (* [comment removed for export] *)
      pose proof (live_blocks_in rho _ _ k t p n Hk He) as Hin.
      assert (Hin' : In (p, rho t, n) (live_blocks rho (rev (a_tags cd)) (g_env g) ++ LB)) by (apply in_or_app; left; exact Hin).
      destruct (HALL _ Hin') as (R1 & R2 & R3 & R4 & R5). cbn [blk_addr blk_size fst snd] in R1, R2, R3, R4, R5. rewrite Es in HA'.
      split; [right; right; exists (p, rho t, n); split; [exact Hin'|]; cbn [blk_addr blk_size fst snd]; lia|].
      split; [lia|]. split; [|lia].
      intros _ x Hx [_ Hc]. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| | lia].
      assert (Hne : blk_id (p, rho t, n) <> blk_id b).
      { apply (nodup_map_app blk_id _ _ _ _ (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ Hheap) Hin Hb). }
      destruct (RMalloc_ifaceP.RHEAP_blocks_disjoint_proof _ _ _ _ _ Hheap Hin' (in_or_app _ _ _ (or_intror Hb)) Hne) as [D|D];
        cbn [blk_addr blk_size fst snd] in D; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma same_dirs_tags (M M' : HxMem.mem) (nx : int) :
  same_dirs M M' -> (forall t rg, mget M t = Some rg -> to_Z t < to_Z nx) -> (forall t rg, mget M' t = Some rg -> to_Z t < to_Z nx).
Proof.
  intros Hd H t rg' G'. specialize (Hd t). rewrite G' in Hd. destruct (mget M t) as [rg|] eqn:G; [|contradiction]. exact (H t rg G).
Qed.

Lemma same_dirs_class (M M' : HxMem.mem) (tl : list int) (env : lenv) :
  same_dirs M M' -> region_class M tl env -> region_class M' tl env.
Proof.
  intros Hd H t rg' G'. specialize (Hd t). rewrite G' in Hd. destruct (mget M t) as [rg|] eqn:G; [|contradiction].
  destruct Hd as (Ea & Es & _ & Ew & _). specialize (H t rg G). rewrite Ea, Es, Ew. exact H.
Qed.

Lemma same_dirs_link (M M' : HxMem.mem) (tl : list int) (env : lenv) :
  same_dirs M M' -> live_link M tl env -> live_link M' tl env.
Proof.
  intros Hd H k t p n Hk He. destruct (H k t p n Hk He) as (rg & G & Ea & Es & Ew). specialize (Hd t). rewrite G in Hd.
  destruct (mget M' t) as [rg'|]; [|contradiction]. destruct Hd as (Ea' & Es' & _ & Ew' & _). exists rg'.
  rewrite Ea', Es', Ew'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma FMem_write (g : ghost) (rho : valuation) (cd : acd) (M M' : HxMem.mem) (nx : int) (m m' : word -> option byte)
    (t : int) (rg : region) (A A' : Z) :
  FMem g rho cd M nx m -> mget M t = Some rg -> rg_wr rg = true ->
  rbase rho t rg <= A -> A <= A' -> A' <= rbase rho t rg + to_Z (rg_size rg) -> 0 <= A ->
  munch [(A, A')] m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' ->
  (forall x, A <= x < A' -> exists b, mrd ctusegs m' (wa x) = Some b) ->
  same_dirs M M' -> FMem g rho cd M' nx m'.
Proof.
  intros HF Eg Hw HA HAA HA' HA0 MU WM MI' HB Hd.
  destruct (wr_facts g rho cd M nx m t rg A A' HF Eg Hw HA HAA HA') as (W1 & W2 & W3 & W4).
  destruct HF as (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hheap & Hrho1 & Hmi & Hstk & Haux & Hagr).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  unfold FMem. repeat (split; [assumption|]).
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class M M' _ _ Hd Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink)|].
  split; [eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact Hheap| exact MU| exact WM| constructor; [exact W1| constructor]]|].
  split; [exact Hrho1|]. split; [exact MI'|].
  split.
  { destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros a Ha. destruct (S3 a Ha) as [Hwv (b & Hb)].
    split; [apply WM; exact Hwv|]. destruct (Z_lt_le_dec a A) as [L|L]; [|destruct (Z_lt_le_dec a A') as [L'|L']].
    - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I].
    - apply HB. lia.
    - exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. cbn [outside]. split; [lia|exact I]. }
  split.
  { eapply rauxv_ok_agree; [exact AG| | |exact Haux].
    - intros a Ha. cbn [outside]. split; [lia|exact I].
    - intros a Ha. cbn [outside]. unfold RMallocRep.RAUXV_CELL in *. split; [lia|exact I]. }
  eapply agree_on_trans; [exact Hagr|]. eapply agree_on_mono; [exact AG|].
  intros a Hc. cbn [outside]. split; [|exact I]. intros Ha. apply (W3 ltac:(lia) a Ha). exact Hc.
Qed.

Lemma FMem_dirs (g : ghost) (rho : valuation) (cd : acd) (M M' : HxMem.mem) (nx : int) (m : word -> option byte) :
  FMem g rho cd M nx m -> same_dirs M M' -> FMem g rho cd M' nx m.
Proof.
  intros (Hops & Hlen & Hn & Hnd & Htl & Htags & Hnx0 & Hnx & Hcls & Hlink & Hrest) Hd.
  unfold FMem. repeat (split; [assumption|]).
  split; [exact (same_dirs_tags M M' nx Hd Htags)|]. split; [exact Hnx0|]. split; [exact Hnx|].
  split; [exact (same_dirs_class M M' _ _ Hd Hcls)|]. split; [exact (same_dirs_link M M' _ _ Hd Hlink)|]. exact Hrest.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem FInv_step : forall g rho cd, step_pres ctusegs rho (FInv g rho cd).
Proof.
  intros g rho cd S S' ms ms' [HF (Hfr & Hfc & Hro & Hnf & Hps)] HRn HRn' Hst Ef Ec Eo Hd Hm Hrs Enx Eabs.
  split; [|rewrite Ef, Ec, Eo; repeat (split; [assumption|]); split; [exact (regs_nf_step _ _ Hnf Hrs) | exact Hps]].
  rewrite Enx. destruct Hm as [->|(t & rg & off & bs & Eg & Hw & Em & Hoff)]; [exact (FMem_dirs _ _ _ _ _ _ _ HF Hd)|]. rewrite Em.
  pose proof (Rn_R ctusegs rho S ms HRn) as (_ & _ & _ & _ & [HRg _]).
  pose proof (Rn_R ctusegs rho S' ms' HRn') as (_ & _ & _ & _ & [HRg' _]).
  destruct (HRg t rg Eg) as (B0 & B1 & B2 & _ & _ & _ & _ & Hby).
  pose proof (to_Z_bounded off) as Bo. pose proof (to_Z_bounded (rg_size rg)) as Bs. unfold two63 in B1.
  set (A := rbase rho t rg + to_Z off) in *.
  assert (WR : wr_at ctusegs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg))).
  { split; [lia|]. split; [lia|]. intros i Hi. destruct (Hby i Hi) as (b & _ & _ & Hwv). exact (Hwv Hw). }
  eapply (FMem_write g rho cd (s_mem S) (s_mem S') (s_next S) (ms_mem ms) _ t rg A (A + Z.of_nat (length bs)) HF Eg Hw);
    try (unfold A; lia); try exact Hd.
  - apply munch_write; [apply munch_refl| unfold A; lia| unfold A; lia|]. cbn [inside]. left. lia.
  - apply wmono_write. apply wmono_refl.
  - apply mem_inv_store; [destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmi & _); exact Hmi|].
    unfold A. apply (wr_at_store_ok ctusegs (ms_mem ms) (rbase rho t rg) (to_Z (rg_size rg)) (to_Z off) (length bs) WR); lia.
  - intros x Hx. specialize (Hd t). rewrite Eg in Hd. destruct (mget (s_mem S') t) as [rg'|] eqn:Eg'; [|contradiction].
    destruct (HRg' t rg' Eg') as (_ & _ & _ & _ & _ & _ & _ & Hby').
    rewrite (rbase_same_dir rho t rg rg' Hd) in Hby'. destruct Hd as (_ & Es & _). rewrite Es in Hby'.
    destruct (Hby' (x - rbase rho t rg) ltac:(unfold A in Hx; lia)) as (b & Hb & _). exists b.
    replace (rbase rho t rg + (x - rbase rho t rg)) with x in Hb by lia. rewrite <- Em. exact Hb.
Qed.
End Inv.
