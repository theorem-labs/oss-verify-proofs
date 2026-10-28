(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxHookSound HxToolkit HxQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.ApHX Require Import HxFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpInit HxpFacts HxpInv HxpHkAligned HxpRun HxpMain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition T (k : Z) : int := of_Z (NEXT0Z + k).

Definition no_region : region := RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty.
Definition fin_region (r : icache * @dres acd) (t : int) : region :=
  match mget (s_mem (end_state r)) t with Some rg => rg | None => no_region end.

Definition TAGS_LITi : list int := map of_Z TAGS_LIT.
Definition TAGS_BLKi : list int := map T KS_BLK.

(* [comment removed for export] *)
Definition FIN : list region * list region := Eval vm_compute in (map (fin_region run_result) TAGS_LITi, map (fin_region run_result) TAGS_BLKi).
Definition FIN_LIT : list region := Eval cbv in (fst FIN).
Definition FIN_BLK : list region := Eval cbv in (snd FIN).

(* [comment removed for export] *)
Definition lit_base (rg : region) : Z := match rg_abs rg with Some a => to_Z a | None => 0 end.

(* [comment removed for export] *)
Definition lit_okb (rg : region) : bool := match rg_abs rg with Some a => negb (a =? 0)%uint63 | None => false end.
Definition blk_okb (tsz : int * Z) (rg : region) : bool :=
  match rg_abs rg with
  | None => (to_Z (rg_size rg) =? snd tsz) && (0 <? snd tsz) && rg_wr rg && negb (fst tsz =? 1)%uint63 && negb (rg_al rg =? 0)%uint63
  | Some _ => false
  end.

Fixpoint forallb2 {A B} (f : A -> B -> bool) (l : list A) (l' : list B) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l1, b :: l2 => f a b && forallb2 f l1 l2
  | _, _ => false
  end.

(* [comment removed for export] *)
Fixpoint nodupb (l : list int) : bool :=
  match l with [] => true | t :: l' => negb (existsb (fun t' => (t =? t')%uint63) l') && nodupb l' end.

Lemma nodupb_ok : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|t l IH]; intros H; [constructor|]. cbn [nodupb] in H. apply andb_prop in H as [H1 H2].
  constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (X : existsb (fun t' => (t =? t')%uint63) l = true) by (apply existsb_exists; exists t; split; [exact Hin | apply Uint63.eqb_refl]).
  congruence.
Qed.

(* [comment removed for export] *)
Lemma fin_checked :
  map (fun t => mget (s_mem S_end) t) TAGS_LITi = map Some FIN_LIT
  /\ map (fun t => mget (s_mem S_end) t) TAGS_BLKi = map Some FIN_BLK
  /\ forallb lit_okb FIN_LIT = true
  /\ forallb2 blk_okb (combine TAGS_BLKi SZ_BLK) FIN_BLK = true
  /\ nodupb TAGS_BLKi = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma exit_ok_end : exit_cells_ok S_end = true.
Proof.
  destruct (run_ok_inv run_result run_checked) as (ic & cd & S & Erun & _ & _ & _ & _ & _ & Hexit).
  destruct (end_state_eq run_result ic cd S Erun) as [E _]. rewrite E. exact Hexit.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ap_init_facts (m : word -> option byte) (OW : list block) : Prop :=
  exists rho : valuation,
       Forall (fun rg => region_export ctusegs m rho (lit_base rg) rg) FIN_LIT
    /\ Forall2 (fun t rg => region_export ctusegs m rho (rho t) rg
                           /\ (exists p, In (p, rho t, to_Z (rg_size rg)) OW)
                           /\ 0 < rho t /\ rho t + to_Z (rg_size rg) < 2 ^ 63 /\ rho t mod 16 = 0) TAGS_BLKi FIN_BLK
    /\ List.NoDup (map rho TAGS_BLKi)
    /\ List.NoDup (map blk_id OW)            (* [comment removed for export] *)
    /\ ossl_exit_cells m.

Section Final.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.

(* [comment removed for export] *)
Lemma heap_block_in (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte)
    (g : ghost) (rho : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (t : int) (rg : region) (n : Z) :
  FMem LB lo B sp0 m0 g rho cd M nx m -> mget M t = Some rg -> rg_abs rg = None -> to_Z (rg_size rg) = n -> t <> 1%uint63 ->
  exists p, In (p, rho t, n) (live_blocks rho (rev (a_tags cd)) (g_env g)).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & Hcls & _) Eg Ea Es Hne. pose proof (Hcls t rg Eg) as C. rewrite Ea in C.
  destruct C as [[C _]|(k & p & n' & Hk & He & Es')]; [contradiction|]. exists p. rewrite <- Es, Es'. exact (live_blocks_in rho _ _ k t p n' Hk He).
Qed.

(* [comment removed for export] *)
Lemma rho_nodup (rho : valuation) (M : HxMem.mem) (m : word -> option byte) : forall tags : list int,
  Rmem ctusegs rho M m -> List.NoDup tags ->
  (forall t, In t tags -> exists rg, mget M t = Some rg /\ rg_abs rg = None /\ 0 < to_Z (rg_size rg) /\ rg_wr rg = true) ->
  List.NoDup (map rho tags).
Proof.
  intros tags [_ Hsep]. induction tags as [|t tags IH]; intros Hnd Hall; [constructor|].
  apply List.NoDup_cons_iff in Hnd as [Hni Hnd]. cbn [map]. constructor; [|apply IH; [exact Hnd | intros t' Ht'; apply Hall; right; exact Ht']].
  intros Hin. apply in_map_iff in Hin as (t' & Er & Ht').
  destruct (Hall t (or_introl eq_refl)) as (rg & G & Ea & Hs & Hw). destruct (Hall t' (or_intror Ht')) as (rg' & G' & Ea' & Hs' & Hw').
  assert (Hne : t <> t') by (intros ->; contradiction).
  destruct (Hsep t t' rg rg' G G' Hne (or_introl Hw)) as [D|D]; unfold rbase in D; rewrite Ea, Ea' in D; lia.
Qed.

(* [comment removed for export] *)
Lemma lit_elem (rho : valuation) (m : word -> option byte) (t : int) (rg : region) :
  Rmem ctusegs rho (s_mem S_end) m -> mget (s_mem S_end) t = Some rg -> lit_okb rg = true -> region_export ctusegs m rho (lit_base rg) rg.
Proof.
  intros HR Hg Hl. unfold lit_okb in Hl. unfold lit_base. destruct (rg_abs rg) as [a|] eqn:Ea; [|discriminate].
  exact (region_export_lit ctusegs rho (s_mem S_end) m t rg a HR Hg Ea).
Qed.

(* [comment removed for export] *)
Definition al4b (rg : region) : bool := (rg_al rg =? 4)%uint63.
Lemma fin_al4 : forallb al4b FIN_BLK = true.
Proof. vm_compute. reflexivity. Qed.

Lemma blk_elem (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (g : ghost) (rho : valuation) (m : word -> option byte)
    (t : int) (sz : Z) (rg : region) :
  FMem LB lo B sp0 m0 g rho cd_end (s_mem S_end) (s_next S_end) m -> Rmem ctusegs rho (s_mem S_end) m ->
  mget (s_mem S_end) t = Some rg -> blk_okb (t, sz) rg = true -> al4b rg = true ->
  (region_export ctusegs m rho (rho t) rg
   /\ (exists p, In (p, rho t, to_Z (rg_size rg)) (live_blocks rho (rev (a_tags cd_end)) (g_env g)))
   /\ 0 < rho t /\ rho t + to_Z (rg_size rg) < 2 ^ 63 /\ rho t mod 16 = 0)
  /\ (rg_abs rg = None /\ 0 < to_Z (rg_size rg) /\ rg_wr rg = true).
Proof.
  intros HF HR Hg Hb H4. unfold blk_okb in Hb. cbn [fst snd] in Hb. destruct (rg_abs rg) as [a|] eqn:Ea; [discriminate|].
  apply andb_prop in Hb as [Hb Hal]. apply andb_prop in Hb as [Hb Hn1]. apply andb_prop in Hb as [Hb Hwr]. apply andb_prop in Hb as [Hsz Hpos].
  apply Z.eqb_eq in Hsz. apply Z.ltb_lt in Hpos. apply negb_true_iff in Hn1.
  assert (Hne : t <> 1%uint63) by (intros ->; rewrite Uint63.eqb_refl in Hn1; discriminate).
  pose proof (proj1 HR t rg Hg) as Hok. pose proof Hok as (B0 & B1 & _ & _ & _ & _ & Bal & _). unfold two63 in B1. unfold rbase in B0, B1, Bal. rewrite Ea in B0, B1, Bal.
  unfold al4b in H4. apply Uint63.eqb_spec in H4. rewrite H4 in Bal. change (2 ^ to_Z 4%uint63) with 16 in Bal.
  assert (Hp : 0 < rho t) by (destruct B0 as [_ [Hpos'|Hz]]; [lia|]; rewrite H4 in Hz; discriminate).
  split.
  - split; [exact (region_export_blk ctusegs rho (s_mem S_end) m t rg HR Hg Ea)|].
    split; [exact (heap_block_in LB lo B sp0 m0 g rho cd_end (s_mem S_end) (s_next S_end) m t rg _ HF Hg Ea eq_refl Hne)|].
    split; [exact Hp|]. split; [lia | exact Bal].
  - split; [reflexivity|]. split; [lia | exact Hwr].
Qed.

(* [comment removed for export] *)
Lemma cons_eq_inv {A} (a b : A) (l l' : list A) : a :: l = b :: l' -> a = b /\ l = l'.
Proof. intros H. split; [exact (f_equal (hd a) H) | exact (f_equal (@tl A) H)]. Qed.

Lemma lits_all_gen (f : int -> option region) (P : region -> Prop) :
  (forall t rg, f t = Some rg -> lit_okb rg = true -> P rg) ->
  forall (ts : list int) (rgs : list region), map f ts = map Some rgs -> forallb lit_okb rgs = true -> Forall P rgs.
Proof.
  intros Hel. induction ts as [|t ts IH]; intros [|rg rgs] Hm Hl; cbn [map] in Hm;
    [constructor | exact (False_ind _ (nil_cons Hm)) | symmetry in Hm; exact (False_ind _ (nil_cons Hm)) |].
  apply cons_eq_inv in Hm as [Hg Hm']. apply (f_equal (fun o => match o with Some r => r | None => no_region end)) in Hg as Hg'. cbn in Hg'.
  cbn [forallb] in Hl. apply andb_prop in Hl as [H1 H2].
  constructor; [| exact (IH rgs Hm' H2)]. apply (Hel t rg); [|exact H1].
  destruct (f t) as [r|]; [cbn in Hg'; subst; reflexivity | discriminate].
Qed.

Lemma blks_all_gen (f : int -> option region) (P : int -> region -> Prop) (Q : int -> Prop) :
  (forall t sz rg, f t = Some rg -> blk_okb (t, sz) rg = true -> al4b rg = true -> P t rg /\ Q t) ->
  forall (ts : list int) (szs : list Z) (rgs : list region),
  map f ts = map Some rgs -> forallb2 blk_okb (combine ts szs) rgs = true -> forallb al4b rgs = true ->
  Forall2 P ts rgs /\ (forall t, In t ts -> Q t).
Proof.
  intros Hel. induction ts as [|t ts IH]; intros szs [|rg rgs] Hm Hb H4; cbn [map] in Hm;
    [split; [constructor | intros t []] | exact (False_ind _ (nil_cons Hm)) | symmetry in Hm; exact (False_ind _ (nil_cons Hm)) |].
  apply cons_eq_inv in Hm as [Hg Hm']. destruct szs as [|sz szs]; [cbn in Hb; discriminate|]. cbn [combine forallb2] in Hb. apply andb_prop in Hb as [H1 H2].
  cbn [forallb] in H4. apply andb_prop in H4 as [H41 H42].
  assert (Hg' : f t = Some rg) by (destruct (f t) as [r|]; [apply (f_equal (fun o => match o with Some r => r | None => no_region end)) in Hg; cbn in Hg; subst; reflexivity | discriminate]).
  destruct (Hel t sz rg Hg' H1 H41) as [E1 E2]. destruct (IH szs rgs Hm' H2 H42) as [IH1 IH2].
  split; [constructor; [exact E1 | exact IH1]|]. intros t' [<-|Ht']; [exact E2 | exact (IH2 t' Ht')].
Qed.

(* [comment removed for export] *)
Lemma hx_final_ap_facts (LB : list block) (lo B sp0 : Z) (m0 m' : word -> option byte) (OW' : list block) :
  hx_final LB lo B sp0 m0 m' OW' -> ap_init_facts m' OW'.
Proof.
  intros (g & rho & HRall & HF & ->). pose proof (HRall rho (agree_below_refl _ _)) as HR.
  destruct fin_checked as (Hlit & Hblk & Hlok & Hbok & Hnd).
  exists rho. split.
  { exact (lits_all_gen (fun t => mget (s_mem S_end) t) _ (fun t rg Hg Hl => lit_elem rho m' t rg HR Hg Hl) TAGS_LITi FIN_LIT Hlit Hlok). }
  destruct (blks_all_gen (fun t => mget (s_mem S_end) t)
              (fun t rg => region_export ctusegs m' rho (rho t) rg
                           /\ (exists p, In (p, rho t, to_Z (rg_size rg)) (live_blocks rho (rev (a_tags cd_end)) (g_env g)))
                           /\ 0 < rho t /\ rho t + to_Z (rg_size rg) < 2 ^ 63 /\ rho t mod 16 = 0)
              (fun t => exists rg, mget (s_mem S_end) t = Some rg /\ rg_abs rg = None /\ 0 < to_Z (rg_size rg) /\ rg_wr rg = true)
              (fun t sz rg Hg Hb H4 => let X := blk_elem LB lo B sp0 m0 g rho m' t sz rg HF HR Hg Hb H4 in
                                     conj (proj1 X) (ex_intro _ rg (conj Hg (proj2 X))))
              TAGS_BLKi SZ_BLK FIN_BLK Hblk Hbok fin_al4) as [HB Hshape].
  assert (HRH : RHEAP (g_s g) (live_blocks rho (rev (a_tags cd_end)) (g_env g) ++ LB) m').
  { destruct HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRH & _). exact HRH. }
  (* [comment removed for export] *)
  remember (live_blocks rho (rev (a_tags cd_end)) (g_env g)) as OW eqn:EOW. clear EOW.
  split; [exact HB|].
  split; [exact (rho_nodup rho (s_mem S_end) m' TAGS_BLKi HR (nodupb_ok _ Hnd) Hshape)|].
  split; [|exact (exit_cells_final rho S_end m' exit_ok_end HR)].
  pose proof (LH_nodup _ _ _ HRH) as ND. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND).
Qed.

End Final.

(* [comment removed for export] *)
Corollary hx_rinit_ap {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} :
  rmalloc_stmt -> RRealloc_iface.rrealloc_stmt ->
  (forall (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (F0 : bvmap 5 word) (fc0 : bv 32) (s0 : PState)
          (ls0 : LS) (POST : LS -> PState -> machine_state -> Prop),
      alloc_ceiling <= lo -> GLOBALS_TOP <= lo -> lo <= sp0 - to_Z STK -> sp0 <= B -> sp0 < 2 ^ 64 ->
      hook_ok' ctusegs ghost (J ls0 POST) (FInv LB lo B sp0 m0 F0 fc0 s0) hkp_posix_memalign) ->
  forall ls0 : LS, lib_init = LibOps.init_of_ops (map dec_op OPS) ls0 ->
  LIBW = LIBW_HX -> to_Z STK <= LIB_STACK ->
  (forall m, lib_pristine m -> hx_pristine m) ->
  (forall m OW, ap_init_facts m OW -> lib_inv ls0 m OW) ->
  rinit_stmt.
Proof.
  intros HM HRe HA ls0 Hinit HW HS HP HI. apply (hx_rinit HM HRe HA ls0 Hinit HW HS HP).
  intros LB lo B sp0 m0 m' OW' Hfin. apply HI. exact (hx_final_ap_facts LB lo B sp0 m0 m' OW' Hfin).
Qed.
