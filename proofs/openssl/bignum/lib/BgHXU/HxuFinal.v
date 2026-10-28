(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Frame.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxToolkit HxQuery.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgHXU Require Import HxuInit HxuInv HxuRun HxuMain.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require Import BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Record query : Type := Q { q_tag : int; q_lo : Z; q_size : Z; q_off : Z; q_ks : list kb }.

Definition q_ok (S : sstate) (q : query) : bool :=
  match mget (s_mem S) (q_tag q) with
  | Some rg => (match rg_abs rg with
                | Some a => (to_Z a =? q_lo q) && negb (q_lo q =? 0)
                | None => (q_lo q =? 0) && (to_Z (rg_size rg) =? q_size q) && rg_wr rg && negb (q_tag q =? 1)%uint63 && (0 <? q_size q)
                          && negb (rg_al rg =? 0)%uint63
                end)
               && (0 <=? q_off q) && (q_off q + Z.of_nat (length (q_ks q)) <=? to_Z (rg_size rg)) && kb_check bgusegs rg (q_off q) (q_ks q)
  | None => false
  end.

Definition q_addr (rho : valuation) (q : query) : Z := (if q_lo q =? 0 then rho (q_tag q) else q_lo q) + q_off q.

Lemma q_sound (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) :
  Rmem bgusegs rho (s_mem S) m -> q_ok S q = true ->
  exists rg bs, mget (s_mem S) (q_tag q) = Some rg /\ Forall2 (kb_ok rho) (q_ks q) bs /\ bytes_at bgusegs m (q_addr rho q) bs
                /\ (rg_wr rg = true -> wr_at bgusegs m (q_addr rho q) (Z.of_nat (length (q_ks q))))
                /\ (q_lo q = 0 -> rg_abs rg = None /\ to_Z (rg_size rg) = q_size q /\ rg_wr rg = true /\ q_tag q <> 1%uint63 /\ 0 < q_size q
                                  /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63).
Proof.
  intros [HRg _] H. unfold q_ok in H. destruct (mget (s_mem S) (q_tag q)) as [rg|] eqn:Eg; [|discriminate].
  apply andb_prop in H as [H Hk]. apply andb_prop in H as [H Hfit]. apply andb_prop in H as [Habs Hoff].
  apply Z.leb_le in Hoff, Hfit. pose proof (HRg _ _ Eg) as Hok.
  destruct (kb_check_sound bgusegs rho (q_tag q) rg m (q_ks q) (q_off q) Hok Hk Hoff Hfit) as (bs & HF & Hb & Hw).
  exists rg, bs. split; [reflexivity|]. split; [exact HF|].
  pose proof Hok as (B0 & B1 & _). unfold two63 in B1. unfold rbase in B0, B1, Hb, Hw |- *. unfold q_addr in *.
  destruct (rg_abs rg) as [a|] eqn:Ea.
  - apply andb_prop in Habs as [Habs Hnz]. apply Z.eqb_eq in Habs. rewrite Habs in *. apply negb_true_iff in Hnz. rewrite Hnz.
    split; [exact Hb|]. split; [exact Hw|]. intros E0. apply Z.eqb_neq in Hnz. contradiction.
  - apply andb_prop in Habs as [Habs H6]. apply andb_prop in Habs as [Habs H5]. apply andb_prop in Habs as [Habs H4]. apply andb_prop in Habs as [Habs H3]. apply andb_prop in Habs as [H1 H2].
    apply Z.eqb_eq in H2. apply Z.ltb_lt in H5. apply negb_true_iff in H4. apply negb_true_iff in H6. rewrite H1 in *.
    assert (Hal0 : to_Z (rg_al rg) <> 0) by (intros X; destruct (eqbP (rg_al rg) 0) as [Y|Y]; [discriminate | apply Y; exact X]).
    split; [exact Hb|]. split; [exact Hw|]. intros _.
    repeat split; try assumption; try lia. intros E1. rewrite E1 in H4. discriminate.
Qed.

Lemma q_cells (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (cs : list Cells.cell) :
  Rmem bgusegs rho (s_mem S) m -> q_ok S q = true -> cells_wf cs ->
  (forall bs, Forall2 (kb_ok rho) (q_ks q) bs -> bs = cells_bytes cs) ->
  ro_cells bgusegs m (q_addr rho q) cs.
Proof.
  intros HR Hq Hwf Hbs. destruct (q_sound rho S m q HR Hq) as (rg & bs & _ & HF & Hb & _). rewrite (Hbs bs HF) in Hb. split; assumption.
Qed.

Lemma q_rw_cells (rho : valuation) (S : sstate) (m : word -> option byte) (q : query) (cs : list Cells.cell) :
  Rmem bgusegs rho (s_mem S) m -> q_ok S q = true -> q_lo q = 0 -> cells_wf cs -> length (q_ks q) = cells_size cs ->
  (forall bs, Forall2 (kb_ok rho) (q_ks q) bs -> bs = cells_bytes cs) ->
  rw_cells bgusegs m (rho (q_tag q) + q_off q) cs.
Proof.
  intros HR Hq E0 Hwf Hl Hbs. destruct (q_sound rho S m q HR Hq) as (rg & bs & _ & HF & Hb & Hw & Hh).
  destruct (Hh E0) as (_ & _ & Hwr & _). unfold q_addr in Hb, Hw. rewrite E0 in Hb, Hw. cbn [Z.eqb] in Hb, Hw.
  rewrite (Hbs bs HF) in Hb. split; [split; assumption|]. rewrite <- Hl. exact (Hw Hwr).
Qed.

Section Blocks.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.
Variables (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte).

Lemma heap_block_in (g : ghost) (rho : valuation) (cd : acd) (M : HxMem.mem) (nx : int) (m : word -> option byte) (t : int) (rg : region) (n : Z) :
  FMem LB lo B sp0 m0 g rho cd M nx m -> mget M t = Some rg -> rg_abs rg = None -> to_Z (rg_size rg) = n -> t <> 1%uint63 ->
  exists p, In (p, rho t, n) (live_blocks rho (rev (a_tags cd)) (g_env g)).
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & Hcls & _) Eg Ea Es Hne. pose proof (Hcls t rg Eg) as C. rewrite Ea in C.
  destruct C as [[C _]|(k & p & n' & Hk & He & Es')]; [contradiction|]. exists p. rewrite <- Es, Es'. exact (live_blocks_in rho _ _ k t p n' Hk He).
Qed.

Lemma rho_nodup (rho : valuation) (M : HxMem.mem) (m : word -> option byte) : forall tags : list int,
  Rmem bgusegs rho M m -> List.NoDup tags ->
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

End Blocks.

Fixpoint nodupb (l : list int) : bool :=
  match l with [] => true | t :: l' => negb (existsb (fun t' => (t =? t')%uint63) l') && nodupb l' end.

Lemma nodupb_ok : forall l, nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|t l IH]; intros H; [constructor|]. cbn [nodupb] in H. apply andb_prop in H as [H1 H2].
  constructor; [|exact (IH H2)]. intros Hin. apply negb_true_iff in H1.
  assert (X : existsb (fun t' => (t =? t')%uint63) l = true) by (apply existsb_exists; exists t; split; [exact Hin | apply Uint63.eqb_refl]).
  congruence.
Qed.

Definition T (k : Z) : int := of_Z (29 + k).

Definition Q_got_malloc : query := Q 5 3262120 0 0 (kbs_Z 8 0xe9138).
Definition Q_got_free : query := Q 5 3262120 0 16 (kbs_Z 8 0xe94dc).
Definition Q_memset_func : query := Q 7 3267328 0 40 (kbs_Z 8 0x2bbae4).
Definition Q_malloc_impl : query := Q 7 3267328 0 16 (kbs_Z 8 0xe9138).
Definition Q_free_impl : query := Q 7 3267328 0 32 (kbs_Z 8 0xe94dc).
Definition Q_no_customize : query := Q 8 3335232 0 536 (kbs_Z 1 1).
Definition Q_stopped : query := Q 8 3335232 0 24 (kbs_Z 1 0).
Definition Q_optsdone : query := Q 8 3335232 0 112 (kbs_Z 8 2).
Definition Q_base_once : query := Q 8 3335232 0 48 (kbs_Z 4 2 ++ kbs_Z 4 1).
Definition Q_master_once : query := Q 8 3335232 0 148 (kbs_Z 4 2 ++ kbs_Z 4 2).
Definition Q_tcb_tsd : query := Q 11 3346232 0 8 (kbs_Z 8 0x352300).
Definition Q_tsd2 : query := Q 13 3481280 0 1104 (kbs_ptr (T 2)).
Definition Q_mk : query := Q (T 2) 0 72 24 (kbs_ptr (T 3)).
Definition Q_sa : query := Q (T 3) 0 32 0 (kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr (T 4)).
Definition Q_nd : query := Q (T 4) 0 128 0 (kbs_ptr (T 1543)).
Definition Q_es : query := Q (T 1543) 0 904 0 (kbs_bytes (repeat 0 704 ++ repeat 255 64 ++ repeat 0 136)).

Definition QS : list query :=
  [Q_got_malloc; Q_got_free; Q_memset_func; Q_malloc_impl; Q_free_impl; Q_no_customize; Q_stopped; Q_optsdone; Q_base_once; Q_master_once; Q_tcb_tsd; Q_tsd2; Q_mk; Q_sa; Q_nd; Q_es].

Definition TAGS4 : list int := [T 2; T 3; T 4; T 1543].

Lemma fin_checked : forallb (q_ok S_end) QS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fin_q (q : query) : In q QS -> q_ok S_end q = true.
Proof. exact (proj1 (forallb_forall (q_ok S_end) QS) fin_checked q). Qed.

Lemma fin_tags : List.NoDup TAGS4.
Proof. apply nodupb_ok. vm_compute. reflexivity. Qed.

Lemma exit_ok_end : exit_cells_ok S_end = true.
Proof.
  destruct (run_ok_inv run_result run_checked) as (ic & cd & S & Erun & _ & _ & _ & _ & _ & Hexit).
  destruct (end_state_eq run_result ic cd S Erun) as [E _]. rewrite E. exact Hexit.
Qed.

Definition bg_init_facts (m : word -> option byte) (OW : list block) : Prop :=
  exists EA : err_addrs, List.NoDup (ea_ids EA) /\ crypto_statics m /\ err_inv m OW EA /\ ossl_exit_cells m.

Section Final.
Context {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec}.

Lemma q_block (LB : list block) (lo B sp0 : Z) (m0 : word -> option byte) (g : ghost) (rho : valuation) (cd : acd) (S : sstate)
    (m : word -> option byte) (q : query) :
  FMem LB lo B sp0 m0 g rho cd (s_mem S) (s_next S) m -> Rmem bgusegs rho (s_mem S) m -> q_ok S q = true -> q_lo q = 0 ->
  exists p, In (p, rho (q_tag q), q_size q) (live_blocks rho (rev (a_tags cd)) (g_env g))
            /\ 0 < rho (q_tag q) /\ rho (q_tag q) + q_size q < 2 ^ 63
            /\ (exists rg, mget (s_mem S) (q_tag q) = Some rg /\ rg_abs rg = None /\ 0 < to_Z (rg_size rg) /\ rg_wr rg = true).
Proof.
  intros HF HR Hq E0. destruct (q_sound rho S m q HR Hq) as (rg & bs & Eg & _ & _ & _ & Hh).
  destruct (Hh E0) as (Ea & Es & Hwr & Hne & Hpos & Hr0 & Hr1).
  destruct (heap_block_in LB lo B sp0 m0 g rho cd (s_mem S) (s_next S) m (q_tag q) rg (q_size q) HF Eg Ea Es Hne) as [p Hp].
  exists p. split; [exact Hp|]. split; [exact Hr0|]. split; [exact Hr1|]. exists rg. split; [exact Eg|]. split; [exact Ea|]. split; [lia | exact Hwr].
Qed.

Local Ltac qin := unfold QS; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma bs_ptr (rho : valuation) (tag : int) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  Forall2 (kb_ok rho) (kbs_ptr tag) bs -> bs = cells_bytes [C8 (wz (rho tag))].
Proof. intros H0 H1 H. cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (kbs_ptr_bytes rho tag bs); [lia | exact H]. Qed.

Lemma bs_lit8 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 8 z) bs -> bs = cells_bytes [C8 (wz z)].
Proof.
  intros Hz H. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (kbs_Z_bytes rho 8 z bs ltac:(lia) H).
  unfold le8, word_to_le_bytes, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity.
Qed.

Lemma bs_lit4 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  Forall2 (kb_ok rho) (kbs_Z 4 z) bs -> bs = le4 (wz z).
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 4 z bs ltac:(lia) H). unfold le4, wz. rewrite Z_to_bv_unsigned, bv_wrap_small by exact Hz. reflexivity. Qed.

Lemma bs_lit1 (rho : valuation) (z : Z) (bs : list byte) : 0 <= z ->
  Forall2 (kb_ok rho) (kbs_Z 1 z) bs -> bs = [Z_to_bv 8 z].
Proof. intros Hz H. rewrite (kbs_Z_bytes rho 1 z bs Hz H). reflexivity. Qed.

Lemma F2_nil (rho : valuation) (bs : list byte) : Forall2 (kb_ok rho) [] bs -> bs = cells_bytes [].
Proof. intros H. inversion H. reflexivity. Qed.

Lemma F2_ptr (rho : valuation) (tag : int) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 < rho tag -> rho tag < 2 ^ 63 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_ptr tag ++ ks) bs -> bs = cells_bytes (C8 (wz (rho tag)) :: cs).
Proof.
  intros H0 H1 Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_ptr rho tag b1 H0 H1 F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit8 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 8 z ++ ks) bs -> bs = cells_bytes (C8 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. pose proof (bs_lit8 rho z b1 Hz F1) as E. cbn [cells_bytes cbytes] in E. rewrite app_nil_r in E. exact E.
Qed.

Lemma F2_lit4 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z < 2 ^ 64 ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 4 z ++ ks) bs -> bs = cells_bytes (C4 (wz z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit4 rho z b1 Hz F1).
Qed.

Lemma F2_lit1 (rho : valuation) (z : Z) (ks : list kb) (cs : list Cells.cell) (bs : list byte) : 0 <= z ->
  (forall bs', Forall2 (kb_ok rho) ks bs' -> bs' = cells_bytes cs) ->
  Forall2 (kb_ok rho) (kbs_Z 1 z ++ ks) bs -> bs = cells_bytes (C1 (Z_to_bv 8 z) :: cs).
Proof.
  intros Hz Hk H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & F1 & F2). cbn [cells_bytes cbytes].
  rewrite (Hk b2 F2). f_equal. exact (bs_lit1 rho z b1 Hz F1).
Qed.

Lemma F2_bytes (rho : valuation) (zs : list Z) (bs : list byte) :
  Forall2 (kb_ok rho) (kbs_bytes zs) bs -> bs = cells_bytes [CB (length zs) (map (Z_to_bv 8) zs)].
Proof. intros H. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact (kbs_bytes_bytes rho zs bs H). Qed.

Lemma F2_tail (rho : valuation) (ks : list kb) (bs : list byte) (P : list byte -> Prop) :
  (forall bs', Forall2 (kb_ok rho) (ks ++ []) bs' -> P bs') -> Forall2 (kb_ok rho) ks bs -> P bs.
Proof. intros H F. apply H. rewrite app_nil_r. exact F. Qed.

Theorem hx_final_bg_facts (LB : list block) (lo B sp0 : Z) (m0 m' : word -> option byte) (OW' : list block) :
  hx_final LB lo B sp0 m0 m' OW' -> bg_init_facts m' OW'.
Proof.
  intros (g & rho & HRall & HF & ->). pose proof (HRall rho (agree_below_refl _ _)) as HR.

  assert (Hin_mk : In (Q_mk) QS) by qin.
  destruct (q_block LB lo B sp0 m0 g rho cd_end S_end m' (Q_mk) HF HR (fin_q (Q_mk) Hin_mk) eq_refl) as (p8 & I8 & P8 & L8 & G8).
  assert (Hin_sa : In (Q_sa) QS) by qin.
  destruct (q_block LB lo B sp0 m0 g rho cd_end S_end m' (Q_sa) HF HR (fin_q (Q_sa) Hin_sa) eq_refl) as (p9 & I9 & P9 & L9 & G9).
  assert (Hin_nd : In (Q_nd) QS) by qin.
  destruct (q_block LB lo B sp0 m0 g rho cd_end S_end m' (Q_nd) HF HR (fin_q (Q_nd) Hin_nd) eq_refl) as (p10 & I10 & P10 & L10 & G10).
  assert (Hin_es : In (Q_es) QS) by qin.
  destruct (q_block LB lo B sp0 m0 g rho cd_end S_end m' (Q_es) HF HR (fin_q (Q_es) Hin_es) eq_refl) as (pE & IE & PE & LE & GE).
  cbn [q_tag q_size Q_mk Q_sa Q_nd Q_es] in I8, I9, I10, IE, P8, P9, P10, PE, L8, L9, L10, LE.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hheap & _).

  remember (live_blocks rho (rev (a_tags cd_end)) (g_env g)) as OW eqn:EOW. clear EOW.
  exists (mkEA (rho (T 2)) (rho (T 3)) (rho (T 4)) (rho (T 1543)) p8 p9 p10 pE).
  cbn [ea_MK ea_SA ea_ND ea_ES ea_pk ea_ps ea_pn ea_pe ea_ids].
  split.
  { assert (HndOW : List.NoDup (map blk_id OW)).
    { pose proof (RMalloc_ifaceP.RHEAP_blocks_nodup_proof _ _ _ Hheap) as ND. rewrite map_app in ND. exact (List.NoDup_app_remove_r _ _ ND). }
    apply (nodup_ids_of_addrs OW [(p8, rho (T 2), 72); (p9, rho (T 3), 32); (p10, rho (T 4), 128); (pE, rho (T 1543), 904)] HndOW).
    - intros b Hb. cbn [In] in Hb.
      destruct Hb as [<-|Hb]; [exact I8|]. destruct Hb as [<-|Hb]; [exact I9|]. destruct Hb as [<-|Hb]; [exact I10|]. destruct Hb as [<-|Hb]; [exact IE|]. destruct Hb.
    - change (List.NoDup (map rho TAGS4)). apply (rho_nodup rho (s_mem S_end) m' TAGS4 HR fin_tags).
      intros t Ht. unfold TAGS4 in Ht. cbn [In] in Ht.
      destruct Ht as [<-|Ht]; [exact G8|]. destruct Ht as [<-|Ht]; [exact G9|]. destruct Ht as [<-|Ht]; [exact G10|]. destruct Ht as [<-|Ht]; [exact GE|]. destruct Ht. }

  assert (HL8 : forall q z, In q QS -> q_ks q = kbs_Z 8 z -> 0 <= z < 2 ^ 64 -> ro_cells bgusegs m' (q_addr rho q) [C8 (wz z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S_end m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz z)])); [|exact H]. intros b' H'. exact (F2_lit8 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL1 : forall q z, In q QS -> q_ks q = kbs_Z 1 z -> 0 <= z -> ro_cells bgusegs m' (q_addr rho q) [C1 (Z_to_bv 8 z)]).
  { intros q z Hin Ek Hz. apply (q_cells rho S_end m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C1 (Z_to_bv 8 z)])); [|exact H]. intros b' H'. exact (F2_lit1 rho z [] [] b' Hz (F2_nil rho) H'). }
  assert (HL44 : forall q z1 z2, In q QS -> q_ks q = kbs_Z 4 z1 ++ kbs_Z 4 z2 -> 0 <= z1 < 2 ^ 64 -> 0 <= z2 < 2 ^ 64 ->
                   ro_cells bgusegs m' (q_addr rho q) [C4 (wz z1); C4 (wz z2)]).
  { intros q z1 z2 Hin Ek Hz1 Hz2. apply (q_cells rho S_end m' q _ HR (fin_q q Hin)); [cbn; tauto|]. rewrite Ek. intros bs H.
    eapply (F2_lit4 rho z1); [exact Hz1 | | exact H]. intros b1 H1.
    eapply (F2_tail rho _ b1 (fun b => b = cells_bytes [C4 (wz z2)])); [|exact H1]. intros b' H'. exact (F2_lit4 rho z2 [] [] b' Hz2 (F2_nil rho) H'). }
  split.
  { unfold crypto_statics.
    split; [exact (HL8 Q_got_malloc _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_got_free _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_memset_func _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_malloc_impl _ ltac:(qin) eq_refl ltac:(lia))|].
    split; [exact (HL8 Q_free_impl _ ltac:(qin) eq_refl ltac:(lia))|].
    exact (HL1 Q_no_customize _ ltac:(qin) eq_refl ltac:(lia)). }
  split.
  {
    split.
    - unfold err_statics.
      split; [exact (HL1 Q_stopped _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL8 Q_optsdone _ ltac:(qin) eq_refl ltac:(lia))|].
      split; [exact (HL44 Q_base_once _ _ ltac:(qin) eq_refl ltac:(lia) ltac:(lia))|].
      split; [exact (HL44 Q_master_once _ _ ltac:(qin) eq_refl ltac:(lia) ltac:(lia))|].
      exact (HL8 Q_tcb_tsd _ ltac:(qin) eq_refl ltac:(lia)).
    - unfold err_mem. cbn [ea_MK ea_SA ea_ND ea_ES ea_pk ea_ps ea_pn ea_pe].
      split; [exact I8|]. split; [exact I9|]. split; [exact I10|]. split; [exact IE|].
      split.
      { assert (Hin : In Q_tsd2 QS) by qin. apply (q_cells rho S_end m' Q_tsd2 _ HR (fin_q Q_tsd2 Hin)); [cbn; tauto|].
        intros bs H. eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz (rho (T 2)))])); [|exact H]. intros b' H'.
        exact (F2_ptr rho (T 2) [] [] b' P8 ltac:(lia) (F2_nil rho) H'). }
      split.
      { apply (q_cells rho S_end m' Q_mk _ HR (fin_q Q_mk Hin_mk)); [cbn; tauto|].
        intros bs H. eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz (rho (T 3)))])); [|exact H]. intros b' H'.
        exact (F2_ptr rho (T 3) [] [] b' P9 ltac:(lia) (F2_nil rho) H'). }
      split.
      { destruct (q_sound rho S_end m' Q_sa HR (fin_q Q_sa Hin_sa)) as (rg & bs & _ & HFs & Hb & _).
        unfold q_addr in Hb. cbn [q_lo q_tag q_off Q_sa Z.eqb] in Hb. rewrite Z.add_0_r in Hb.
        unfold Q_sa in HFs. cbn [q_ks] in HFs.
        destruct (Forall2_app_split _ _ _ _ HFs) as (b1 & r1 & -> & F1 & HF1).
        destruct (Forall2_app_split _ _ _ _ HF1) as (pad & r2 & -> & F2 & HF2).
        exists pad. split; [cbn [cells_wf cell_wf]; split; [exact I|]; split; [symmetry; exact (Forall2_length F2)|]; cbn; tauto|].
        cbn [cells_bytes cbytes]. rewrite (bs_lit4 rho 1 b1 ltac:(lia) F1) in Hb.
        assert (E2 : r2 = cells_bytes [C8 (wz 0); C8 (wz 1); C8 (wz (rho (T 4)))]).
        { eapply (F2_lit8 rho 0); [lia | | exact HF2]. intros b3 H3.
          eapply (F2_lit8 rho 1); [lia | | exact H3]. intros b4 H4.
          eapply (F2_tail rho _ b4 (fun b => b = cells_bytes [C8 (wz (rho (T 4)))])); [|exact H4]. intros b' H'.
          exact (F2_ptr rho (T 4) [] [] b' P10 ltac:(lia) (F2_nil rho) H'). }
        rewrite E2 in Hb. exact Hb. }
      split.
      { pose proof (q_cells rho S_end m' Q_nd [C8 (wz (rho (T 1543)))] HR (fin_q Q_nd Hin_nd) ltac:(cbn; tauto)) as X.
        unfold q_addr in X. cbn [q_lo q_tag q_off Q_nd Z.eqb] in X. rewrite Z.add_0_r in X. apply X.
        intros bs H. eapply (F2_tail rho _ bs (fun b => b = cells_bytes [C8 (wz (rho (T 1543)))])); [|exact H]. intros b' H'.
        exact (F2_ptr rho (T 1543) [] [] b' PE ltac:(lia) (F2_nil rho) H'). }
      pose proof (q_rw_cells rho S_end m' Q_es [CB 904 ES_CLEARED] HR (fin_q Q_es Hin_es) eq_refl ltac:(cbn; tauto) eq_refl) as X.
      cbn [q_tag q_off Q_es] in X. rewrite Z.add_0_r in X. apply X. intros bs H. rewrite (F2_bytes rho _ bs H). reflexivity. }

  exact (exit_cells_final rho S_end m' exit_ok_end HR).
Qed.

End Final.

Corollary hx_rinit_bg {CE__ : Ceiling} {RN__ : RunRnd} {LM : LibModel} {LSP : LibSpec} :
  rmalloc_stmt -> RRealloc_iface.rrealloc_stmt ->
  forall ls0 : LS, lib_init = LibOps.init_of_ops (map dec_op OPS) ls0 ->
  LIBW = LIBW_HX -> to_Z STK <= LIB_STACK ->
  (forall m, lib_pristine m -> hx_pristine m) ->
  (forall m OW, bg_init_facts m OW -> lib_inv ls0 m OW) ->
  rinit_stmt.
Proof.
  intros HM HRe ls0 Hinit HW HS HP HI. apply (hx_rinit HM HRe ls0 Hinit HW HS HP).
  intros LB lo B sp0 m0 m' OW' Hfin. apply HI. exact (hx_final_bg_facts LB lo B sp0 m0 m' OW' Hfin).
Qed.

