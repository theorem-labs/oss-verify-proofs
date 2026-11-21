(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (17 recorded proofs replaced by written proofs (pans_mem_range, mrun_ret, mrun_peek and 14 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocTree () := "C35stdpp4base7is_SomeC35stdpp4base6LookupI59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I35stdpp8fin_maps6FinMap00C35stdpp8fin_maps7MapFoldC35stdpp8fin_maps:map_insertC35stdpp4base5EmptyC35stdpp4base4FMapC35stdpp4base4OMapC35stdpp4base6InsertC35stdpp4base<PartialAlterC35stdpp4base5MergeI35stdpp4gmap4gmap00C35stdpp8fin_maps:map_eq_iffC59OSSVerify5KrLib4Spec6Malloc4cptrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC35stdpp4gmap:gmap_emptyC35stdpp4gmapBgmap_partial_alterC35stdpp4gmap9gmap_foldC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3powK46Stdlib9micromega6VarMap1t01c59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib6Malloc:MallocTree4mrunC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec5STree5stree01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I59OSSVerify5KrLib4Spec6Malloc<undef_reason00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5STree8steq_indC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree4steq00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree4steq01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree4steq02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4prunC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc:MallocTree7leaf_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl6followC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec5STree5erunsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec:MallocCtrl4pselC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02c59OSSVerify5KrLib6Malloc:MallocTree8pupd_memC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc:MallocTree9mrun_peekC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2or00C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef:Forall_indK47Corelib4Init5Logic4True01c59OSSVerify5KrLib6Malloc:MallocTree7ptrs_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_free_meta_headC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc:MallocTree7optr_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<c_avail_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBc_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6g_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_prevC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC45stdpp7numbers1Z6eq_decC35stdpp9countable;N_countableC35stdpp9countable;Z_countableC59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec6Malloc;iv_disjointC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC46Stdlib5Lists4List>forallb_forallC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z3lebC46Stdlib4Bool4Bool8orb_propC56Stdlib6ZArith6BinInt1Z6leb_leK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init9Datatypes3sndK46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes3orbC47Corelib4Init5Logic5proj2C46Stdlib4Bool4Bool:orb_true_rc59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02c59OSSVerify5KrLib6Malloc:MallocTreeAranges_free_introC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List:in_map_iffI35stdpp4base<list_elem_of00C35stdpp4base7elem_ofC35stdpp4base?list_elem_of_InC35stdpp4gmap9gmap_fmapC35stdpp4gmap9gmap_omapC35stdpp4gmap:gmap_mergeC35stdpp4gmap;gmap_finmapC35stdpp8fin_mapsCelem_of_map_to_listK47Corelib4Init5Logic2or02C46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps;map_to_listI59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List8map_consc59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc:MallocTree>In_live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr04I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9in_app_orC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic7f_equalK46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00K59OSSVerify5KrLib4Spec6Malloc5rkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition mem := word -> option byte.

Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
  match o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
(* [comment removed for export] *)
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.

Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
  intros. unfold pans_mem. destruct (o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists ans o', follow (mrun o t) ans = Some (o', r).

Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.

Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  intros He (ans & o' & H). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
  destruct e; cbn [psel]; try exact H; destruct He.
Qed.

Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
  leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. intros (ans & o' & H). exists ans, o'. rewrite mrun_peek. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
  match p, r with
  | None, None => True
  | Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
  | _, _ => False
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AUXV_CELL : Z := LIBC + 8.

Definition auxv_list (x3 x4 x5 x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

(* [comment removed for export] *)
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => ps_brk s = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
  match p with Some q => P (fst q) | None => True end.

Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
             /\ optr_in P (m_mem (get_meta_rec st g)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).

Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
  intros HP (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; destruct (H8 g) as (X1 & X2 & X3); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < ATOP /\ ranges_free (live_ranges st) a 1 = true.

Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
  a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
Lemma fresh_image st a : fresh_addr st a -> s_reserved st = agent_reserved -> a < 0x10000 \/ 0x1b000 <= a.
Proof.
  intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)). lia.
Qed.

(* [comment removed for export] *)
Lemma fresh_addr_anti st st' a :
  s_reserved st' = s_reserved st ->
  (forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  fresh_addr st' a -> fresh_addr st a.
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. destruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.

End CANSEC1.
