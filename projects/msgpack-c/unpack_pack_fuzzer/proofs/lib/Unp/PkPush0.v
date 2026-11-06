(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib GWin PkStack PkAux PkU PkUSem PkCost.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL PkStack PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkPush0.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Hypothesis CW3' : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m -> cw_holds CW 3 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Local Ltac inl := cbn [In]; repeat (first [left; reflexivity| right]).

Lemma root_type_lit_sound E fs (Hfs : facts_hold E fs) v t :
  root_type_lit fs v = Some t -> den E v = den E (VL t).
Proof.
  unfold root_type_lit, dec_true. intros H. destruct v as [c| | | | | | | | | |]; try (injection H as <-; reflexivity).
  all: match type of H with (if match ?d with _ => _ end then _ else _) = _ =>
         destruct d as [[|]|] eqn:D7;
         [ injection H as <-; pose proof (decide_eq_sound E fs Hfs _ _ _ D7) as X; apply (proj1 (eqb_iff _ _ true)) in X; exact X | |] end.
  all: match type of H with (if match ?d with _ => _ end then _ else _) = _ =>
         destruct d as [[|]|] eqn:D8; try discriminate H;
         injection H as <-; pose proof (decide_eq_sound E fs Hfs _ _ _ D8) as X; apply (proj1 (eqb_iff _ _ true)) in X; exact X end.
Qed.

Lemma push0_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> push0_apply st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP.
  unfold push0_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct ee as [|kT oT| | | | | | | | |]; try discriminate.
  destruct eb as [|kB oB| | | | | | | | |]; try discriminate.
  destruct ecap as [|kE offC| | | | | | | | |]; try discriminate.
  destruct (root_type_lit (s_facts st) rootT) as [t|] eqn:RTL; [|discriminate].
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  cbv zeta in AP.
  destruct (cell_at rT 0 8%uint63) as [np|] eqn:CNP; [|discriminate].
  destruct (cell_at rT 8 8%uint63) as [nn|] eqn:CNN; [|discriminate].
  destruct (flags_at rT 16) as [f|] eqn:CF; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (PkU.pku_flip (s_facts st) (fun _ => true) true ws) as [wsF|] eqn:FLIP; [|discriminate AP].
  injection AP as <-.
  apply andb_prop in COND as [COND DFL]. apply andb_prop in COND as [COND DNN]. apply andb_prop in COND as [COND DNP].
  apply andb_prop in COND as [COND W]. apply andb_prop in COND as [COND HI]. apply andb_prop in COND as [COND LO].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND EX]. apply andb_prop in COND as [COND T78].
  apply andb_prop in COND as [COND LC]. apply andb_prop in COND as [COND TC].
  apply andb_prop in COND as [COND K1]. apply andb_prop in COND as [COND K0]. apply andb_prop in COND as [COND KTE]. apply andb_prop in COND as [COND KTB].
  apply andb_prop in COND as [COND OB]. apply andb_prop in COND as [COND OT].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply (proj1 (weqb_ok _ _)) in OT. apply (proj1 (weqb_ok _ _)) in OB. subst oT oB. apply Z.ltb_lt in WLEN.
  apply Uint63.eqb_correct in KTB. apply Uint63.eqb_correct in KTE. subst kB kE.
  apply negb_true_iff in K0. apply negb_true_iff in K1. apply negb_true_iff in TC. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  apply Uint63.leb_spec in LC. change (to_Z 24%uint63) with 24 in LC.
  apply existsb_exists in EX as (w24 & INw24 & EQ24). apply win3_eqb_eq in EQ24. subst w24.
  set (ismap := weqb t (wlit 8)) in *.

  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  change (v_end (k_evec g) = bv_unsigned (den E (VP kT wzero))) in Lee.
  change (v_begin (k_evec g) = bv_unsigned (den E (VP kT wzero))) in Leb.
  change (v_capend (k_evec g) = bv_unsigned (den E (VP kT offC))) in Lecap.
  change (obj_type (k_tree g) = bv_unsigned (den E rootT)) in LT. rewrite (root_type_lit_sound E (s_facts st) Pfacts rootT t RTL) in LT.
  change (obj_cnt (k_tree g) = bv_unsigned (den E n1)) in LN.
  change (obj_ptr (k_tree g) = bv_unsigned (den E P1)) in LP.
  cbn [den] in LT. rewrite wbv_unsigned in LT.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).

  assert (T78' : obj_type (k_tree g) = 7 \/ obj_type (k_tree g) = 8).
  { rewrite LT. apply orb_prop in T78 as [T7|T8]; [left| right]; apply (proj1 (weqb_ok _ _)) in T7 || apply (proj1 (weqb_ok _ _)) in T8; subst t; rewrite wlit_ok; reflexivity. }
  destruct (obj_type_cont (k_tree g) T78') as [FCONT FMAP].
  assert (ISM : ismap = is_mapo (k_tree g)).
  { subst ismap. destruct (is_mapo (k_tree g)) eqn:IM.
    - apply (proj2 (weqb_w2Z _ _)). pose proof (proj1 FMAP eq_refl) as T8. rewrite LT in T8. rewrite wlit_ok. exact T8.
    - destruct (weqb t (wlit 8)) eqn:Q; [exfalso| reflexivity]. apply (proj1 (weqb_ok _ _)) in Q. subst t.
      rewrite wlit_ok in LT. change (to_Z 8%uint63) with 8 in LT. pose proof (proj2 FMAP LT) as X. discriminate X. }

  assert (HIZg : forall Ex, hiZ Ex rT = 24) by (intros Ex; unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (HIZg E) as HIZ24.
  assert (LOZ0 : loZ rT = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ (Preg kT rT FT) K0) as [RR1 RR2]. rewrite HIZ24 in RR2. rewrite LOZ0 in RR1.
  assert (KV : bv_unsigned (ev E kT) = v_begin (k_evec g)) by (rewrite Leb; symmetry; exact (den_VP0 E kT wzero (weqb_refl _))).
  assert (EE : v_end (k_evec g) = v_begin (k_evec g)) by (rewrite Lee, Leb; reflexivity).
  assert (LS0 : ls = []).
  { unfold v_end in EE. rewrite EL, SZ in EE. unfold ELEM_SIZE in EE. destruct ls; [reflexivity| cbn [length] in EE; lia]. }
  subst ls.
  assert (OFFC : w2Zs offC = to_Z (wl offC)) by (rewrite w2Zs_eq; unfold w2Z; rewrite TC; lia).
  pose proof (int_range (wl offC)) as RC.
  assert (CAPE : v_capend (k_evec g) = v_begin (k_evec g) + to_Z (wl offC)).
  { assert (D : v_capend (k_evec g) = (bv_unsigned (ev E kT) + w2Zs offC) mod two64) by (rewrite Lecap; apply den_VP).
    rewrite KV, OFFC in D. rewrite Z.mod_small in D; [exact D|].

    pose proof (bv_unsigned_in_range _ (den E (VP kT offC))) as R. rewrite bv_modulus_64, <- Lecap in R. unfold two64, two63 in *.
    split; [lia|].
    destruct (Z.lt_ge_cases (v_begin (k_evec g) + to_Z (wl offC)) 18446744073709551616) as [X|X]; [exact X| exfalso].
    rewrite <- (Z_mod_plus_full _ (-1)) in D. rewrite Z.mod_small in D by lia. unfold v_capend in D. destruct VE as [(B0 & C0 & _)|[(VV1 & _) (CP & _)]]; [rewrite B0, C0 in D; lia|].
      rewrite EL in D. unfold ELEM_SIZE in D. nia. }
  assert (VVX : vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g))).
  { destruct VE as [(B0 & C0 & _)|X]; [exfalso| exact X]. unfold v_capend in CAPE. rewrite B0, C0 in CAPE. lia. }
  destruct VVX as [(VX1 & VX2 & VX3 & VX4) (CP & CP2)].
  assert (CAPB : v_capend (k_evec g) = v_begin (k_evec g) + v_bytes (k_evec g)) by (unfold v_capend, v_bytes; lia).
  assert (ROOMS : 0 + 1 <= v_cap (k_evec g)) by lia.
  assert (ROOM : v_begin (k_evec g) + 24 <= v_capend (k_evec g)) by (unfold v_capend; rewrite EL; unfold ELEM_SIZE; clear - CP; nia).
  pose proof (owned_evec g VX3) as OWN.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (B1 & B2 & B3 & B4 & _). cbn [fst snd] in B1, B2, B3.

  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 0 np (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) CNP)) as Unp.
  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 8 nn (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) CNN)) as Unn.
  rewrite Z.add_0_r in Unp. rewrite KV in Unp, Unn.
  rewrite (deq_sound E _ _ _ Pfacts DNP) in Unp. rewrite (deq_sound E _ _ _ Pfacts DNN) in Unn.
  destruct (flags_sound segs E (s_priv st) (ms_mem ms) kT rT 16 f ismap (s_facts st) (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) Pfacts CF DFL) as [Ufl0 Ufl1].
  rewrite KV in Ufl0, Ufl1.
  assert (MATB : forall a, v_begin (k_evec g) <= a < v_begin (k_evec g) + 24 -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model _ a HA (proj1 O _ OWN)). unfold in_iv. cbn [fst snd]. lia. }
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws) _ a DEC)). auto. }
  set (rN := top_region P1 n1 ismap ismap) in *.
  assert (HIN : forall Ex, hiZ Ex rN = 24) by (intros Ex; reflexivity).
  assert (LON : loZ rN = 0) by reflexivity.
  assert (LEN' : Z.of_nat (length ws) < two63) by (unfold two63; lia).

  destruct (PkUSem.flip_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ ws wsF FLIP) as (LENfl & INWS1 & KEEP1 & WF1 & WK1 & GH1 & CO1).
  assert (LENF : Z.of_nat (length wsF) < two63) by (rewrite LENfl; exact LEN').
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kT] [(kT, rN)] (mk_args 3%uint63 aw wsF _) (p1_align P1) (s_next st)).
  - intros k' [<-|[]]. split; [exact K0|]. exists rT. auto.
  - constructor; [intros []| constructor].
  - intros k' r' [H|[]]. injection H as <- <-. exact K0.
  -
    intros k' r' [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) kT rN K0).
    + subst rN. cbn [top_region rg_cells]. apply IMap.bst_add. apply IMap.bst_add. apply IMap.bst_add. exact I.
    + reflexivity.
    + rewrite KV, LON. lia.
    + rewrite KV, HIN. lia.
    + intros a Ha. rewrite KV, LON, HIN in Ha. apply MATB. lia.
    + intros gk gr F. destruct (top_region_find _ _ _ _ gk gr F) as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [g_cells].
      * change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E (ms_mem ms) (bv_unsigned (ev E kT)) 0%uint63 _ (bv_unsigned (den E P1))); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, KV. exact Unp.
           ++ reflexivity.
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 1%uint63) with 1. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E (ms_mem ms) (bv_unsigned (ev E kT) + 8 * 1) 0%uint63 _ (bv_unsigned (den E n1))); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, KV. replace (v_begin (k_evec g) + 8 * 1) with (v_begin (k_evec g) + 8) by lia. exact Unn.
           ++ reflexivity.
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 2%uint63) with 2. split.
        -- split; [cbn [slot_sorted c_idx c_w]; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; split; [lia| exact (conj I I)]|]. constructor; [| constructor; [|constructor]].
           ++ apply (cell_ok_of_u8 segs E (ms_mem ms) (bv_unsigned (ev E kT) + 8 * 2) 0%uint63 _ (b2Z ismap)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
              ** change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, KV. replace (v_begin (k_evec g) + 8 * 2) with (v_begin (k_evec g) + 16) by lia. exact Ufl0.
              ** rewrite den_b2v. destruct ismap; reflexivity.
           ++ apply (cell_ok_of_u8 segs E (ms_mem ms) (bv_unsigned (ev E kT) + 8 * 2) 1%uint63 _ (b2Z ismap)); [change (to_Z 1%uint63) with 1; lia| change (to_Z 1%uint63) with 1; lia| |].
              ** change (to_Z 1%uint63) with 1. rewrite KV. replace (v_begin (k_evec g) + 8 * 2 + 1) with (v_begin (k_evec g) + 16 + 1) by lia. exact Ufl1.
              ** rewrite den_b2v. destruct ismap; reflexivity.
        -- intros c i [<-|[<-|[]]] Hi; cbn [c_w c_idx] in Hi |- *; change (to_Z 1%uint63) with 1 in *; try change (to_Z 0%uint63) with 0; rewrite LON, HIN; lia.
  -
    intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite LON, HIN in IR.
    right. exists kT, rT. split; [left; reflexivity|]. split; [exact FT|]. unfold inR. rewrite HIZ24, LOZ0. lia.
  - intros k1' r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E aw), (map (wden E) wsF), _, LB.
    split; [apply (mk_args_sound E 3%uint63 aw wsF _ LENF)|]. split; [exact (aw_keep segs IMGX AW _ _ _ _ _ _ HA (KEEP1 LB))|].
    split; [exact (WF1 segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model) WF)|].
    apply CW3'. unfold cw_pk_holds. cbn [unparse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP map decode_pk].
    set (g' := PKG (k_tree g) (vec_inc (k_evec g)) (k_zone g)).
    destruct (vec_inc_valid (k_evec g) (conj VX1 (conj VX2 (conj VX3 VX4))) ltac:(rewrite SZ; cbn [length Z.of_nat]; lia)) as [VVP VEP].
    exists g', [(k_tree g, 0)]. split; [| split; [| split; [| split]]].
    +
      unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
      change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
      split; [cbn [den]; rewrite wbv_unsigned; exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|]. split; [exact Leb|]. split.
      { rewrite VEP, EL, EE. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, KV. change (to_Z 24%uint63) with 24.
        unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small by lia. unfold ELEM_SIZE. lia. }
      split; [exact Lecap|]. split.
      * unfold last_opt. cbn [rev app]. rewrite !den_b2v, ISM, <- LP, <- LN.
        destruct (k_tree g); try discriminate FCONT; unfold elem_of; cbn [pe_ptr pe_rest pe_map pe_key obj_ptr okids obj_cnt is_mapo b2Z];
          rewrite ?Zdiv_0_l, ?Z.mul_0_r, ?Z.add_0_r, ?Z.sub_0_r; repeat split; reflexivity.
      * intros X. exfalso. apply X. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
    +
      unfold pure_pk. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
      split.
      { cbn [levels_ok]. split; [reflexivity|]. split; [exact FCONT|]. split; [lia|].
        destruct (nth_error (okids (k_tree g)) (Z.to_nat 0)) as [k0|] eqn:NK; [exact I|].
        split; [reflexivity|]. split; [| reflexivity]. destruct (okids (k_tree g)) as [|x xs] eqn:OK; [reflexivity| cbn in NK; discriminate NK]. }
      split; [exact EL|]. split; [cbn [vec_inc v_size length Z.of_nat]; rewrite SZ; reflexivity|].
      split; [right; exact (conj VVP (conj CP CP2))|]. split; [| exact ZV]. change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)). exact CE.
    +   exact O.
    +
      apply (WK1 g').
      unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx) NS) as [D|[NB ET]]; [left; exact D| right].
      split; [exact NB|]. destruct ET as (K6 & _). pose proof (only_kind_sound E 6 _ ws OK6 x Hx ltac:(unfold K_ETOP in K6; exact K6)) as [= <-].
      rewrite etop_win_den, KV. unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_inc (k_evec g)). rewrite VEP, EL, EE.
      change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)).
      change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity].
    +
      split; [| split].
      2: { apply (GH1 g'). destruct GH as [SE EP]. split; [exact SE|]. intros _. exists (wden E (etop_win kT 24)). split; [apply in_map; exact INw24|].
           rewrite etop_win_den, KV. unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_inc (k_evec g)). rewrite VEP, EL, EE.
           change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)).
           change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity]. }
      2: {
           apply (CO1 _ g [] _ g' [(k_tree g, 0)] CO). intros fr v _ LE. cbn [a_cf den]. rewrite wbv_unsigned, wzero_ok. change (0 =? 0) with true.
           change (k_tree g') with (k_tree g). erewrite (PkCost.np_push0 (k_tree g)). exact LE. }
      unfold mem_pk. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
      change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). cbn [a_root removelast]. cbn [a_root] in ICB.
      split; [exact TW|]. split; [exact KA|]. split; [exact ICB|]. split; [exact CH|]. intros _. exact I.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E) wsF) _ a (mk_args_sound E 3%uint63 aw wsF _ LENF))) in FPa as (RA & NI & NWF).
    assert (NW : ~ in_ws (map (wden E) ws) a) by (intros X; apply NWF; apply INWS1; exact X).
    split; [left; exact (FPold a RA NI NW)|].
    intros k' r' [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite LON, HIN, KV in IR.
    apply NW. apply in_ws_map_iff. exists (etop_win kT 24). split; [exact INw24|].
    rewrite etop_win_den, KV. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. change (to_Z 24%uint63) with 24. lia.
  -
    unfold p1_align. destruct P1 as [|kP oP| | | | | | | | |]; try constructor.
    destruct (weqb oP wzero && negb (PrimInt63.eqb kP 0%uint63)) eqn:C; [|constructor].
    apply andb_prop in C as [C1 _]. apply (proj1 (weqb_ok _ _)) in C1. subst oP.
    constructor; [|constructor]. cbn [fact_holds]. change (2 ^ to_Z 3%uint63) with 8.
    rewrite <- (den_VP0 E kP wzero (weqb_refl _)), <- LP.
    destruct (k_tree g) as [| ? | ? | ? | ? | ? | ? ? | ? ? | ? ? | p kids | p kids] eqn:KT; try discriminate FCONT; cbn [obj_ptr].
    + apply tree_wf_arr in TW. destruct TW as (_ & E0 & NE & _).
      destruct kids as [|k0 ks0]; [rewrite (proj1 E0 eq_refl); reflexivity | exact (proj1 (NE ltac:(discriminate)))].
    + apply tree_wf_map in TW. destruct TW as (_ & _ & E0 & NE & _).
      destruct kids as [|k0 ks0]; [rewrite (proj1 E0 eq_refl); reflexivity | exact (proj1 (NE ltac:(discriminate)))].
Qed.

Theorem push0_sound : forall pc, contract_sound segs OPS MP PB (push0_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [push0_contract c_apply] in HAP.
  destruct (push0_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. apply (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP).
       exact (push0_sound_main E st ms model st' HS AP). }
  all: exfalso; unfold push0_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End PkPush0.
