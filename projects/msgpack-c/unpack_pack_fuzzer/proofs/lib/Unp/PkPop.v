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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree KidsFacts PkOps PkLib GLib GWin PkStack PkAux.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkU PkUSem PkCost.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL PkStack PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkPop.

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

Lemma pop_sound_main : forall all E st ms model sts,
  st_ok segs OPS E st ms model -> pop_apply_g all st = Some sts ->
  exists st' E', In st' sts /\ env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros all E st ms model sts HS0 AP.
  unfold pop_apply_g in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct ee as [|kT oT| | | | | | | | |]; try discriminate.
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND DNE]. apply andb_prop in COND as [COND IMPL]. apply andb_prop in COND as [COND DEQ].
  apply andb_prop in COND as [COND W]. apply andb_prop in COND as [COND HI]. apply andb_prop in COND as [COND LO].
  apply andb_prop in COND as [COND EX]. apply andb_prop in COND as [COND K1].
  apply andb_prop in COND as [COND K0]. apply andb_prop in COND as [COND OT].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply (proj1 (weqb_ok _ _)) in OT. subst oT. apply Z.ltb_lt in WLEN.
  apply negb_true_iff in K0. apply negb_true_iff in K1. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with 4611686018427387896 in NLT.
  assert (N62 : to_Z (s_next st) < to_Z bit62i) by (change (to_Z bit62i) with 4611686018427387904; lia).
  apply existsb_exists in EX as (w24 & INw24 & EQ24). apply win3_eqb_eq in EQ24. subst w24.
  set (n := s_next st) in *.
  pose proof (to_Z_add_small n 1%uint63 N62 ltac:(change (to_Z 1%uint63) with 1; lia)) as AD1.
  pose proof (to_Z_add_small n 2%uint63 N62 ltac:(change (to_Z 2%uint63) with 2; lia)) as AD2.
  pose proof (to_Z_add_small n 3%uint63 N62 ltac:(change (to_Z 3%uint63) with 3; lia)) as AD3.
  change (to_Z 1%uint63) with 1 in AD1. change (to_Z 2%uint63) with 2 in AD2. change (to_Z 3%uint63) with 3 in AD3.

  pose proof HS0 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
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
  change (v_end (k_evec g) = bv_unsigned (den E (VP kT (wlit 24%uint63)))) in Lee.
  change (v_begin (k_evec g) = bv_unsigned (den E eb)) in Leb.
  change (v_capend (k_evec g) = bv_unsigned (den E ecap)) in Lecap.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).

  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; eb; VP kT (wlit 24%uint63); ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INAW : In aw (op_args o)) by (rewrite ARGS; right; left; reflexivity).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (KTn : PrimInt63.ltb kT n = true) by exact (VBo (VP kT (wlit 24%uint63)) (INCA _ ltac:(do 7 right; left; reflexivity))).
  assert (DRgen : forall E', env_ext n E E' -> forall v, In v (op_args o) -> den E' v = den E v).
  { intros E' HX v Hv. exact (den_reval n E E' HX v (VBo v Hv)). }
  assert (INWS : forall a b c, In (a, b, c) ws -> In a (op_args o) /\ In b (op_args o) /\ In c (op_args o)).
  { intros a b c Hw. destruct (in_flat_windows ws a b c Hw) as (A1 & A2 & A3). rewrite ARGS.
    split; [| split]; right; right; right; apply in_app_iff; left; assumption. }
  assert (WDRgen : forall E', env_ext n E E' -> forall ws1, (forall w, In w ws1 -> In w ws) -> map (wden E') ws1 = map (wden E) ws1).
  { intros E' HX ws1 SUB. apply map_ext_in. intros [[a b] c] Hw. destruct (INWS a b c (SUB _ Hw)) as (A1 & A2 & A3).
    unfold wden. rewrite !(DRgen E' HX) by assumption. reflexivity. }

  assert (HIZg : forall Ex, hiZ Ex rT = 24) by (intros Ex; unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (HIZg E) as HIZ24.
  assert (LOZ0 : loZ rT = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ (Preg kT rT FT) K0) as [RR1 RR2]. rewrite HIZ24 in RR2. rewrite LOZ0 in RR1.
  assert (KV : bv_unsigned (ev E kT) = v_end (k_evec g) - 24).
  { rewrite Lee. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }
  pose proof (PlanS.implied_sound E _ _ Pz Pfacts IMPL) as BEG. cbn [fact_holds] in BEG. rewrite (den_VP0 E kT wzero (weqb_refl _)), <- Leb, KV in BEG.
  assert (NEQ : v_begin (k_evec g) <> v_end (k_evec g) - 24).
  { intros X. unfold dec_false in DNE. destruct (decide_eq (s_facts st) eb (VP kT wzero)) as [[|]|] eqn:D; try discriminate.
    pose proof (proj1 (ValP.eqb_iff _ _ false) (decide_eq_sound E (s_facts st) Pfacts _ _ _ D)) as Q.
    apply Q. apply bv_eq. rewrite (den_VP0 E kT wzero (weqb_refl _)), <- Leb, KV. exact X. }

  assert (VVX : vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g))).
  { destruct VE as [(B0 & C0 & LS0)|X]; [exfalso| exact X]. subst ls. cbn [length Z.of_nat] in SZ.
    unfold v_end in KV. rewrite B0, SZ in KV. lia. }
  destruct VVX as [(VX1 & VX2 & VX3 & VX4) (CP & CP2)].
  assert (LEN2 : 2 <= Z.of_nat (length ls)).
  { unfold v_end in BEG, NEQ. rewrite EL, SZ in BEG, NEQ. unfold ELEM_SIZE in BEG, NEQ. nia. }
  assert (CAPB : v_capend (k_evec g) = v_begin (k_evec g) + v_bytes (k_evec g)) by (unfold v_capend, v_bytes; lia).
  assert (ENDCAP : v_end (k_evec g) <= v_capend (k_evec g)) by (unfold v_end, v_capend; rewrite EL; unfold ELEM_SIZE; nia).
  pose proof (owned_evec g VX3) as OWN.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (B1 & B2 & B3 & B4 & _). cbn [fst snd] in B1, B2, B3.
  assert (E48 : v_begin (k_evec g) + 48 <= v_end (k_evec g)) by (unfold v_end; rewrite EL, SZ; unfold ELEM_SIZE; clear - LEN2; nia).

  assert (SPL : exists ls0 l, ls = ls0 ++ [l]) by (destruct ls as [|x xs] using rev_ind; [cbn in LEN2; lia| eauto]).
  destruct SPL as (ls0 & l & ELS).
  assert (SPL1 : exists ls1 lp, ls0 = ls1 ++ [lp]).
  { destruct ls0 as [|x xs] using rev_ind; [| eauto]. exfalso. subst ls. cbn [app length Z.of_nat] in LEN2. lia. }
  destruct SPL1 as (ls1 & lp & ELS0). subst ls0.
  assert (LENls : Z.of_nat (length ls) = Z.of_nat (length ls1) + 2) by (rewrite ELS, !length_app; cbn [length]; lia).
  assert (LV0 : levels_ok (k_tree g) (ls1 ++ [lp])).
  { rewrite ELS in LV. destruct l as [lo s]. exact (proj1 (proj1 (levels_snoc _ _ _ _) LV)). }
  destruct lp as [lo sp].
  pose proof (proj1 (levels_snoc _ _ _ _) LV0) as (LV1 & FOC1 & LCp & LSp & _).
  assert (NODE : exists kd, nth_error (okids lo) (Z.to_nat sp) = Some kd).
  { rewrite ELS in LV.
    pose proof (levels_nodes _ _ _ LV) as NN. apply Forall_app in NN as [_ NN]. apply Forall_inv in NN. exact NN. }
  destruct NODE as [kd NKD].
  assert (SLT : sp < Z.of_nat (length (okids lo))).
  { assert (Z.to_nat sp < length (okids lo))%nat by (apply nth_error_Some; rewrite NKD; discriminate). lia. }
  pose proof (proj1 (Forall_forall _ _) (levels_wf _ _ _ _ TW LV0) (lo, sp) ltac:(apply in_app_iff; right; left; reflexivity)) as TWL. cbn [fst] in TWL.

  assert (RL : removelast ls = ls1 ++ [(lo, sp)]) by (rewrite ELS, removelast_snoc; reflexivity).
  pose proof (PE VX3) as PEL. rewrite RL, map_app in PEL. cbn [map] in PEL.
  apply (proj1 (pelems_at_app _ _ _ _)) in PEL as [PEL1 PEL2]. rewrite length_map in PEL2.
  cbn [pelems_at] in PEL2. destruct PEL2 as (Up & Ur & Um & Uk & _).
  set (e := elem_of (lo, sp)) in *.
  set (A := v_begin (k_evec g) + ELEM_SIZE * Z.of_nat (length ls1)) in *.
  assert (AV : A = v_end (k_evec g) - 48) by (subst A; unfold v_end; rewrite EL, SZ, LENls; unfold ELEM_SIZE; lia).

  destruct (elem_of_bounds _ _ lo sp LCp LSp SLT TWL) as (ch & Hch & ICH & ERr & EAL). fold e in ICH, ERr, EAL.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (C1 & C2 & C3 & C4 & _).
  assert (EP0 : 0 <= pe_ptr e /\ pe_ptr e + 24 <= two64).
  { clear - ICH C1 C3 C4. unfold in_chunk, chunk_lo, chunk_hi, chunk_block, CHUNK_HDR, OBJ_SIZE in *. cbn [fst snd] in C1, C3. lia. }
  destruct EP0 as [EP0 EPT].

  assert (EPB : 4104 <= pe_ptr e /\ pe_ptr e + 24 <= 4611686018427387904).
  { pose proof (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch)) as INB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA INB) as (Bd1 & Bd2 & Bd3 & Bd4 & Bd5).
    pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA INB) as BLO.
    pose proof (aw_ceiling_small segs IMGX AW model) as CS. unfold Mem.two62Z in CS.
    unfold chunk_block in Bd1, Bd2, Bd3, BLO. cbn [fst snd] in Bd1, Bd2, Bd3, BLO.
    clear - ICH Bd1 Bd2 Bd3 BLO CS. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in *. lia. }

  set (wT := Z_to_bv 64 (v_end (k_evec g) - 48)). set (wP := Z_to_bv 64 (pe_ptr e)). set (wR := Z_to_bv 64 (pe_rest e)).
  set (E' := env_upd (env_upd (env_upd E n wT) (PrimInt63.add n 1) wP) (PrimInt63.add n 2) wR).
  assert (HX : env_ext n E E').
  { subst E'. eapply (env_ext_trans n (PrimInt63.add n 2)); [lia| | apply env_upd_ext].
    eapply (env_ext_trans n (PrimInt63.add n 1)); [lia| | apply env_upd_ext]. apply env_upd_ext. }
  assert (EVn : ev E' n = wT) by (subst E'; rewrite 2!ev_upd_other by lia; apply env_upd_same).
  assert (EVp : ev E' (PrimInt63.add n 1) = wP) by (subst E'; rewrite 1!ev_upd_other by lia; apply env_upd_same).
  assert (EVr : ev E' (PrimInt63.add n 2) = wR) by (subst E'; apply env_upd_same).
  pose proof (DRgen E' HX) as DR. pose proof (WDRgen E' HX) as WDR.
  assert (EVkT : ev E' kT = ev E kT) by exact (ev_reval n E E' HX kT KTn).
  clearbody E'.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  assert (UT : bv_unsigned (ev E' n) = v_end (k_evec g) - 48) by (rewrite EVn; subst wT; apply u64_of_Z; lia).
  assert (UP : bv_unsigned (ev E' (PrimInt63.add n 1)) = pe_ptr e) by (rewrite EVp; subst wP; apply u64_of_Z; lia).
  assert (UR : bv_unsigned (ev E' (PrimInt63.add n 2)) = pe_rest e) by (rewrite EVr; subst wR; apply u64_of_Z; unfold two64; lia).
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).

  set (ws0 := List.filter (fun w => negb (win3_eqb w (etop_win kT 24))) ws) in *.
  assert (SUB0 : forall w, In w ws0 -> In w ws /\ w <> etop_win kT 24%uint63).
  { intros w Hw. apply filter_In in Hw as [Hw NS]. split; [exact Hw|]. intros ->. rewrite win3_eqb_refl in NS. discriminate. }

  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    rewrite (map_ext_in (den E') (den E) (op_args o) DR).
    apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws) _ a DEC)). split; [lia| auto]. }

  assert (SAFE : forall a, a < v_end (k_evec g) - 24 -> PK.safe g (map (wden E) ws) a).
  { intros a Ha w Hw (K6 & _ & _ & E2 & _) Hin. unfold in_iv, w_iv, ELEM_SIZE in *. cbn [fst snd] in Hin. lia. }
  assert (BYTE : forall a, v_end (k_evec g) - 48 <= a < v_end (k_evec g) - 24 ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (pk_owned_byte_props segs IMGX AW _ LB (ms_mem ms) model g (map (wden E) ws) _ a HA WF O Wk OWN).
    - unfold in_iv. cbn [fst snd]. lia.
    - apply SAFE. lia. }

  set (m := pe_map e). set (k := pe_key e).
  assert (MK : (m = false /\ k = false) \/ (m = true /\ k = true) \/ (m = true /\ k = false)).
  { subst m k e. destruct lo; try discriminate LCp; unfold elem_of; cbn [pe_map pe_key]; [left; auto|]. destruct (Z.even sp); auto. }
  destruct (PkU.pku_flip (s_facts st) (fun _ => true) false (ws0 ++ [etop_win n 24])) as [wsF|] eqn:FLIP; [|discriminate AP].
  set (mkB := fun (m k : bool) =>
     repoint_g all (VP kT wzero) (VP n (wlit 24))
       (surg st [kT] [(n, top_region (VP (PrimInt63.add n 1) wzero) (VP (PrimInt63.add n 2) wzero) m k)]
          (mk_args 3 aw wsF
             (unparse_ca (PC root rootT n1 P1 zh c0 eb (VP n (wlit 24)) ecap (VP (PrimInt63.add n 1) wzero) (VP (PrimInt63.add n 2) wzero) (b2v m) (b2v k) (VL wzero) (VL wzero) (VL wzero) (VL wzero))))
          ([FEq (VP n (wlit 24)) (VP kT wzero); FRange (PrimInt63.add n 2) (wlit 1) (wlit 1000); FAlign (PrimInt63.add n 1) 3; FULe eb (VP n wzero); FULe (VP n (wlit 24)) ecap] ++ top_facts (s_facts st) eb n
            ++ KF.kids_facts (VP (PrimInt63.add n 2) wzero) (VP (PrimInt63.add n 1) wzero))
          (PrimInt63.add n 3))).
  assert (STS : sts = [mkB false false; mkB true true; mkB true false]) by (symmetry; exact (f_equal _ AP) || (injection AP as <-; reflexivity)).
  exists (mkB m k), E'. split; [| split; [exact HX|]].
  { rewrite STS. destruct MK as [[-> ->]|[[-> ->]|[-> ->]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity]. }
  subst mkB. cbn beta.
  apply repoint_g_sound; [| cbn [den]; rewrite EVkT, EVn; subst wT; apply bv_eq; rewrite !bv_add_unsigned, !wbv_unsigned, wzero_ok, wlit_ok, Z_to_bv_unsigned;
                           change (to_Z 24%uint63) with 24; unfold bv_wrap; rewrite bv_modulus_64, KV; rewrite (Z.mod_small (v_end (k_evec g) - 48)) by lia;
                           f_equal; lia
                      | reflexivity].
  set (rN := top_region (VP (PrimInt63.add n 1) wzero) (VP (PrimInt63.add n 2) wzero) m k) in *.
  assert (HIN : forall Ex, hiZ Ex rN = 24) by (intros Ex; reflexivity).
  assert (LON : loZ rN = 0) by reflexivity.
  set (wsB := ws0 ++ [etop_win n 24]) in *.
  assert (LENB : Z.of_nat (length wsB) < two63).
  { subst wsB. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w (etop_win kT 24))) ws). unfold two63. subst ws0. lia. }

  destruct (PkUSem.flip_sound E' (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ wsB wsF FLIP) as (LEN1 & INWS1 & KEEP1 & WF1 & WK1 & GH1 & CO1).
  assert (LENF : Z.of_nat (length wsF) < two63) by (rewrite LEN1; exact LENB).
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kT] [(n, rN)] (mk_args 3%uint63 aw wsF _) _ (PrimInt63.add n 3)).
  - intros k' [<-|[]]. split; [exact K0|]. exists rT. auto.
  - constructor; [intros []| constructor].
  - intros k' r' [H|[]]. injection H as <- <-. exact NZ.
  -
    intros k' r' [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n rN NZ).
    + subst rN. cbn [top_region rg_cells]. apply IMap.bst_add. apply IMap.bst_add. apply IMap.bst_add. exact I.
    + reflexivity.
    + rewrite UT, LON. lia.
    + rewrite UT, HIN. lia.
    + intros a Ha. rewrite UT, LON, HIN in Ha. destruct (BYTE a ltac:(lia)) as (_ & _ & _ & MT & NSG). auto.
    + intros gk gr F. destruct (top_region_find _ _ _ _ gk gr F) as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [g_cells].
      * change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 _ (pe_ptr e)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT, <- AV. exact Up.
           ++ exact (eq_trans (den_VP0 E' _ wzero (weqb_refl _)) UP).
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 1%uint63) with 1. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 1) 0%uint63 _ (pe_rest e)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT. replace (v_end (k_evec g) - 48 + 8 * 1) with (A + 8) by lia. exact Ur.
           ++ exact (eq_trans (den_VP0 E' _ wzero (weqb_refl _)) UR).
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 2%uint63) with 2. split.
        -- split; [cbn [slot_sorted c_idx c_w]; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; split; [lia| exact (conj I I)]|]. constructor; [| constructor; [|constructor]].
           ++ apply (cell_ok_of_u8 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 2) 0%uint63 _ (b2Z m)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
              ** change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT. replace (v_end (k_evec g) - 48 + 8 * 2) with (A + 16) by lia. subst m. unfold b2Z. exact Um.
              ** rewrite den_b2v. destruct m; reflexivity.
           ++ apply (cell_ok_of_u8 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 2) 1%uint63 _ (b2Z k)); [change (to_Z 1%uint63) with 1; lia| change (to_Z 1%uint63) with 1; lia| |].
              ** change (to_Z 1%uint63) with 1. rewrite UT. replace (v_end (k_evec g) - 48 + 8 * 2 + 1) with (A + 17) by lia. subst k. unfold b2Z. exact Uk.
              ** rewrite den_b2v. destruct k; reflexivity.
        -- intros c i [<-|[<-|[]]] Hi; cbn [c_w c_idx] in Hi |- *; change (to_Z 1%uint63) with 1 in *; try change (to_Z 0%uint63) with 0; rewrite LON, HIN; lia.
  -
    intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite UT, LON, HIN in IR.
    destruct (BYTE a ltac:(lia)) as (RA & NI & NW & _). left. exact (FPold a ltac:(lia) NI NW).
  - intros k1' r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E' aw), (map (wden E') wsF), _, LB.
    split; [apply (mk_args_sound E' 3%uint63 aw wsF _ LENF)|]. split.
    { rewrite (DR aw INAW). pose proof HA as HA'. rewrite <- (WDR ws ltac:(intros w Hw; exact Hw)) in HA'.
      refine (aw_keep segs IMGX AW _ _ _ _ _ _ (aw_keep segs IMGX AW _ _ _ _ _ _ HA' _) (KEEP1 LB)). apply (UOK.wins_keep_map_intro E' LB ws wsB).
      - intros x Hx. subst wsB. apply in_app_iff in Hx as [Hx|[<-|[]]]; [left; exact (proj1 (SUB0 x Hx))| right; apply UOK.kind_new_sub; reflexivity].
      - intros x Hx. destruct (UOK.filter_old ws [etop_win n 24] (fun w => negb (win3_eqb w (etop_win kT 24))) x Hx) as [H1|F]; [left; exact H1| right].
        apply negb_false_iff in F. apply win3_eqb_eq in F. subst x.
        split; [apply etop_untied|]. intros _ _.
        apply (block_keep_evidence LB _ (v_begin (k_evec g)) (v_bytes (k_evec g)) _ (wden E' (etop_win n 24)) (proj1 O _ OWN)).
        + rewrite etop_win_den. cbn [w_lo]. rewrite EVkT, KV. lia.
        + apply in_map. subst wsB. apply in_app_iff. right. left. reflexivity.
        + apply etop_heap_kind.
        + rewrite etop_win_den. cbn [w_len]. change (to_Z 24%uint63) with 24. lia.
        + rewrite etop_win_den. cbn [w_lo]. rewrite UT. lia. }
    split.
    +
      apply (WF1 segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. subst wsB. rewrite map_app. apply Forall_app. split.
      * rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply Forall_forall. intros w Hw.
        apply in_map_iff in Hw as (x & <- & Hx). exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ (proj1 (SUB0 x Hx)))).
      * constructor; [|constructor]. rewrite etop_win_den, UT. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 24%uint63) with 24.
        split; [lia|]. split; [lia|]. split; [lia|].
        right; right. split; [unfold K_SUB; lia|]. exists (v_begin (k_evec g), v_bytes (k_evec g)). split; [exact (proj1 O _ OWN)|].
        intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
    +
      apply CW3'. unfold cw_pk_holds. cbn [unparse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP map decode_pk].
      set (g' := PKG (k_tree g) (vec_dec (k_evec g)) (k_zone g)).
      assert (OWE : owned g' = owned g) by reflexivity.
      destruct (vec_dec_valid (k_evec g) (conj VX1 (conj VX2 (conj VX3 VX4))) ltac:(rewrite SZ; lia)) as [VVP VEP].
      exists g', (ls1 ++ [(lo, sp)]). split; [| split; [| split; [| split]]].
      *
        unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
        change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_dec (k_evec g)).
        rewrite (DR root), (DR rootT), (DR n1), (DR P1), (DR c0), (DR eb), (DR ecap) by (apply INCA; inl).
        split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|]. split; [exact Leb|]. split.
        { rewrite VEP, EL. cbn [den]. rewrite EVn. subst wT. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
          unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small (v_end (k_evec g) - 48)) by lia. rewrite Z.mod_small by lia. unfold ELEM_SIZE. lia. }
        split; [exact Lecap|]. split.
        -- unfold last_opt. rewrite rev_app_distr. cbn [rev app]. fold e.
           rewrite (den_VP0 E' _ wzero (weqb_refl _)), (den_VP0 E' _ wzero (weqb_refl _)), UP, UR, !den_b2v. subst m k. repeat split; reflexivity.
        -- intros X. exfalso. apply X. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
      *
        unfold pure_pk. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_dec (k_evec g)).
        split; [exact LV0|]. split; [exact EL|]. split; [cbn [vec_dec v_size]; rewrite SZ, LENls, length_app; cbn [length]; lia|].
        split; [right; exact (conj VVP (conj CP CP2))|]. split; [| exact ZV]. change (v_capend (vec_dec (k_evec g))) with (v_capend (k_evec g)). exact CE.
      *   exact O.
      *
        apply (WK1 g').
        unfold wins_pk. apply Forall_forall. intros w Hw NS. subst wsB. rewrite map_app in Hw. apply in_app_iff in Hw as [Hw|Hw].
        -- rewrite (WDR ws0 ltac:(intros x Hx; exact (proj1 (SUB0 x Hx)))) in Hw. apply in_map_iff in Hw as (x & <- & Hx).
           destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ (proj1 (SUB0 x Hx))) NS) as [D|[NB ET]]; [left; rewrite OWE; exact D| right].
           split; [exact NB|]. destruct ET as (E1 & E2 & E3 & E4 & E5). unfold etop_ok. change (k_evec g') with (vec_dec (k_evec g)). rewrite VEP.
           change (v_begin (vec_dec (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_dec (k_evec g))) with (v_capend (k_evec g)). repeat split; try assumption. lia.
        -- destruct Hw as [<-|[]]. right. rewrite etop_win_den, UT. cbn [w_kind w_lo w_len]. split; [unfold K_BLOCK; lia|].
           unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_dec (k_evec g)). rewrite VEP.
           change (v_begin (vec_dec (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_dec (k_evec g))) with (v_capend (k_evec g)).
           change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity].
      *
        split; [| split].
        2: { apply (GH1 g'). destruct GH as [SE EP]. split.
             - change (k_zone g') with (k_zone g). apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw K9.
               subst wsB. rewrite map_app in Hw. apply in_app_iff in Hw as [Hw|Hw].
               + rewrite (WDR ws0 ltac:(intros x Hx; exact (proj1 (SUB0 x Hx)))) in Hw. apply in_map_iff in Hw as (x & <- & Hx).
                 apply in_map. exact (proj1 (SUB0 x Hx)).
               + destruct Hw as [<-|[]]. exfalso. rewrite etop_win_den in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. lia.
             - intros _. exists (wden E' (etop_win n 24)). split.
               + subst wsB. rewrite map_app. apply in_app_iff. right. left. reflexivity.
               + rewrite etop_win_den, UT. unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_dec (k_evec g)). rewrite VEP.
                 change (v_begin (vec_dec (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_dec (k_evec g))) with (v_capend (k_evec g)).
                 change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity]. }
        2: {
             eapply (CO1 _ g ls).
             - eapply cost_pk_ws; [exact CO|]. intros w Hw NV. subst wsB. rewrite map_app in Hw. apply in_app_iff in Hw as [Hw|Hw].
               + rewrite (WDR ws0 ltac:(intros x Hx; exact (proj1 (SUB0 x Hx)))) in Hw. apply in_map_iff in Hw as (x & <- & Hx).
                 apply in_map. exact (proj1 (SUB0 x Hx)).
               + destruct Hw as [<-|[]]. exfalso. apply NV. apply pku_val_none_kind. rewrite etop_win_den. cbn [w_kind]. unfold K_ETOP. lia.
             - intros fr v _ LE. cbn [a_cf den]. rewrite wbv_unsigned, wzero_ok. change (0 =? 0) with true.
               change (k_tree g') with (k_tree g). rewrite ELS in LE. refine (Z.le_trans _ _ _ _ LE).
               apply (PkCost.np_pop (bmem_of segs (ms_mem ms)) (k_zone g) (k_tree g) ls1 (lo, sp) l fr).
               + exact (proj1 (Forall_forall _ _) (levels_wf _ _ _ _ TW LV) l ltac:(rewrite ELS; apply in_app_iff; right; left; reflexivity)).
               + intros fo HFO. apply (focus_tree_wf _ _ (k_tree g) (ls1 ++ [(lo, sp)]) l fo TW); [rewrite <- ELS; exact LV| exact HFO]. }
        unfold mem_pk in *. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_dec (k_evec g)).
        change (v_begin (vec_dec (k_evec g))) with (v_begin (k_evec g)). cbn [a_root] in *. rewrite (DR root) by (apply INCA; left; reflexivity).
        split; [exact TW|]. split; [exact KA|]. split; [exact ICB|]. split; [exact CH|].
        intros _. rewrite removelast_snoc. exact PEL1.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E') wsF) _ a (mk_args_sound E' 3%uint63 aw _ _ LENF))) in FPa as (RA & NI & NWF).
    assert (NW : ~ in_ws (map (wden E') wsB) a) by (intros X; apply NWF; apply INWS1; exact X).
    subst wsB. unfold in_ws in NW. rewrite map_app in NW. fold (in_ws (map (wden E') ws0 ++ map (wden E') [etop_win n 24])) in NW.
    split.
    * destruct (in_ws_dec (map (wden E) ws) a) as [IN|NIN]; [right| left; exact (FPold a RA NI NIN)].
      apply in_ws_map_iff in IN as (x & Hx & Ha).
      destruct (win3_eqb x (etop_win kT 24)) eqn:ISW.
      -- apply win3_eqb_eq in ISW. subst x. rewrite etop_win_den in Ha. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha. change (to_Z 24%uint63) with 24 in Ha.
         exists kT, rT. split; [left; reflexivity|]. split; [exact FT|]. unfold inR. rewrite EVkT, (HIZg E'), LOZ0. lia.
      -- exfalso. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left.
         rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply in_ws_map_iff. exists x. split; [| exact Ha].
         apply filter_In. split; [exact Hx|]. rewrite ISW. reflexivity.
    * intros k' r' [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
      cbn [map]. rewrite etop_win_den. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
      unfold inR in IR. rewrite LON, HIN in IR. change (to_Z 24%uint63) with 24. lia.
  -
    assert (TF : Forall (fact_holds E') (top_facts (s_facts st) eb n)).
    { apply (top_facts_sound E' (s_facts st) eb n (so_facts _ _ _ _ _ _ HS)).
      - rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, UT. pose proof (aw_ceiling_small segs IMGX AW model). unfold Mem.two62Z in *. lia.
      - rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, UT. unfold v_end. rewrite EL, SZ, LENls. unfold ELEM_SIZE.
        replace (v_begin (k_evec g) + 24 * (Z.of_nat (length ls1) + 2) - 48 - v_begin (k_evec g)) with ((3 * Z.of_nat (length ls1)) * 8) by lia.
        apply Z.mod_mul. lia. }
    assert (KFs : Forall (fact_holds E') (KF.kids_facts (VP (PrimInt63.add n 2) wzero) (VP (PrimInt63.add n 1) wzero))).
    { apply (KF.kids_facts_sound E' _ _ (pe_rest e) (pe_ptr e)).
      - rewrite (den_VP0 E' _ wzero (weqb_refl _)). exact UR.
      - rewrite (den_VP0 E' _ wzero (weqb_refl _)). exact UP.
      - lia.
      - lia.
      - lia.
      - unfold KF.KF_BIGZ. lia. }
    constructor; [| constructor; [| constructor; [| constructor; [|constructor; [|apply Forall_app; split; [exact TF| exact KFs]]]]]]; cbn [fact_holds].
    * cbn [den]. rewrite EVn, EVkT. subst wT. apply bv_eq. rewrite !bv_add_unsigned, Z_to_bv_unsigned, !wbv_unsigned, wlit_ok, wzero_ok. change (to_Z 24%uint63) with 24.
      unfold bv_wrap. rewrite bv_modulus_64, KV. rewrite (Z.mod_small (v_end (k_evec g) - 48)) by lia. rewrite !Z.mod_small by lia. lia.
    * rewrite UR, !wlit_ok. change (to_Z 1%uint63) with 1. change (to_Z 1000%uint63) with 1000. lia.
    * rewrite UP. change (2 ^ to_Z 3%uint63) with 8. exact EAL.
    * rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, (den_VP0 E' n wzero (weqb_refl _)), UT. lia.
    * rewrite (DR ecap) by (apply INCA; inl). rewrite <- Lecap. cbn [den]. rewrite EVn. subst wT. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wlit_ok.
      change (to_Z 24%uint63) with 24. unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small (v_end (k_evec g) - 48)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem pop_sound : forall pc, contract_sound segs OPS MP PB (pop_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pop_contract c_apply] in HAP.
  destruct (pop_sound_main false E st ms model sts HS HAP) as (st' & E' & IN & HX & HS').
  exact (Hk st' IN E' ms model HX HMP HS').
Qed.

Theorem pop_a_sound : forall pc, contract_sound segs OPS MP PB (pop_contract_a pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pop_contract_a c_apply] in HAP.
  destruct (pop_sound_main true E st ms model sts HS HAP) as (st' & E' & IN & HX & HS').
  exact (Hk st' IN E' ms model HX HMP HS').
Qed.

End Sound.
End PkPop.
