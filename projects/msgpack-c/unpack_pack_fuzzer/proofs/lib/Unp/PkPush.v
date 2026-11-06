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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib GWin PkStack PkAux.
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

Module PkPush.

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

Lemma push_sound_main : forall all E st ms model sts,
  st_ok segs OPS E st ms model -> push_apply_g all st = Some sts ->
  exists st' E', In st' sts /\ env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros all E st ms model sts HS0 AP.
  unfold push_apply_g in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct ee as [|kT oT| | | | | | | | |]; try discriminate.
  destruct fT as [t| | | | | | | | | |]; try discriminate.
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  cbv zeta in AP.
  destruct (top_cells rT 0) as [[[[op on] om] ok]|] eqn:TC; [|discriminate].
  destruct (cell_at rT 24 8%uint63) as [np|] eqn:CNP; [|discriminate].
  destruct (cell_at rT 32 8%uint63) as [nn|] eqn:CNN; [|discriminate].
  destruct (flags_at rT 40) as [f|] eqn:CF; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND DFL]. apply andb_prop in COND as [COND DNN]. apply andb_prop in COND as [COND DNP].
  apply andb_prop in COND as [COND DOK]. apply andb_prop in COND as [COND DOM]. apply andb_prop in COND as [COND SON]. apply andb_prop in COND as [COND SOP].
  apply andb_prop in COND as [COND DCF].
  apply andb_prop in COND as [COND W]. apply andb_prop in COND as [COND HI]. apply andb_prop in COND as [COND LO].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND EX]. apply andb_prop in COND as [COND T78].
  apply andb_prop in COND as [COND K1]. apply andb_prop in COND as [COND K0]. apply andb_prop in COND as [COND OT].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply (proj1 (weqb_ok _ _)) in OT. subst oT. apply Z.ltb_lt in WLEN.
  apply negb_true_iff in K0. apply negb_true_iff in K1. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  apply sv_eqb_eq in SOP. apply sv_eqb_eq in SON. subst op on.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with 4611686018427387896 in NLT.
  assert (N62 : to_Z (s_next st) < to_Z bit62i) by (change (to_Z bit62i) with 4611686018427387904; lia).
  apply existsb_exists in EX as (w48 & INw48 & EQ48). apply win3_eqb_eq in EQ48. subst w48.
  set (n := s_next st) in *.
  pose proof (to_Z_add_small n 1%uint63 N62 ltac:(change (to_Z 1%uint63) with 1; lia)) as AD1. change (to_Z 1%uint63) with 1 in AD1.
  set (ismap := weqb t (wlit 8)) in *.

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

  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; eb; VP kT (wlit 24%uint63); ecap; tptr; trest; tmap; tkey; cf; VL t; fN; fP] -> In v (op_args o)).
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

  pose proof (dnz_sound E _ _ Pfacts DCF) as CFNZ.
  destruct (LCF CFNZ) as (LSNE & CFA & fo & FOC & FOT & FOV & FOP).
  cbn [den] in FOT. rewrite wbv_unsigned in FOT.
  assert (T78' : obj_type fo = 7 \/ obj_type fo = 8).
  { rewrite FOT. apply orb_prop in T78 as [T7|T8]; [left| right]; apply (proj1 (weqb_ok _ _)) in T7 || apply (proj1 (weqb_ok _ _)) in T8; subst t; rewrite wlit_ok; reflexivity. }
  destruct (obj_type_cont fo T78') as [FCONT FMAP].
  assert (ISM : ismap = is_mapo fo).
  { subst ismap. destruct (is_mapo fo) eqn:IM.
    - apply (proj2 (weqb_w2Z _ _)). pose proof (proj1 FMAP eq_refl) as T8. rewrite FOT in T8. rewrite wlit_ok. exact T8.
    - destruct (weqb t (wlit 8)) eqn:Q; [exfalso| reflexivity]. apply (proj1 (weqb_ok _ _)) in Q. subst t.
      rewrite wlit_ok in FOT. change (to_Z 8%uint63) with 8 in FOT. pose proof (proj2 FMAP FOT) as X. discriminate X. }

  assert (HIZg : forall Ex, hiZ Ex rT = 48) by (intros Ex; unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (HIZg E) as HIZ48.
  assert (LOZ0 : loZ rT = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ (Preg kT rT FT) K0) as [RR1 RR2]. rewrite HIZ48 in RR2. rewrite LOZ0 in RR1.
  assert (KV : bv_unsigned (ev E kT) = v_end (k_evec g) - 24).
  { rewrite Lee. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }

  assert (VVX : vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g))).
  { destruct VE as [(B0 & C0 & LS0)|X]; [exfalso; exact (LSNE LS0)| exact X]. }
  destruct VVX as [(VX1 & VX2 & VX3 & VX4) (CP & CP2)].
  assert (LEN1 : 1 <= Z.of_nat (length ls)) by (destruct ls; [exfalso; exact (LSNE eq_refl)| cbn [length]; lia]).
  assert (CAPB : v_capend (k_evec g) = v_begin (k_evec g) + v_bytes (k_evec g)) by (unfold v_capend, v_bytes; lia).
  assert (ENDCAP : v_end (k_evec g) <= v_capend (k_evec g)) by (unfold v_end, v_capend; rewrite EL; unfold ELEM_SIZE; clear - VX2; nia).
  assert (E24 : v_begin (k_evec g) + 24 <= v_end (k_evec g)) by (unfold v_end; rewrite EL, SZ; unfold ELEM_SIZE; clear - LEN1; nia).
  pose proof (owned_evec g VX3) as OWN.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (B1 & B2 & B3 & B4 & _). cbn [fst snd] in B1, B2, B3.

  assert (ROOM : v_end (k_evec g) + 24 <= v_capend (k_evec g)).
  { destruct (proj1 (Forall_forall _ _) Wk (wden E (etop_win kT 48)) (in_map _ _ _ INw48) ltac:(rewrite etop_win_den; cbn [w_kind]; unfold K_STACK; lia)) as [[_ D]|[_ ET]].
    - exfalso. apply (D _ OWN (v_end (k_evec g) - 24)).
      + rewrite etop_win_den, KV. unfold in_iv, w_iv. cbn [fst snd w_lo w_len]. change (to_Z 48%uint63) with 48. lia.
      + unfold in_iv. cbn [fst snd]. lia.
    - destruct ET as (_ & _ & _ & _ & E5). rewrite etop_win_den, KV in E5. cbn [w_lo w_len] in E5. change (to_Z 48%uint63) with 48 in E5. lia. }
  assert (ROOMS : v_size (k_evec g) + 1 <= v_cap (k_evec g)) by (unfold v_end, v_capend in ROOM; rewrite EL in ROOM; unfold ELEM_SIZE in ROOM; clear - ROOM; nia).

  assert (SPL : exists ls0 l, ls = ls0 ++ [l]) by (destruct ls as [|x xs] using rev_ind; [cbn in LEN1; lia| eauto]).
  destruct SPL as (ls0 & l & ELS).
  assert (LENls : Z.of_nat (length ls) = Z.of_nat (length ls0) + 1) by (rewrite ELS, length_app; cbn [length]; lia).
  rewrite ELS in LTOP. unfold last_opt in LTOP. rewrite rev_app_distr in LTOP. cbn [rev app] in LTOP. destruct LTOP as (Ltp & Ltr & Ltm & Ltk).
  set (e := elem_of l) in *.

  assert (TCELLS : cell_at rT 0 8%uint63 = Some tptr /\ cell_at rT 8 8%uint63 = Some trest /\ cell_at rT 16 1%uint63 = Some om /\ cell_at rT 17 1%uint63 = Some ok).
  { unfold top_cells in TC. rewrite !Z.add_0_l in TC.
    destruct (cell_at rT 0 8%uint63), (cell_at rT 8 8%uint63), (cell_at rT 16 1%uint63), (cell_at rT 17 1%uint63); try discriminate. injection TC as <- <- <- <-. auto. }
  destruct TCELLS as (C0 & C8 & C16 & C17).
  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 0 tptr (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) C0)) as Up.
  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 8 trest (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) C8)) as Ur.
  pose proof (proj1 (cell_at_u8 segs _ E _ kT rT 16 om (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) C16)) as Um.
  pose proof (proj1 (cell_at_u8 segs _ E _ kT rT 17 ok (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) C17)) as Uk.
  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 24 np (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) CNP)) as Unp.
  pose proof (proj1 (cell_at_u64 segs _ E _ kT rT 32 nn (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) CNN)) as Unn.
  rewrite Z.add_0_r in Up. rewrite KV in Up, Ur, Um, Uk, Unp, Unn.
  rewrite Ltp in Up. rewrite Ltr in Ur.
  rewrite (deq_sound E _ _ _ Pfacts DOM) in Um. rewrite (deq_sound E _ _ _ Pfacts DOK) in Uk.
  rewrite Ltm in Um. rewrite Ltk in Uk.
  replace (b2Z (pe_map e) mod 2 ^ 8) with (b2Z (pe_map e)) in Um by (destruct (pe_map e); reflexivity).
  replace (b2Z (pe_key e) mod 2 ^ 8) with (b2Z (pe_key e)) in Uk by (destruct (pe_key e); reflexivity).
  rewrite (deq_sound E _ _ _ Pfacts DNP) in Unp. rewrite (deq_sound E _ _ _ Pfacts DNN) in Unn.

  destruct (flags_sound segs E (s_priv st) (ms_mem ms) kT rT 40 f ismap (s_facts st) (Preg kT rT FT) K0 ltac:(lia) ltac:(unfold two62Z; lia) Pfacts CF DFL) as [Ufl0 Ufl1].
  rewrite KV in Ufl0, Ufl1.
  replace (v_end (k_evec g) - 24 + 40 + 1) with (v_end (k_evec g) + 17) in Ufl1 by lia.

  set (wT := Z_to_bv 64 (v_end (k_evec g))).
  set (E' := env_upd E n wT).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  assert (EVn : ev E' n = wT) by apply env_upd_same.
  pose proof (DRgen E' HX) as DR. pose proof (WDRgen E' HX) as WDR.
  assert (EVkT : ev E' kT = ev E kT) by exact (ev_reval n E E' HX kT KTn).
  clearbody E'.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  assert (UT : bv_unsigned (ev E' n) = v_end (k_evec g)) by (rewrite EVn; subst wT; apply u64_of_Z; lia).
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).

  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    rewrite (map_ext_in (den E') (den E) (op_args o) DR).
    apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws) _ a DEC)). split; [lia| auto]. }
  assert (MATB : forall a, v_end (k_evec g) - 24 <= a < v_end (k_evec g) + 24 -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model _ a HA (proj1 O _ OWN)). unfold in_iv. cbn [fst snd]. lia. }

  set (ws' := List.map (fun w => if win3_eqb w (etop_win kT 48) then etop_win n 24 else w) ws) in *.
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; lia).
  assert (INWS' : forall w, In w ws' -> (In w ws /\ w <> etop_win kT 48) \/ w = etop_win n 24).
  { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQ & Hx). destruct (win3_eqb x (etop_win kT 48)) eqn:Q.
    - right. congruence.
    - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate. }
  destruct (PkU.pku_flip (s_facts st) negb true ws') as [wsF|] eqn:FLIP; [|discriminate AP].
  injection AP as <-.
  eexists _, E'. split; [left; reflexivity|]. split; [exact HX|].
  apply repoint_g_sound; [| cbn [den]; rewrite EVkT, EVn; subst wT; apply bv_eq; rewrite !bv_add_unsigned, !wbv_unsigned, !wlit_ok, Z_to_bv_unsigned;
                           change (to_Z 24%uint63) with 24; change (to_Z 48%uint63) with 48; unfold bv_wrap; rewrite bv_modulus_64, KV;
                           rewrite (Z.mod_small (v_end (k_evec g))) by lia; f_equal; lia
                      | reflexivity].
  set (rN := top_region fP fN ismap ismap) in *.
  assert (HIN : forall Ex, hiZ Ex rN = 24) by (intros Ex; reflexivity).
  assert (LON : loZ rN = 0) by reflexivity.

  destruct (PkUSem.flip_sound E' (s_facts st) (so_facts _ _ _ _ _ _ HS) _ _ ws' wsF FLIP) as (LENfl & INWS1 & KEEP1 & WF1 & WK1 & GH1 & CO1).
  assert (LENF : Z.of_nat (length wsF) < two63) by (rewrite LENfl; exact LEN').
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kT] [(n, rN)] (mk_args 3%uint63 aw wsF _) _ (PrimInt63.add n 1)).
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
    + intros a Ha. rewrite UT, LON, HIN in Ha. apply MATB. lia.
    + intros gk gr F. destruct (top_region_find _ _ _ _ gk gr F) as [[-> ->]|[[-> ->]|[-> ->]]]; cbn [g_cells].
      * change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 _ (bv_unsigned (den E fP))); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT. replace (v_end (k_evec g)) with (v_end (k_evec g) - 24 + 24) by lia. exact Unp.
           ++ rewrite (DR fP) by (apply INCA; inl). reflexivity.
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 1%uint63) with 1. split.
        -- split; [exact (conj I I)|]. constructor; [|constructor].
           apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 1) 0%uint63 _ (bv_unsigned (den E fN))); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT. replace (v_end (k_evec g) + 8 * 1) with (v_end (k_evec g) - 24 + 32) by lia. exact Unn.
           ++ rewrite (DR fN) by (apply INCA; inl). reflexivity.
        -- intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LON, HIN. lia.
      * change (keyZ 2%uint63) with 2. split.
        -- split; [cbn [slot_sorted c_idx c_w]; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; split; [lia| exact (conj I I)]|]. constructor; [| constructor; [|constructor]].
           ++ apply (cell_ok_of_u8 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 2) 0%uint63 _ (b2Z ismap)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
              ** change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, UT. replace (v_end (k_evec g) + 8 * 2) with (v_end (k_evec g) - 24 + 40) by lia. exact Ufl0.
              ** rewrite den_b2v. destruct ismap; reflexivity.
           ++ apply (cell_ok_of_u8 segs E' (ms_mem ms) (bv_unsigned (ev E' n) + 8 * 2) 1%uint63 _ (b2Z ismap)); [change (to_Z 1%uint63) with 1; lia| change (to_Z 1%uint63) with 1; lia| |].
              ** change (to_Z 1%uint63) with 1. rewrite UT. replace (v_end (k_evec g) + 8 * 2 + 1) with (v_end (k_evec g) + 17) by lia. exact Ufl1.
              ** rewrite den_b2v. destruct ismap; reflexivity.
        -- intros c i [<-|[<-|[]]] Hi; cbn [c_w c_idx] in Hi |- *; change (to_Z 1%uint63) with 1 in *; try change (to_Z 0%uint63) with 0; rewrite LON, HIN; lia.
  -
    intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite UT, LON, HIN in IR.
    right. exists kT, rT. split; [left; reflexivity|]. split; [exact FT|]. unfold inR. rewrite EVkT, (HIZg E'), LOZ0, KV. lia.
  - intros k1' r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E' aw), (map (wden E') wsF), _, LB.
    split; [apply (mk_args_sound E' 3%uint63 aw wsF _ LENF)|]. split.
    { rewrite (DR aw INAW). pose proof HA as HA'. rewrite <- (WDR ws ltac:(intros w Hw; exact Hw)) in HA'.
      refine (aw_keep segs IMGX AW _ _ _ _ _ _ (aw_keep segs IMGX AW _ _ _ _ _ _ HA' _) (KEEP1 LB)). apply (UOK.wins_keep_map_intro E' LB ws ws').
      - intros x Hx. destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right; apply UOK.kind_new_sub; reflexivity].
      - intros x Hx. destruct (UOK.map_replace_old ws (etop_win kT 48) (etop_win n 24) x Hx) as [H1| ->]; [left; exact H1| right].
        split; [apply etop_untied|]. intros _ _.
        apply (block_keep_evidence LB _ (v_begin (k_evec g)) (v_bytes (k_evec g)) _ (wden E' (etop_win n 24)) (proj1 O _ OWN)).
        + rewrite etop_win_den. cbn [w_lo]. rewrite EVkT, KV. lia.
        + apply in_map. subst ws'. apply in_map_iff. exists (etop_win kT 48). rewrite win3_eqb_refl. split; [reflexivity| exact INw48].
        + apply etop_heap_kind.
        + rewrite etop_win_den. cbn [w_len]. change (to_Z 24%uint63) with 24. lia.
        + rewrite etop_win_den. cbn [w_lo]. rewrite UT. lia. }
    split.
    +
      apply (WF1 segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (INWS' x Hx) as [[Hx0 _]| ->].
      * rewrite <- (WDR [x] ltac:(intros w [<-|[]]; exact Hx0)) in WF |- * || idtac.
        replace (wden E' x) with (wden E x) by (symmetry; exact (f_equal (fun l => hd (wden E x) l) (WDR [x] ltac:(intros w [<-|[]]; exact Hx0)))).
        exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ Hx0)).
      * rewrite etop_win_den, UT. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 24%uint63) with 24.
        split; [lia|]. split; [lia|]. split; [lia|].
        right; right. split; [unfold K_SUB; lia|]. exists (v_begin (k_evec g), v_bytes (k_evec g)). split; [exact (proj1 O _ OWN)|].
        intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
    +
      apply CW3'. unfold cw_pk_holds. cbn [unparse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP map decode_pk].
      set (g' := PKG (k_tree g) (vec_inc (k_evec g)) (k_zone g)).
      destruct (vec_inc_valid (k_evec g) (conj VX1 (conj VX2 (conj VX3 VX4))) ROOMS) as [VVP VEP].
      exists g', (ls ++ [(fo, 0)]). split; [| split; [| split; [| split]]].
      *
        unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
        change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
        rewrite (DR root), (DR rootT), (DR n1), (DR P1), (DR c0), (DR eb), (DR ecap), (DR fP), (DR fN) by (apply INCA; inl).
        split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|]. split; [exact Leb|]. split.
        { rewrite VEP, EL. cbn [den]. rewrite EVn. subst wT. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
          unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small (v_end (k_evec g))) by lia. rewrite Z.mod_small by lia. unfold ELEM_SIZE. lia. }
        split; [exact Lecap|]. split.
        -- unfold last_opt. rewrite rev_app_distr. cbn [rev app]. rewrite !den_b2v, ISM, <- FOP, <- FOV.
           destruct fo; try discriminate FCONT; unfold elem_of; cbn [pe_ptr pe_rest pe_map pe_key obj_ptr okids obj_via is_mapo b2Z];
             rewrite ?Zdiv_0_l, ?Z.mul_0_r, ?Z.add_0_r, ?Z.sub_0_r; repeat split; reflexivity.
        -- intros X. exfalso. apply X. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
      *
        unfold pure_pk. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
        split.
        { apply (proj2 (levels_snoc _ _ _ _)). split; [exact LV|]. split; [exact FOC|]. split; [exact FCONT|]. split; [lia|].
          destruct (okids fo) as [|k0 ks] eqn:OK; [right; auto| left; exists k0; reflexivity]. }
        split; [exact EL|]. split; [cbn [vec_inc v_size]; rewrite SZ, length_app; cbn [length]; lia|].
        split; [right; exact (conj VVP (conj CP CP2))|]. split; [| exact ZV]. change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)). exact CE.
      *   exact O.
      *
        apply (WK1 g').
        unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (INWS' x Hx) as [[Hx0 NEx]| ->].
        -- replace (wden E' x) with (wden E x) in NS |- * by (symmetry; exact (f_equal (fun l => hd (wden E x) l) (WDR [x] ltac:(intros w [<-|[]]; exact Hx0)))).
           destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS) as [D|[NB ET]]; [left; exact D| exfalso].
           destruct ET as (K6 & _). pose proof (only_kind_sound E 6 _ ws OK6 x Hx0 ltac:(unfold K_ETOP in K6; exact K6)) as [= EQ]. exact (NEx (eq_sym EQ)).
        -- right. rewrite etop_win_den, UT. cbn [w_kind w_lo w_len]. split; [unfold K_BLOCK; lia|].
           unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_inc (k_evec g)). rewrite VEP, EL.
           change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)).
           change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity].
      *
        split; [| split].
        2: { apply (GH1 g'). destruct GH as [SE EP]. split.
             - change (k_zone g') with (k_zone g). apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
               destruct (INWS' x Hx) as [[Hx0 NEx]| ->].
               + replace (wden E' x) with (wden E x) by (symmetry; exact (f_equal (fun l => hd (wden E x) l) (WDR [x] ltac:(intros w [<-|[]]; exact Hx0)))).
                 apply in_map. exact Hx0.
               + exfalso. rewrite etop_win_den in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. lia.
             - intros _. exists (wden E' (etop_win n 24)). split.
               + apply in_map. subst ws'. apply in_map_iff. exists (etop_win kT 48). rewrite win3_eqb_refl. split; [reflexivity| exact INw48].
               + rewrite etop_win_den, UT. unfold etop_ok. cbn [w_kind w_lo w_len]. change (k_evec g') with (vec_inc (k_evec g)). rewrite VEP, EL.
                 change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). change (v_capend (vec_inc (k_evec g))) with (v_capend (k_evec g)).
                 change (to_Z 24%uint63) with 24. unfold K_ETOP, ELEM_SIZE in *. repeat split; first [exact VX3| lia| reflexivity]. }
        2: {
             eapply (CO1 _ g ls).
             - eapply cost_pk_ws; [exact CO|]. intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
               destruct (INWS' x Hx) as [[Hx0 NEx]| ->].
               + replace (wden E' x) with (wden E x) by (symmetry; exact (f_equal (fun l => hd (wden E x) l) (WDR [x] ltac:(intros w [<-|[]]; exact Hx0)))).
                 apply in_map. exact Hx0.
               + exfalso. apply NV. apply pku_val_none_kind. rewrite etop_win_den. cbn [w_kind]. unfold K_ETOP. lia.
             - intros fr v OKfr LE. destruct fr; [discriminate OKfr|]. cbn [a_cf den]. rewrite wbv_unsigned, wzero_ok. change (0 =? 0) with true.
               change (k_tree g') with (k_tree g). cbn [a_cf] in LE.
               destruct (Z.eqb_spec (bv_unsigned (den E cf)) 0) as [X|_]; [exfalso; exact (CFNZ X)|].
               rewrite ELS in LE |- *. rewrite (PkCost.np_push (k_tree g) ls0 l fo); [exact LE|].
               rewrite ELS, PkCost.focus_node_snoc in FOC. exact FOC. }
        unfold mem_pk. change (k_tree g') with (k_tree g). change (k_zone g') with (k_zone g). change (k_evec g') with (vec_inc (k_evec g)).
        change (v_begin (vec_inc (k_evec g))) with (v_begin (k_evec g)). cbn [a_root]. rewrite (DR root) by (apply INCA; left; reflexivity).
        cbn [a_root] in ICB.
        split; [exact TW|]. split; [exact KA|]. split; [exact ICB|]. split; [exact CH|].
        intros _. rewrite removelast_snoc, ELS, map_app. cbn [map]. apply (proj2 (pelems_at_app _ _ _ _)). split.
        -- rewrite ELS, removelast_snoc in PE. exact (PE VX3).
        -- rewrite length_map. replace (v_begin (k_evec g) + ELEM_SIZE * Z.of_nat (length ls0)) with (v_end (k_evec g) - 24) by (unfold v_end; rewrite EL, SZ, LENls; unfold ELEM_SIZE; lia).
           cbn [pelems_at]. fold e. split; [exact Up|]. split; [exact Ur|]. split; [| split; [| exact I]].
           ++ replace (v_end (k_evec g) - 24 + 16) with (v_end (k_evec g) - 24 + 16) by lia. unfold b2Z in Um. exact Um.
           ++ unfold b2Z in Uk. exact Uk.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E') wsF) _ a (mk_args_sound E' 3%uint63 aw _ _ LENF))) in FPa as (RA & NI & NWF).
    assert (NW : ~ in_ws (map (wden E') ws') a) by (intros X; apply NWF; apply INWS1; exact X).
    split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IN|NIN]; [right| left; exact (FPold a RA NI NIN)].
      apply in_ws_map_iff in IN as (x & Hx & Ha).
      destruct (win3_eqb x (etop_win kT 48)) eqn:ISW.
      * apply win3_eqb_eq in ISW. subst x. rewrite etop_win_den in Ha. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha. change (to_Z 48%uint63) with 48 in Ha.
        exists kT, rT. split; [left; reflexivity|]. split; [exact FT|]. unfold inR. rewrite EVkT, (HIZg E'), LOZ0. lia.
      * exfalso. apply NW. apply in_ws_map_iff. exists x. split.
        -- subst ws'. apply in_map_iff. exists x. rewrite ISW. auto.
        -- replace (wden E' x) with (wden E x) by (symmetry; exact (f_equal (fun l => hd (wden E x) l) (WDR [x] ltac:(intros w [<-|[]]; exact Hx)))). exact Ha.
    + intros k' r' [H|[]] IR. injection H as <- <-. apply NW. apply in_ws_map_iff. exists (etop_win n 24). split.
      * subst ws'. apply in_map_iff. exists (etop_win kT 48). rewrite win3_eqb_refl. auto.
      * rewrite etop_win_den. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. unfold inR in IR. rewrite LON, HIN in IR. change (to_Z 24%uint63) with 24. lia.
  -
    assert (TF : Forall (fact_holds E') (top_facts (s_facts st) eb n)).
    { apply (top_facts_sound E' (s_facts st) eb n (so_facts _ _ _ _ _ _ HS)).
      - rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, UT. pose proof (aw_ceiling_small segs IMGX AW model). unfold Mem.two62Z in *. lia.
      - rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, UT. unfold v_end. rewrite EL. unfold ELEM_SIZE.
        replace (v_begin (k_evec g) + 24 * v_size (k_evec g) - v_begin (k_evec g)) with ((3 * v_size (k_evec g)) * 8) by lia.
        apply Z.mod_mul. lia. }
    constructor; [| constructor; [|constructor; [|exact TF]]]; cbn [fact_holds].
    + cbn [den]. rewrite EVn, EVkT. subst wT. apply bv_eq. rewrite !bv_add_unsigned, Z_to_bv_unsigned, !wbv_unsigned, wlit_ok, wzero_ok. change (to_Z 24%uint63) with 24.
      unfold bv_wrap. rewrite bv_modulus_64, KV. rewrite (Z.mod_small (v_end (k_evec g))) by lia. rewrite !Z.mod_small by lia. lia.
    + rewrite (DR eb) by (apply INCA; inl). rewrite <- Leb, (den_VP0 E' n wzero (weqb_refl _)), UT. lia.
    + rewrite (DR ecap) by (apply INCA; inl). rewrite <- Lecap. cbn [den]. rewrite EVn. subst wT. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wlit_ok.
      change (to_Z 24%uint63) with 24. unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small (v_end (k_evec g))) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem push_sound : forall pc, contract_sound segs OPS MP PB (push_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [push_contract c_apply] in HAP.
  destruct (push_sound_main false E st ms model sts HS HAP) as (st' & E' & IN & HX & HS').
  exact (Hk st' IN E' ms model HX HMP HS').
Qed.

Theorem push_a_sound : forall pc, contract_sound segs OPS MP PB (push_contract_a pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [push_contract_a c_apply] in HAP.
  destruct (push_sound_main true E st ms model sts HS HAP) as (st' & E' & IN & HX & HS').
  exact (Hk st' IN E' ms model HX HMP HS').
Qed.

End Sound.
End PkPush.
