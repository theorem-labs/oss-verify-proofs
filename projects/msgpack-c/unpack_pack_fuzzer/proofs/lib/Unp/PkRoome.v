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
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR PK PKL PkStack PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkRoome.

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

Lemma roome_sound_main : forall af E st ms model st',
  st_ok segs OPS E st ms model -> roome_apply_g af st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros af E st ms model st' HS AP.
  unfold roome_apply_g in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct ee as [|kT oT| | | | | | | | |]; try discriminate.
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND IMPL]. apply andb_prop in COND as [COND DLT]. apply andb_prop in COND as [COND BG].
  apply andb_prop in COND as [COND W]. apply andb_prop in COND as [COND HI]. apply andb_prop in COND as [COND LO].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND EX]. apply andb_prop in COND as [COND K1].
  apply andb_prop in COND as [COND K0]. apply andb_prop in COND as [COND OT].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply (proj1 (weqb_ok _ _)) in OT. subst oT. apply Z.ltb_lt in WLEN.
  apply negb_true_iff in K0. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  assert (BGN : rg_bg rT = BGNone) by (destruct (rg_bg rT); try discriminate; reflexivity).
  apply existsb_exists in EX as (w24 & INw24 & EQ24). apply win3_eqb_eq in EQ24. subst w24.
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
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  change (v_end (k_evec g) = bv_unsigned (den E (VP kT (wlit 24%uint63)))) in Lee.
  change (v_capend (k_evec g) = bv_unsigned (den E ecap)) in Lecap.
  change (v_begin (k_evec g) = bv_unsigned (den E eb)) in Leb.

  pose proof (dltu_sound E _ _ _ Pfacts DLT) as LTC. rewrite <- Lee, <- Lecap in LTC.
  assert (VVX : vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g))).
  { destruct VE as [(B0 & C0 & LS0)|X]; [exfalso| exact X]. subst ls. cbn [length Z.of_nat] in SZ.
    unfold v_end, v_capend in LTC. rewrite B0, C0, SZ in LTC. lia. }
  destruct VVX as [(VX1 & VX2 & VX3 & VX4) (CP & CP2)].
  assert (ROOM : v_end (k_evec g) + 24 <= v_capend (k_evec g)).
  { unfold v_end, v_capend in *. rewrite EL in *. unfold ELEM_SIZE in *. nia. }
  assert (CAPB : v_capend (k_evec g) = v_begin (k_evec g) + v_bytes (k_evec g)) by (unfold v_capend, v_bytes; lia).
  pose proof (owned_evec g VX3) as OWN.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (B1 & B2 & B3 & B4 & _). cbn [fst snd] in B1, B2, B3.

  assert (HIZ24 : hiZ E rT = 24) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (LOZ0 : loZ rT = 0) by (unfold loZ; rewrite LO; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ (Preg kT rT FT) K0) as [RR1 RR2]. rewrite HIZ24 in RR2. rewrite LOZ0 in RR1.
  assert (KV : bv_unsigned (ev E kT) = v_end (k_evec g) - 24).
  { rewrite Lee. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }

  pose proof (PlanS.implied_sound E _ _ Pz Pfacts IMPL) as BEG. cbn [fact_holds] in BEG. rewrite (den_VP0 E kT wzero (weqb_refl _)), <- Leb, KV in BEG.
  set (rT' := Region 0%uint63 (VL (wlit 48%uint63)) true BGNone (rg_cells rT)) in *.
  set (ws' := List.map (fun w => if win3_eqb w (etop_win kT 24) then etop_win kT 48 else w) ws) in *.
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; lia).
  assert (HIZ48 : hiZ E rT' = 48) by (unfold hiZ; subst rT'; cbn [rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (LOZ48 : loZ rT' = 0) by reflexivity.
  assert (INWS' : forall w, In w ws' -> (In w ws /\ w <> etop_win kT 24) \/ w = etop_win kT 48).
  { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQ & Hx). destruct (win3_eqb x (etop_win kT 24)) eqn:Q.
    - right. congruence.
    - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate. }

  assert (SAFE : forall a, v_end (k_evec g) <= a -> PK.safe g (map (wden E) ws) a).
  { intros a Ha w Hw (K6 & _) Hin. apply in_map_iff in Hw as (x & <- & Hx).
    pose proof (only_kind_sound E 6 _ ws OK6 x Hx ltac:(unfold K_ETOP in K6; exact K6)) as [= <-].
    rewrite etop_win_den, KV in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. change (to_Z 24%uint63) with 24 in Hin. lia. }
  assert (BYTE : forall a, v_end (k_evec g) <= a < v_end (k_evec g) + 24 ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (pk_owned_byte_props segs IMGX AW _ LB (ms_mem ms) model g (map (wden E) ws) _ a HA WF O Wk OWN).
    - unfold in_iv. cbn [fst snd]. unfold v_end, v_capend, v_bytes in *. nia.
    - apply SAFE. lia. }
  assert (MATB : forall a, v_end (k_evec g) - 24 <= a < v_end (k_evec g) + 24 -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model _ a HA (proj1 O _ OWN)). unfold in_iv. cbn [fst snd]. lia. }
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws) _ a DEC)). auto. }
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kT] [(kT, rT')] (mk_args 3%uint63 aw ws' _) (if af then [FULe (VP kT (wlit 48%uint63)) ecap] else []) (s_next st)).
  - intros k' [<-|[]]. split; [exact K0|]. exists rT. auto.
  - constructor; [intros []| constructor].
  - intros k' r' [H|[]]. injection H as <- <-. exact K0.
  -
    intros k' r' [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) kT rT' K0).
    + subst rT'. cbn [rg_cells]. exact (ro_bst _ _ _ _ _ _ (Preg kT rT FT)).
    + reflexivity.
    + rewrite LOZ48, KV. lia.
    + rewrite HIZ48, KV. lia.
    + intros a Ha. rewrite LOZ48, HIZ48, KV in Ha. apply MATB. lia.
    + intros gk gr F. subst rT'. cbn [rg_cells] in F. split.
      * exact (ro_cells _ _ _ _ _ _ (Preg kT rT FT) gk gr F).
      * intros c i Hc Hi. pose proof (proj1 (ro_cells_in _ _ _ _ _ _ (Preg kT rT FT) gk gr c i F Hc Hi) K0) as CI.
        rewrite LOZ0, HIZ24 in CI. rewrite HIZ48. unfold loZ. cbn [rg_lo]. change (keyZ 0%uint63) with 0. lia.
  -
    intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite LOZ48, HIZ48, KV in IR.
    destruct (Z.lt_ge_cases a (v_end (k_evec g))) as [LOW|HIGH].
    + right. exists kT, rT. split; [left; reflexivity|]. split; [exact FT|]. unfold inR. rewrite LOZ0, HIZ24, KV. lia.
    + left. destruct (BYTE a ltac:(lia)) as (RA & NI & NW & _). exact (FPold a ltac:(lia) NI NW).
  - intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E aw), (map (wden E) ws'), _, LB.
    split; [apply (mk_args_sound E 3%uint63 aw ws' _ LEN')|]. split.
    { apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA). apply (UOK.wins_keep_map_intro E LB ws ws').
      - intros x Hx. destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right; apply UOK.kind_new_sub; reflexivity].
      - intros x Hx. destruct (UOK.map_replace_old ws (etop_win kT 24) (etop_win kT 48) x Hx) as [H1| ->]; [left; exact H1| right].
        split; [apply etop_untied|]. intros _ _.
        apply (block_keep_evidence LB _ (v_begin (k_evec g)) (v_bytes (k_evec g)) _ (wden E (etop_win kT 48)) (proj1 O _ OWN)).
        + rewrite etop_win_den. cbn [w_lo]. rewrite KV. lia.
        + apply in_map. subst ws'. apply in_map_iff. exists (etop_win kT 24). rewrite win3_eqb_refl. split; [reflexivity| exact INw24].
        + apply etop_heap_kind.
        + rewrite etop_win_den. cbn [w_len]. change (to_Z 48%uint63) with 48. lia.
        + rewrite etop_win_den. cbn [w_lo]. rewrite KV. lia. }
    split.
    + unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (INWS' x Hx) as [[Hx0 _]| ->].
      * exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ Hx0)).
      * rewrite etop_win_den, KV. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 48%uint63) with 48.
        split; [lia|]. split; [lia|]. split; [lia|].
        right; right. split; [unfold K_SUB; lia|].
        exists (v_begin (k_evec g), v_bytes (k_evec g)). split; [exact (proj1 O _ OWN)|].
        intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
    + apply CW3'. unfold cw_pk_holds. cbn [map decode_pk].
      exists g, ls. split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [| split; [exact M|]].
      2: {
           split; [destruct GH as [SE EP]; split|].
           3: { apply (cost_pk_ws _ g ls (map (wden E) ws)); [exact CO|]. intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                destruct (INWS' x Hx) as [[Hx0 _]| ->]; [apply in_map; exact Hx0|].
                exfalso. apply NV. apply pku_val_none_kind. rewrite etop_win_den. cbn [w_kind]. unfold K_ETOP. lia. }
           - apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
             destruct (INWS' x Hx) as [[Hx0 _]| ->]; [apply in_map; exact Hx0|].
             exfalso. rewrite etop_win_den in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. lia.
           - intros _. exists (wden E (etop_win kT 48)). split.
             + apply in_map. subst ws'. apply in_map_iff. exists (etop_win kT 24). rewrite win3_eqb_refl. split; [reflexivity| exact INw24].
             + rewrite etop_win_den, KV. unfold etop_ok. cbn [w_kind w_lo w_len]. change (to_Z 48%uint63) with 48. unfold K_ETOP.
               split; [| lia]. split; [reflexivity|]. split; [exact VX3|]. unfold ELEM_SIZE. lia. }
      unfold wins_pk in *. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (INWS' x Hx) as [[Hx0 _]| ->].
      * exact (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS).
      * right. rewrite etop_win_den, KV in *. split; [cbn [w_kind]; unfold K_BLOCK; lia|].
        unfold etop_ok. cbn [w_kind w_lo w_len]. change (to_Z 48%uint63) with 48. unfold K_ETOP.
        split; [reflexivity|]. split; [exact VX3|]. unfold ELEM_SIZE. lia.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws') _ a (mk_args_sound E 3%uint63 aw ws' _ LEN'))) in FPa as (RA & NI & NW).
    split.
    + left. apply (FPold a RA NI). intros IN. apply NW. apply in_ws_map_iff in IN as (x & Hx & Ha). apply in_ws_map_iff.
      destruct (win3_eqb x (etop_win kT 24)) eqn:Q.
      * apply win3_eqb_eq in Q. subst x. exists (etop_win kT 48). split.
        -- subst ws'. apply in_map_iff. exists (etop_win kT 24). rewrite win3_eqb_refl. split; [reflexivity| exact INw24].
        -- rewrite etop_win_den in Ha |- *. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *.
           change (to_Z 24%uint63) with 24 in Ha. change (to_Z 48%uint63) with 48. lia.
      * exists x. split; [| exact Ha]. subst ws'. apply in_map_iff. exists x. rewrite Q. auto.
    + intros k' r' [H|[]] IR. injection H as <- <-. apply NW. apply in_ws_map_iff. exists (etop_win kT 48). split.
      * subst ws'. apply in_map_iff. exists (etop_win kT 24). rewrite win3_eqb_refl. split; [reflexivity| exact INw24].
      * rewrite etop_win_den. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. unfold inR in IR. rewrite LOZ48, HIZ48 in IR. change (to_Z 48%uint63) with 48. lia.
  -
    destruct af; [| constructor]. constructor; [| constructor]. cbn [fact_holds].
    rewrite <- Lecap. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, KV. change (to_Z 48%uint63) with 48.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; [lia|]. unfold v_end, v_capend, v_bytes in *. lia.
Qed.

Theorem roome_g_sound : forall af pc, contract_sound segs OPS MP PB (Contract pc (roome_apply_g af)).
Proof.
  intros af pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [c_apply] in HAP.
  destruct (roome_apply_g af st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. apply (Hk st' (or_introl eq_refl) E ms model); [| exact HMP| exact (roome_sound_main af E st ms model st' HS AP)].
       split; [reflexivity|]. intros kk Hk'. split; reflexivity. }
  all: exfalso; unfold roome_apply_g in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

Theorem roome_sound : forall pc, contract_sound segs OPS MP PB (roome_contract pc).
Proof. intros pc. exact (roome_g_sound false pc). Qed.

Theorem roome_a_sound : forall pc, contract_sound segs OPS MP PB (roome_contract_a pc).
Proof. intros pc. exact (roome_g_sound true pc). Qed.

End Sound.
End PkRoome.
