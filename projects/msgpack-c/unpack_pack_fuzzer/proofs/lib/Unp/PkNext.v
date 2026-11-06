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

Module PkNext.

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

Lemma den_add_wones : forall E x, bv_unsigned (den E (sv_alu ALU_ADD x (VL wones))) = (bv_unsigned (den E x) - 1) mod two64.
Proof.
  intros E x. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned.
  rewrite (weqb_wones_unsigned wones (weqb_refl _)). unfold bv_wrap. rewrite bv_modulus_64.
  replace (bv_unsigned (den E x) + (two64 - 1)) with (bv_unsigned (den E x) - 1 + 1 * two64) by lia.
  rewrite Z.mod_add by (unfold two64; lia). reflexivity.
Qed.

Lemma next_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> next_apply st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP.
  unfold next_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct ee as [|kT oT| | | | | | | | |]; try discriminate.
  destruct (lit01 tmap) as [m|] eqn:LM; [|discriminate]. destruct (lit01 tkey) as [k|] eqn:LK; [|discriminate].
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  destruct (top_cells rT 0) as [[[[np nn] nm] nk]|] eqn:TC; [|discriminate].
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (PkU.pku_flip (s_facts st) (fun _ => true) true ws) as [ws1|] eqn:FLIP; [|discriminate].
  injection AP as <-.
  apply andb_prop in COND as [COND DNN]. apply andb_prop in COND as [COND DK]. apply andb_prop in COND as [COND DM].
  apply andb_prop in COND as [COND DN]. apply andb_prop in COND as [COND DP]. apply andb_prop in COND as [COND DTR].
  apply andb_prop in COND as [COND WIN]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND OT].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply (proj1 (weqb_ok _ _)) in OT. subst oT. apply Z.ltb_lt in WLEN.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).

  pose proof (dnz_sound E _ _ Pfacts DTR) as TRNZ.
  destruct (last_opt ls) as [l|] eqn:LAST; [| exfalso; destruct LTOP as (_ & T0 & _); exact (TRNZ T0)].
  destruct LTOP as (Ltp & Ltr & Ltm & Ltk).
  pose proof (last_opt_spec ls) as LS. rewrite LAST in LS. destruct LS as [ls0 ELS].
  assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
  destruct l as [lo s].
  apply (proj1 (levels_snoc _ _ _ _)) in HLV as (L0 & FOC & LC & LS0 & LALT).
  pose proof (proj1 (Forall_forall _ _) (levels_wf _ _ _ _ TW LV) (lo, s) ltac:(rewrite ELS; apply in_app_iff; right; left; reflexivity)) as TWL. cbn [fst] in TWL.

  pose proof (lit01_sound E tmap m LM) as DMm. pose proof (lit01_sound E tkey k LK) as DKk.
  assert (PM : pe_map (elem_of (lo, s)) = m) by (rewrite DMm in Ltm; destruct (pe_map (elem_of (lo, s))), m; cbn in Ltm; congruence).
  assert (PK' : pe_key (elem_of (lo, s)) = k) by (rewrite DKk in Ltk; destruct (pe_key (elem_of (lo, s))), k; cbn in Ltk; congruence).

  pose proof (deq_sound E _ _ _ Pfacts DP) as NP. pose proof (deq_sound E _ _ _ Pfacts DN) as NN.
  pose proof (deq_sound E _ _ _ Pfacts DM) as NM. pose proof (deq_sound E _ _ _ Pfacts DK) as NK.
  pose proof (dnz_sound E _ _ Pfacts DNN) as NNZ.

  assert (NODE : exists kd, nth_error (okids lo) (Z.to_nat s) = Some kd).
  { destruct LALT as [X|[OK S0]]; [exact X| exfalso]. subst s. apply TRNZ. rewrite Ltr. unfold elem_of. unfold okids in OK.
    destruct lo; try discriminate LC; cbn [pe_rest obj_ptr okids] ; subst; cbn; reflexivity. }
  destruct NODE as [kd NKD].
  assert (SLT : s < Z.of_nat (length (okids lo))).
  { apply nth_error_Some_length' in NKD || (assert (Z.to_nat s < length (okids lo))%nat by (apply nth_error_Some; rewrite NKD; discriminate); lia). }

  assert (KZ : forall p kids, (lo = OArr p kids \/ lo = OMap p kids) -> exists ch, In ch (z_chunks (k_zone g)) /\ in_chunk ch p (OBJ_SIZE * Z.of_nat (length kids))
            /\ 0 <= fst ch /\ fst ch + (CHUNK_HDR + snd ch) <= Mem.two62Z).
  { intros p kids ALT.
    assert (NE : kids <> []) by (intros ->; destruct ALT as [-> | ->]; cbn in SLT; lia).
    assert (IZ : in_zone (k_zone g) p (OBJ_SIZE * Z.of_nat (length kids))).
    { destruct ALT as [-> | ->]; [apply tree_wf_arr in TWL; destruct TWL as (_ & _ & X & _)| apply tree_wf_map in TWL; destruct TWL as (_ & _ & _ & X & _)]; exact (proj2 (X NE)). }
    destruct IZ as (ch & Hch & ICH). exists ch. split; [exact Hch|]. split; [exact ICH|].
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (B1 & B2 & B3 & B4 & B5).
    pose proof (aw_ceiling_small segs IMGX AW model). unfold chunk_block in B1, B3. cbn [fst snd] in B1, B3. lia. }

  assert (NEW : (exists kd', nth_error (okids lo) (Z.to_nat (s + 1)) = Some kd') /\
                bv_unsigned (den E np) = pe_ptr (elem_of (lo, s + 1)) /\ bv_unsigned (den E nn) = pe_rest (elem_of (lo, s + 1)) /\
                m = pe_map (elem_of (lo, s + 1)) /\ (if m then negb k else false) = pe_key (elem_of (lo, s + 1))).
  { rewrite NN in NNZ. rewrite NP, NN. pose proof (bv_unsigned_in_range _ (den E tptr)) as RT. pose proof (bv_unsigned_in_range _ (den E trest)) as RR.
    rewrite bv_modulus_64 in RT, RR.
    destruct lo as [| | | | | | | | |p kids|p kids]; try discriminate LC; cbn [okids] in *.
    -   destruct (KZ p kids (or_introl eq_refl)) as (ch & Hch & ICH & B1 & B3).
      unfold elem_of in Ltp, Ltr, PM, PK' |- *. cbn [pe_ptr pe_rest pe_map pe_key obj_ptr okids] in Ltp, Ltr, PM, PK' |- *. subst m k. cbn [andb negb] in NNZ |- *.
      rewrite den_add_lit, den_add_wones, Ltp, Ltr. change (to_Z 24%uint63) with 24. change (to_Z 1%uint63) with 1.
      assert (S1 : s + 1 < Z.of_nat (length kids)).
      { rewrite den_add_wones, Ltr in NNZ. change (to_Z 1%uint63) with 1 in NNZ. rewrite Z.mod_small in NNZ; [lia|]. unfold two64 in *. lia. }
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE, Mem.two62Z in ICH, B1, B3.
      split; [| split; [| split; [| split; reflexivity]]].
      + destruct (nth_error kids (Z.to_nat (s + 1))) as [kd'|] eqn:NK'; [exists kd'; reflexivity| exfalso].
        apply nth_error_None in NK'. lia.
      + rewrite Z.mod_small; [lia|]. unfold two64 in *. nia.
      + rewrite Z.mod_small; [lia|]. unfold two64 in *. lia.
    -   destruct (KZ p kids (or_intror eq_refl)) as (ch & Hch & ICH & B1 & B3).
      apply tree_wf_map in TWL. destruct TWL as (EVN & _).
      unfold elem_of in Ltp, Ltr, PM, PK' |- *. cbn [pe_ptr pe_rest pe_map pe_key obj_ptr okids] in Ltp, Ltr, PM, PK' |- *. subst m.
      pose proof (Z.div_mod s 2 ltac:(lia)) as DVs. pose proof (Z.mod_pos_bound s 2 ltac:(lia)) as MBs.
      pose proof (Z.div_mod (Z.of_nat (length kids)) 2 ltac:(lia)) as DVn. pose proof (even_len_even _ kids EVN) as EVn.
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE, Mem.two62Z in ICH, B1, B3.
      assert (KEV : k = Z.even s) by (rewrite <- PK'; reflexivity).
      assert (SPAR : if k then s mod 2 = 0 else s mod 2 = 1).
      { rewrite KEV. destruct (Z.even s) eqn:EV; [rewrite Zeven_mod in EV; apply Z.eqb_eq in EV; exact EV|].
        assert (s mod 2 <> 0) by (intros X; rewrite Zeven_mod, X in EV; discriminate EV). lia. }
      destruct k; cbn [andb negb] in NNZ |- *.
      +   rewrite Ltp, Ltr.
        assert (S1 : s + 1 < Z.of_nat (length kids)) by lia.
        assert (DIV1 : (s + 1) / 2 = s / 2) by (symmetry; apply (Z.div_unique (s + 1) 2 (s / 2) 1); lia).
        split; [| split; [rewrite DIV1; reflexivity| split; [rewrite DIV1; reflexivity| split; [reflexivity|]]]].
        * destruct (nth_error kids (Z.to_nat (s + 1))) as [kd'|] eqn:NK'; [exists kd'; reflexivity| exfalso]. apply nth_error_None in NK'. lia.
        * rewrite Z.even_add, <- KEV. reflexivity.
      +   rewrite den_add_lit, den_add_wones, Ltp, Ltr. change (to_Z 48%uint63) with 48. change (to_Z 1%uint63) with 1.
        rewrite den_add_wones, Ltr in NNZ. change (to_Z 1%uint63) with 1 in NNZ.
        assert (RPOS : 1 <= Z.of_nat (length kids) / 2 - s / 2) by lia.
        rewrite Z.mod_small in NNZ by (unfold two64 in *; lia).
        assert (S1 : s + 1 < Z.of_nat (length kids)) by lia.
        assert (DIV1 : (s + 1) / 2 = s / 2 + 1) by (symmetry; apply (Z.div_unique (s + 1) 2 (s / 2 + 1) 0); lia).
        split; [| split; [| split; [| split; [reflexivity|]]]].
        * destruct (nth_error kids (Z.to_nat (s + 1))) as [kd'|] eqn:NK'; [exists kd'; reflexivity| exfalso]. apply nth_error_None in NK'. lia.
        * rewrite Z.mod_small; [rewrite DIV1; lia|]. unfold two64 in *. nia.
        * rewrite Z.mod_small; [rewrite DIV1; lia|]. unfold two64 in *. lia.
        * rewrite Z.even_add, <- KEV. reflexivity. }
  destruct NEW as ([kd' NKD'] & ENP & ENN & ENM & ENK).
  set (ls' := ls0 ++ [(lo, s + 1)]).
  assert (LV' : levels_ok (k_tree g) ls').
  { apply (proj2 (levels_snoc _ _ _ _)). split; [exact L0|]. split; [exact FOC|]. split; [exact LC|]. split; [lia|]. left. exists kd'. exact NKD'. }
  assert (LAST' : last_opt ls' = Some (lo, s + 1)) by (subst ls'; unfold last_opt; rewrite rev_app_distr; reflexivity).
  assert (RL' : removelast ls' = removelast ls) by (subst ls'; rewrite ELS, !removelast_snoc; reflexivity).
  assert (LEN' : length ls' = length ls) by (subst ls'; rewrite ELS, !length_app; reflexivity).
  pose proof (DECf E) as DEC.

  destruct (PkUSem.flip_sound E (s_facts st) Pfacts _ _ ws ws1 FLIP) as (LEN1 & INWS1 & KEEP1 & WF1 & WK1 & GH1 & CO1).
  assert (LENw1 : Z.of_nat (length ws1) < two63) by (rewrite LEN1; exact LEN).
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [] _ _ (s_next st)).
  - intros kk [].
  - constructor.
  - intros kk r [].
  - intros kk r [].
  - intros kk r a [].
  - intros k1 r1 k2 r2 a [].
  - rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E aw), (map (wden E) ws1), _, LB.
    split; [apply (mk_args_sound E 3%uint63 aw ws1 _ LENw1)|].
    split; [exact (aw_keep segs IMGX AW _ _ _ _ _ _ HA (KEEP1 LB))|].
    split; [exact (WF1 segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model) WF)|].
    apply CW3'. unfold cw_pk_holds. cbn [unparse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP map decode_pk].
    exists g, ls'. split; [| split; [| split; [exact O| split; [exact (WK1 g Wk)|]]]].
    + unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
      split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|]. split; [exact Leb|]. split; [exact Lee|]. split; [exact Lecap|].
      split.
      * rewrite LAST'. rewrite !den_b2v. rewrite ENP, ENN, ENK, ENM. repeat split; reflexivity.
      * intros X. exfalso. apply X. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
    + unfold pure_pk. rewrite LEN'. split; [exact LV'|]. split; [exact EL|]. split; [exact SZ|]. split; [| exact (conj CE ZV)].
      destruct VE as [(_ & _ & X)|X]; [exfalso; rewrite ELS in X; destruct ls0; discriminate X| right; exact X].
    + split; [| split; [exact (GH1 g GH)|]]. { unfold mem_pk in M |- *. cbn [a_root] in M |- *. rewrite RL'. exact M. }

      apply (CO1 _ g ls _ g ls' CO). intros fr v _ LE. cbn [a_cf den]. rewrite wbv_unsigned, wzero_ok. change (0 =? 0) with true.
      subst ls'. rewrite ELS in LE. refine (Z.le_trans _ _ _ _ LE).
      apply (PkCost.np_next (bmem_of segs (ms_mem ms)) (k_zone g) (k_tree g) ls0 lo s kd'); [lia| exact NKD'|].
      intros fo HFO. apply (focus_tree_wf _ _ (k_tree g) ls0 (lo, s) fo TW); [rewrite <- ELS; exact LV| exact HFO].
  - intros a FPa. split; [| intros kk r []]. left. unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
    apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws) _ a DEC)).
    destruct (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E) ws1) _ a (mk_args_sound E 3%uint63 aw ws1 _ LENw1)) FPa) as (F1 & F2 & F3).
    split; [exact F1|]. split; [exact F2|]. intros X. apply F3. apply INWS1. exact X.
  - constructor.
Qed.

Theorem next_sound : forall pc, contract_sound segs OPS MP PB (next_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [next_contract c_apply] in HAP.
  destruct (next_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. apply (Hk st' (or_introl eq_refl) E ms model); [| exact HMP| exact (next_sound_main E st ms model st' HS AP)].
       split; [reflexivity|]. intros kk Hk'. split; reflexivity. }
  all: exfalso; unfold next_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End PkNext.
