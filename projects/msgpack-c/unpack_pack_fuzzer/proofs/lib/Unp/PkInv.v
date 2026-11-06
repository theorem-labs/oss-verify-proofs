(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree KidsFacts PkOps PkLib GLib GWin GCap PkStack PkAux PkPeek.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkInv.

Definition W24 : w64 := wlit 24%uint63.

Definition geom_facts (eb ee ecap : sv) : list fact :=
  match ee with
  | VP kT o => if weqb o W24 && negb (PrimInt63.eqb kT 0%uint63) then [FULe eb (VP kT wzero); FULe ee ecap] else [FULe eb ee; FULe ee ecap]
  | _ => [FULe eb ee; FULe ee ecap]
  end.

Definition cap_facts (eb ecap : sv) : list fact :=
  match eb with
  | VP kB ob =>
      if weqb ob wzero then
        match GCap.cap_var kB ecap with
        | Some x => [FULe (VL W24) (VP x wzero); FULe (VP x wzero) (VL GW.HMAX)]
        | None => []
        end
      else []
  | _ => []
  end.

Definition kids_facts_s (cnt ptr : sv) : list fact :=
  [FULe cnt ptr; FULe (sv_alu ALU_ADD ptr (sv_md M_MUL cnt (VL (wlit 48%uint63)))) (VL KF.KF_BIG); FULe ptr (VL KF.KF_BIG)].

Definition align_fact (fs : list fact) (tptr : sv) : list fact :=
  match tptr with
  | VP kp o => if PrimInt63.eqb (PrimInt63.land (wl o) 7%uint63) 0%uint63 && negb (PrimInt63.eqb kp 0%uint63)
                  && negb (PrimInt63.leb 3%uint63 (find_align fs kp))
               then [FAlign kp 3%uint63] else []
  | _ => []
  end.

Definition inv_facts (fs : list fact) (ca : list sv) : list fact :=
  match ca with
  | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
      if PkPeek.dec_false (decide_eq0 fs trest)
      then geom_facts eb ee ecap ++ cap_facts eb ecap ++ kids_facts_s trest tptr ++ align_fact fs tptr
      else []
  | _ => []
  end.

Definition fresh_facts (fs new : list fact) : list fact :=
  List.filter (fun f => negb (existsb (fact_eqb f) fs)) new.
Definition addfacts (st : sstate) (l : list fact) : sstate := fold_right (fun f s => addfact s f) st l.

Section WithPc.
Variable INV_PC : int.

Definition pkinv_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63
      then Some [addfacts st (fresh_facts (s_facts st) (inv_facts (s_facts st) ca))]
      else None
  | None => None
  end.

Definition pkinv_contract : contract := Contract INV_PC pkinv_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma addfacts_sound : forall E l st ms model,
  st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E l. induction l as [|f l IH]; intros st ms model HS FH; [exact HS|].
  cbn [addfacts fold_right]. inversion FH as [|? ? Hf Hl]; subst.
  apply (addfact_sound segs OPS); [exact (IH st ms model HS Hl)| exact Hf].
Qed.

Lemma fresh_facts_sound : forall E fs new, Forall (fact_holds E) new -> Forall (fact_holds E) (fresh_facts fs new).
Proof.
  intros E fs new H. unfold fresh_facts. apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _].
  exact (proj1 (Forall_forall _ _) H f Hf).
Qed.

Lemma inv_facts_sound : forall E st ms model md aw ws ca,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) -> PrimInt63.eqb md 3%uint63 = true ->
  Forall (fact_holds E) (inv_facts (s_facts st) ca).
Proof.
  intros E st ms model md aw ws ca HS TO MD. apply Uint63.eqb_correct in MD. subst md.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  unfold inv_facts.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try apply Forall_nil.
  destruct (PkPeek.dec_false (decide_eq0 (s_facts st) trest)) eqn:DNZ; [|apply Forall_nil].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (mdZ & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in Leb, Lee, Lecap, LTOP.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).

  unfold PkPeek.dec_false in DNZ. destruct (decide_eq0 (s_facts st) trest) as [[|]|] eqn:DZ; try discriminate.
  pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as TNZ. apply (proj1 (eqb_iff _ _ false)) in TNZ.
  assert (TR0 : bv_unsigned (den E trest) <> 0).
  { intros X. apply TNZ. apply bv_eq. rewrite X. reflexivity. }
  destruct (last_opt ls) as [l|] eqn:LAST.
  2: { destruct LTOP as (_ & T0 & _). contradiction. }
  destruct LTOP as (TP & TRr & _ & _).
  pose proof (last_opt_spec ls) as LS. rewrite LAST in LS. destruct LS as [ls0 ELS].
  assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
  pose proof (bv_unsigned_in_range _ (den E trest)) as RTR. rewrite bv_modulus_64 in RTR.
  assert (RPOS : 0 < pe_rest (elem_of l)) by lia.
  destruct (rest_pos_node _ _ _ HLV RPOS) as (fo & FO).
  destruct l as [lo sp].
  pose proof (proj1 (Forall_forall _ _) (levels_forall _ _ HLV) (lo, sp) ltac:(apply in_app_iff; right; left; reflexivity)) as [LCp LSp].
  cbn [fst snd] in LCp, LSp.
  assert (SLT : sp < Z.of_nat (length (okids lo))).
  { unfold lev_node in FO. cbn [fst snd] in FO.
    destruct (Z_lt_ge_dec sp (Z.of_nat (length (okids lo)))) as [Lt|Ge]; [exact Lt|].
    exfalso. assert (N : nth_error (okids lo) (Z.to_nat sp) = None) by (apply nth_error_None; lia). rewrite N in FO. discriminate FO. }
  pose proof (proj1 (Forall_forall _ _) (levels_wf _ _ _ _ TW HLV) (lo, sp) ltac:(apply in_app_iff; right; left; reflexivity)) as TWL. cbn [fst] in TWL.
  destruct (PkAux.elem_of_bounds _ _ lo sp LCp LSp SLT TWL) as (ch & Hch & ICH & ERr & EAL).
  set (e := elem_of (lo, sp)) in *.

  assert (INB : In (chunk_block ch) LB) by (apply (proj1 O); unfold owned; apply in_app_iff; right; apply in_map; exact Hch).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA INB) as (Bd1 & Bd2 & Bd3 & Bd4 & Bd5).
  pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA INB) as BLO.
  pose proof (aw_ceiling_small segs IMGX AW model) as CS. unfold Mem.two62Z in CS.
  unfold chunk_block in Bd1, Bd2, Bd3, BLO. cbn [fst snd] in Bd1, Bd2, Bd3, BLO.
  unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in ICH. unfold CHUNK_HDR in Bd2, Bd3.

  assert (LSNE : ls <> []) by (rewrite ELS; destruct ls0; discriminate).
  destruct VE as [(_ & _ & E0)|[VV (CP & _)]]; [contradiction|].
  destruct VV as (V1 & V2 & V3 & V4).
  assert (SZ1 : 1 <= v_size (k_evec g)).
  { rewrite SZ, ELS, length_app. cbn [length]. lia. }
  assert (EIN : In (v_begin (k_evec g), v_bytes (k_evec g)) LB).
  { apply (proj1 O). unfold owned, evec_blocks. destruct (Z.eqb_spec (v_begin (k_evec g)) 0) as [Z0|NZ]; [contradiction|]. left. reflexivity. }
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA EIN) as (Be1 & Be2 & Be3 & Be4 & _).
  cbn [fst snd] in Be1, Be2, Be3. unfold v_bytes in Be2, Be3. rewrite EL in Be2, Be3. unfold ELEM_SIZE in Be2, Be3.
  assert (DEB : bv_unsigned (den E eb) = v_begin (k_evec g)) by (symmetry; exact Leb).
  assert (DEE : bv_unsigned (den E ee) = v_begin (k_evec g) + 24 * v_size (k_evec g)).
  { rewrite <- Lee. unfold v_end. rewrite EL. reflexivity. }
  assert (DEC : bv_unsigned (den E ecap) = v_begin (k_evec g) + 24 * v_cap (k_evec g)).
  { rewrite <- Lecap. unfold v_capend. rewrite EL. reflexivity. }
  pose proof two64_eq as T64.
  apply Forall_app. split.
  {
    unfold geom_facts.
    assert (GEN : Forall (fact_holds E) [FULe eb ee; FULe ee ecap]).
    { constructor; [|constructor; [|constructor]]; cbn [fact_holds]; rewrite ?DEB, ?DEE, ?DEC; nia. }
    destruct ee as [|kT oT| | | | | | | | |]; try exact GEN.
    destruct (weqb oT W24 && negb (PrimInt63.eqb kT 0%uint63)) eqn:C0; [|exact GEN].
    apply andb_prop in C0 as [O24 _]. apply weqb_eq in O24. subst oT.
    constructor; [|constructor; [|constructor]]; cbn [fact_holds].
    -
      rewrite DEB. pose proof (evk_range E kT) as RK.
      assert (W24v : w2Z W24 = 24) by (unfold W24; rewrite wlit_ok; reflexivity).
      rewrite den_VPu, W24v in DEE. rewrite (den_VP0 E kT wzero (weqb_refl _)).
      assert (EK : bv_unsigned (ev E kT) = v_begin (k_evec g) + 24 * v_size (k_evec g) - 24).
      { destruct (Z_lt_ge_dec (bv_unsigned (ev E kT) + 24) two64) as [Lt|Ge].
        - rewrite Z.mod_small in DEE by lia. lia.
        - exfalso. assert (X : (bv_unsigned (ev E kT) + 24) mod two64 = bv_unsigned (ev E kT) + 24 - two64).
          { symmetry. apply (Z.mod_unique_pos _ _ 1); lia. }
          rewrite X in DEE. nia. }
      rewrite EK. nia.
    - rewrite DEE, DEC. nia. }
  apply Forall_app. split.
  {
    unfold cap_facts.
    destruct eb as [|kB ob| | | | | | | | |]; try constructor.
    destruct (weqb ob wzero) eqn:OB; [|constructor].
    destruct (GCap.cap_var kB ecap) as [x|] eqn:CV; [|constructor].
    rewrite (den_VP0 E kB ob OB) in DEB.
    pose proof (evk_range E x) as RX. pose proof (evk_range E kB) as RB.
    assert (EX : bv_unsigned (ev E x) = 24 * v_cap (k_evec g)).
    { unfold GCap.cap_var in CV. destruct ecap as [| |op a1 a2| | | | | | | |]; try discriminate. destruct op; try discriminate.
      destruct a1 as [|k1 o1| | | | | | | | |]; try discriminate. destruct a2 as [|k2 o2| | | | | | | | |]; try discriminate.
      destruct (weqb o1 wzero && weqb o2 wzero) eqn:OO; [|discriminate]. apply andb_prop in OO as [O1 O2].
      assert (DC' : (bv_unsigned (ev E k1) + bv_unsigned (ev E k2)) mod two64 = v_begin (k_evec g) + 24 * v_cap (k_evec g)).
      { rewrite <- DEC. change (den E (VAlu ALU_ADD (VP k1 o1) (VP k2 o2))) with (bv_add (den E (VP k1 o1)) (den E (VP k2 o2))).
        rewrite bv_add_unsigned, (den_VP0 E k1 o1 O1), (den_VP0 E k2 o2 O2). unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
      destruct (PrimInt63.eqb k1 kB) eqn:K1.
      - injection CV as <-. apply Uint63.eqb_correct in K1. subst k1. rewrite DEB in DC'.
        apply (GCap.mod_add_cancel (v_begin (k_evec g)) _ (24 * v_cap (k_evec g))); nia.
      - destruct (PrimInt63.eqb k2 kB) eqn:K2; [|discriminate]. injection CV as <-. apply Uint63.eqb_correct in K2. subst k2.
        rewrite DEB, Z.add_comm in DC'. apply (GCap.mod_add_cancel (v_begin (k_evec g)) _ (24 * v_cap (k_evec g))); nia. }
    constructor; [|constructor; [|constructor]].
    - cbn [fact_holds]. rewrite den_VL, (den_VP0 E x wzero (weqb_refl _)), EX. unfold W24. rewrite wlit_ok. change (to_Z 24%uint63) with 24. nia.
    - cbn [fact_holds]. rewrite den_VL, (den_VP0 E x wzero (weqb_refl _)), EX, GW.HMAX_val. unfold two62Z in *. lia. }
  apply Forall_app. split.
  {
    assert (KS : Forall (fact_holds E) (KF.kids_facts trest tptr) -> Forall (fact_holds E) (kids_facts_s trest tptr)).
    { unfold KF.kids_facts, kids_facts_s. intros K. inversion K as [|? ? K1 K']; subst. inversion K' as [|? ? K2 K'']; subst.
      constructor; [exact K1|]. constructor; [|exact K''].
      cbn [fact_holds] in K2 |- *. rewrite den_sv_alu. rewrite den_sv_md. exact K2. }
    apply KS.
    apply (KF.kids_facts_sound E trest tptr (pe_rest e) (pe_ptr e)).
    - exact TRr.
    - exact TP.
    - lia.
    - lia.
    - lia.
    - unfold KF.KF_BIGZ. lia. }
  { unfold align_fact. destruct tptr as [|kp op| | | | | | | | |]; try constructor.
    destruct (PrimInt63.eqb (PrimInt63.land (wl op) 7%uint63) 0%uint63 && negb (PrimInt63.eqb kp 0%uint63)
              && negb (PrimInt63.leb 3%uint63 (find_align (s_facts st) kp))) eqn:C0; [|constructor].
    apply andb_prop in C0 as [C0 _]. apply andb_prop in C0 as [OP _].
    constructor; [|constructor]. cbn [fact_holds]. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8.
    apply Uint63.eqb_correct in OP.
    assert (O8 : w2Z op mod 8 = 0).
    { unfold w2Z. pose proof (Uint63.land_spec' (wl op) 7%uint63) as LS. rewrite OP in LS. change (to_Z 0%uint63) with 0 in LS.
      change (to_Z 7%uint63) with (Z.ones 3) in LS. rewrite Z.land_ones in LS by lia. change (2 ^ 3) with 8 in LS.
      destruct (wt op).
      - replace two63 with (1152921504606846976 * 8) by reflexivity. rewrite Z.add_comm, Z_mod_plus_full. lia.
      - rewrite Z.add_0_l. lia. }
    rewrite den_VPu in TP. pose proof (evk_range E kp) as RK.
    assert (M8 : ((bv_unsigned (ev E kp) + w2Z op) mod two64) mod 8 = 0) by (rewrite TP; exact EAL).
    rewrite two64_eq in M8. rewrite <- (Znumtheory.Zmod_div_mod 8 18446744073709551616) in M8; [|lia|lia|exists 2305843009213693952; reflexivity].
    rewrite Z.add_mod in M8 by lia. rewrite O8, Z.add_0_r, Z.mod_mod in M8 by lia. exact M8. }
Qed.

Theorem pkinv_sound : contract_sound segs OPS MP PB pkinv_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [pkinv_contract c_apply] in HA. unfold pkinv_apply in HA.
  destruct (the_op st) as [[[[md aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb md 3%uint63) eqn:MD; [|discriminate].
  injection HA as <-.
  set (st' := addfacts st (fresh_facts (s_facts st) (inv_facts (s_facts st) ca))).
  assert (OK' : st_ok segs OPS E st' ms model).
  { apply addfacts_sound; [exact HS|]. apply fresh_facts_sound. exact (inv_facts_sound E st ms model md aw ws ca HS TO MD). }
  assert (NX : s_next st' = s_next st).
  { subst st'. generalize (fresh_facts (s_facts st) (inv_facts (s_facts st) ca)). intros l. induction l as [|f l IH]; [reflexivity|].
    cbn [addfacts fold_right]. unfold addfact. cbn [s_next]. exact IH. }
  exact (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP OK').
Qed.

End Sound.
End WithPc.
End PkInv.
