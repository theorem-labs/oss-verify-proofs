(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge TdOps GLib.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG TD.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module Td.

Definition two62w : w64 := wlit bit62i.

Definition chunk_region (nxt : sv) : region :=
  Region 0%uint63 (VL (wlit 8%uint63)) true BGNone (IMap.add 0%uint63 (Gran true [Cell 0%uint63 8%uint63 nxt]) IMap.empty).

Definition chunk_region_f (kl : int) (nxt : sv) : region :=
  Region 0%uint63 (VP kl wzero) true BGNone (IMap.add 0%uint63 (Gran true [Cell 0%uint63 8%uint63 nxt]) IMap.empty).
Definition chunk_region_g (fs : list fact) (kl : int) (nxt : sv) : region := if asan_on fs then chunk_region_f kl nxt else chunk_region nxt.

Definition dec_false (o : option bool) : bool := match o with Some false => true | _ => false end.
Definition dec_true (o : option bool) : bool := match o with Some true => true | _ => false end.

Section WithPc.
Variable ZNEXT_PC : int.

Definition al8_fact (fs : list fact) (kl : int) : list fact := if asan_on fs then [FAlign kl 3%uint63] else [].
Definition znext_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 5%uint63 then
      match ca with
      | [cur; cnt] =>
          let fs := s_facts st in let n := s_next st in
          let kc := n in let kl := PrimInt63.add n 1%uint63 in
          let kn := PrimInt63.add n 2%uint63 in let kq := PrimInt63.add n 3%uint63 in
          if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63)
             && Z.ltb (Z.of_nat (length ws)) 4095
             && dec_true (decide_eq fs (getr st X10) cur) && dec_false (decide_eq0 fs cur)
          then
            let wnew := (VP kc wzero, VP kl wzero, VL (wlit 1%uint63)) in
            let factsC := [FEq (VP kc wzero) cur; FRange kc (wlit 16%uint63) two62w; FAlign kc 4%uint63;
                           FRange kl (wlit 8200%uint63) two62w; FULe (VL (wlit 8%uint63)) (VP kl wzero)] ++ al8_fact fs kl in
            let stA := setr (surg st [] [(kc, chunk_region_g fs kl (VP kn wzero))]
                               (mk_args 5%uint63 aw (ws ++ [wnew]) [VP kn wzero; VP kq wzero])
                               (factsC ++ [FRange kn (wlit 16%uint63) two62w; FAlign kn 4%uint63; FULt (VP kq wzero) cnt])
                               (PrimInt63.add n 4%uint63)) X10 (VP kc wzero) in
            let stB := setr (surg st [] [(kc, chunk_region_g fs kl (VL wzero))]
                               (mk_args 0%uint63 aw (ws ++ [wnew]) [])
                               factsC (PrimInt63.add n 4%uint63)) X10 (VP kc wzero) in
            Some [stA; stB]
          else None
      | _ => None
      end
      else None
  | None => None
  end.

Definition znext_contract : contract := Contract ZNEXT_PC znext_apply.

End WithPc.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW5 : forall ca LB ws m, cw_holds CW 5 ca LB ws m -> TD.td_client segs ca LB ws m.
Hypothesis CW5' : forall ca LB ws m, TD.td_client segs ca LB ws m -> cw_holds CW 5 ca LB ws m.
Hypothesis CW0 : forall ca LB ws m, TD.nosub ws -> cw_holds CW 0 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma env_upd_other : forall E n w k, k <> n -> ev (env_upd E n w) k = ev E k.
Proof. intros E n w k NE. cbn [env_upd ev]. destruct (PrimInt63.eqb k n) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. contradiction. Qed.

Lemma u64_of_Z : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. exact Hz. Qed.

Lemma znext_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> znext_apply st = Some sts ->
  exists st' E', In st' sts /\ env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model sts HS0 AP.
  unfold znext_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 5) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|cur [|cnt [|? ?]]]; try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND DNZ]. apply andb_prop in COND as [COND DEQ]. apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with (4611686018427387904 - 8) in NLT.
  injection AP as <-.
  set (n := s_next st) in *.
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).
  pose proof HS0 as [Ppc0 Px00 Pregs0 _ _ _ _ _ _ Pbst0 _ _ _ Pfacts0 Pops0 _ _ _].
  destruct (the_op_full st 5%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (INCA : forall v, In v [cur; cnt] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VB10 : sv_vars_below n (getr st X10) = true) by (unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  assert (VBcur : sv_vars_below n cur = true) by (apply VBo; apply INCA; left; reflexivity).
  assert (VBcnt : sv_vars_below n cnt = true) by (apply VBo; apply INCA; right; left; reflexivity).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 5%uint63) with 5 in HC.
  apply CW5 in HC. destruct HC as [HC NOSUB]. unfold td_client0 in HC. cbn [map decode_td] in HC.
  destruct HC as (cs & Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat & SEALt).

  unfold dec_false in DNZ. destruct (decide_eq0 (s_facts st) cur) as [[|]|] eqn:DZ; try discriminate.
  pose proof (decide_eq0_sound E (s_facts st) Pfacts0 _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
  destruct cs as [|[c sz] rest].
  { exfalso. cbn [hd_addr] in Hcur. apply CNZ. apply bv_eq. rewrite Hcur. reflexivity. }
  cbn [hd_addr] in Hcur. cbn [length] in Hcnt.
  unfold dec_true in DEQ. destruct (decide_eq (s_facts st) (getr st X10) cur) as [[|]|] eqn:DQ; try discriminate.
  pose proof (decide_eq_sound E (s_facts st) Pfacts0 _ _ _ DQ) as X10EQ. apply (proj1 (eqb_iff _ _ true)) in X10EQ.
  pose proof (proj1 (Forall_forall _ _) Hok (c, sz) (or_introl eq_refl)) as (C1 & C2 & C3). cbn [fst snd] in C1, C2, C3.
  pose proof (Hlb (c, sz) (or_introl eq_refl)) as CLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block (c, sz)) HA CLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
  set (nxt := hd_addr rest).

  assert (N1 : to_Z (PrimInt63.add n 1) = to_Z n + 1) by (rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (N2 : to_Z (PrimInt63.add n 2) = to_Z n + 2) by (rewrite Uint63.add_spec; change (to_Z 2%uint63) with 2; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (N3 : to_Z (PrimInt63.add n 3) = to_Z n + 3) by (rewrite Uint63.add_spec; change (to_Z 3%uint63) with 3; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (N4 : to_Z (PrimInt63.add n 4) = to_Z n + 4) by (rewrite Uint63.add_spec; change (to_Z 4%uint63) with 4; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (NE1 : n <> PrimInt63.add n 1) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE2 : n <> PrimInt63.add n 2) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE3 : n <> PrimInt63.add n 3) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE12 : PrimInt63.add n 1 <> PrimInt63.add n 2) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE13 : PrimInt63.add n 1 <> PrimInt63.add n 3) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE23 : PrimInt63.add n 2 <> PrimInt63.add n 3) by (intros X; apply (f_equal to_Z) in X; lia).
  set (E1 := env_upd E n (Z_to_bv 64 c)).
  set (E2 := env_upd E1 (PrimInt63.add n 1) (Z_to_bv 64 (8 + sz))).
  set (E3 := env_upd E2 (PrimInt63.add n 2) (Z_to_bv 64 nxt)).
  set (E' := env_upd E3 (PrimInt63.add n 3) (Z_to_bv 64 (Z.of_nat (length rest)))).
  assert (HX : env_ext n E E').
  { apply (env_ext_trans n (PrimInt63.add n 3) E E3); [lia| | apply env_upd_ext].
    apply (env_ext_trans n (PrimInt63.add n 2) E E2); [lia| | apply env_upd_ext].
    apply (env_ext_trans n (PrimInt63.add n 1) E E1); [lia| apply env_upd_ext | apply env_upd_ext]. }
  assert (EVn : ev E' n = Z_to_bv 64 c).
  { subst E' E3 E2 E1. rewrite (env_upd_other _ _ _ _ NE3), (env_upd_other _ _ _ _ NE2), (env_upd_other _ _ _ _ NE1). apply env_upd_same. }
  assert (EVn1 : ev E' (PrimInt63.add n 1) = Z_to_bv 64 (8 + sz)).
  { subst E' E3 E2 E1. rewrite (env_upd_other _ _ _ _ NE13), (env_upd_other _ _ _ _ NE12). apply env_upd_same. }
  assert (EVn2 : ev E' (PrimInt63.add n 2) = Z_to_bv 64 nxt).
  { subst E' E3 E2 E1. rewrite (env_upd_other _ _ _ _ NE23). apply env_upd_same. }
  assert (EVn3 : ev E' (PrimInt63.add n 3) = Z_to_bv 64 (Z.of_nat (length rest))).
  { subst E' E3 E2 E1. apply env_upd_same. }
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n E E' HX v (VBo v Hv))).
  assert (Dcur : den E' cur = den E cur) by exact (den_reval n E E' HX cur VBcur).
  assert (Dcnt : den E' cnt = den E cnt) by exact (den_reval n E E' HX cnt VBcnt).
  assert (D10 : den E' (getr st X10) = den E (getr st X10)) by exact (den_reval n E E' HX _ VB10).
  clearbody E'. clear E1 E2 E3.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  assert (AWE : den E' aw = den E aw) by (apply DR; rewrite ARGS; right; left; reflexivity).
  assert (WSE : map (wden E') ws = map (wden E) ws).
  { apply map_ext_in. intros [[wa wb] wc] Hw. unfold wden.
    destruct (in_flat_windows ws wa wb wc Hw) as (Ia & Ib & Ic).
    rewrite !DR; [reflexivity| | |]; rewrite ARGS; right; right; right; apply in_app_iff; left; assumption. }
  pose proof (DECf E') as DEC.
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 5 _ (map (wden E') ws) _ a DEC)). rewrite WSE. auto. }

  assert (CHB : forall a, c <= a < c + (8 + sz) ->
            (0 <= a /\ a < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha.
    assert (INB : in_iv (chunk_block (c, sz)) a) by (unfold in_iv, chunk_block, CHUNK_HDR; cbn [fst snd]; lia).
    destruct (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model _ a HA CLB INB) as [MAT NS].
    split; [unfold CHUNK_HDR in *; lia|]. split; [exact (Bc5 a INB)|]. split; [| split; [exact MAT| exact NS]].
    intros X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    destruct (Z.eq_dec (w_kind w) K_STACK) as [K|NK].
    - pose proof (proj1 (Forall_forall _ _) WF w Hw) as (_ & _ & _ & [[_ S]|[[K' _]|[K' _]]]).
      + unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. unfold CHUNK_HDR in *. lia.
      + rewrite K in K'. discriminate.
      + rewrite K in K'. unfold K_SUB, K_STACK in K'. lia.
    - exact (proj1 (Forall_forall _ _) Hws w Hw NK (c, sz) (or_introl eq_refl) a Hin INB). }
  assert (C16 : 16 <= c) by (unfold CHUNK_HDR in *; assert (c mod 16 = c - 16 * (c / 16)) by (pose proof (Z.div_mod c 16 ltac:(lia)); lia); lia).
  assert (DCUR : den E' cur = Z_to_bv 64 c) by (rewrite Dcur; apply bv_eq; rewrite Hcur, u64_of_Z; [reflexivity| unfold CHUNK_HDR in *; lia]).
  assert (DN0 : den E' (VP n wzero) = Z_to_bv 64 c) by (apply bv_eq; rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn; reflexivity).
  assert (DN1 : bv_unsigned (den E' (VP (PrimInt63.add n 1) wzero)) = 8 + sz) by (rewrite (den_VP0 E' _ wzero (weqb_refl _)), EVn1; apply u64_of_Z; unfold CHUNK_HDR in *; lia).

  assert (LT62 : c + (8 + sz) <= 4611686018427387904) by (unfold CHUNK_HDR in *; lia).
  assert (F1 : fact_holds E' (FEq (VP n wzero) cur)) by (cbn [fact_holds]; rewrite DN0, DCUR; reflexivity).
  assert (F2 : fact_holds E' (FRange n (wlit 16%uint63) two62w)).
  { cbn [fact_holds]. rewrite EVn, u64_of_Z by (unfold two64; lia). unfold two62w. rewrite !wlit_ok.
    change (to_Z bit62i) with 4611686018427387904. change (to_Z 16%uint63) with 16. unfold CHUNK_SIZE0 in *. lia. }
  assert (F3 : fact_holds E' (FAlign n 4%uint63)).
  { cbn [fact_holds]. rewrite EVn, u64_of_Z by (unfold two64; lia). change (2 ^ to_Z 4%uint63) with 16. exact C2. }
  assert (F4 : fact_holds E' (FRange (PrimInt63.add n 1) (wlit 8200%uint63) two62w)).
  { cbn [fact_holds]. rewrite EVn1, u64_of_Z by (unfold two64, CHUNK_SIZE0 in *; lia). unfold two62w. rewrite !wlit_ok.
    change (to_Z bit62i) with 4611686018427387904. change (to_Z 8200%uint63) with 8200. unfold CHUNK_SIZE0 in *. lia. }
  assert (F5 : fact_holds E' (FULe (VL (wlit 8%uint63)) (VP (PrimInt63.add n 1) wzero))).
  { cbn [fact_holds]. rewrite DN1. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. unfold CHUNK_SIZE0 in *. lia. }
  assert (F6 : fact_holds E' (FAlign (PrimInt63.add n 1) 3%uint63)).
  { cbn [fact_holds]. rewrite EVn1, u64_of_Z by (unfold two64, CHUNK_SIZE0 in *; lia). change (2 ^ to_Z 3%uint63) with 8.
    pose proof (proj2 SEALt (c, sz) (or_introl eq_refl)) as A8. cbn [snd] in A8. unfold CHUNK_HDR in *. Z.div_mod_to_equations. lia. }
  assert (FC : Forall (fact_holds E') ([FEq (VP n wzero) cur; FRange n (wlit 16%uint63) two62w; FAlign n 4%uint63;
                                      FRange (PrimInt63.add n 1) (wlit 8200%uint63) two62w; FULe (VL (wlit 8%uint63)) (VP (PrimInt63.add n 1) wzero)] ++ al8_fact (s_facts st) (PrimInt63.add n 1))).
  { apply Forall_app. split; [constructor; [exact F1|]; constructor; [exact F2|]; constructor; [exact F3|]; constructor; [exact F4|]; constructor; [exact F5|]; constructor|].
    unfold al8_fact. destruct (asan_on (s_facts st)); [constructor; [exact F6| constructor]| constructor]. }

  assert (CRR : forall nx a, inR E' n (chunk_region_g (s_facts st) (PrimInt63.add n 1) nx) a -> c <= a < c + (8 + sz)).
  { intros nx a IR. unfold chunk_region_g in IR. destruct (asan_on (s_facts st)).
    - unfold inR, loZ, hiZ in IR. cbn [chunk_region_f rg_lo rg_hi] in IR. change (keyZ 0%uint63) with 0 in IR. rewrite DN1 in IR.
      rewrite EVn, u64_of_Z in IR by (unfold two64; lia). lia.
    - unfold inR, loZ, hiZ in IR. cbn [chunk_region rg_lo rg_hi den] in IR. change (keyZ 0%uint63) with 0 in IR.
      rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 8%uint63) with 8 in IR. rewrite EVn, u64_of_Z in IR by (unfold two64; lia). unfold CHUNK_SIZE0 in *. lia. }
  assert (REGOKF : forall nx, bv_unsigned (den E' nx) = nxt -> region_ok segs (s_priv st) E' (ms_mem ms) n (chunk_region_f (PrimInt63.add n 1) nx)).
  { intros nx Hnx. apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n (chunk_region_f (PrimInt63.add n 1) nx) NZ).
    - cbn [chunk_region_f rg_cells]. apply IMap.bst_add. apply IMap.bst_empty.
    - reflexivity.
    - unfold loZ. cbn [chunk_region_f rg_lo]. change (keyZ 0%uint63) with 0. rewrite EVn, u64_of_Z by (unfold two64; lia). lia.
    - unfold hiZ. cbn [chunk_region_f rg_hi]. rewrite DN1.
      rewrite EVn, u64_of_Z by (unfold two64; lia). unfold two64, CHUNK_SIZE0 in *. lia.
    - intros a Ha. unfold loZ, hiZ in Ha. cbn [chunk_region_f rg_lo rg_hi] in Ha. change (keyZ 0%uint63) with 0 in Ha.
      rewrite DN1 in Ha. rewrite EVn, u64_of_Z in Ha by (unfold two64; lia).
      destruct (CHB a ltac:(unfold CHUNK_SIZE0 in *; lia)) as (_ & _ & _ & MT & NS). split; [exact MT| exact NS].
    - intros g gr F. cbn [chunk_region_f rg_cells] in F.
      destruct (PrimInt63.eqb 0%uint63 g) eqn:G0.
      + apply Uint63.eqb_correct in G0. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-.
        cbn [g_cells]. change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
        * split; [cbn; split; exact I|]. constructor; [|constructor].
          apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 nx nxt).
          -- change (to_Z 0%uint63) with 0. lia.
          -- change (to_Z 0%uint63) with 0. lia.
          -- change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, EVn, u64_of_Z by (unfold two64; lia). exact (proj1 Hat).
          -- exact Hnx.
        * intros c0 i [<-|[]] Hi. cbn [c_w c_idx] in *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0.
          unfold loZ, hiZ. cbn [chunk_region_f rg_lo rg_hi]. change (keyZ 0%uint63) with 0. rewrite DN1. unfold CHUNK_SIZE0 in *. lia.
      + rewrite (IMap.find_add_other_eqb _ _ _ _ IMap.bst_empty G0) in F. rewrite IMap.find_empty in F. discriminate. }
  assert (REGOK0 : forall nx, bv_unsigned (den E' nx) = nxt -> region_ok segs (s_priv st) E' (ms_mem ms) n (chunk_region nx)).
  { intros nx Hnx. apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n (chunk_region nx) NZ).
    - cbn [chunk_region rg_cells]. apply IMap.bst_add. apply IMap.bst_empty.
    - reflexivity.
    - unfold loZ. cbn [chunk_region rg_lo]. change (keyZ 0%uint63) with 0. rewrite EVn, u64_of_Z by (unfold two64; lia). lia.
    - unfold hiZ. cbn [chunk_region rg_hi den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8.
      rewrite EVn, u64_of_Z by (unfold two64; lia). unfold two64, CHUNK_SIZE0 in *. lia.
    - intros a Ha. unfold loZ, hiZ in Ha. cbn [chunk_region rg_lo rg_hi den] in Ha. change (keyZ 0%uint63) with 0 in Ha.
      rewrite wbv_unsigned, wlit_ok in Ha. change (to_Z 8%uint63) with 8 in Ha. rewrite EVn, u64_of_Z in Ha by (unfold two64; lia).
      destruct (CHB a ltac:(unfold CHUNK_SIZE0 in *; lia)) as (_ & _ & _ & MT & NS). split; [exact MT| exact NS].
    - intros g gr F. cbn [chunk_region rg_cells] in F.
      destruct (PrimInt63.eqb 0%uint63 g) eqn:G0.
      + apply Uint63.eqb_correct in G0. subst g. rewrite IMap.find_add_same in F by apply IMap.bst_empty. injection F as <-.
        cbn [g_cells]. change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
        * split; [cbn; split; exact I|]. constructor; [|constructor].
          apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 nx nxt).
          -- change (to_Z 0%uint63) with 0. lia.
          -- change (to_Z 0%uint63) with 0. lia.
          -- change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, EVn, u64_of_Z by (unfold two64; lia). exact (proj1 Hat).
          -- exact Hnx.
        * intros c0 i [<-|[]] Hi. cbn [c_w c_idx] in *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0.
          unfold loZ, hiZ. cbn [chunk_region rg_lo rg_hi den]. change (keyZ 0%uint63) with 0. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. lia.
      + rewrite (IMap.find_add_other_eqb _ _ _ _ IMap.bst_empty G0) in F. rewrite IMap.find_empty in F. discriminate. }
  assert (REGOK : forall nx, bv_unsigned (den E' nx) = nxt -> region_ok segs (s_priv st) E' (ms_mem ms) n (chunk_region_g (s_facts st) (PrimInt63.add n 1) nx)).
  { intros nx Hnx. unfold chunk_region_g. destruct (asan_on (s_facts st)); [exact (REGOKF nx Hnx)| exact (REGOK0 nx Hnx)]. }

  assert (WNEW : wden E' (VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63)) = Win c (8 + sz) K_BLOCK).
  { unfold wden. rewrite DN1. rewrite DN0, u64_of_Z by (unfold two64; lia). cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (LEN' : Z.of_nat (length (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))])) < two63) by (rewrite length_app; cbn [length]; unfold two63; lia).
  assert (WSE' : map (wden E') (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))]) = map (wden E) ws ++ [Win c (8 + sz) K_BLOCK]).
  { rewrite map_app, WSE. cbn [map]. rewrite WNEW. reflexivity. }

  assert (SURG : forall nx (md' : int) ca' nf,
     bv_unsigned (den E' nx) = nxt ->
     cw_holds CW (to_Z md') (map (den E') ca') LB (map (wden E) ws ++ [Win c (8 + sz) K_BLOCK]) (ms_mem ms) ->
     Forall (fact_holds E') nf ->
     st_ok segs OPS E' (setr (surg st [] [(n, chunk_region_g (s_facts st) (PrimInt63.add n 1) nx)]
                               (mk_args md' aw (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))]) ca') nf
                               (PrimInt63.add n 4)) X10 (VP n wzero)) ms model).
  { intros nx md' ca' nf Hnx HCW HNF.
    apply setreg_sound; [| intros X; discriminate X| transitivity (den E' (getr st X10)); [reflexivity|]; rewrite D10, X10EQ, <- Dcur, DCUR, DN0; reflexivity].
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [(n, chunk_region_g (s_facts st) (PrimInt63.add n 1) nx)] _ _ (PrimInt63.add n 4)).
    - intros k [].
    - constructor; [intros []| constructor].
    - intros k r [H|[]]. injection H as <- <-. exact NZ.
    - intros k r [H|[]]. injection H as <- <-. exact (REGOK nx Hnx).
    - intros k r a [H|[]] IR. injection H as <- <-. left.
      apply CRR in IR.
      destruct (CHB a IR) as (RA & NI & NW & _). exact (FPold a RA NI NW).
    - intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE12'. injection X1 as <- <-. injection X2 as <- <-. contradiction.
    - rewrite (ho_holds _ _ _ _ _ HOPS).
      exists (to_Z md'), (den E' aw), (map (wden E') (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))])), (map (den E') ca'), LB.
      split; [apply mk_args_sound; exact LEN'|].
      split.
      { rewrite AWE, WSE'. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA). apply wins_keep_intro.
        - intros w Hw. apply in_app_iff in Hw as [Hw|[<-|[]]]; [left; exact Hw| right]. split; [unfold aw_tied, K_STACK, K_GHOST; cbn [w_kind]; unfold K_BLOCK; lia|].
          intros _ g0 Hg K a Ha Hb. apply in_app_iff in Hg as [Hg|[<-|[]]]; [| cbn [w_kind] in K; unfold K_GHOST, K_BLOCK in K; lia].
          exact (proj1 (Forall_forall _ _) Hws g0 Hg ltac:(unfold K_STACK, K_GHOST in *; lia) (c, sz) (or_introl eq_refl) a Ha Hb).
        - intros w Hw. left. apply in_app_iff. left. exact Hw. }
      split.
      + rewrite WSE'. unfold windows_wf in *. apply Forall_app. split; [exact WF|]. constructor; [|constructor].
        unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [lia|]. split; [unfold CHUNK_SIZE0 in *; lia|]. split; [unfold two64, CHUNK_SIZE0 in *; lia|].
        right; left. split; [reflexivity|]. exact CLB.
      + rewrite WSE'. exact HCW.
    - intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ (to_Z md') _ (map (wden E') (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))])) _ a (mk_args_sound E' md' aw _ _ LEN'))) in FPa as (RA & NI & NW).
      rewrite WSE' in NW. split.
      + left. apply (FPold a RA NI). intros X. apply NW. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
      + intros k r [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
        cbn [map]. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        apply CRR in IR. lia.
    - exact HNF. }

  destruct rest as [|[c' sz'] rest'].
  -
    assert (OUT : st_ok segs OPS E' (setr (surg st [] [(n, chunk_region_g (s_facts st) (PrimInt63.add n 1) (VL wzero))]
                               (mk_args 0%uint63 aw (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))]) [])
                               ([FEq (VP n wzero) cur; FRange n (wlit 16%uint63) two62w; FAlign n 4%uint63;
                                FRange (PrimInt63.add n 1) (wlit 8200%uint63) two62w; FULe (VL (wlit 8%uint63)) (VP (PrimInt63.add n 1) wzero)] ++ al8_fact (s_facts st) (PrimInt63.add n 1))
                               (PrimInt63.add n 4)) X10 (VP n wzero)) ms model).
    { apply (SURG (VL wzero) 0%uint63 []).
      - cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
      - apply CW0. apply TD.nosub_app; [exact NOSUB| apply TD.nosub_one; left; unfold K_BLOCK, K_SUB; lia].
      - exact FC. }
    eexists. exists E'. split; [right; left; reflexivity|]. split; [exact HX| exact OUT].
  -
    pose proof (proj1 (Forall_forall _ _) Hok (c', sz') (or_intror (or_introl eq_refl))) as (C1' & C2' & C3'). cbn [fst snd] in C1', C2', C3'.
    pose proof (Hlb (c', sz') (or_intror (or_introl eq_refl))) as CLB'.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block (c', sz')) HA CLB') as (Bd1 & Bd2 & Bd3 & _ & _).
    unfold chunk_block in Bd1, Bd2, Bd3. cbn [fst snd] in Bd1, Bd2, Bd3.
    assert (C16' : 16 <= c') by (assert (c' mod 16 = c' - 16 * (c' / 16)) by (pose proof (Z.div_mod c' 16 ltac:(lia)); lia); lia).
    cbn [hd_addr] in nxt. subst nxt.
    assert (DN2 : bv_unsigned (den E' (VP (PrimInt63.add n 2) wzero)) = c') by (rewrite (den_VP0 E' _ wzero (weqb_refl _)), EVn2; apply u64_of_Z; unfold two64, CHUNK_HDR in *; lia).
    assert (LENR : Z.of_nat (length rest') < two64 - 1).
    { pose proof (bv_unsigned_in_range _ (den E cnt)) as R. rewrite Hcnt in R. cbn [length] in R. rewrite !Nat2Z.inj_succ in R.
      unfold bv_modulus in R. cbn [Z.of_N] in R. unfold two64. lia. }
    assert (DN3 : bv_unsigned (den E' (VP (PrimInt63.add n 3) wzero)) = Z.of_nat (length ((c', sz') :: rest'))).
    { rewrite (den_VP0 E' _ wzero (weqb_refl _)), EVn3. apply u64_of_Z. cbn [length]. unfold two64 in *. lia. }
    assert (OUT : st_ok segs OPS E' (setr (surg st [] [(n, chunk_region_g (s_facts st) (PrimInt63.add n 1) (VP (PrimInt63.add n 2) wzero))]
                               (mk_args 5%uint63 aw (ws ++ [(VP n wzero, VP (PrimInt63.add n 1) wzero, VL (wlit 1%uint63))])
                                        [VP (PrimInt63.add n 2) wzero; VP (PrimInt63.add n 3) wzero])
                               (([FEq (VP n wzero) cur; FRange n (wlit 16%uint63) two62w; FAlign n 4%uint63;
                                 FRange (PrimInt63.add n 1) (wlit 8200%uint63) two62w; FULe (VL (wlit 8%uint63)) (VP (PrimInt63.add n 1) wzero)] ++ al8_fact (s_facts st) (PrimInt63.add n 1))
                                ++ [FRange (PrimInt63.add n 2) (wlit 16%uint63) two62w; FAlign (PrimInt63.add n 2) 4%uint63;
                                    FULt (VP (PrimInt63.add n 3) wzero) cnt])
                               (PrimInt63.add n 4)) X10 (VP n wzero)) ms model).
    { apply (SURG (VP (PrimInt63.add n 2) wzero) 5%uint63 [VP (PrimInt63.add n 2) wzero; VP (PrimInt63.add n 3) wzero]).
      - exact DN2.
      - apply CW5'. split; [| apply TD.nosub_app; [exact NOSUB| apply TD.nosub_one; left; unfold K_BLOCK, K_SUB; lia]]. unfold td_client0. cbn [map decode_td]. rewrite DN2, DN3.
        exists ((c', sz') :: rest'). split; [reflexivity|]. split; [reflexivity|].
        split; [exact (Forall_inv_tail Hok)|]. split; [inversion Hdisj; assumption|].
        split; [intros x Hx; apply Hlb; right; exact Hx|]. split; [| split; [exact (proj2 Hat)|]].
        2: {
             apply Seal.seal_ok_app; [| constructor; [cbn [w_kind]; unfold K_BLOCK, Seal.K_TWIN; lia| constructor]].
             apply (Seal.seal_ok_mono _ _ _ _ SEALt); [intros w Hw _; exact Hw| intros x Hx; right; exact Hx]. }
        apply Forall_app. split.
        + apply Forall_forall. intros w Hw NK x Hx. exact (proj1 (Forall_forall _ _) Hws w Hw NK x (or_intror Hx)).
        + constructor; [|constructor]. cbn [w_kind w_iv w_lo w_len]. intros _ x Hx a Ha Hb.
          inversion Hdisj as [|hd tl HD _]; subst. pose proof (proj1 (Forall_forall _ _) HD x Hx) as D.
          unfold chunk_disj, rdisj, chunk_block, in_iv, w_iv, CHUNK_HDR in D, Ha, Hb. cbn [fst snd w_lo w_len] in D, Ha, Hb. lia.
      - apply Forall_app. split; [exact FC|]. constructor; [| constructor; [| constructor; [|constructor]]]; cbn [fact_holds].
        + rewrite EVn2, u64_of_Z by (unfold two64, CHUNK_HDR in *; lia). unfold two62w. rewrite !wlit_ok.
          change (to_Z bit62i) with 4611686018427387904. change (to_Z 16%uint63) with 16. unfold CHUNK_HDR, CHUNK_SIZE0 in *. lia.
        + rewrite EVn2, u64_of_Z by (unfold two64, CHUNK_HDR in *; lia). change (2 ^ to_Z 4%uint63) with 16. exact C2'.
        + rewrite DN3, Dcnt, Hcnt. cbn [length]. lia. }
    eexists. exists E'. split; [left; reflexivity|]. split; [exact HX| exact OUT].
Qed.

Theorem znext_sound : forall pc, contract_sound segs OPS MP PB (znext_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [znext_contract c_apply] in HAP.
  destruct (znext_sound_main E st ms model sts HS HAP) as (st' & E' & IN & HX & HS').
  exact (Hk st' IN E' ms model HX HMP HS').
Qed.

End Sound.

End Td.
