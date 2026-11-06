(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree TdOps CapLen TdEnter PkOps PkLib GLib GWin PkStack PkAux.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkU PkUSwap.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG GW TR TD PK PKL PkStack PkAux CapLen.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkExit.
Import TdEnter.

Section WithPc.
Variable EXIT_PC : int.

Definition pkexit_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match parse_ca ca with
      | Some c =>
          match c_zh c with
          | VP kZ oZ =>
              let n := s_next st in
              if common_ok st ws && kinds_lit ws && weqb oZ wzero then
              match sub_anchors st ws, IMap.find kZ (s_regs st) with
              | Some ks, Some rZ =>
                  if match cell_at rZ 24 8%uint63 with Some v => sv_eqb v (c_c0 c) | None => false end then
                  match PkU.pku_drop (s_facts st) ws with
                  | None => None
                  | Some ws0 =>
                  let kept := List.filter is_kept ws0 in
                  match c_eb c with
                  | VL z =>
                      if weqb z wzero
                      then Some [surg st ks [] (mk_args 5%uint63 aw kept [c_c0 c; VP n wzero]) [] (PrimInt63.add n 1%uint63)]
                      else None
                  | VP kB oB =>

                      match cap_len kB (c_ecap c) with
                      | Some lenB =>
                          if weqb oB wzero && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kB 1%uint63)
                             && (dec_true (decide_ltu (s_facts st) (VL wzero) lenB) || dec_true (decide_ltu (s_facts st) (c_eb c) (c_ecap c))) && anchor_free st ks kB
                          then
                               Some [surg st ks [(kB, empty_region lenB)]
                                       (mk_args 5%uint63 aw (kept ++ [(VP kB wzero, lenB, VL (wlit 1%uint63))]) [c_c0 c; VP n wzero])
                                       (FULt (VL wzero) lenB :: vd_facts (c_eb c) (c_ee c) (PrimInt63.add n 1%uint63) 24%uint63) (PrimInt63.add n 2%uint63)]
                          else None
                      | None => None
                      end
                  | _ => None
                  end
                  end
                  else None
              | _, _ => None
              end
              else None
          | _ => None
          end
      | None => None
      end
      else None
  | None => None
  end.

Definition pkexit_contract : contract := Contract EXIT_PC pkexit_apply.
End WithPc.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Hypothesis CW5' : forall ca LB ws m, TD.td_client segs ca LB ws m -> cw_holds CW 5 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Local Ltac inl := cbn [In]; repeat (first [left; reflexivity| right]).

Lemma pkexit_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> pkexit_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP.
  unfold pkexit_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbn [parse_ca c_root c_rootT c_n1 c_P1 c_zh c_c0 c_eb c_ee c_ecap c_tptr c_trest c_tmap c_tkey c_cf c_fT c_fN c_fP] in AP.
  destruct zh as [|kZ oZ| | | | | | | | |]; try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND OZ]. apply andb_prop in COND as [COND KL].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with 4611686018427387896 in NLT.
  apply (proj1 (weqb_ok _ _)) in OZ. subst oZ.
  destruct (sub_anchors st ws) as [ks|] eqn:SA; [|discriminate].
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:CELL; [|discriminate] end.
  destruct (PkU.pku_drop (s_facts st) ws) as [ws0|] eqn:DROP; [|discriminate].
  set (n := s_next st) in *.
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).
  pose proof HS0 as [Ppc0 Px00 Pregs0 _ _ _ _ _ _ Pbst0 _ _ _ Pfacts0 Pops0 _ _ _].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  destruct (sub_anchors_spec st ws ks SA) as [KS1 KS2].

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  change (v_begin (k_evec g) = bv_unsigned (den E eb)) in Leb.
  change (v_capend (k_evec g) = bv_unsigned (den E ecap)) in Lecap.
  change (z_head (k_zone g) = bv_unsigned (den E c0)) in Lc0.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).
  pose proof (proj1 ZV) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  set (cs := z_chunks (k_zone g)) in *.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.

  assert (TOK : Forall tchunk_ok cs) by (apply Forall_forall; intros c Hc; exact (Z3 c Hc)).
  assert (OWNCH : forall c, In c cs -> In (chunk_block c) (owned g)) by (intros c Hc; unfold owned; apply in_app_iff; right; apply in_map; exact Hc).
  assert (CNT : Z.of_nat (length cs) <= 4611686018427387904).
  { apply (chunks_len_bound cs 4611686018427387904 TOK Z7); [|lia]. intros c Hc.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block c) HA (proj1 O _ (OWNCH c Hc))) as (B1 & B2 & B3 & _).
    unfold chunk_block, CHUNK_HDR in B1, B2, B3. cbn [fst snd] in B1, B2, B3. lia. }

  assert (N1 : to_Z (PrimInt63.add n 1) = to_Z n + 1) by (rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (UPDO : forall E0 k w k', k' <> k -> ev (env_upd E0 k w) k' = ev E0 k').
  { intros E0 k w k' NE. cbn [env_upd ev]. destruct (PrimInt63.eqb k' k) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. contradiction. }
  set (E1 := env_upd E n (Z_to_bv 64 (Z.of_nat (length cs)))).
  set (E' := env_upd E1 (PrimInt63.add n 1) (Z_to_bv 64 (v_size (k_evec g)))).
  assert (HX : env_ext n E E').
  { apply (env_ext_trans n (PrimInt63.add n 1) E E1); [lia| apply env_upd_ext| apply env_upd_ext]. }
  assert (EVn : ev E' n = Z_to_bv 64 (Z.of_nat (length cs))).
  { subst E' E1. rewrite UPDO by (intros X; apply (f_equal to_Z) in X; lia). apply env_upd_same. }
  assert (EVj1 : ev E' (PrimInt63.add n 1) = Z_to_bv 64 (v_size (k_evec g))) by (subst E'; apply env_upd_same).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n E E' HX v (VBo v Hv))).
  assert (INW : forall a b c, In (a, b, c) ws -> In a (op_args o) /\ In b (op_args o) /\ In c (op_args o)).
  { intros a b c Hw. destruct (in_flat_windows ws a b c Hw) as (Ia & Ib & Ic). rewrite ARGS.
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (INCA : forall v, In v [root; rootT; n1; P1; VP kZ wzero; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (EVR : forall k o', In (VP k o') (op_args o) -> ev E' k = ev E k).
  { intros k o' Hin. apply (ev_reval n E E' HX). exact (VBo _ Hin). }
  assert (WSE : map (wden E') ws = map (wden E) ws).
  { apply map_ext_in. intros [[wa wb] wc] Hw. unfold wden. destruct (INW wa wb wc Hw) as (Ia & Ib & Ic). rewrite !DR by assumption. reflexivity. }
  clearbody E'.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear Ppc0 Px00 Pregs0 Pbst0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (DECf E') as DEC.
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E') ws) _ a DEC)). rewrite WSE. auto. }

  assert (SUBR : forall w3 a, In w3 ws -> is_sub w3 = true -> in_iv (w_iv (wden E w3)) a ->
            exists k0 r0, In k0 ks /\ IMap.find k0 (s_regs st) = Some r0 /\ inR E' k0 r0 a).
  { intros w3 a Hw3 SB Ha. destruct (KS2 w3 Hw3 SB) as (k0 & Hk0 & AN).
    destruct (sub_anchor_spec st w3 k0 AN) as (len & kd & r0 & -> & K0 & K1 & F0 & LO & W0 & HI).
    exists k0, r0. split; [exact Hk0|]. split; [exact F0|].
    destruct (INW _ _ _ Hw3) as (Ia & Ib & Ic).
    unfold inR, loZ, hiZ. rewrite LO, HI. change (keyZ 0%uint63) with 0. rewrite (DR len Ib), (EVR k0 wzero Ia).
    unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E k0 wzero (weqb_refl _)) in Ha. lia. }

  assert (OWNB : forall ob a, In ob (owned g) -> in_iv ob a ->
            (0 <= a /\ a < two64) /\ ~ in_ivs IMGX a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None /\
            (FP OPS E' (op_args o) a \/ exists k0 r0, In k0 ks /\ IMap.find k0 (s_regs st) = Some r0 /\ inR E' k0 r0 a)).
  { intros ob a Hob Ha. pose proof (proj1 O ob Hob) as OLB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model ob HA OLB) as (B1 & B2 & B3 & B4 & B5).
    destruct (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model ob a HA OLB Ha) as [MAT NS].
    assert (RA : 0 <= a /\ a < two64) by (unfold in_iv in Ha; lia).
    split; [exact RA|]. split; [exact (B5 a Ha)|]. split; [exact MAT|]. split; [exact NS|].
    destruct (in_ws_dec (map (wden E) ws) a) as [IW|NW].
    - right. apply (proj1 (in_ws_map_iff E ws a)) in IW as (w3 & Hw3 & Hin).
      destruct (Z.eq_dec (w_kind (wden E w3)) K_STACK) as [K|NK].
      + exfalso. pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hw3)) as (_ & _ & _ & [[_ S]|[[K' _]|[K' _]]]).
        * unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. unfold in_iv in Ha. lia.
        * rewrite K in K'. discriminate.
        * rewrite K in K'. unfold K_SUB, K_STACK in K'. lia.
      + destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3) NK) as [[_ D]|[NB ET]].
        * exfalso. exact (D ob Hob a Hin Ha).
        * apply (SUBR w3 a Hw3); [|exact Hin]. destruct ET as (K6 & _).
          pose proof (proj1 (forallb_forall _ _) KL w3 Hw3) as Q. cbn beta in Q. unfold is_sub.
          destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate]. rewrite (kind_of_sound E w3 kd KD) in K6. unfold K_ETOP in K6. subst kd. reflexivity.
    - left. exact (FPold a RA (B5 a Ha) NW). }

  assert (SUBK : forall w3, In w3 ws -> is_kept w3 = false -> K_SUB <= w_kind (wden E w3) < K_GHOST).
  { intros w3 Hw3 IK. pose proof (kept_or_sub ws w3 KL Hw3 IK) as IS. unfold is_sub in IS. destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate IS].
    rewrite (kind_of_sound E w3 kd KD). apply andb_prop in IS as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2. unfold K_SUB, K_GHOST. lia. }

  destruct (PkU.pku_drop_spec E (s_facts st) Pfacts0 ws ws0 DROP) as (DSUB & DOLD & DLEN).
  set (kept := List.filter is_kept ws0) in *.
  assert (KEPT : forall w, In w kept -> In w ws /\ is_kept w = true) by (intros w Hw; apply filter_In in Hw; split; [exact (DSUB w (proj1 Hw))| exact (proj2 Hw)]).
  assert (LENK : (length kept <= length ws)%nat).
  { assert (X : (length kept <= length ws0)%nat) by (subst kept; clear; induction ws0 as [|w ws IH]; cbn; [lia|]; destruct (is_kept w); cbn; lia). lia. }
  assert (WSK : map (wden E') kept = map (wden E) kept).
  { apply map_ext_in. intros [[wa wb] wc] Hw. destruct (KEPT _ Hw) as [Hw' _]. unfold wden. destruct (INW wa wb wc Hw') as (Ia & Ib & Ic). rewrite !DR by assumption. reflexivity. }

  assert (TD5 : forall wsx, Forall (fun w => w_kind w <> K_STACK -> forall c, In c cs -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) wsx ->
            Seal.seal_ok wsx cs -> TD.nosub wsx ->
            TD.td_client segs (map (den E') [c0; VP n wzero]) LB wsx (ms_mem ms)).
  { intros wsx HW SEALx NSx. split; [| exact NSx]. unfold TD.td_client0. cbn [map TD.decode_td]. exists cs.
    split. { rewrite (DR c0 ltac:(apply INCA; inl)), <- Lc0. subst cs. unfold z_head, TD.hd_addr. reflexivity. }
    split. { rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, u64_of_Z; [reflexivity| unfold two64; lia]. }
    split; [exact TOK|]. split; [exact Z7|]. split; [intros c Hc; exact (proj1 O _ (OWNCH c Hc))|]. split; [exact HW| split; [exact CH| exact SEALx]]. }
  assert (KEPTW : Forall (fun w => w_kind w <> K_STACK -> forall c, In c cs -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) (map (wden E) kept)).
  { apply Forall_forall. intros w Hw NK c Hc a Ha Hb. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' IK].
    pose proof (is_kept_kind E w3 IK) as KK.
    destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3') NK) as [[_ D]|[NB (K6 & _)]].
    - exact (D (chunk_block c) (OWNCH c Hc) a Ha Hb).
    - unfold K_ETOP in K6. lia. }
  assert (KNOSUB : TD.nosub (map (wden E) kept)).
  { apply TD.nosub_kinds. intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [_ IK]. pose proof (is_kept_kind E w3 IK) as KK. unfold K_SUB, K_GHOST. lia. }
  assert (KSEAL : Seal.seal_ok (map (wden E) kept) cs).
  { destruct GH as [SE _]. apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw _. apply in_map_iff in Hw as (w3 & <- & Hw3).
    apply in_map. exact (proj1 (KEPT w3 Hw3)). }
  assert (KEPTWF : Forall (window_wf LB (aw_ceiling segs IMGX AW model)) (map (wden E) kept)).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' _].
    exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hw3')). }
  assert (HKS : forall k, In k ks -> PrimInt63.eqb k 0%uint63 = false /\ exists r, IMap.find k (s_regs st) = Some r /\ rg_w r = true).
  { intros k Hk. destruct (KS1 k Hk) as (w3 & Hw3 & SB & AN).
    destruct (sub_anchor_spec st w3 k AN) as (len & kd & r0 & -> & K0 & K1 & F0 & LO & W0 & HI). split; [exact K0|]. exists r0. auto. }

  assert (NEWFP : forall a, ~ in_ivs IMGX a -> 0 <= a < two64 -> ~ in_ws (map (wden E) kept) a ->
            FP OPS E' (op_args o) a \/ exists k0 r0, In k0 ks /\ IMap.find k0 (s_regs st) = Some r0 /\ inR E' k0 r0 a).
  { intros a NI RA NW. destruct (in_ws_dec (map (wden E) ws) a) as [IW|NWo]; [| left; exact (FPold a RA NI NWo)].
    apply (proj1 (in_ws_map_iff E ws a)) in IW as (w3 & Hw3 & Hin).
    destruct (is_kept w3) eqn:IK.
    - exfalso. destruct (DOLD w3 Hw3) as [Hw0|[q PVq]]; [| exact (PkUSwap.no_byte _ q a PVq Hin)].
      apply NW. apply in_ivs_In. exists (w_iv (wden E w3)). split; [| exact Hin]. apply in_map. apply in_map. apply filter_In. auto.
    - right. exact (SUBR w3 a Hw3 (kept_or_sub ws w3 KL Hw3 IK) Hin). }
  exists E'. split; [exact HX|].

  destruct eb as [z|kB oB| | | | | | | | |]; try discriminate.
  -
    destruct (weqb z wzero) eqn:ZZ; [|discriminate]. injection AP as <-.
    assert (LEN' : Z.of_nat (length kept) < two63) by (unfold two63; lia).
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH ks [] _ _ (PrimInt63.add n 1)).
    + exact HKS.
    + constructor.
    + intros k r [].
    + intros k r [].
    + intros k r a [].
    + intros k1 r1 k2 r2 a [].
    + rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 5, (den E' aw), (map (wden E') kept), (map (den E') [c0; VP n wzero]), LB.
      split; [apply (mk_args_sound E' 5%uint63 aw kept _ LEN')|].
      split.
      { rewrite (DR aw ltac:(rewrite ARGS; right; left; reflexivity)), WSK. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA). apply wins_keep_intro.
        - intros w Hw. left. apply in_map_iff in Hw as (w3 & <- & Hw3). apply in_map. exact (proj1 (KEPT w3 Hw3)).
        - intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (is_kept w3) eqn:IK.
          + destruct (DOLD w3 Hw3) as [Hw0|[q PVq]].
            * left. apply in_map. subst kept. apply filter_In. split; assumption.
            * right. split; [exact (PkUSwap.not_tied _ q PVq)|]. intros HK _. exfalso. destruct (PK.pku_val_kind _ q PVq) as [K0 _]. unfold heap_kind, K_BLOCK in HK. lia.
          + exfalso. pose proof (SUBK w3 Hw3 IK) as [K1 K2].
            destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3) ltac:(unfold K_SUB, K_STACK in *; lia)) as [[KD _]|[_ ET]].
            * unfold K_SUB, K_GHOST, K_BLOCK in *. lia.
            * destruct ET as (_ & VNZ & _). apply VNZ. apply (proj1 (weqb_ok _ _)) in ZZ. subst z. rewrite Leb. cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity. }
      split.
      * unfold windows_wf. rewrite WSK. exact KEPTWF.
      * apply CW5'. apply TD5; rewrite WSK; [exact KEPTW| exact KSEAL| exact KNOSUB].
    + intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 5 _ (map (wden E') kept) _ a (mk_args_sound E' 5%uint63 aw kept _ LEN'))) in FPa as (RA & NI & NW).
      rewrite WSK in NW. split; [exact (NEWFP a NI RA NW)| intros k r []].
    + constructor.
  -
    destruct (cap_len kB ecap) as [lenB|] eqn:CLB; [|discriminate].
    match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
    injection AP as <-.
    apply andb_prop in C2 as [C2 AFB]. apply andb_prop in C2 as [C2 LPOS].
    apply andb_prop in C2 as [C2 KB1]. apply andb_prop in C2 as [OB KB0].
    apply (proj1 (weqb_ok _ _)) in OB. subst oB.
    apply negb_true_iff in KB0. apply negb_true_iff in KB1.
    assert (DLB : den E' lenB = den E lenB).
    { apply (den_reval n E E' HX). apply (cap_len_below n kB ecap lenB CLB); [apply VBo; apply INCA; inl| change (sv_vars_below n (VP kB wzero) = true); apply VBo; apply INCA; inl]. }
    assert (LPZ' : 0 < bv_unsigned (den E lenB) \/ v_begin (k_evec g) < v_capend (k_evec g)).
    { apply orb_prop in LPOS as [LPa|LPa].
      - left. pose proof (dltu_sound E' (s_facts st) (VL wzero) lenB Pfacts LPa) as Q. rewrite den_VL, DLB in Q. change (w2Z wzero) with 0 in Q. exact Q.
      - right. pose proof (dltu_sound E' (s_facts st) (VP kB wzero) ecap Pfacts LPa) as Q.
        rewrite (DR (VP kB wzero)), (DR ecap) in Q by (apply INCA; inl). rewrite <- Leb, <- Lecap in Q. exact Q. }

    assert (KBV : bv_unsigned (ev E kB) = v_begin (k_evec g)) by (rewrite Leb; symmetry; exact (den_VP0 E kB wzero (weqb_refl _))).
    assert (VX3 : v_begin (k_evec g) <> 0).
    { intros X. destruct VE as [(B0 & C0 & LS0)|[(VV1 & VV2 & VV3 & VV4) CP]]; [| exact (VV3 X)].

      assert (Q : bv_unsigned (den E lenB) = 0).
      { apply (cap_len_sound E kB ecap lenB 0 CLB); [| lia | rewrite KBV, B0; lia].
        rewrite <- Lecap, KBV. unfold v_capend. rewrite B0, C0. lia. }
      destruct LPZ' as [LPZ|BLT]; [lia| unfold v_capend in BLT; rewrite B0, C0 in BLT; lia]. }
    pose proof (owned_evec g VX3) as OWN.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5). cbn [fst snd] in Bb1, Bb2, Bb3.
    pose proof (aw_ceiling_small segs IMGX AW model) as CEILB. unfold Mem.two62Z in CEILB.
    assert (SZC : bv_unsigned (den E lenB) = v_bytes (k_evec g)).
    { apply (cap_len_sound E kB ecap lenB _ CLB); [| lia | rewrite KBV; lia].
      rewrite <- Lecap, KBV. unfold v_capend, v_bytes. reflexivity. }
    assert (LPZ : 0 < bv_unsigned (den E lenB)).
    { destruct LPZ' as [LPq|BLT]; [exact LPq|]. rewrite SZC. unfold v_capend, v_bytes in *. lia. }
    assert (EkB : ev E' kB = ev E kB) by (apply (EVR kB wzero); apply INCA; inl).
    assert (KBV' : bv_unsigned (ev E' kB) = v_begin (k_evec g)) by (rewrite EkB; exact KBV).
    assert (HIB : hiZ E' (empty_region lenB) = v_bytes (k_evec g)).
    { unfold hiZ. cbn [empty_region rg_hi]. rewrite DLB. exact SZC. }
    assert (LOE : loZ (empty_region lenB) = 0) by reflexivity.
    assert (REGB : region_ok segs (s_priv st) E' (ms_mem ms) kB (empty_region lenB)).
    { apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) kB (empty_region lenB) KB0).
      - apply IMap.bst_empty.
      - reflexivity.
      - rewrite LOE, KBV'. lia.
      - rewrite HIB, KBV'. unfold two64 in *. lia.
      - intros a Ha. rewrite LOE, HIB, KBV' in Ha.
        destruct (OWNB _ a OWN ltac:(unfold in_iv; cbn [fst snd]; lia)) as (_ & _ & MT & NS & _). split; [exact MT| exact NS].
      - intros gk gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }
    set (ws' := kept ++ [(VP kB wzero, lenB, VL (wlit 1%uint63))]) in *.
    assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_app; cbn [length]; unfold two63; lia).
    assert (WNB : wden E' (VP kB wzero, lenB, VL (wlit 1%uint63)) = Win (v_begin (k_evec g)) (v_bytes (k_evec g)) K_BLOCK).
    { unfold wden. rewrite (den_VP0 E' kB wzero (weqb_refl _)), KBV', DLB, SZC. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
    assert (WS' : map (wden E') ws' = map (wden E) kept ++ [Win (v_begin (k_evec g)) (v_bytes (k_evec g)) K_BLOCK]).
    { subst ws'. rewrite map_app, WSK. cbn [map]. rewrite WNB. reflexivity. }
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH ks
             [(kB, empty_region lenB)] _ _ (PrimInt63.add n 2)).
    + exact HKS.
    + cbn [map fst]. constructor; [intros []| constructor].
    + intros k r [X|[]]; injection X as <- <-; assumption.
    + intros k r [X|[]]; injection X as <- <-; assumption.
    + intros k r a [X|[]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE, HIB, KBV' in IR.
      exact (proj2 (proj2 (proj2 (proj2 (OWNB _ a OWN ltac:(unfold in_iv; cbn [fst snd]; lia)))))).
    + intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE12; injection X1 as <- <-; injection X2 as <- <-; contradiction.
    + rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 5, (den E' aw), (map (wden E') ws'), (map (den E') [c0; VP n wzero]), LB.
      split; [apply (mk_args_sound E' 5%uint63 aw ws' _ LEN')|].
      split.
      { rewrite (DR aw ltac:(rewrite ARGS; right; left; reflexivity)), WS'. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA). apply wins_keep_intro.
        - intros w Hw. apply in_app_iff in Hw as [Hw|[<-|[]]].
          + left. apply in_map_iff in Hw as (w3 & <- & Hw3). apply in_map. exact (proj1 (KEPT w3 Hw3)).
          + right. split; [unfold aw_tied, K_STACK, K_GHOST, K_BLOCK; cbn [w_kind]; lia|].
            intros _ g0 Hg KG a Ha Hb. apply in_app_iff in Hg as [Hg|[<-|[]]]; [| cbn [w_kind] in KG; unfold K_GHOST, K_BLOCK in KG; lia].
            apply in_map_iff in Hg as (w3 & <- & Hw3).
            destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ (proj1 (KEPT w3 Hw3))) ltac:(unfold K_STACK, K_GHOST in *; lia)) as [[_ D]|[_ ET]].
            * exact (D _ OWN a Ha Hb).
            * destruct ET as (K6 & _). unfold PK.K_ETOP, K_GHOST in *. lia.
        - intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (is_kept w3) eqn:IK.
          + destruct (DOLD w3 Hw3) as [Hw0|[q PVq]].
            * left. apply in_app_iff. left. apply in_map. subst kept. apply filter_In. split; assumption.
            * right. split; [exact (PkUSwap.not_tied _ q PVq)|]. intros HK _. exfalso. destruct (PK.pku_val_kind _ q PVq) as [K0 _]. unfold heap_kind, K_BLOCK in HK. lia.
          + right. pose proof (SUBK w3 Hw3 IK) as [K1 K2].
            split; [unfold aw_tied, K_SUB, K_STACK, K_GHOST in *; lia|]. intros _ LENW.
            destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3) ltac:(unfold K_SUB, K_STACK in *; lia)) as [[KD _]|[_ ET]];
              [exfalso; unfold K_SUB, K_GHOST, K_BLOCK in *; lia|].
            destruct ET as (_ & _ & EE1 & _ & EE3).
            apply (block_keep_evidence LB _ (v_begin (k_evec g)) (v_bytes (k_evec g)) _ (Win (v_begin (k_evec g)) (v_bytes (k_evec g)) K_BLOCK) (proj1 O _ OWN)).
            * unfold v_capend, v_bytes in *. lia.
            * apply in_app_iff. right. left. reflexivity.
            * unfold heap_kind, K_BLOCK, K_GHOST. cbn [w_kind]. lia.
            * cbn [w_len]. pose proof (PK.owned_pos g ls P _ OWN) as POS. cbn [snd] in POS. exact POS.
            * cbn [w_lo]. pose proof (PK.owned_pos g ls P _ OWN) as POS. cbn [snd] in POS. lia. }
      split.
      * rewrite WS'. unfold windows_wf in *. apply Forall_app. split; [exact KEPTWF|].
        constructor; [|constructor]. unfold window_wf; cbn [w_lo w_len w_kind w_iv].
        split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|]. right; left. split; [reflexivity|]. exact (proj1 O _ OWN).
      * apply CW5'. apply TD5; rewrite WS'.
        3: { apply TD.nosub_app; [exact KNOSUB| apply TD.nosub_one; left; unfold K_BLOCK, K_SUB; lia]. }
        2: { apply Seal.seal_ok_app; [exact KSEAL|]. constructor; [|constructor]. cbn [w_kind]. unfold K_BLOCK, Seal.K_TWIN. lia. }
        apply Forall_app. split; [exact KEPTW|].
        constructor; [|constructor]. cbn [w_kind w_iv w_lo w_len]. intros _ c Hc a Ha Hb.
        pose proof (PK.evec_chunk_disj g LB O c VX3 Hc) as D. unfold rdisj, in_iv, chunk_block, w_iv in D, Ha, Hb. cbn [fst snd w_lo w_len] in D, Ha, Hb. lia.
    + intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 5 _ (map (wden E') ws') _ a (mk_args_sound E' 5%uint63 aw ws' _ LEN'))) in FPa as (RA & NI & NW).
      rewrite WS' in NW. split.
      * apply (NEWFP a NI RA). intros X. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
      * intros k r [X|[]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE, HIB, KBV' in IR. apply NW. unfold in_ws. rewrite map_app.
        apply (proj2 (in_ivs_app _ _ _)). right. cbn [map]. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
    +
      destruct VE as [(B0 & _)|[(VV1 & (VV2a & VV2b) & VV3 & VV4) CP]]; [contradiction|].
      constructor; [cbn [fact_holds]; rewrite den_VL, DLB; change (w2Z wzero) with 0; exact LPZ|].
      apply (vd_facts_sound E' _ ee _ 24%uint63 (v_begin (k_evec g)) (v_size (k_evec g))).
      * rewrite (DR (VP kB wzero) ltac:(apply INCA; inl)). symmetry. exact Leb.
      * rewrite (DR ee ltac:(apply INCA; inl)), <- Lee. unfold v_end. rewrite EL. reflexivity.
      * unfold v_bytes in Bb3. rewrite EL in Bb3. unfold ELEM_SIZE in Bb3. unfold VD_MAXZ. lia.
      * lia.
      * change (to_Z 24%uint63) with 24. unfold v_bytes in Bb3. rewrite EL in Bb3. unfold ELEM_SIZE in Bb3. unfold two64. lia.
      * exact EVj1.
Qed.

Theorem pkexit_sound : forall pc, contract_sound segs OPS MP PB (pkexit_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pkexit_contract c_apply] in HAP.
  destruct (pkexit_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. destruct (pkexit_sound_main E st ms model st' HS AP) as (E' & HX & HS').
       exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS'). }
  all: exfalso; unfold pkexit_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End PkExit.
