(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib GUnp.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GRoom.

Definition top_win (k : int) (len : int) (kd : int) : sv * sv * sv := (VP k wzero, VL (wlit len), VL (wlit kd)).

Definition only_kind (kd : Z) (w0 : option (sv * sv * sv)) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with
                    | Some k' => if k' =? kd then match w0 with Some x => win3_eqb w x | None => false end else true
                    | None => false
                    end) ws.

Definition grow16 (r : region) : region := Region (rg_lo r) (VL (wlit 16%uint63)) (rg_w r) (rg_bg r) (rg_cells r).
Definition empty8 : region := Region 0%uint63 (VL (wlit 8%uint63)) true BGNone IMap.empty.

Definition cells_in8 (r : region) : bool :=
  IMap.forallb (fun g gr => PrimInt63.eqb g 0%uint63 && forallb (fun c => PrimInt63.leb (PrimInt63.add (c_idx c) (c_w c)) 8%uint63
                                                                     && PrimInt63.ltb (c_idx c) 8%uint63 && PrimInt63.leb (c_w c) 8%uint63) (g_cells gr))
               (rg_cells r).

Section WithPc.
Variable ROOM_PC : int.
Variable isV : bool.

Definition KD : int := if isV then 3%uint63 else 2%uint63.

Definition groom_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let b := if isV then vb else cb in
          let e := if isV then ve else ce in
          let cap := if isV then vcap else ccap in
          let fs := s_facts st in
          if Z.ltb (Z.of_nat (length ws)) 4096
             && match decide_ltu fs e cap with Some true => true | _ => false end then
          match e with
          | VP k oe =>
              if weqb oe (wlit 8%uint63) && negb (PrimInt63.eqb k 0%uint63)
                 && (isV || match decide_ltu fs b e with Some true => true | _ => false end) then

                match IMap.find k (s_regs st) with
                | Some r =>
                    if PrimInt63.eqb (rg_lo r) 0%uint63 && rg_w r && cells_in8 r
                       && match rg_bg r with BGNone => true | _ => false end then
                      if sv_eqb (rg_hi r) (VL (wlit 16%uint63)) && only_kind (to_Z KD) (Some (top_win k 16%uint63 KD)) ws
                      then Some [st]
                      else if sv_eqb (rg_hi r) (VL (wlit 8%uint63)) && only_kind (to_Z KD) (Some (top_win k 8%uint63 KD)) ws
                              && existsb (win3_eqb (top_win k 8%uint63 KD)) ws then
                        let ws' := List.map (fun w => if win3_eqb w (top_win k 8%uint63 KD) then top_win k 16%uint63 KD else w) ws in
                        Some [surg st [k] [(k, grow16 r)] (mk_args 1%uint63 aw ws' ca) [] (s_next st)]
                      else None
                    else None
                | None => None
                end
              else if negb isV && weqb oe wzero && negb (PrimInt63.eqb k 0%uint63) && sv_eqb cb ce
                      && only_kind (to_Z KD) None ws
                      && match IMap.find k (s_regs st) with None => true | Some _ => false end then

                Some [surg st [] [(k, empty8)] (mk_args 1%uint63 aw (ws ++ [top_win k 8%uint63 2%uint63]) ca) [] (s_next st)]
              else None
          | _ => None
          end
          else None
      | _ => None
      end
      else None
  | None => None
  end.

Definition groom_contract : contract := Contract ROOM_PC groom_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma top_win_den : forall E k len kd, wden E (top_win k len kd) = Win (bv_unsigned (ev E k)) (to_Z len) (to_Z kd).
Proof.
  intros E k len kd. unfold top_win, wden. rewrite (den_VP0 E k wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.

Lemma only_kind_sound : forall E kd w0 ws, only_kind kd w0 ws = true ->
  forall x, In x ws -> w_kind (wden E x) = kd -> w0 = Some x.
Proof.
  intros E kd w0 ws H x Hx K. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [k'|] eqn:KO; [|discriminate]. rewrite (kind_of_sound E x k' KO) in K. subst k'. rewrite Z.eqb_refl in Q.
  destruct w0 as [w0|]; [|discriminate]. apply win3_eqb_eq in Q. congruence.
Qed.

Lemma cells_in8_sound : forall r g gr c, cells_in8 r = true -> IMap.bst (rg_cells r) -> IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) ->
  g = 0%uint63 /\ to_Z (c_idx c) + to_Z (c_w c) <= 8.
Proof.
  intros r g gr c H B F Hc. pose proof (proj1 (IMap.forallb_spec _ _ B) H g gr F) as Q. apply andb_prop in Q as [Q1 Q2].
  apply Uint63.eqb_correct in Q1. split; [exact Q1|].
  pose proof (proj1 (forallb_forall _ _) Q2 c Hc) as R. apply andb_prop in R as [R W8]. apply andb_prop in R as [R I8].
  apply Uint63.leb_spec in R. apply Uint63.ltb_spec in I8. apply Uint63.leb_spec in W8. change (to_Z 8%uint63) with 8 in R, I8, W8.
  rewrite Uint63.add_spec, Z.mod_small in R by (pose proof (int_range (c_idx c)); pose proof (int_range (c_w c)); rewrite wB_two63; unfold two63; lia). exact R.
Qed.

Lemma groom_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> groom_apply st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP.
  unfold groom_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  set (b := if isV then vb else cb) in AP. set (e := if isV then ve else ce) in AP. set (cap := if isV then vcap else ccap) in AP.
  destruct (Z.ltb (Z.of_nat (length ws)) 4096 && match decide_ltu (s_facts st) e cap with Some true => true | _ => false end) eqn:C0; [|discriminate].
  apply andb_prop in C0 as [WLEN DLT]. apply Z.ltb_lt in WLEN.
  destruct (decide_ltu (s_facts st) e cap) as [[|]|] eqn:DL; try discriminate.

  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & AX0 & SE).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV' & LV & LA & ZV).
  pose proof VC as (VC1 & VC2 & VC3 & VC4). pose proof VV as (VV1 & VV2 & VV3 & VV4).

  set (vec := if isV then u_vstk g else u_cstk g).
  assert (Lb : v_begin vec = bv_unsigned (den E b)) by (subst vec b; destruct isV; assumption).
  assert (Le : v_end vec = bv_unsigned (den E e)) by (subst vec e; destruct isV; assumption).
  assert (Lc : v_capend vec = bv_unsigned (den E cap)) by (subst vec cap; destruct isV; assumption).
  assert (VEL : v_elt vec = 8) by (subst vec; destruct isV; assumption).
  assert (VVX : vec_valid vec) by (subst vec; destruct isV; assumption).
  pose proof VVX as (VX1 & VX2 & VX3 & VX4).
  assert (OWN : In (v_begin vec, v_bytes vec) (owned g)) by (subst vec; destruct isV; [exact (owned_vstk g)| exact (owned_cstk g)]).

  pose proof (decide_ltu_sound E (s_facts st) Pfacts _ _ _ DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
  rewrite <- Le, <- Lc in LT.
  assert (ROOM : v_end vec + 8 <= v_capend vec) by (unfold v_end, v_capend in *; rewrite VEL in *; nia).

  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA (proj1 O _ OWN)) as (B1 & B2 & B3 & B4 & _). cbn [fst snd] in B1, B2, B3.

  assert (SAFE : forall a (w0 : option (sv * sv * sv)), only_kind (to_Z KD) w0 ws = true ->
            v_begin vec <= a < v_capend vec ->
            (forall x, w0 = Some x -> ~ in_iv (w_iv (wden E x)) a) ->
            (a < v_end vec - 8 \/ True) ->
            safe 1 g (map (wden E) ws) a).
  { intros a w0 OK Ha NOTW _ w Hw SO Hin. apply in_map_iff in Hw as (x & <- & Hx).
    unfold sub_ok in SO. cbv zeta in SO.
    destruct SO as [(KK & I1 & I2 & I3)|[(KK & I1 & I2 & I3)|[(KK & lD & HlD & I2 & I3)|(KK & I2 & I3)]]].
    -   destruct isV eqn:IV.
      +   subst vec. pose proof (disj_cv g LB O) as D. unfold rdisj, v_bytes, v_end, v_capend, in_iv, w_iv in *.
        cbn [fst snd] in Hin. rewrite EC, EV in *. nia.
      + pose proof (only_kind_sound E (to_Z KD) w0 ws OK x Hx ltac:(unfold KD; rewrite IV; exact KK)) as W0. exact (NOTW x W0 Hin).
    -   destruct isV eqn:IV.
      + pose proof (only_kind_sound E (to_Z KD) w0 ws OK x Hx ltac:(unfold KD; rewrite IV; exact KK)) as W0. exact (NOTW x W0 Hin).
      + subst vec. pose proof (disj_cv g LB O) as D. unfold rdisj, v_bytes, v_end, v_capend, in_iv, w_iv in *.
        cbn [fst snd] in Hin. rewrite EC, EV in *. nia.
    -
      destruct (top_level g lD HlD) as (ls0 & EL & _ & HinD). destruct (level_array g P lD HinD) as (V & A & G1 & G2 & G4 & c & Hc & IC).
      assert (D : rdisj (v_begin vec) (v_bytes vec) (fst c) (CHUNK_HDR + snd c)) by (subst vec; destruct isV; [exact (disj_vc g LB O c Hc)| exact (disj_cc g LB O c Hc)]).
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes, v_end, v_capend, in_iv, w_iv in *. cbn [fst snd] in Hin.
      assert (lv_slot lD <= w_lo (wden E x)) by (destruct (1 =? CM_CONS); unfold OBJ_SIZE in *; lia). rewrite VEL in *. nia.
    -
      destruct (head_chunk g P) as (h & r & EH & H1 & H2 & H3). rewrite EH in I3. cbn [hd] in I3.
      assert (D : rdisj (v_begin vec) (v_bytes vec) (fst h) (CHUNK_HDR + snd h)) by (subst vec; destruct isV; [exact (disj_vc g LB O h ltac:(rewrite EH; left; reflexivity))| exact (disj_cc g LB O h ltac:(rewrite EH; left; reflexivity))]).
      unfold chunk_lo, chunk_hi, CHUNK_HDR, rdisj, v_bytes, v_end, v_capend, in_iv, w_iv in *. cbn [fst snd] in Hin. rewrite VEL in *. nia. }
  assert (CAPB : v_capend vec <= v_begin vec + v_bytes vec) by (unfold v_capend, v_bytes; lia).
  assert (BYTE : forall a (w0 : option (sv * sv * sv)), only_kind (to_Z KD) w0 ws = true ->
            v_begin vec <= a < v_capend vec -> (forall x, w0 = Some x -> ~ in_iv (w_iv (wden E x)) a) ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a w0 OK Ha NW. apply (owned_byte_props segs IMGX AW _ LB (ms_mem ms) model 1 g (map (wden E) ws) _ a HA WF O Wk OWN).
    - unfold in_iv. cbn [fst snd]. lia.
    - exact (SAFE a w0 OK Ha NW (or_intror I)). }
  assert (MATB : forall a, v_begin vec <= a < v_capend vec -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model _ a HA (proj1 O _ OWN)). unfold in_iv. cbn [fst snd]. lia. }
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws) _ a DEC)). auto. }

  destruct e as [|k oe| | | | | | | | |]; try discriminate.
  destruct (weqb oe (wlit 8) && negb (PrimInt63.eqb k 0) && (isV || match decide_ltu (s_facts st) b (VP k oe) with Some true => true | _ => false end)) eqn:C1.
  -
    apply andb_prop in C1 as [C1 SZ]. apply andb_prop in C1 as [OE K0]. apply (proj1 (weqb_ok _ _)) in OE. subst oe. apply negb_true_iff in K0.
    destruct (IMap.find k (s_regs st)) as [r|] eqn:FR; [|discriminate].
    destruct (PrimInt63.eqb (rg_lo r) 0 && rg_w r && cells_in8 r && match rg_bg r with BGNone => true | _ => false end) eqn:C2; [|discriminate].
    apply andb_prop in C2 as [C2 BG]. apply andb_prop in C2 as [C2 CI8]. apply andb_prop in C2 as [LO W]. apply Uint63.eqb_correct in LO.
    assert (BGN : rg_bg r = BGNone) by (destruct (rg_bg r); try discriminate; reflexivity).

    pose proof (ro_range _ _ _ _ _ _ (Preg k r FR) K0) as [_ RR2].
    assert (SIZE1 : v_begin vec + 8 <= v_end vec).
    { destruct isV eqn:IV.
      - subst vec. unfold v_end. rewrite EV, SV'. pose proof (Zle_0_nat (length (u_levels g))). unfold u_D. lia.
      - cbn [orb] in SZ. destruct (decide_ltu (s_facts st) b (VP k (wlit 8))) as [[|]|] eqn:DB; try discriminate.
        pose proof (decide_ltu_sound E (s_facts st) Pfacts _ _ _ DB) as LTB. apply (proj1 (ltu_iff _ _ true)) in LTB.
        rewrite <- Lb, <- Le in LTB. unfold v_end in *. rewrite VEL in *. nia. }
    destruct (sv_eqb (rg_hi r) (VL (wlit 16)) && only_kind (to_Z KD) (Some (top_win k 16 KD)) ws) eqn:C16.
    {   injection AP as <-. exact HS. }
    destruct (sv_eqb (rg_hi r) (VL (wlit 8)) && only_kind (to_Z KD) (Some (top_win k 8 KD)) ws && existsb (win3_eqb (top_win k 8 KD)) ws) eqn:C8; [|discriminate].
    apply andb_prop in C8 as [C8 EX8]. apply andb_prop in C8 as [HI8 OK8]. apply sv_eqb_eq in HI8.
    apply existsb_exists in EX8 as (w8 & INw8 & EQ8). apply win3_eqb_eq in EQ8. subst w8.
    injection AP as <-.
    assert (HIZ8 : hiZ E r = 8) by (unfold hiZ; rewrite HI8; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    assert (KV : bv_unsigned (ev E k) = v_end vec - 8).
    { rewrite Le. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8.
      pose proof (bv_unsigned_in_range _ (ev E k)) as RK. rewrite bv_modulus_64 in RK. rewrite HIZ8 in RR2.
      unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }
    set (ws' := List.map (fun w => if win3_eqb w (top_win k 8 KD) then top_win k 16 KD else w) ws) in *.
    assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; lia).
    assert (HIZ16 : hiZ E (grow16 r) = 16) by (unfold hiZ, grow16; cbn [rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    assert (LOZ16 : loZ (grow16 r) = 0) by (unfold loZ, grow16; cbn [rg_lo]; rewrite LO; reflexivity).
    assert (LOZ8 : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
    assert (INWS' : forall w, In w ws' -> (In w ws /\ w <> top_win k 8 KD) \/ w = top_win k 16 KD).
    { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQ & Hx). destruct (win3_eqb x (top_win k 8 KD)) eqn:Q.
      - right. congruence.
      - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate. }
    apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [k] [(k, grow16 r)] (mk_args 1%uint63 aw ws' _) [] (s_next st)).
    + intros k' [<-|[]]. split; [exact K0|]. exists r. auto.
    + constructor; [intros []| constructor].
    + intros k' r' [H|[]]. injection H as <- <-. exact K0.
    +
      intros k' r' [H|[]]. injection H as <- <-.
      apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) k (grow16 r) K0).
      * cbn [grow16 rg_cells]. exact (ro_bst _ _ _ _ _ _ (Preg k r FR)).
      * cbn [grow16 rg_bg]. exact BGN.
      * rewrite LOZ16, KV. lia.
      * rewrite HIZ16, KV. unfold v_capend, v_bytes in *. lia.
      * intros a Ha. rewrite LOZ16, HIZ16, KV in Ha. apply MATB. lia.
      * intros gk gr F. cbn [grow16 rg_cells] in F. split.
        -- exact (ro_cells _ _ _ _ _ _ (Preg k r FR) gk gr F).
        -- intros c i Hc Hi. destruct (cells_in8_sound r gk gr c CI8 (ro_bst _ _ _ _ _ _ (Preg k r FR)) F Hc) as [-> LE8].
           change (keyZ 0%uint63) with 0. rewrite LOZ16, HIZ16. pose proof (int_range (c_idx c)). lia.
    +
      intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite LOZ16, HIZ16, KV in IR.
      destruct (Z.lt_ge_cases a (v_end vec)) as [LOW|HIGH].
      * right. exists k, r. split; [left; reflexivity|]. split; [exact FR|]. unfold inR. rewrite LOZ8, HIZ8, KV. lia.
      * left. destruct (BYTE a (Some (top_win k 8 KD)) OK8 ltac:(lia)) as (RA & NI & NW & _).
        -- intros x [= <-]. rewrite top_win_den, KV. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. change (to_Z 8%uint63) with 8. lia.
        -- exact (FPold a ltac:(lia) NI NW).
    + intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
    +
      rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 1, (den E aw), (map (wden E) ws'), (map (den E) [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]), LB.
      split; [apply mk_args_sound; exact LEN'|].
      split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E 1 g LB ws ws' P O Wk);
              [intros x Hx; destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right; left; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]
              |intros x Hx; destruct (UOK.map_replace_old ws (top_win k 8 KD) (top_win k 16 KD) x Hx) as [H0| ->];
               [left; exact H0| right; left; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]]|]. split.
      * unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (INWS' x Hx) as [[Hx0 _]| ->].
        -- exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ Hx0)).
        -- rewrite top_win_den, KV. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 16%uint63) with 16.
           split; [lia|]. split; [lia|]. split; [unfold v_capend, v_bytes in *; lia|].
           right; right. split; [unfold KD, K_SUB; destruct isV; [change (to_Z 3%uint63) with 3| change (to_Z 2%uint63) with 2]; lia|].
           exists (v_begin vec, v_bytes vec). split; [exact (proj1 O _ OWN)|].
           intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold v_capend, v_bytes in *. lia.
      * cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
        assert (NP : forall w, In w (map (wden E) ws') -> pot_win w -> In w (map (wden E) ws)).
        { apply UOK.pot_map_old. intros x Hx. destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right].
          rewrite top_win_den. cbn [w_kind]. unfold KD, K_STACK. destruct isV; [change (to_Z 3%uint63) with 3| change (to_Z 2%uint63) with 2]; lia. }
        exists g. split; [exact L| split; [exact P| split; [exact O| split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS0 NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX0 NP)|]]]]]]];
          [|
             apply (SealX.seal_ok_map _ _ _ _ _ SE); intros x Hx; destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right];
             rewrite top_win_den; cbn [w_kind]; unfold KD, Seal.K_TWIN; destruct isV; [change (to_Z 3%uint63) with 3| change (to_Z 2%uint63) with 2]; lia].
        unfold wins_ok in *. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (INWS' x Hx) as [[Hx0 _]| ->].
        -- exact (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS).
        -- right. rewrite top_win_den, KV in *. split; [cbn [w_kind]; unfold KD, K_BLOCK; destruct isV; [change (to_Z 3%uint63) with 3| change (to_Z 2%uint63) with 2]; lia|].
           unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. change (to_Z 16%uint63) with 16.
           subst vec. unfold KD in *. destruct isV; cbn [K_CTOP K_VTOP].
           ++ change (to_Z 3%uint63) with 3. right; left. split; [reflexivity|]. lia.
           ++ change (to_Z 2%uint63) with 2. left. split; [reflexivity|]. lia.
    +
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws') _ a (mk_args_sound E 1%uint63 aw ws' _ LEN'))) in FPa as (RA & NI & NW).
      split.
      * left. apply (FPold a RA NI). intros IN. apply NW. apply in_ws_map_iff in IN as (x & Hx & Ha). apply in_ws_map_iff.
        destruct (win3_eqb x (top_win k 8 KD)) eqn:Q.
        -- apply win3_eqb_eq in Q. subst x. exists (top_win k 16 KD). split.
           ++ subst ws'. apply in_map_iff. exists (top_win k 8 KD). rewrite win3_eqb_refl. split; [reflexivity| exact INw8].
           ++ rewrite top_win_den in Ha |- *. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *.
              change (to_Z 8%uint63) with 8 in Ha. change (to_Z 16%uint63) with 16. lia.
        -- exists x. split; [| exact Ha]. subst ws'. apply in_map_iff. exists x. rewrite Q. auto.
      * intros k' r' [H|[]] IR. injection H as <- <-. apply NW. apply in_ws_map_iff. exists (top_win k 16 KD). split.
        -- subst ws'. apply in_map_iff. exists (top_win k 8 KD). rewrite win3_eqb_refl. split; [reflexivity| exact INw8].
        -- rewrite top_win_den. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. unfold inR in IR. rewrite LOZ16, HIZ16 in IR. change (to_Z 16%uint63) with 16. lia.
    + constructor.
  -
    destruct (negb isV && weqb oe wzero && negb (PrimInt63.eqb k 0) && sv_eqb cb ce && only_kind (to_Z KD) None ws
              && match IMap.find k (s_regs st) with None => true | Some _ => false end) eqn:C2; [|discriminate].
    apply andb_prop in C2 as [C2 FK]. apply andb_prop in C2 as [C2 OK0]. apply andb_prop in C2 as [C2 CE]. apply andb_prop in C2 as [C2 K0].
    apply andb_prop in C2 as [NV OE]. apply negb_true_iff in NV. apply (proj1 (weqb_ok _ _)) in OE. subst oe. apply negb_true_iff in K0.
    apply sv_eqb_eq in CE.
    injection AP as <-.
    assert (D0 : v_end vec = v_begin vec).
    { subst vec b cap. rewrite NV in *. rewrite Lcb, Lce, CE. cbn in Le |- *. reflexivity. }
    assert (KV : bv_unsigned (ev E k) = v_begin vec).
    { rewrite <- D0, Le. symmetry. exact (den_VP0 E k wzero (weqb_refl _)). }
    assert (HIZ8 : hiZ E empty8 = 8) by reflexivity. assert (LOZ8 : loZ empty8 = 0) by reflexivity.
    assert (LEN' : Z.of_nat (length (ws ++ [top_win k 8 2])) < two63) by (rewrite length_app; cbn [length]; unfold two63; lia).
    assert (KD2 : KD = 2%uint63) by (unfold KD; rewrite NV; reflexivity).
    apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [(k, empty8)] (mk_args 1%uint63 aw (ws ++ [top_win k 8%uint63 2%uint63]) _) [] (s_next st)).
    + intros k' [].
    + constructor; [intros []| constructor].
    + intros k' r' [H|[]]. injection H as <- <-. exact K0.
    + intros k' r' [H|[]]. injection H as <- <-.
      apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) k empty8 K0).
      * exact I.
      * reflexivity.
      * rewrite LOZ8, KV. lia.
      * rewrite HIZ8, KV. unfold v_capend, v_bytes in *. lia.
      * intros a Ha. rewrite LOZ8, HIZ8, KV in Ha. apply MATB. lia.
      * intros gk gr F. cbn [empty8 rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
    + intros k' r' a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite LOZ8, HIZ8, KV in IR. left.
      destruct (BYTE a None OK0 ltac:(lia) ltac:(intros x X; discriminate)) as (RA & NI & NW & _).
      exact (FPold a ltac:(lia) NI NW).
    + intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
    + rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 1, (den E aw), (map (wden E) (ws ++ [top_win k 8 2])), (map (den E) [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]), LB.
      split; [apply mk_args_sound; exact LEN'|]. split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite map_app; apply wins_keep_app; intros w0 [<-|[]]; apply UOK.kind_sub_untied; vm_compute; reflexivity|]. split.
      * unfold windows_wf in *. rewrite map_app. apply Forall_app. split; [exact WF|]. constructor; [|constructor].
        rewrite top_win_den, KV. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 8%uint63) with 8. change (to_Z 2%uint63) with 2.
        split; [lia|]. split; [lia|]. split; [unfold v_capend, v_bytes in *; lia|].
        right; right. split; [unfold K_SUB; lia|]. exists (v_begin vec, v_bytes vec). split; [exact (proj1 O _ OWN)|].
        intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold v_capend, v_bytes in *. lia.
      * cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
        assert (NP : forall w, In w (map (wden E) (ws ++ [top_win k 8 2])) -> pot_win w -> In w (map (wden E) ws)).
        { apply UOK.pot_map_old. intros x Hx. apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact Hx| right; apply kind_ne; vm_compute; reflexivity]. }
        exists g. split; [exact L| split; [exact P| split; [exact O| split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS0 NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX0 NP)|]]]]]]];
          [|
             rewrite map_app; apply SealX.seal_ok_app_other; [exact SE|]; intros w [<-|[]]; rewrite top_win_den; cbn [w_kind]; unfold Seal.K_TWIN;
             change (to_Z 2%uint63) with 2; lia].
        unfold wins_ok in *. rewrite map_app. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
        intros _. right. rewrite top_win_den, KV. split; [cbn [w_kind]; unfold K_BLOCK; change (to_Z 2%uint63) with 2; lia|].
        unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. change (to_Z 8%uint63) with 8. change (to_Z 2%uint63) with 2.
        left. subst vec. rewrite NV in *. split; [reflexivity|]. lia.
    + intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E) (ws ++ [top_win k 8 2])) _ a (mk_args_sound E 1%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
      rewrite map_app in NW. split.
      * left. apply (FPold a RA NI). intros X. apply NW. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
      * intros k' r' [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
        cbn [map]. rewrite top_win_den. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite LOZ8, HIZ8 in IR. change (to_Z 8%uint63) with 8. lia.
    + constructor.
Qed.

Theorem groom_sound : contract_sound segs OPS MP PB groom_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [groom_contract c_apply] in HAP.
  destruct (groom_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. apply (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP).
       exact (groom_sound_main E st ms model st' HS AP). }
  all: exfalso; unfold groom_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End GRoom.
