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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Ops TdOps GLib CapLen.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PotDrop.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG TD CapLen.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module TdEnter.

Definition kinds_lit (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with Some _ => true | None => false end) ws.

Definition is_sub (w : sv * sv * sv) : bool :=
  match kind_of w with Some kd => Z.leb 2 kd && Z.leb kd 6 | None => false end.
Definition is_kept (w : sv * sv * sv) : bool :=
  match kind_of w with Some kd => Z.ltb kd 2 || Z.leb 7 kd | None => false end.

Definition sub_anchor (st : sstate) (w : sv * sv * sv) : option int :=
  match w with
  | (VP k o, len, _) =>
      if weqb o wzero && negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb k 1%uint63) then
        match IMap.find k (s_regs st) with
        | Some r => if PrimInt63.eqb (rg_lo r) 0%uint63 && rg_w r && sv_eqb (rg_hi r) len then Some k else None
        | None => None
        end
      else None
  | _ => None
  end.

Fixpoint sub_anchors (st : sstate) (ws : list (sv * sv * sv)) : option (list int) :=
  match ws with
  | [] => Some []
  | w :: ws' => match sub_anchors st ws' with
               | Some ks => if is_sub w then match sub_anchor st w with Some k => Some (k :: ks) | None => None end
                            else Some ks
               | None => None
               end
  end.

Definition anchor_free (st : sstate) (ks : list int) (k : int) : bool :=
  match IMap.find k (s_regs st) with
  | None => true
  | Some _ => existsb (PrimInt63.eqb k) ks
  end.

Section WithPc.
Variable ENTER_PC : int.

Definition tdenter_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let n := s_next st in
          match cb, vb, zh with
          | VP kCB oCB, VP kVB oVB, VP kZ oZ =>
            match cap_len kCB ccap, cap_len kVB vcap with
            | Some lenC, Some lenV =>
              if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63)
                 && Z.ltb (Z.of_nat (length ws)) 4000 && kinds_lit ws
                 && weqb oCB wzero && weqb oVB wzero && weqb oZ wzero
                 && negb (PrimInt63.eqb kCB kVB)
                 && negb (PrimInt63.eqb kCB 0%uint63) && negb (PrimInt63.eqb kCB 1%uint63)
                 && negb (PrimInt63.eqb kVB 0%uint63) && negb (PrimInt63.eqb kVB 1%uint63)
              then
                match sub_anchors st ws, IMap.find kZ (s_regs st) with
                | Some ks, Some rZ =>
                    if anchor_free st ks kCB && anchor_free st ks kVB
                       && match cell_at rZ 24 8%uint63 with Some v => sv_eqb v c0 | None => false end
                    then
                      match PotDrop.pot_drop (s_facts st) ws with
                      | None => None
                      | Some ws0 =>
                      let kept := List.filter is_kept ws0 in
                      let ws' := kept ++ [(VP kCB wzero, lenC, VL (wlit 1%uint63)); (VP kVB wzero, lenV, VL (wlit 1%uint63))] in

                      Some [surg st ks [(kCB, empty_region lenC); (kVB, empty_region lenV)]
                                 (mk_args 5%uint63 aw ws' [c0; VP n wzero])
                                 (vd_facts cb ce (PrimInt63.add n 1%uint63) 8%uint63 ++ vd_facts vb ve (PrimInt63.add n 2%uint63) 8%uint63)
                                 (PrimInt63.add n 3%uint63)]
                      end
                    else None
                | _, _ => None
                end
              else None
            | _, _ => None
            end
          | _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition tdenter_contract : contract := Contract ENTER_PC tdenter_apply.

End WithPc.

Lemma sub_anchor_spec : forall st w k, sub_anchor st w = Some k ->
  exists len kd r, w = (VP k wzero, len, kd) /\ PrimInt63.eqb k 0%uint63 = false /\ PrimInt63.eqb k 1%uint63 = false /\
    IMap.find k (s_regs st) = Some r /\ rg_lo r = 0%uint63 /\ rg_w r = true /\ rg_hi r = len.
Proof.
  intros st [[a len] kd] k H. unfold sub_anchor in H. destruct a as [|k' o| | | | | | | | |]; try discriminate.
  destruct (weqb o wzero && negb (PrimInt63.eqb k' 0) && negb (PrimInt63.eqb k' 1)) eqn:C; [|discriminate].
  apply andb_prop in C as [C K1]. apply andb_prop in C as [O K0]. apply (proj1 (weqb_ok _ _)) in O. subst o.
  apply negb_true_iff in K0. apply negb_true_iff in K1.
  destruct (IMap.find k' (s_regs st)) as [r|] eqn:F; [|discriminate].
  destruct (PrimInt63.eqb (rg_lo r) 0 && rg_w r && sv_eqb (rg_hi r) len) eqn:C2; [|discriminate]. injection H as <-.
  apply andb_prop in C2 as [C2 HI]. apply andb_prop in C2 as [LO W]. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  exists len, kd, r. repeat split; auto.
Qed.

Lemma sub_anchors_spec : forall st ws ks, sub_anchors st ws = Some ks ->
  (forall k, In k ks -> exists w, In w ws /\ is_sub w = true /\ sub_anchor st w = Some k) /\
  (forall w, In w ws -> is_sub w = true -> exists k, In k ks /\ sub_anchor st w = Some k).
Proof.
  intros st ws. induction ws as [|w ws IH]; intros ks H; cbn [sub_anchors] in H.
  - injection H as <-. split; [intros k []| intros w0 [] _].
  - destruct (sub_anchors st ws) as [ks0|] eqn:SA; [|discriminate].
    destruct (IH ks0 eq_refl) as [A B].
    destruct (is_sub w) eqn:SB.
    + destruct (sub_anchor st w) as [k0|] eqn:AN; [|discriminate]. injection H as <-. split.
      * intros k [<-|Hk]; [exists w; split; [left; reflexivity| auto]|].
        destruct (A k Hk) as (w' & Hw' & S' & AN'). exists w'. split; [right; exact Hw'| auto].
      * intros w0 [<-|Hw0] S0; [exists k0; split; [left; reflexivity| exact AN]|].
        destruct (B w0 Hw0 S0) as (k & Hk & ANk). exists k. split; [right; exact Hk| exact ANk].
    + injection H as <-. split.
      * intros k Hk. destruct (A k Hk) as (w' & Hw' & S' & AN'). exists w'. split; [right; exact Hw'| auto].
      * intros w0 [<-|Hw0] S0; [rewrite SB in S0; discriminate|]. exact (B w0 Hw0 S0).
Qed.

Lemma kept_or_sub : forall ws w, kinds_lit ws = true -> In w ws -> is_kept w = false -> is_sub w = true.
Proof.
  intros ws w KL Hw NK. pose proof (proj1 (forallb_forall _ _) KL w Hw) as Q. cbn beta in Q.
  unfold is_kept in NK. unfold is_sub. destruct (kind_of w) as [kd|]; [|discriminate]. apply orb_false_iff in NK as [N1 N2].
  apply Z.ltb_ge in N1. apply Z.leb_gt in N2. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma is_sub_kind : forall E w, is_sub w = true -> 2 <= w_kind (wden E w).
Proof.
  intros E w H. unfold is_sub in H. destruct (kind_of w) as [kd|] eqn:K; [|discriminate]. apply andb_prop in H as [H _]. apply Z.leb_le in H.
  rewrite (kind_of_sound E w kd K). exact H.
Qed.
Lemma is_kept_kind : forall E w, is_kept w = true -> w_kind (wden E w) < 2 \/ 7 <= w_kind (wden E w).
Proof.
  intros E w H. unfold is_kept in H. destruct (kind_of w) as [kd|] eqn:K; [|discriminate]. rewrite (kind_of_sound E w kd K).
  apply orb_prop in H as [H|H]; [left; apply Z.ltb_lt in H; exact H| right; apply Z.leb_le in H; exact H].
Qed.

Lemma chunks_len_bound : forall (cs : list (Z * Z)) (M : Z),
  Forall tchunk_ok cs -> ForallOrdPairs chunk_disj cs -> (forall c, In c cs -> 0 <= fst c /\ fst c + (8 + snd c) <= M) -> 0 <= M ->
  Z.of_nat (length cs) <= M.
Proof.
  intros cs M OK DJ BND HM.
  assert (ND : List.NoDup (map (fun c : Z * Z => Z.to_nat (fst c)) cs)).
  { induction cs as [|c cs IH]; [constructor|]. cbn [map]. inversion OK as [|c1 cs1 OKc OKs]; subst. inversion DJ as [|c2 cs2 Dc Ds]; subst.
    constructor; [| exact (IH OKs Ds ltac:(intros c0 H0; apply BND; right; exact H0))].
    intros Hin. apply in_map_iff in Hin as (c' & EQ & Hc').
    pose proof (proj1 (Forall_forall _ _) Dc c' Hc') as D. pose proof (proj1 (Forall_forall _ _) OKs c' Hc') as (_ & _ & S').
    destruct OKc as (_ & _ & S). destruct (BND c (or_introl eq_refl)) as [P1 _]. destruct (BND c' (or_intror Hc')) as [P2 _].
    unfold chunk_disj, rdisj, CHUNK_HDR, CHUNK_SIZE0 in *.
    assert (fst c = fst c') by lia. lia. }
  pose proof (fun INCL => List.NoDup_incl_length ND (l' := seq 0 (Z.to_nat M)) INCL) as L.
  rewrite length_map, length_seq in L.
  assert (INCL : incl (map (fun c : Z * Z => Z.to_nat (fst c)) cs) (seq 0 (Z.to_nat M))).
  { intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply in_seq. destruct (BND c Hc) as [B1 B2].
    pose proof (proj1 (Forall_forall _ _) OK c Hc) as (_ & _ & S). unfold CHUNK_SIZE0 in S. split; [lia|].
    apply Z2Nat.inj_lt; lia. }
  specialize (L INCL). lia.
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW12 : forall md ca LB ws m, (md = 1 \/ md = 2) -> cw_holds CW md ca LB ws m ->
  match decode_uc ca with Some u => unp_client segs md u LB ws m | None => False end.
Hypothesis CW5' : forall ca LB ws m, TD.td_client segs ca LB ws m -> cw_holds CW 5 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma u64_of_Z : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. exact Hz. Qed.

Lemma tdenter_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> tdenter_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP.
  unfold tdenter_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1 || PrimInt63.eqb mdi 2) eqn:MD; [|discriminate].
  assert (MD12 : to_Z mdi = 1 \/ to_Z mdi = 2).
  { apply orb_prop in MD as [M|M]; apply Uint63.eqb_correct in M; subst mdi; [left|right]; reflexivity. }
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  destruct cb as [|kCB oCB| | | | | | | | |]; try discriminate.
  destruct vb as [|kVB oVB| | | | | | | | |]; try discriminate.
  destruct zh as [|kZ oZ| | | | | | | | |]; try discriminate.
  destruct (cap_len kCB ccap) as [lenC|] eqn:CLC; [|discriminate].
  destruct (cap_len kVB vcap) as [lenV|] eqn:CLV; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND KV1]. apply andb_prop in COND as [COND KV0]. apply andb_prop in COND as [COND KC1]. apply andb_prop in COND as [COND KC0].
  apply andb_prop in COND as [COND KCV].
  apply andb_prop in COND as [COND OZ]. apply andb_prop in COND as [COND OV]. apply andb_prop in COND as [COND OC].
  apply andb_prop in COND as [COND KL]. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with (4611686018427387904 - 8) in NLT.
  apply (proj1 (weqb_ok _ _)) in OC. apply (proj1 (weqb_ok _ _)) in OV. apply (proj1 (weqb_ok _ _)) in OZ. subst oCB oVB oZ.
  apply negb_true_iff in KCV. apply negb_true_iff in KC0. apply negb_true_iff in KC1. apply negb_true_iff in KV0. apply negb_true_iff in KV1.
  destruct (sub_anchors st ws) as [ks|] eqn:SA; [|discriminate].
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  apply andb_prop in COND2 as [COND2 CELL]. apply andb_prop in COND2 as [AFC AFV].
  destruct (cell_at rZ 24 8%uint63) as [v24|] eqn:C24; [|discriminate]. apply sv_eqb_eq in CELL. subst v24.
  destruct (PotDrop.pot_drop (s_facts st) ws) as [ws0|] eqn:DROP; [|discriminate].
  injection AP as <-.
  set (n := s_next st) in *.
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).
  pose proof HS0 as [Ppc0 Px00 Pregs0 _ _ _ _ _ _ Pbst0 _ _ _ Pfacts0 Pops0 _ _ _].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  destruct (sub_anchors_spec st ws ks SA) as [KS1 KS2].

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-.
  apply (CW12 _ _ _ _ _ MD12) in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & AXu & SEALu).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof (UO.pf g P) as (VC & EC & SC & VV & EV & SV' & LVL & LA & ZV).
  pose proof ZV as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  set (cs := z_chunks (u_zone g)) in *.

  pose proof (proj1 O _ (UO.owned_cstk g)) as CLB. pose proof (proj1 O _ (UO.owned_vstk g)) as VLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (cstk_block g) HA CLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (vstk_block g) HA VLB) as (Bv1 & Bv2 & Bv3 & _ & Bv5).
  unfold cstk_block in Bc1, Bc2, Bc3. unfold vstk_block in Bv1, Bv2, Bv3. cbn [fst snd] in Bc1, Bc2, Bc3, Bv1, Bv2, Bv3.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
  pose proof (UO.disj_cv g LB O) as DCV.

  assert (CBV : bv_unsigned (ev E kCB) = v_begin (u_cstk g)) by (rewrite Lcb; symmetry; exact (den_VP0 E kCB wzero (weqb_refl _))).
  assert (VBV : bv_unsigned (ev E kVB) = v_begin (u_vstk g)) by (rewrite Lvb; symmetry; exact (den_VP0 E kVB wzero (weqb_refl _))).
  assert (SZC : bv_unsigned (den E lenC) = v_bytes (u_cstk g)).
  { apply (cap_len_sound E kCB ccap lenC _ CLC); [| lia | rewrite CBV; lia].
    rewrite <- Lccap, CBV. unfold v_capend, v_bytes. reflexivity. }
  assert (SZV : bv_unsigned (den E lenV) = v_bytes (u_vstk g)).
  { apply (cap_len_sound E kVB vcap lenV _ CLV); [| lia | rewrite VBV; lia].
    rewrite <- Lvcap, VBV. unfold v_capend, v_bytes. reflexivity. }

  assert (TOK : Forall tchunk_ok cs) by (apply Forall_forall; intros c Hc; exact (Z3 c Hc)).
  assert (CNT : Z.of_nat (length cs) <= 4611686018427387904).
  { apply (chunks_len_bound cs 4611686018427387904 TOK Z7); [|lia]. intros c Hc.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block c) HA (proj1 O _ (UO.owned_chunk g c Hc))) as (B1 & B2 & B3 & _).
    unfold chunk_block, CHUNK_HDR in B1, B2, B3. cbn [fst snd] in B1, B2, B3. lia. }

  assert (N1 : to_Z (PrimInt63.add n 1) = to_Z n + 1) by (rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (N2 : to_Z (PrimInt63.add n 2) = to_Z n + 2) by (rewrite Uint63.add_spec; change (to_Z 2%uint63) with 2; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (UPDO : forall E0 k w k', k' <> k -> ev (env_upd E0 k w) k' = ev E0 k').
  { intros E0 k w k' NE. cbn [env_upd ev]. destruct (PrimInt63.eqb k' k) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. contradiction. }
  set (E1 := env_upd E n (Z_to_bv 64 (Z.of_nat (length cs)))).
  set (E2 := env_upd E1 (PrimInt63.add n 1) (Z_to_bv 64 (v_size (u_cstk g)))).
  set (E' := env_upd E2 (PrimInt63.add n 2) (Z_to_bv 64 (v_size (u_vstk g)))).
  assert (HX : env_ext n E E').
  { apply (env_ext_trans n (PrimInt63.add n 2) E E2); [lia| | apply env_upd_ext].
    apply (env_ext_trans n (PrimInt63.add n 1) E E1); [lia| apply env_upd_ext| apply env_upd_ext]. }
  assert (EVn : ev E' n = Z_to_bv 64 (Z.of_nat (length cs))).
  { subst E' E2 E1. rewrite UPDO by (intros X; apply (f_equal to_Z) in X; lia). rewrite UPDO by (intros X; apply (f_equal to_Z) in X; lia). apply env_upd_same. }
  assert (EVj1 : ev E' (PrimInt63.add n 1) = Z_to_bv 64 (v_size (u_cstk g))).
  { subst E' E2. rewrite UPDO by (intros X; apply (f_equal to_Z) in X; lia). apply env_upd_same. }
  assert (EVj2 : ev E' (PrimInt63.add n 2) = Z_to_bv 64 (v_size (u_vstk g))) by (subst E'; apply env_upd_same).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n E E' HX v (VBo v Hv))).
  assert (INW : forall a b c, In (a, b, c) ws -> In a (op_args o) /\ In b (op_args o) /\ In c (op_args o)).
  { intros a b c Hw. destruct (in_flat_windows ws a b c Hw) as (Ia & Ib & Ic). rewrite ARGS.
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (INCA : forall v, In v [root; VP kCB wzero; ce; ccap; VP kVB wzero; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; VP kZ wzero] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (EVR : forall k o', In (VP k o') (op_args o) -> ev E' k = ev E k).
  { intros k o' Hin. apply (ev_reval n E E' HX). exact (VBo _ Hin). }
  assert (EkCB : ev E' kCB = ev E kCB) by (apply (EVR kCB wzero); apply INCA; right; left; reflexivity).
  assert (EkVB : ev E' kVB = ev E kVB) by (apply (EVR kVB wzero); apply INCA; do 4 right; left; reflexivity).
  assert (DLC : den E' lenC = den E lenC).
  { apply (den_reval n E E' HX). apply (cap_len_below n kCB ccap lenC CLC); [apply VBo; apply INCA; do 3 right; left; reflexivity| change (sv_vars_below n (VP kCB wzero) = true); apply VBo; apply INCA; right; left; reflexivity]. }
  assert (DLV : den E' lenV = den E lenV).
  { apply (den_reval n E E' HX). apply (cap_len_below n kVB vcap lenV CLV); [apply VBo; apply INCA; do 6 right; left; reflexivity| change (sv_vars_below n (VP kVB wzero) = true); apply VBo; apply INCA; do 4 right; left; reflexivity]. }
  assert (WSE : map (wden E') ws = map (wden E) ws).
  { apply map_ext_in. intros [[wa wb] wc] Hw. unfold wden. destruct (INW wa wb wc Hw) as (Ia & Ib & Ic). rewrite !DR by assumption. reflexivity. }
  clearbody E'.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear Ppc0 Px00 Pregs0 Pbst0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (DECf E') as DEC.
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ (to_Z mdi) _ (map (wden E') ws) _ a DEC)). rewrite WSE. auto. }

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
      + destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3) NK) as [[_ D]|[NB SO]].
        * exfalso. exact (D ob Hob a Hin Ha).
        * apply (SUBR w3 a Hw3); [|exact Hin].
          pose proof (proj1 (forallb_forall _ _) KL w3 Hw3) as Q. cbn beta in Q. unfold is_sub.
          destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate]. rewrite (kind_of_sound E w3 kd KD) in NK, NB.
          destruct SO as [(KK_ & _)|[(KK_ & _)|[(KK_ & _)|(KK_ & _)]]]; rewrite (kind_of_sound E w3 kd KD) in KK_; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE in KK_; subst kd; reflexivity.
    - left. exact (FPold a RA (B5 a Ha) NW). }

  assert (HIC : hiZ E' (empty_region lenC) = v_bytes (u_cstk g)).
  { unfold hiZ. cbn [empty_region rg_hi]. rewrite DLC. exact SZC. }
  assert (HIV : hiZ E' (empty_region lenV) = v_bytes (u_vstk g)).
  { unfold hiZ. cbn [empty_region rg_hi]. rewrite DLV. exact SZV. }
  assert (LOE : forall x, loZ (empty_region x) = 0) by (intros x; reflexivity).
  assert (CBV' : bv_unsigned (ev E' kCB) = v_begin (u_cstk g)) by (rewrite EkCB; exact CBV).
  assert (VBV' : bv_unsigned (ev E' kVB) = v_begin (u_vstk g)) by (rewrite EkVB; exact VBV).
  assert (REGC : region_ok segs (s_priv st) E' (ms_mem ms) kCB (empty_region lenC)).
  { apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) kCB (empty_region lenC) KC0).
    - apply IMap.bst_empty.
    - reflexivity.
    - rewrite LOE, CBV'. lia.
    - rewrite HIC, CBV'. unfold two64 in *. lia.
    - intros a Ha. rewrite LOE, HIC, CBV' in Ha.
      destruct (OWNB (cstk_block g) a (UO.owned_cstk g) ltac:(unfold in_iv, cstk_block; cbn [fst snd]; lia)) as (_ & _ & MT & NS & _). split; [exact MT| exact NS].
    - intros gk gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }
  assert (REGV : region_ok segs (s_priv st) E' (ms_mem ms) kVB (empty_region lenV)).
  { apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) kVB (empty_region lenV) KV0).
    - apply IMap.bst_empty.
    - reflexivity.
    - rewrite LOE, VBV'. lia.
    - rewrite HIV, VBV'. unfold two64 in *. lia.
    - intros a Ha. rewrite LOE, HIV, VBV' in Ha.
      destruct (OWNB (vstk_block g) a (UO.owned_vstk g) ltac:(unfold in_iv, vstk_block; cbn [fst snd]; lia)) as (_ & _ & MT & NS & _). split; [exact MT| exact NS].
    - intros gk gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }

  assert (SUBK : forall w3, In w3 ws -> is_kept w3 = false -> K_SUB <= w_kind (wden E w3) < K_GHOST).
  { intros w3 Hw3 IK. pose proof (kept_or_sub ws w3 KL Hw3 IK) as IS. unfold is_sub in IS. destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate IS].
    rewrite (kind_of_sound E w3 kd KD). apply andb_prop in IS as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2. unfold K_SUB, K_GHOST. lia. }

  destruct (PotDrop.pot_drop_spec E (s_facts st) ws ws0 Pfacts0 DROP) as (DSUB & DOLD & DLEN).
  set (kept := List.filter is_kept ws0) in *.
  set (ws' := kept ++ [(VP kCB wzero, lenC, VL (wlit 1%uint63)); (VP kVB wzero, lenV, VL (wlit 1%uint63))]) in *.
  assert (KEPT : forall w, In w kept -> In w ws /\ is_kept w = true) by (intros w Hw; apply filter_In in Hw; split; [exact (DSUB w (proj1 Hw))| exact (proj2 Hw)]).
  assert (KSEALu : Seal.seal_ok (map (wden E) kept) (z_chunks (u_zone g))).
  { apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SEALu|]. intros w Hw _. apply in_map_iff in Hw as (w3 & <- & Hw3).
    apply in_map. exact (proj1 (KEPT w3 Hw3)). }
  assert (LENK : (length kept <= length ws)%nat).
  { assert (X : (length kept <= length ws0)%nat) by (subst kept; clear; induction ws0 as [|w ws IH]; cbn; [lia|]; destruct (is_kept w); cbn; lia). lia. }
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_app; cbn [length]; unfold two63; lia).
  assert (WNC : wden E' (VP kCB wzero, lenC, VL (wlit 1%uint63)) = Win (v_begin (u_cstk g)) (v_bytes (u_cstk g)) K_BLOCK).
  { unfold wden. rewrite (den_VP0 E' kCB wzero (weqb_refl _)), CBV', DLC, SZC. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (WNV : wden E' (VP kVB wzero, lenV, VL (wlit 1%uint63)) = Win (v_begin (u_vstk g)) (v_bytes (u_vstk g)) K_BLOCK).
  { unfold wden. rewrite (den_VP0 E' kVB wzero (weqb_refl _)), VBV', DLV, SZV. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (WSK : map (wden E') kept = map (wden E) kept).
  { apply map_ext_in. intros [[wa wb] wc] Hw. destruct (KEPT _ Hw) as [Hw' _]. unfold wden. destruct (INW wa wb wc Hw') as (Ia & Ib & Ic). rewrite !DR by assumption. reflexivity. }
  assert (WS' : map (wden E') ws' = map (wden E) kept ++ [Win (v_begin (u_cstk g)) (v_bytes (u_cstk g)) K_BLOCK; Win (v_begin (u_vstk g)) (v_bytes (u_vstk g)) K_BLOCK]).
  { subst ws'. rewrite map_app, WSK. cbn [map]. rewrite WNC, WNV. reflexivity. }

  exists E'. split; [exact HX|].
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH ks
           [(kCB, empty_region lenC); (kVB, empty_region lenV)] _ _ (PrimInt63.add n 3)).
  -   intros k Hk. destruct (KS1 k Hk) as (w3 & Hw3 & SB & AN).
    destruct (sub_anchor_spec st w3 k AN) as (len & kd & r0 & -> & K0 & K1 & F0 & LO & W0 & HI). split; [exact K0|]. exists r0. auto.
  -   cbn [map fst]. constructor; [| constructor; [intros []| constructor]]. intros [X|[]]. rewrite X, Uint63.eqb_refl in KCV. discriminate.
  -   intros k r [X|[X|[]]]; injection X as <- <-; assumption.
  -   intros k r [X|[X|[]]]; injection X as <- <-; assumption.
  -   intros k r a [X|[X|[]]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE in IR.
    + rewrite HIC, CBV' in IR. exact (proj2 (proj2 (proj2 (proj2 (OWNB (cstk_block g) a (UO.owned_cstk g) ltac:(unfold in_iv, cstk_block; cbn [fst snd]; lia)))))).
    + rewrite HIV, VBV' in IR. exact (proj2 (proj2 (proj2 (proj2 (OWNB (vstk_block g) a (UO.owned_vstk g) ltac:(unfold in_iv, vstk_block; cbn [fst snd]; lia)))))).
  -   intros k1 r1 k2 r2 a [X1|[X1|[]]] [X2|[X2|[]]] NE12; injection X1 as <- <-; injection X2 as <- <-; try contradiction;
      unfold inR; rewrite !LOE, ?HIC, ?HIV, ?CBV', ?VBV'; unfold rdisj in DCV; lia.
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 5, (den E' aw), (map (wden E') ws'), (map (den E') [c0; VP n wzero]), LB.
    split; [apply (mk_args_sound E' 5%uint63 aw ws' _ LEN')|].
    split.
    { rewrite (DR aw ltac:(rewrite ARGS; right; left; reflexivity)), WS'.
      refine (aw_keep segs IMGX AW _ _ _ _ _ _ (aw_keep segs IMGX AW _ _ _ _ _ _ HA (PotDrop.drop_keep E LB ws ws0 DSUB DOLD)) _).
      match type of Wk with wins_ok ?mdz _ _ => assert (Wk0 : wins_ok mdz g (map (wden E) ws0)) end.
      { unfold wins_ok in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        exact (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ (DSUB x Hx))). }
      apply (UOK.unp_wins_keep _ g LB _ _ P O Wk0).
      - intros w Hw. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]].
        + left. apply in_map_iff in Hw as (w3 & <- & Hw3). apply in_map. exact (proj1 (proj1 (filter_In _ _ _) Hw3)).
        + right. right. split; [reflexivity|]. exact (UO.owned_cstk g).
        + right. right. split; [reflexivity|]. exact (UO.owned_vstk g).
      - intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (is_kept w3) eqn:IK.
        + left. apply in_app_iff. left. apply in_map. subst kept. apply filter_In. split; assumption.
        + right. left. exact (SUBK w3 (DSUB w3 Hw3) IK). }
    split.
    +   rewrite WS'. unfold windows_wf in *. apply Forall_app. split.
      * apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' _].
        exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hw3')).
      * constructor; [| constructor; [|constructor]]; unfold window_wf; cbn [w_lo w_len w_kind w_iv].
        -- split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|]. right; left. split; [reflexivity|]. exact CLB.
        -- split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|]. right; left. split; [reflexivity|]. exact VLB.
    +   apply CW5'. split.
      2: { rewrite WS'. apply TD.nosub_app.
           - apply TD.nosub_kinds. intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [_ IK]. pose proof (is_kept_kind E w3 IK) as KK. unfold K_SUB, K_GHOST. lia.
           - unfold TD.nosub. repeat (constructor; [cbn [w_kind]; unfold K_BLOCK, K_SUB, K_GHOST; lia|]). constructor. }
      unfold td_client0. cbn [map decode_td]. exists cs.
      split. { rewrite (DR c0 ltac:(apply INCA; do 9 right; left; reflexivity)), <- Lc0. subst cs. unfold z_head, hd_addr. reflexivity. }
      split. { rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, u64_of_Z; [reflexivity| unfold two64; lia]. }
      split; [exact TOK|]. split; [exact Z7|]. split; [intros c Hc; exact (proj1 O _ (UO.owned_chunk g c Hc))|]. split.
      * rewrite WS'. apply Forall_app. split.
        -- apply Forall_forall. intros w Hw NK c Hc a Ha Hb. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' IK].
           pose proof (is_kept_kind E w3 IK) as KK.
           destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3') NK) as [[_ D]|[NB SOk]].
           ++ exact (D (chunk_block c) (UO.owned_chunk g c Hc) a Ha Hb).
           ++ exfalso. destruct SOk as [(KK_ & _)|[(KK_ & _)|[(KK_ & _)|(KK_ & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE in KK_; lia.
        -- constructor; [| constructor; [|constructor]]; cbn [w_kind w_iv w_lo w_len]; intros _ c Hc a Ha Hb.
           ++ pose proof (UO.disj_cc g LB O c Hc) as D. unfold rdisj, in_iv, chunk_block, w_iv in D, Ha, Hb. cbn [fst snd w_lo w_len] in D, Ha, Hb. lia.
           ++ pose proof (UO.disj_vc g LB O c Hc) as D. unfold rdisj, in_iv, chunk_block, w_iv in D, Ha, Hb. cbn [fst snd w_lo w_len] in D, Ha, Hb. lia.
      * destruct M as (_ & _ & _ & CH & _). split; [exact CH|].

        rewrite WS'. apply Seal.seal_ok_app; [exact KSEALu|]. constructor; [cbn [w_kind]; unfold K_BLOCK, Seal.K_TWIN; lia| constructor; [cbn [w_kind]; unfold K_BLOCK, Seal.K_TWIN; lia| constructor]].
  -   intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 5 _ (map (wden E') ws') _ a (mk_args_sound E' 5%uint63 aw ws' _ LEN'))) in FPa as (RA & NI & NW).
    rewrite WS' in NW. split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IW|NWo]; [| left; exact (FPold a RA NI NWo)].
      apply (proj1 (in_ws_map_iff E ws a)) in IW as (w3 & Hw3 & Hin).
      destruct (is_kept w3) eqn:IK.
      * exfalso. destruct (DOLD w3 Hw3) as [Hw0|PS]; [| exact (PotDrop.pseudo_no_byte _ a PS Hin)].
        apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left.
        apply in_ivs_In. exists (w_iv (wden E w3)). split; [| exact Hin]. apply in_map. apply in_map. apply filter_In. auto.
      * right. exact (SUBR w3 a Hw3 (kept_or_sub ws w3 KL Hw3 IK) Hin).
    + intros k r [X|[X|[]]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE in IR; apply NW; unfold in_ws; rewrite map_app;
        apply (proj2 (in_ivs_app _ _ _)); right; cbn [map]; unfold in_ivs.
      * rewrite HIC, CBV' in IR. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
      * rewrite HIV, VBV' in IR. apply Exists_cons_tl. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
  -
    destruct P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DL & _). unfold LIMIT in DL.
    destruct VC as (_ & (VC0 & VC1) & _). destruct VV as (_ & (VV0 & VV1) & _).
    assert (FA : forall l1 l2, Forall (fact_holds E') l1 -> Forall (fact_holds E') l2 -> Forall (fact_holds E') (l1 ++ l2)) by (intros; apply Forall_app; split; assumption).
    refine (FA (vd_facts (VP kCB wzero) ce (PrimInt63.add n 1) 8%uint63) (vd_facts (VP kVB wzero) ve (PrimInt63.add n 2) 8%uint63) _ _).
    + apply (vd_facts_sound E' _ ce _ 8%uint63 (v_begin (u_cstk g)) (v_size (u_cstk g))).
      * rewrite (DR _ ltac:(apply INCA; right; left; reflexivity)). symmetry. exact Lcb.
      * rewrite (DR ce ltac:(apply INCA; do 2 right; left; reflexivity)), <- Lce. unfold v_end. rewrite EC. reflexivity.
      * unfold VD_MAXZ; lia.
      * lia.
      * change (to_Z 8%uint63) with 8. unfold v_bytes in Bc3. rewrite EC in Bc3. unfold two64. lia.
      * exact EVj1.
    + apply (vd_facts_sound E' _ ve _ 8%uint63 (v_begin (u_vstk g)) (v_size (u_vstk g))).
      * rewrite (DR _ ltac:(apply INCA; do 4 right; left; reflexivity)). symmetry. exact Lvb.
      * rewrite (DR ve ltac:(apply INCA; do 5 right; left; reflexivity)), <- Lve. unfold v_end. rewrite EV. reflexivity.
      * unfold VD_MAXZ; lia.
      * lia.
      * change (to_Z 8%uint63) with 8. unfold v_bytes in Bv3. rewrite EV in Bv3. unfold two64. lia.
      * exact EVj2.
Qed.

Theorem tdenter_sound : forall pc, contract_sound segs OPS MP PB (tdenter_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [tdenter_contract c_apply] in HAP.
  destruct (tdenter_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. destruct (tdenter_sound_main E st ms model st' HS AP) as (E' & HX & HS').
       exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS'). }
  all: exfalso; unfold tdenter_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.

End TdEnter.
