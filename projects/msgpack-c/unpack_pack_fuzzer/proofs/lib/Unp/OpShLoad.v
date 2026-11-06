(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Tree Seal PkStack PkOps PkLib PkAux TdOps PkPeek PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib PkStep PkStepA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import DecPre.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB HeapOp UG TR PkStack PK PKL.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Module OpShLoad.
Definition SBw : w64 := wlit 0x7fff8000%uint63.
Abbreviation SBz := Seal.SBz (only parsing).
Abbreviation shadZ := Seal.shadZ (only parsing).
Abbreviation seal_ok := Seal.seal_ok (only parsing).

Definition shadow_ptr (a : sv) : option sv :=
  match a with
  | VAlu ALU_ADD (VAlu ALU_SRL p (VL c3)) (VL sb) => if weqb c3 (wlit 3%uint63) && weqb sb SBw then Some p else None
  | VAlu ALU_ADD (VL sb) (VAlu ALU_SRL p (VL c3)) => if weqb c3 (wlit 3%uint63) && weqb sb SBw then Some p else None
  | _ => None
  end.
Definition dec_true (o : option bool) : bool := match o with Some true => true | _ => false end.
Definition dec_false (o : option bool) : bool := match o with Some false => true | _ => false end.

Fixpoint within (fs : list fact) (p base : sv) (d : int) (n : nat) : bool :=
  match n with
  | O => false
  | S n' => if dec_true (decide_eq fs p (sv_alu ALU_ADD base (VL (wlit d)))) then true else within fs p base (PrimInt63.add d 1%uint63) n'
  end.
Section WithSegs.
Variable segs : list Segment.

Definition opshload_apply_spec (st : sstate) : option (list sstate) :=
  match PkPeek.load_at segs (s_pc st), the_op st with
  | Some (SZ1, sx, rd, rs, off), Some (md, aw, ws, ca) =>
      match shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off)) with
      | Some p =>
          let fs := s_facts st in
          let ok :=
            if PrimInt63.eqb md 3%uint63 then
              match ca with
              | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
                  (dec_false (decide_eq0 fs cf) && within fs p cf 0%uint63 24)
                  || (match tmap, tkey with
                      | VL m, VL k =>
                          let expect := if weqb m (wlit 1%uint63) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24%uint63)) else tptr in
                          (weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))
                          && dec_true (decide_ltu fs (VL wzero) trest) && within fs p expect 0%uint63 24
                      | _, _ => false
                      end)

                  || (match PkBody.body_src fs eb rootT n1 P1 cf fT fN fP with
                      | Some (VL t, _, fPb) => weqb t PkBody.T_EXTw && dec_true (decide_eq fs p fPb)
                      | _ => false
                      end)
              | _ => false
              end
            else if PrimInt63.eqb md 5%uint63 then
              match ca with
              | [cur; cnt] => dec_false (decide_eq0 fs cur) && within fs p cur 0%uint63 16
              | _ => false
              end
            else false in
          if ok && negb (r5_eqb rd X0) && PrimInt63.ltb (s_pc st) bit62i
          then Some [setpc (setr st rd (VL wzero)) (PrimInt63.add (s_pc st) 4%uint63)]
          else None
      | None => None
      end
  | _, _ => None
  end.

Fixpoint within_d (dc : DecPre.DecPre.dctx) (fs : list fact) (p base : sv) (d : int) (n : nat) : bool :=
  match n with
  | O => false
  | S n' => if dec_true (DecPre.DecPre.decide_eq_d dc fs p (sv_alu ALU_ADD base (VL (wlit d)))) then true else within_d dc fs p base (PrimInt63.add d 1%uint63) n'
  end.

Fixpoint within_syn (p base : sv) (d : int) (n : nat) : bool :=
  match n with
  | O => false
  | S n' => if sv_eqb p (sv_alu ALU_ADD base (VL (wlit d))) then true else within_syn p base (PrimInt63.add d 1%uint63) n'
  end.
Definition body_src_d (dc : DecPre.DecPre.dctx) (fs : list fact) (eb rootT n1 P1 cf fT fN fP : sv) : option (sv * sv * sv) :=
  if sv_eqb eb (VL wzero) then Some (rootT, n1, P1)
  else if dec_false (DecPre.DecPre.decide_eq0_d dc fs cf) then Some (fT, fN, fP) else None.

Definition arm2_shape (tmap tkey tptr : sv) : option sv :=
  match tmap, tkey with
  | VL m, VL k =>
      if (weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))
      then Some (if weqb m (wlit 1%uint63) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24%uint63)) else tptr)
      else None
  | _, _ => None
  end.
Definition opshload_apply (st : sstate) : option (list sstate) :=
  match PkPeek.load_at segs (s_pc st), the_op st with
  | Some (SZ1, sx, rd, rs, off), Some (md, aw, ws, ca) =>
      match shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off)) with
      | Some p =>
          let fs := s_facts st in
          let ok :=
            if PrimInt63.eqb md 3%uint63 then
              match ca with
              | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>

                  if (match decide_eq0_b fs cf with Some false => within_syn p cf 0%uint63 24 | _ => false end) then true
                  else if (match arm2_shape tmap tkey tptr with
                           | Some expect => match DecPre.DecPre.decide_ltu_c fs (VL wzero) trest with Some true => within_syn p expect 0%uint63 24 | _ => false end
                           | None => false
                           end) then true
                  else

                  let dc := DecPre.DecPre.mk_dc fs in
                  if (if dec_false (DecPre.DecPre.decide_eq0_d dc fs cf) then within_d dc fs p cf 0%uint63 24 else false) then true
                  else if (match arm2_shape tmap tkey tptr with
                           | Some expect => if dec_true (DecPre.DecPre.decide_ltu_d dc fs (VL wzero) trest) then within_d dc fs p expect 0%uint63 24 else false
                           | None => false
                           end) then true
                  else (match body_src_d dc fs eb rootT n1 P1 cf fT fN fP with
                        | Some (VL t, _, fPb) => if weqb t PkBody.T_EXTw then dec_true (DecPre.DecPre.decide_eq_d dc fs p fPb) else false
                        | _ => false
                        end)
              | _ => false
              end
            else if PrimInt63.eqb md 5%uint63 then
              match ca with
              | [cur; cnt] =>
                  if (match decide_eq0_b fs cur with Some false => within_syn p cur 0%uint63 16 | _ => false end) then true
                  else let dc := DecPre.DecPre.mk_dc fs in
                       if dec_false (DecPre.DecPre.decide_eq0_d dc fs cur) then within_d dc fs p cur 0%uint63 16 else false
              | _ => false
              end
            else false in
          if (if negb (r5_eqb rd X0) then PrimInt63.ltb (s_pc st) bit62i else false)
          then (if ok then Some [setpc (setr st rd (VL wzero)) (PrimInt63.add (s_pc st) 4%uint63)] else None)
          else None
      | None => None
      end
  | _, _ => None
  end.

Lemma within_d_eq : forall dc fs, DecPre.DecPre.dc_ok fs dc -> forall p base n d, within_d dc fs p base d n = within fs p base d n.
Proof.
  intros dc fs Hdc p base n. induction n as [|n IH]; intros d; cbn [within_d within]; [reflexivity|].
  rewrite (DecPre.DecPre.decide_eq_d_eq fs dc Hdc), IH. reflexivity.
Qed.
Lemma within_syn_within : forall fs p base n d, within_syn p base d n = true -> within fs p base d n = true.
Proof.
  intros fs p base n. induction n as [|n IH]; intros d H; cbn [within_syn within] in *; [discriminate H|].
  destruct (sv_eqb p (sv_alu ALU_ADD base (VL (wlit d)))) eqn:E.
  - unfold decide_eq, decide_eq_s. rewrite E. reflexivity.
  - rewrite (IH _ H). destruct (dec_true _); reflexivity.
Qed.
Lemma body_src_d_eq : forall dc fs, DecPre.DecPre.dc_ok fs dc -> forall eb rootT n1 P1 cf fT fN fP,
  body_src_d dc fs eb rootT n1 P1 cf fT fN fP = PkBody.body_src fs eb rootT n1 P1 cf fT fN fP.
Proof. intros dc fs Hdc *. unfold body_src_d, PkBody.body_src. rewrite (DecPre.DecPre.decide_eq0_d_eq fs dc Hdc). reflexivity. Qed.
Lemma decide_eq0_b_false : forall fs v, decide_eq0_b fs v = Some false -> dec_false (decide_eq0 fs v) = true.
Proof. intros fs v H. unfold decide_eq0. rewrite H. reflexivity. Qed.
Lemma decide_ltu_c_true : forall fs a b, DecPre.DecPre.decide_ltu_c fs a b = Some true -> dec_true (decide_ltu fs a b) = true.
Proof.
  intros fs a b H. unfold DecPre.DecPre.decide_ltu_c in H. unfold decide_ltu.
  destruct (decide_ltu_s fs a b) as [r|]; [rewrite H; reflexivity|]. rewrite H. reflexivity.
Qed.

Lemma opshload_apply_eq : forall st, opshload_apply st = opshload_apply_spec st.
Proof.
  intros st. unfold opshload_apply, opshload_apply_spec.
  destruct (PkPeek.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|]; [|reflexivity]. destruct sz; try reflexivity.
  destruct (the_op st) as [[[[md aw] ws] ca]|]; [|reflexivity].
  destruct (shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off))) as [p|]; [|reflexivity].
  cbv zeta. set (fs := s_facts st).
  pose proof (DecPre.DecPre.mk_dc_ok fs) as Hdc. set (dc := DecPre.DecPre.mk_dc fs) in *.
  set (ok3 := match ca with | [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] => _ | _ => false end).
  set (ok3s := match ca with | [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _] => _ | _ => false end).
  set (ok5 := match ca with | [_; _] => _ | _ => false end).
  set (ok5s := match ca with | [_; _] => _ | _ => false end).
  assert (E3 : ok3 = ok3s).
  { subst ok3 ok3s. destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
      try reflexivity.
    rewrite (body_src_d_eq dc fs Hdc).

    assert (A2 : forall W : sv -> bool,
              match arm2_shape tmap tkey tptr with Some expect => W expect | None => false end
              = match tmap, tkey with
                | VL m, VL k => (weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))
                                && W (if weqb m (wlit 1%uint63) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24%uint63)) else tptr)
                | _, _ => false
                end).
    { intros W. unfold arm2_shape. destruct tmap as [m| | | | | | | | | |]; try reflexivity. destruct tkey as [k| | | | | | | | | |]; try reflexivity.
      destruct ((weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))); reflexivity. }

    destruct (match decide_eq0_b fs cf with Some false => within_syn p cf 0%uint63 24 | _ => false end) eqn:F1.
    { destruct (decide_eq0_b fs cf) as [[|]|] eqn:B; try discriminate F1.
      rewrite (decide_eq0_b_false _ _ B), (within_syn_within fs _ _ _ _ F1). reflexivity. }
    clear F1.

    destruct (match arm2_shape tmap tkey tptr with
              | Some expect => match DecPre.DecPre.decide_ltu_c fs (VL wzero) trest with Some true => within_syn p expect 0%uint63 24 | _ => false end
              | None => false end) eqn:F2.
    { destruct (arm2_shape tmap tkey tptr) as [expect|] eqn:S2; [|discriminate F2].
      destruct (DecPre.DecPre.decide_ltu_c fs (VL wzero) trest) as [[|]|] eqn:C; try discriminate F2.
      unfold arm2_shape in S2. destruct tmap as [m| | | | | | | | | |]; try discriminate S2. destruct tkey as [k| | | | | | | | | |]; try discriminate S2.
      destruct ((weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))); [|discriminate S2].
      injection S2 as <-. rewrite (decide_ltu_c_true _ _ _ C), (within_syn_within fs _ _ _ _ F2). cbn [andb].
      destruct (dec_false (decide_eq0 fs cf) && within fs p cf 0%uint63 24); reflexivity. }
    clear F2.

    destruct (PkBody.body_src fs eb rootT n1 P1 cf fT fN fP) as [[[t fNb] fPb]|];
      [destruct t as [tw| | | | | | | | | |] |];
      destruct tmap as [mw| | | | | | | | | |]; destruct tkey as [kw| | | | | | | | | |]; cbn [arm2_shape]; cbv zeta;
      try destruct ((weqb mw wzero || weqb mw (wlit 1%uint63)) && (weqb kw wzero || weqb kw (wlit 1%uint63)));
      rewrite ?(within_d_eq dc fs Hdc), ?(DecPre.DecPre.decide_eq0_d_eq fs dc Hdc), ?(DecPre.DecPre.decide_ltu_d_eq fs dc Hdc),
              ?(DecPre.DecPre.decide_eq_d_eq fs dc Hdc);
      destruct (dec_false (decide_eq0 fs cf)); try destruct (within fs p cf 0%uint63 24);
      try destruct (dec_true (decide_ltu fs (VL wzero) trest));
      try destruct (within fs p _ 0%uint63 24);
      try destruct (weqb tw PkBody.T_EXTw); try destruct (dec_true (decide_eq fs p fPb)); reflexivity. }
  assert (E5 : ok5 = ok5s).
  { subst ok5 ok5s. destruct ca as [|cur [|cnt [|? ?]]]; try reflexivity.
    destruct (match decide_eq0_b fs cur with Some false => within_syn p cur 0%uint63 16 | _ => false end) eqn:F1.
    { destruct (decide_eq0_b fs cur) as [[|]|] eqn:B; try discriminate F1.
      rewrite (decide_eq0_b_false _ _ B), (within_syn_within fs _ _ _ _ F1). reflexivity. }
    rewrite (within_d_eq dc fs Hdc), (DecPre.DecPre.decide_eq0_d_eq fs dc Hdc).
    destruct (dec_false (decide_eq0 fs cur)); reflexivity. }
  clearbody ok3 ok3s ok5 ok5s. subst ok3 ok5.
  destruct (PrimInt63.eqb md 3%uint63); [| destruct (PrimInt63.eqb md 5%uint63)];
    destruct ok3s, ok5s, (r5_eqb rd X0), (PrimInt63.ltb (s_pc st) bit62i); reflexivity.
Qed.

Definition opshload_c (pc : int) : contract := Contract pc opshload_apply.
End WithSegs.

Lemma shadow_ptr_sound : forall E a p, shadow_ptr a = Some p ->
  bv_unsigned (den E a) = shadZ (bv_unsigned (den E p)).
Proof.
  intros E a p H. unfold shadow_ptr in H.
  assert (CORE : forall q, bv_unsigned (bv_add (alu64 ALU_SRL (den E q) (wbv (wlit 3%uint63))) (wbv SBw)) = shadZ (bv_unsigned (den E q))).
  { intros q. cbn [alu64 alu]. rewrite bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv. change (to_Z (shamt6 (wlit 3%uint63))) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SBw. rewrite wbv_unsigned, wlit_ok. change (to_Z 2147450880%uint63) with SBz.
    pose proof (bv_unsigned_in_range 64 (den E q)) as R. rewrite bv_modulus_64 in R. unfold shadZ.
    apply bv_wrap_small. rewrite bv_modulus_64. unfold two64, SBz in *. split; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
    assert (bv_unsigned (den E q) / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct a as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [sb| |opx p' c3| | | | | | | |]; try discriminate H.
  -   destruct y as [| |opy p' c3| | | | | | | |]; try discriminate H. destruct opy; try discriminate H.
    destruct c3 as [c3| | | | | | | | | |]; try discriminate H.
    destruct (weqb c3 (wlit 3%uint63) && weqb sb SBw) eqn:C; [|discriminate H]. injection H as <-.
    apply andb_prop in C as [C3 CS]. apply (proj1 (weqb_ok _ _)) in C3. apply (proj1 (weqb_ok _ _)) in CS. subst c3 sb.
    cbn [den]. rewrite <- (CORE p'). cbn [alu64 alu]. rewrite !bv_add_unsigned. f_equal. apply Z.add_comm.
  - destruct opx; try discriminate H. destruct c3 as [c3| | | | | | | | | |]; try discriminate H.
    destruct y as [sb| | | | | | | | | |]; try discriminate H.
    destruct (weqb c3 (wlit 3%uint63) && weqb sb SBw) eqn:C; [|discriminate H]. injection H as <-.
    apply andb_prop in C as [C3 CS]. apply (proj1 (weqb_ok _ _)) in C3. apply (proj1 (weqb_ok _ _)) in CS. subst c3 sb.
    cbn [den]. exact (CORE p').
Qed.

Lemma within_sound : forall E fs, facts_hold E fs -> forall p base n d,
  to_Z d + Z.of_nat n <= 1000 -> within fs p base d n = true ->
  exists j, to_Z d <= j < to_Z d + Z.of_nat n /\ bv_unsigned (den E p) = (bv_unsigned (den E base) + j) mod two64.
Proof.
  intros E fs Hfs p base n. induction n as [|n IH]; intros d B H; cbn [within] in H; [discriminate|].
  destruct (dec_true (decide_eq fs p (sv_alu ALU_ADD base (VL (wlit d))))) eqn:D.
  - exists (to_Z d). split; [lia|]. rewrite (PkAux.deq_sound E fs _ _ Hfs D). apply PkAux.den_add_lit.
  - pose proof (int_range d) as RD.
    assert (E1 : to_Z (PrimInt63.add d 1%uint63) = to_Z d + 1).
    { rewrite Uint63.add_spec. change (to_Z 1%uint63) with 1. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
    destruct (IH (PrimInt63.add d 1%uint63) ltac:(rewrite E1; lia) H) as (j & J & EQ). rewrite E1 in J. exists j. split; [lia| exact EQ].
Qed.

Lemma pk_chunk_apart : forall g ls LB ws c, pure_pk g ls -> own_pk g LB -> wins_pk g ws -> In c (z_chunks (k_zone g)) ->
  forall w, In w ws -> w_kind w <> K_STACK -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a.
Proof.
  intros g ls LB ws c P O Wk Hc w Hw K a Ha.
  assert (OW : In (chunk_block c) (owned g)) by (unfold owned; apply in_app_iff; right; apply in_map; exact Hc).
  destruct (proj1 (Forall_forall _ _) Wk w Hw K) as [[_ D]|[_ ET]]; [exact (D _ OW a Ha)|].
  destruct ET as (_ & VB & E1 & _ & E3).
  pose proof (PkAux.owned_evec g VB) as OV.
  destruct O as [_ OP].
  unfold owned, evec_blocks in OP. destruct (v_begin (k_evec g) =? 0) eqn:Z0; [apply Z.eqb_eq in Z0; contradiction|].
  cbn [app] in OP. inversion OP as [|x l FA _]; subst.
  pose proof (proj1 (Forall_forall _ _) FA (chunk_block c) (in_map _ _ _ Hc)) as RD. cbn [fst snd] in RD.
  unfold in_iv, w_iv in *. cbn [fst snd] in *. unfold rdisj, v_capend, v_bytes in *. intros X. lia.
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.

Hypothesis CW3S : forall ca LB ws m, cw_holds CW 3 ca LB ws m ->
  match decode_pk ca with
  | Some u => exists g ls, link_pk u g ls /\ pure_pk g ls /\ own_pk g LB /\ wins_pk g ws /\ mem_pk (bmem_of segs m) u g ls /\
                           seal_ok ws (z_chunks (k_zone g))
  | None => False
  end.
Hypothesis CW5S : forall ca LB ws m, cw_holds CW 5 ca LB ws m ->
  match TD.decode_td ca with
  | Some (cur, cnt) => exists cs, TD.td_inv cur cnt LB ws (bmem_of segs m) cs /\ seal_ok ws cs
  | None => False
  end.

Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.

Hypothesis SHLAW : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds segs IMGX AW aw LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) ->
  seal_ok ws cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) p ->
  m (Z_to_bv 64 (shadZ p)) = Some (Z_to_bv 8 0) /\ CHS os m mo (shadZ p).
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma opsh_tail : forall E st ms model sx rd rs off p o md awZ wsZ caZ LB cs c,
  st_ok segs OPS E st ms model -> MP model ->
  PkPeek.load_at segs (s_pc st) = Some (SZ1, sx, rd, rs, off) ->
  shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off)) = Some p ->
  PrimInt63.ltb (s_pc st) bit62i = true ->
  In o (s_ops st) -> op_id o = OPID -> decode (map (den E) (op_args o)) = Some (md, awZ, wsZ, caZ) ->
  aw_holds segs IMGX AW awZ LB wsZ (ms_mem ms) model -> windows_wf wsZ LB (aw_ceiling segs IMGX AW model) ->
  seal_ok wsZ cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w wsZ -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) (bv_unsigned (den E p)) ->
  exists ms' mo', mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                  st_ok segs OPS E (setpc (setr st rd (VL wzero)) (pc4 st)) ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sx rd rs off p o md awZ wsZ caZ LB cs c HS HMP LA SP PCB OIN OID DEC HA WF SEAL Hc HLB APART INP.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (PkPeek.load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.
  set (P := bv_unsigned (den E p)) in *.
  assert (INS : In (OPID, map (den E) (op_args o)) (insts E (s_ops st))).
  { unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact OIN]. }
  destruct (SHLAW (insts E (s_ops st)) _ md awZ wsZ caZ LB (ms_mem ms) model cs c P INS DEC HA WF SEAL Hc HLB APART INP) as [BYTE CH].
  pose proof (bv_unsigned_in_range 64 (den E p)) as RP. rewrite bv_modulus_64 in RP. fold P in RP.
  assert (SHB : 0 <= shadZ P /\ shadZ P + 1 <= two64).
  { unfold shadZ, SBz, two64 in *. assert (0 <= P / 8) by (apply Z.div_pos; lia).
    assert (P / 8 < 2305843009213693952) by (apply Z.div_lt_upper_bound; lia). lia. }
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL off)) = Z_to_bv 64 (shadZ P)).
  { apply bv_eq. rewrite (shadow_ptr_sound E _ p SP). fold P. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  assert (RD : rdZ (bmem_of segs (ms_mem ms)) (shadZ P) (Z.to_nat (to_Z (msize_bytes SZ1))) = Some 0).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ].
    rewrite (bmem_of_some segs (ms_mem ms) (shadZ P) (Z_to_bv 8 0) ltac:(lia)); [reflexivity|].
    unfold rb. rewrite BYTE. reflexivity. }
  assert (DV : den E (VL wzero) = ext_word sx 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 0)).
  { cbn [den]. rewrite wbv_wzero. change (to_Z (msize_bytes SZ1)) with 1. symmetry. apply PkStep.ext_word_small; lia. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS CHS LAWS MP HMPA E st ms model w i SZ1 sx rd rs off (shadZ P) 0 (VL wzero)
              HS HMP PCB FW EC DA OI HAD ltac:(lia) ltac:(change (to_Z (msize_bytes SZ1)) with 1; lia) RD DV) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  { intros j Hj. change (to_Z (msize_bytes SZ1)) with 1 in Hj. replace j with 0 by lia. rewrite Z.add_0_r. exact CH. }
  exists ms', mo'. auto.
Qed.

Lemma ext_body_in_zone : forall bm z fo, tree_wf bm z fo -> obj_type fo = T_EXT -> in_zone z (obj_ptr fo) 1.
Proof.
  intros bm z fo TW TY. destruct fo; cbn [obj_type] in TY; unfT; try (exfalso; lia).
  cbn [tree_wf] in TW. destruct TW as (A & B & C & (c & Hc & IC) & _). cbn [obj_ptr].
  exists c. split; [exact Hc|]. unfold in_chunk in *. lia.
Qed.

Lemma opshload_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> opshload_apply segs st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP. rewrite opshload_apply_eq in AP. unfold opshload_apply_spec in AP.
  destruct (PkPeek.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off))) as [p|] eqn:SP; [|discriminate].
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [OKC RDX].
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DECE. rewrite DECE in DEC0. injection DEC0 as <- <- <- <-.
  set (P := bv_unsigned (den E p)) in *.
  pose proof (bv_unsigned_in_range 64 (den E p)) as RP. rewrite bv_modulus_64 in RP. fold P in RP.
  enough (GOAL : exists cs c, seal_ok (map (wden E) ws) cs /\ In c cs /\ In (chunk_block c) LB /\
            (forall w, In w (map (wden E) ws) -> w_kind w <> K_STACK -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) /\
            in_iv (chunk_block c) P).
  { destruct GOAL as (cs & c & SEAL & Hc & HLB & APART & INP).
    destruct (opsh_tail E st ms model sx rd rs off p o _ _ _ _ LB cs c HS HMP LA SP PCB (op_in_In st o OPS1) OID DECE HA WF SEAL Hc HLB (fun w Hw HK => APART w Hw ltac:(destruct HK as [HK|HK]; unfold K_BLOCK, K_GHOST, K_STACK in *; lia)) INP)
      as (ms' & mo' & STEP & MEM & ST2 & MP2).
    exists (setpc (setr st rd (VL wzero)) (pc4 st)), ms', mo'. split; [reflexivity|]. auto. }
  destruct (PrimInt63.eqb mdi 3) eqn:MD3.
  -
    apply Uint63.eqb_correct in MD3. subst mdi. change (to_Z 3%uint63) with 3 in HC.
    destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
      try discriminate.
    apply CW3S in HC. cbn [map decode_pk] in HC.
    destruct HC as (g & ls & L & Pp & O & Wk & M & SEAL).
    pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
    cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
    pose proof Pp as (LV & EL & SZ & VE & CE & ZV).
    pose proof M as (TW & KA & [IC IB] & CH & PE).

    enough (ZR : exists A n, in_zone (k_zone g) A n /\ A <= P < A + n).
    { destruct ZR as (A & n & (c & Hc & ICH) & AP).
      exists (z_chunks (k_zone g)), c. split; [exact SEAL|]. split; [exact Hc|].
      split; [exact (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hc))|].
      split; [exact (pk_chunk_apart g ls LB _ c Pp O Wk Hc)|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH. unfold CHUNK_HDR. lia. }
    apply orb_prop in OKC as [OKC|BODY]; [apply orb_prop in OKC as [FOC|EXP]|].
    +
      apply andb_prop in FOC as [DNZ WI].
      pose proof (PkAux.dnz_sound E _ _ Pfacts DNZ) as CF0.
      destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
      pose proof (last_opt_spec ls) as LS. unfold focus_node in FN. unfold focus_addr in CFA.
      destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
      assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      assert (AZ : in_zone (k_zone g) (lev_addr l) OBJ_SIZE).
      { apply IC. apply (focus_cells _ _ _ _ _ (lev_addr l) HLV FN). destruct fo; cbn; left; reflexivity. }
      destruct (within_sound E _ Pfacts p cf 24 0%uint63 ltac:(change (to_Z 0%uint63) with 0; cbn; lia) WI) as (j & J & EQ).
      change (to_Z 0%uint63) with 0 in J. change (Z.of_nat 24) with 24 in J. fold P in EQ. rewrite CFA in EQ.
      exists (lev_addr l), OBJ_SIZE. split; [exact AZ|].
      destruct AZ as (ch & Hch & ICH).
      destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA
                  (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
      unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in *. rewrite Z.mod_small in EQ by lia. lia.
    +
      destruct tmap as [m| | | | | | | | | |]; try discriminate EXP. destruct tkey as [k| | | | | | | | | |]; try discriminate EXP.
      apply andb_prop in EXP as [EXP WI]. apply andb_prop in EXP as [EXP DREST]. apply andb_prop in EXP as [MB KB].
      pose proof (PkAux.dltu_sound E _ _ _ Pfacts DREST) as REST. cbn [den] in REST. rewrite wbv_unsigned, wzero_ok in REST.
      destruct (last_opt ls) as [l|] eqn:LAST.
      2: { exfalso. destruct LTOP as (_ & T0 & _). lia. }
      destruct LTOP as (Ltp & Ltr & Ltm & Ltk).
      pose proof (last_opt_spec ls) as LS. rewrite LAST in LS. destruct LS as [ls0 ELS].
      assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      assert (RPOS : 0 < pe_rest (elem_of l)) by lia.
      destruct (rest_pos_node _ _ _ HLV RPOS) as [fo HFO].
      pose proof (proj1 (Forall_forall _ _) (levels_forall _ _ HLV) l ltac:(apply in_app_iff; right; left; reflexivity)) as [LC LS0].
      assert (AZ : in_zone (k_zone g) (lev_addr l) OBJ_SIZE).
      { apply IC. apply (focus_cells _ _ _ _ _ (lev_addr l) HLV HFO). destruct fo; cbn; left; reflexivity. }
      assert (PMAP : pe_map (elem_of l) = weqb m (wlit 1%uint63)).
      { cbn [den] in Ltm. rewrite wbv_unsigned in Ltm. apply orb_prop in MB as [MB|MB]; apply (proj1 (weqb_ok _ _)) in MB; subst m;
        [rewrite wzero_ok in Ltm | rewrite wlit_ok in Ltm; change (to_Z 1%uint63) with 1 in Ltm];
        destruct (pe_map (elem_of l)); cbn [b2Z] in Ltm; try lia; reflexivity. }
      assert (PKEY : pe_key (elem_of l) = weqb k (wlit 1%uint63)).
      { cbn [den] in Ltk. rewrite wbv_unsigned in Ltk. apply orb_prop in KB as [KB|KB]; apply (proj1 (weqb_ok _ _)) in KB; subst k;
        [rewrite wzero_ok in Ltk | rewrite wlit_ok in Ltk; change (to_Z 1%uint63) with 1 in Ltk];
        destruct (pe_key (elem_of l)); cbn [b2Z] in Ltk; try lia; reflexivity. }
      assert (PM : pe_map (elem_of l) && negb (pe_key (elem_of l)) = (weqb m (wlit 1%uint63) && weqb k wzero)).
      { rewrite PMAP, PKEY. apply orb_prop in KB as [KB|KB]; apply (proj1 (weqb_ok _ _)) in KB; subst k; reflexivity. }
      pose proof (elem_of_obj l LS0) as POBJ. unfold pe_obj in POBJ. rewrite PM in POBJ.
      pose proof (bv_unsigned_in_range _ (den E tptr)) as TPR. rewrite bv_modulus_64 in TPR.
      destruct AZ as (ch & Hch & ICH).
      destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA
                  (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
      unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
      set (expect := if weqb m (wlit 1%uint63) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24%uint63)) else tptr) in *.
      assert (EXA : bv_unsigned (den E expect) = lev_addr l).
      { subst expect. destruct (weqb m (wlit 1%uint63) && weqb k wzero).
        - rewrite PkAux.den_add_lit. change (to_Z 24%uint63) with 24.
          unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in *. rewrite Z.mod_small by lia. lia.
        - lia. }
      destruct (within_sound E _ Pfacts p expect 24 0%uint63 ltac:(change (to_Z 0%uint63) with 0; cbn; lia) WI) as (j & J & EQ).
      change (to_Z 0%uint63) with 0 in J. change (Z.of_nat 24) with 24 in J. fold P in EQ. rewrite EXA in EQ.
      exists (lev_addr l), OBJ_SIZE. split; [exists ch; split; assumption|].
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in *. rewrite Z.mod_small in EQ by lia. lia.
    +
      destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
      destruct fTv as [t| | | | | | | | | |]; try discriminate.
      apply andb_prop in BODY as [TY DEQP].
      assert (FO : exists fo, tree_wf (bmem_of segs (ms_mem ms)) (k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
                /\ obj_ptr fo = bv_unsigned (den E fPv)).
      { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
        - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
          exists (k_tree g). split; [exact TW|]. split; [exact LT| exact LP].
        - destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ0; try discriminate SRCB. injection SRCB as <- <- <-.
          assert (CF0 : bv_unsigned (den E cf) <> 0).
          {
            pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ0) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
            intros X. apply CNZ. apply bv_eq. rewrite X. reflexivity. }
          destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
          pose proof (last_opt_spec ls) as LS. unfold focus_node in FN.
          destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
          assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
          exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
      destruct FO as (fo & TWF & FT & FPTR).
      unfold PkBody.T_EXTw in TY. apply (proj1 (weqb_ok _ _)) in TY. subst t.
      assert (FT' : obj_type fo = T_EXT) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
      pose proof (ext_body_in_zone _ _ fo TWF FT') as BZ.
      exists (obj_ptr fo), 1. split; [exact BZ|].
      rewrite FPTR. unfold P. rewrite (PkAux.deq_sound E _ _ _ Pfacts DEQP). lia.
  - destruct (PrimInt63.eqb mdi 5) eqn:MD5; [|discriminate].

    apply Uint63.eqb_correct in MD5. subst mdi. change (to_Z 5%uint63) with 5 in HC.
    destruct ca as [|cur [|cnt [|? ?]]]; try discriminate.
    apply andb_prop in OKC as [DNZ WI].
    apply CW5S in HC. cbn [map TD.decode_td] in HC. destruct HC as (cs & (Hcur & Hcnt & Hok & Hdisj & Hlb & Hws & Hat) & SEAL).
    pose proof (PkAux.dnz_sound E _ _ Pfacts DNZ) as CUR0.
    destruct cs as [|[c0 sz0] cs']; [exfalso; apply CUR0; rewrite Hcur; reflexivity|]. cbn [TD.hd_addr] in Hcur.
    exists ((c0, sz0) :: cs'), (c0, sz0). split; [exact SEAL|]. split; [left; reflexivity|].
    split; [apply Hlb; left; reflexivity|].
    split. { intros w Hw K a Ha. exact (proj1 (Forall_forall _ _) Hws w Hw K (c0, sz0) (or_introl eq_refl) a Ha). }
    destruct (within_sound E _ Pfacts p cur 16 0%uint63 ltac:(change (to_Z 0%uint63) with 0; cbn; lia) WI) as (j & J & EQ).
    change (to_Z 0%uint63) with 0 in J. change (Z.of_nat 16) with 16 in J. fold P in EQ. rewrite Hcur in EQ.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block (c0, sz0)) HA (Hlb _ (or_introl eq_refl))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
    pose proof (proj1 (Forall_forall _ _) Hok (c0, sz0) (or_introl eq_refl)) as (_ & _ & S0).
    unfold chunk_block, in_iv in *. cbn [fst snd] in *. unfold CHUNK_HDR, CHUNK_SIZE0 in *. rewrite Z.mod_small in EQ by lia. lia.
Qed.

Theorem opshload_sound : forall pc, contract_sound segs OPS MP PB (opshload_c segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [opshload_c c_apply] in HAP.
  destruct (opshload_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.

End OpShLoad.
