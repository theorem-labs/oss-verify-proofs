(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Cells Step Frame Omono.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops Tree PkOps PkLib GLib GUnp G3 GWin PkStack PkAux.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW TR PK PKL CtrLib CtrFX PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkRegrow.

Definition ETOPk : int := 6%uint63.

Definition kinds_lit (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with Some _ => true | None => false end) ws.

Definition anchor_facts (fs : list fact) (k : int) (dlo dhi : Z) (kA : int) : list fact :=
  match find_range fs k with
  | Some (lo, hi) =>
      if negb (wt lo) && negb (wt hi) && (0 <=? dlo) && (dlo <=? dhi) && (w2Z hi + dhi <? two63)
      then [FRange kA (wlit (Uint63.of_Z (w2Z lo + dlo))) (wlit (Uint63.of_Z (w2Z hi + dhi)))] else []
  | None => []
  end.

Definition range_nz (fs : list fact) (k : int) : bool :=
  match find_range fs k with Some (lo, hi) => negb (wt hi) && negb (weqb lo wzero) | None => false end.

Definition no_other_at (kC : int) (w0 : sv * sv * sv) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match w with (VP k _, _, _) => negb (PrimInt63.eqb k kC) || win3_eqb w w0 | _ => true end) ws.

Definition two40Z : Z := 140737488355328.

Definition dst_anchor (dx n12 : sv) (L : Z) : option int :=
  match dx with
  | VP k o => if weqb o wzero then Some k else None
  | VAlu ALU_SUB (VP k o) x => if negb (wt o) && (w2Z o =? L) && sv_eqb x n12 then Some k else None
  | _ => None
  end.

Definition len_ok (n12 e b : sv) (L : Z) : bool :=
  sv_eqb n12 (VAlu ALU_SUB e b) || sv_eqb n12 (sv_alu ALU_SUB e b)
  || match n12 with VL w => negb (wt w) && (w2Z w =? L) | _ => false end.

Definition kept_r5 : list r5 := [X2; X3; X4; X8; X9; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27].
Fixpoint repl_regs (rs : list r5) (dx v : sv) (st : sstate) : sstate :=
  match rs with
  | [] => st
  | r :: rs' => repl_regs rs' dx v (if sv_eqb (getr st r) dx then setr st r v else st)
  end.

Definition empty_region (L : Z) : region := Region 0%uint63 (VL (wlit (Uint63.of_Z L))) true BGNone IMap.empty.

Definition other_blocks_ok (fs : list fact) (R : IMap.t region) (kN : int) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match w with
                    | (lo, len, VL kd) =>
                        if wt kd || negb (PrimInt63.eqb (wl kd) 1%uint63) then true else
                        match lo with
                        | VP k' o' =>
                            PrimInt63.eqb k' kN
                            || (weqb o' wzero && negb (PrimInt63.eqb k' 0%uint63)
                                && match IMap.find k' R with
                                   | Some r' => PrimInt63.eqb (rg_lo r') 0%uint63
                                                && match decide_ltu fs (VL wzero) (rg_hi r') with Some true => true | _ => false end
                                   | None => false
                                   end)
                        | _ => false
                        end
                    | _ => false
                    end) ws.

Definition sub_windows_ok (R : IMap.t region) (kN : int) (wT : sv * sv * sv) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match w with
                    | (lo, len, VL kd) =>
                        if wt kd || Z.ltb (to_Z (wl kd)) 2 || Z.leb 7 (to_Z (wl kd)) then true else
                        win3_eqb w wT
                        || match lo with
                           | VP k' o' =>
                               negb (PrimInt63.eqb k' kN) && weqb o' wzero && negb (PrimInt63.eqb k' 0%uint63)
                               && match IMap.find k' R with
                                  | Some r' => PrimInt63.eqb (rg_lo r') 0%uint63 && sv_eqb (rg_hi r') len
                                  | None => false
                                  end
                           | _ => false
                           end
                    | _ => false
                    end) ws.

Definition gcells (r : region) (g : int) : option slot :=
  match IMap.find g (rg_cells r) with Some gr => Some (g_cells gr) | None => None end.

Definition region48 (c0 c1 c2 c3 c4 c5 : slot) : region :=
  Region 0%uint63 (VL (wlit 48%uint63)) true BGNone
    (IMap.add 5%uint63 (Gran true c5) (IMap.add 4%uint63 (Gran true c4) (IMap.add 3%uint63 (Gran true c3)
      (IMap.add 2%uint63 (Gran true c2) (IMap.add 1%uint63 (Gran true c1) (IMap.add 0%uint63 (Gran true c0) IMap.empty)))))).

Section WithPc.
Variable MEMCPY_PC : int.

Definition regrow0 (st : sstate) (r : int) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) : option (list sstate) :=
  let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
  let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 0 with
  | Some kN =>
      let wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63)) in
      if sv_eqb (PkStack.c_ee c) (VL wzero) && sv_eqb (PkStack.c_ecap c) (VL wzero)
         && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VL wzero) && len_ok n12 (VL wzero) (VL wzero) 0
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && PkStack.only_kind 6 None ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wN ws
      then
        match IMap.find kN R with
        | Some rN =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) (VL (wlit 24%uint63)) && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
            then
              let st1 := clobber st in
              let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr st1 X10 (VP kN wzero)) in
              let st3 := setpc st2 r in
              let ws' := List.map (fun w => if win3_eqb w wN then top_win kN 24%uint63 ETOPk else w) ws in
              let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                          (VP kN wzero) (VP kN wzero) (VP kN (wlit 24%uint63))
                          (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                          (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
              Some [surg st3 [] [] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) [] (PrimInt63.add n0 15%uint63)]
            else None
        | None => None
        end
      else None
  | None => None
  end.

Definition regrow1 (st : sstate) (r : int) (aw : sv) (ws : list (sv * sv * sv)) (c : PkStack.pkca) (kB kT : int) (oc : w64) : option (list sstate) :=
  let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
  let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
  match dst_anchor dx n12 L with
  | Some kN =>
      let wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63)) in
      let wT := top_win kT 24%uint63 ETOPk in
      if negb (wt oc) && (24 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
         && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63) && negb (PrimInt63.eqb kN 1%uint63)
         && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
         && (PrimInt63.eqb kT kB || match IMap.find kB R with None => true | Some _ => false end)
         && Z.ltb (Z.of_nat (length ws)) 4000
         && sv_eqb (getr st X11) (VP kB wzero) && len_ok n12 (VP kT (wlit 24%uint63)) (VP kB wzero) L
         && implied fs (FULe (VP kT (wlit 24%uint63)) (VP kB oc)) && implied fs (FULe (VP kB oc) (VP kT (wlit 24%uint63)))
         && existsb (win3_eqb wN) ws && no_other_at kN wN ws
         && existsb (win3_eqb wT) ws && PkStack.only_kind 6 (Some wT) ws
         && PrimInt63.leb 3%uint63 (find_align fs kN) && range_nz fs kN
         && kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws
      then
        match IMap.find kN R, IMap.find kT R with
        | Some rN, Some rT =>
            if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) (VL (wlit (Uint63.of_Z (2 * L)))) && rg_w rN
               && match rg_bg rN with BGNone | BGUnk => true | _ => false end
               && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 24%uint63)) && rg_w rT
            then
              let g := Uint63.of_Z (L / 8) in
              match gcells rT 0%uint63, gcells rT 1%uint63, gcells rT 2%uint63,
                    gcells rN g, gcells rN (PrimInt63.add g 1%uint63), gcells rN (PrimInt63.add g 2%uint63) with
              | Some t0, Some t1, Some t2, Some e0, Some e1, Some e2 =>
                  let nT := PrimInt63.add n0 15%uint63 in
                  let st1 := clobber st in
                  let st1' := setregs st1 (IMap.add kN (empty_region (2 * L)) (s_regs st1)) in
                  let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr st1' X10 (VP kN wzero)) in
                  let st3 := setpc st2 r in
                  let rT' := region48 t0 t1 t2 e0 e1 e2 in
                  let rB' := empty_region L in
                  let wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63)) in
                  let wNT := top_win nT 48%uint63 ETOPk in
                  let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT] in
                  let b' := VP kN wzero in let e' := VP nT (wlit 24%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                  let c' := PkStack.PC (PkStack.c_root c) (PkStack.c_rootT c) (PkStack.c_n1 c) (PkStack.c_P1 c) (PkStack.c_zh c) (PkStack.c_c0 c)
                              b' e' cap'
                              (PkStack.c_tptr c) (PkStack.c_trest c) (PkStack.c_tmap c) (PkStack.c_tkey c)
                              (PkStack.c_cf c) (PkStack.c_fT c) (PkStack.c_fN c) (PkStack.c_fP c) in
                  let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 24)))); FULe b' (VP nT wzero); FULe e' cap']
                            ++ top_facts fs b' nT
                            ++ anchor_facts fs kN (L - 24) (L - 24) nT in
                  Some [surg st3 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 3%uint63 aw ws' (PkStack.unparse_ca c')) nf (PrimInt63.add n0 16%uint63)]
              | _, _, _, _, _, _ => None
              end
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition pkregrow_apply (st : sstate) : option (list sstate) :=
  match the_op st, call_pre st with
  | Some (md, aw, ws, ca), Some r =>
      if PrimInt63.eqb md 3%uint63 then
      match PkStack.parse_ca ca with
      | Some c =>
          match PkStack.c_eb c, PkStack.c_ee c, PkStack.c_ecap c with
          | VL b0, _, _ => if weqb b0 wzero then regrow0 st r aw ws c else None
          | VP kB ob, VP kT oe, VP kB' oc =>
              if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63) then regrow1 st r aw ws c kB kT oc else None
          | _, _, _ => None
          end
      | None => None
      end
      else None
  | _, _ => None
  end.

Definition pkregrow_contract : contract := Contract MEMCPY_PC pkregrow_apply.

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
Hypothesis OPS_plain : plain_table OPS.

Definition kept_regs : list (bv 5) := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Hypothesis MEMCPY :
  forall (R F : bvmap 5 word) (fc : bv 32) (M : word -> option byte) (mo : Model) (d s n : Z) (src junk : list byte) (K : TSet),
    PropExec.getr R 10%bv = Z_to_bv 64 d -> PropExec.getr R 11%bv = Z_to_bv 64 s -> PropExec.getr R 12%bv = Z_to_bv 64 n ->
    0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
    MState.ret_pc (PropExec.getr R 1%bv) = PropExec.getr R 1%bv ->
    Lib.Mem.bytes_at segs M s src -> length src = Z.to_nat n ->
    rw_cells segs M d [CB (Z.to_nat n) junk] ->
    (s + n <= d \/ d + n <= s) ->
    Lib.Mem.mem_inv segs M -> m_halted mo = None -> m_vm_lazy mo = [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte),
        (forall r, In r kept_regs -> PropExec.getr R' r = PropExec.getr R r) -> PropExec.getr R' 10%bv = Z_to_bv 64 d ->
        munch [(d, d + n)] M M' -> wmono segs M M' -> Lib.Mem.mem_inv segs M' ->
        rw_cells segs M' d [CB (Z.to_nat n) src] -> Lib.Mem.bytes_at segs M' s src ->
        omono M M' ->
        realizes segs (mkCfg (MS R' F (PropExec.getr R 1%bv) fc None M' (seg_rom segs)) mo) K) ->
    realizes segs (mkCfg (MS R F (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None M (seg_rom segs)) mo) K.

Ltac is_arith T :=
  lazymatch T with
  | (@eq Z _ _) => idtac | (not (@eq Z _ _)) => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | (_ /\ _) => idtac | (_ \/ _) => idtac
  | _ => fail
  end.
Ltac revert_arith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then revert H else fail
         end.
Ltac alia := revert_arith; let K := fresh "aliaK" in pose proof I as K; clear - K; intros; unfold two64, two63, two62Z in *; lia.
Ltac inlist := cbn [In]; repeat first [left; reflexivity | right].

Lemma neqb_neq : forall a b, negb (PrimInt63.eqb a b) = true -> a <> b.
Proof. intros a b H. apply negb_true_iff in H. exact (Uint63.eqb_false_correct _ _ H). Qed.
Lemma neq_eqb : forall a b, a <> b -> PrimInt63.eqb a b = false.
Proof. intros a b H. apply (proj2 (Uint63.eqb_false_spec _ _)). exact H. Qed.
Lemma existsb_win_In : forall w ws, existsb (win3_eqb w) ws = true -> In w ws.
Proof.
  intros w ws H. apply existsb_exists in H as (x & Hx & Q).
  assert (E0 : x = w).
  { unfold win3_eqb in Q. destruct w as [[a1 a2] a3]. destruct x as [[b1 b2] b3].
    apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2].
    apply sv_eqb_eq in Q1. apply sv_eqb_eq in Q2. apply sv_eqb_eq in Q3. congruence. }
  subst x. exact Hx.
Qed.

Lemma win3_eqb_kind_false : forall a b ka kb, kind_of a = Some ka -> kind_of b = Some kb -> ka <> kb -> win3_eqb a b = false.
Proof.
  intros a b ka kb Ha Hb NE. destruct (win3_eqb a b) eqn:Q; [|reflexivity]. apply win3_eqb_eq in Q. subst b. rewrite Ha in Hb. injection Hb. intros; subst; contradiction.
Qed.

Lemma den_VP_nowrap : forall E k o, bv_unsigned (ev E k) + w2Z o < two64 ->
  bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E k o H. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  pose proof (bv_unsigned_in_range _ (ev E k)). pose proof (w2Z_range o). apply Z.mod_small. lia.
Qed.

Lemma den_VAlu : forall E op a b, den E (VAlu op a b) = alu64 op (den E a) (den E b).
Proof. reflexivity. Qed.

Lemma kinds_lit_kind : forall E ws, kinds_lit ws = true -> forall x, In x ws -> exists kd, kind_of x = Some kd /\ w_kind (wden E x) = kd.
Proof.
  intros E ws H x Hx. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [kd|] eqn:K; [|discriminate]. exists kd. split; [reflexivity| exact (kind_of_sound E x kd K)].
Qed.

Lemma anchor_facts_sound : forall E fs k dlo dhi kA, facts_hold E fs ->
  bv_unsigned (ev E k) + dlo <= bv_unsigned (ev E kA) <= bv_unsigned (ev E k) + dhi ->
  Forall (fact_holds E) (anchor_facts fs k dlo dhi kA).
Proof.
  intros E fs k dlo dhi kA FH B. unfold anchor_facts.
  destruct (find_range fs k) as [[lo hi]|] eqn:FR; [|constructor].
  destruct (negb (wt lo) && negb (wt hi) && (0 <=? dlo) && (dlo <=? dhi) && (w2Z hi + dhi <? two63)) eqn:C; [|constructor].
  apply andb_prop in C as [C H5]. apply andb_prop in C as [C H4]. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
  pose proof (find_range_sound_gen E fs FH k lo hi FR) as [R1 R2]. pose proof (w2Z_range lo). pose proof (w2Z_range hi).
  constructor; [|constructor]. cbn [fact_holds]. rewrite !wlit_ok, !of_Z_small by (unfold two63 in *; lia). lia.
Qed.

Lemma repl_regs_fields : forall rs dx v st,
  s_pc (repl_regs rs dx v st) = s_pc st /\ s_ff (repl_regs rs dx v st) = s_ff st /\ s_resv (repl_regs rs dx v st) = s_resv st /\
  s_regs (repl_regs rs dx v st) = s_regs st /\ s_facts (repl_regs rs dx v st) = s_facts st /\ s_ops (repl_regs rs dx v st) = s_ops st /\
  s_priv (repl_regs rs dx v st) = s_priv st /\ s_next (repl_regs rs dx v st) = s_next st.
Proof.
  induction rs as [|r rs IH]; intros dx v st; cbn [repl_regs]; [repeat split; reflexivity|].
  destruct (sv_eqb (getr st r) dx); [| apply IH].
  destruct (IH dx v (setr st r v)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). rewrite A1, A2, A3, A4, A5, A6, A7, A8.
  destruct st, r; repeat split; reflexivity.
Qed.

Lemma repl_regs_sound : forall rs dx v E st ms mo,
  st_ok segs OPS E st ms mo -> ~ In X0 rs -> den E dx = den E v -> st_ok segs OPS E (repl_regs rs dx v st) ms mo.
Proof.
  induction rs as [|r rs IH]; intros dx v E st ms mo HS NX D; cbn [repl_regs]; [exact HS|].
  apply IH; [| intros X; apply NX; right; exact X| exact D].
  destruct (sv_eqb (getr st r) dx) eqn:Q; [|exact HS].
  apply sv_eqb_eq in Q. apply setreg_sound; [exact HS| intros ->; apply NX; left; reflexivity| rewrite Q; exact D].
Qed.

Arguments repl_regs : simpl never.
Local Opaque repl_regs.

Lemma present_bytes : forall (m : word -> option byte) lo n,
  (forall a, lo <= a < lo + Z.of_nat n -> m (Z_to_bv 64 a) <> None) -> 0 <= lo -> lo + Z.of_nat n <= 2 ^ 64 ->
  exists bs, length bs = n /\ Lib.Mem.bytes_at segs m lo bs.
Proof.
  intros m lo n BY L0 LH.
  exists (map (fun i => match m (Z_to_bv 64 (lo + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
  rewrite length_map, length_seq. split; [reflexivity|].
  split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec i n); [|lia]. cbn [option_map Nat.add]. unfold Lib.Mem.mrd, Lib.Mem.wa.
  destruct (m (Z_to_bv 64 (lo + Z.of_nat i))) eqn:Mb; [reflexivity|]. exfalso. exact (BY (lo + Z.of_nat i) ltac:(lia) Mb).
Qed.

Lemma iv_sep : forall (D S hd hs n : Z),
  (forall a, D <= a < D + hd -> ~ (S <= a < S + hs)) -> 0 < n -> n <= hd -> n <= hs -> S + n <= D \/ D + n <= S.
Proof.
  intros D S hd hs n DISJ Hn Nd Ns.
  destruct (Z_lt_le_dec D S) as [L|G].
  - destruct (Z_lt_le_dec S (D + n)) as [L2|G2]; [| right; exact G2]. exfalso. apply (DISJ S); lia.
  - destruct (Z_lt_le_dec D (S + n)) as [L2|G2]; [| left; exact G2]. exfalso. apply (DISJ D); lia.
Qed.

Lemma rdZ_shift : forall (bm bm' : bmem) n a a',
  (forall i, 0 <= i < Z.of_nat n -> bm' (a' + i) = bm (a + i)) -> rdZ bm' a' n = rdZ bm a n.
Proof.
  intros bm bm' n. induction n as [|n IH]; intros a a' H; [reflexivity|].
  rewrite !rdZ_succ. pose proof (H 0 ltac:(lia)) as H0. rewrite !Z.add_0_r in H0. rewrite H0.
  rewrite (IH (a + 1) (a' + 1)); [reflexivity|]. intros i Hi. replace (a' + 1 + i) with (a' + (1 + i)) by lia. replace (a + 1 + i) with (a + (1 + i)) by lia.
  apply H. lia.
Qed.

Lemma slot_ok_shift : forall E (m m' : word -> option byte) A A' cs,
  slot_ok segs E m A cs -> (forall i, 0 <= i < 8 -> rb segs m' (A' + i) = rb segs m (A + i)) -> slot_ok segs E m' A' cs.
Proof.
  intros E m m' A A' cs [SS FA] RB. split; [exact SS|]. apply Forall_forall. intros c Hc.
  pose proof (proj1 (Forall_forall _ _) FA c Hc) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  intros i Hi. rewrite <- Z.add_assoc, (RB (to_Z (c_idx c) + i)) by lia. rewrite Z.add_assoc. exact (B4 i Hi).
Qed.

Lemma range_nz_sound : forall E fs k, facts_hold E fs -> range_nz fs k = true -> bv_unsigned (ev E k) <> 0.
Proof.
  intros E fs k FH H. unfold range_nz in H. destruct (find_range fs k) as [[lo hi]|] eqn:FR; [|discriminate].
  apply andb_prop in H as [_ H]. apply negb_true_iff in H. pose proof (find_range_sound_gen E fs FH k lo hi FR) as [L _].
  assert (w2Z lo <> 0).
  { intros X. assert (lo = wzero) by (apply w2Z_inj; rewrite X, wzero_ok; reflexivity). subst lo. rewrite weqb_refl in H. discriminate H. }
  pose proof (w2Z_range lo). lia.
Qed.

Lemma empty_region_ok : forall priv E m k L,
  PrimInt63.eqb k 0%uint63 = false -> 0 <= L < two62Z -> bv_unsigned (ev E k) + L < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + L -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  region_ok segs priv E m k (empty_region L) /\ hiZ E (empty_region L) = L /\ loZ (empty_region L) = 0.
Proof.
  intros priv E m k L K RL R BY. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  assert (HI : hiZ E (empty_region L) = L).
  { unfold hiZ. cbn [empty_region rg_hi den]. rewrite wbv_unsigned, wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. unfold two62Z in RL. lia. }
  assert (LO : loZ (empty_region L) = 0) by reflexivity.
  split; [| split; [exact HI| exact LO]].
  apply (region_ok_fresh segs priv E m k _ K).
  - exact I.
  - reflexivity.
  - rewrite LO. lia.
  - rewrite HI. lia.
  - intros a Ha. rewrite LO, HI in Ha. apply BY. lia.
  - intros g gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma reg_of_X1 : reg_of_r5 X1 = 1%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X10 : reg_of_r5 X10 = 10%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X11 : reg_of_r5 X11 = 11%bv. Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_of_X12 : reg_of_r5 X12 = 12%bv. Proof. apply bv_eq. reflexivity. Qed.

Lemma call_pre_inv : forall st r, call_pre st = Some r ->
  s_resv st = RNone /\ fresh_ok st = true /\ PrimInt63.land r 1%uint63 = 0%uint63 /\
  exists ra, getr st X1 = VL ra /\ wt ra = false /\ PrimInt63.ltb (wl ra) bit62i = true /\ r = wl ra.
Proof.
  intros st r H. unfold call_pre in H. destruct (s_resv st); try discriminate H. split; [reflexivity|].
  destruct (fresh_ok st); [|discriminate]. split; [reflexivity|].
  unfold ret_pc, small_lit in H. destruct (getr st X1) as [ra| | | | | | | | | |]; try discriminate.
  destruct (wt ra) eqn:WT; [discriminate|]. cbn [negb andb] in H. destruct (PrimInt63.ltb (wl ra) bit62i) eqn:LT; [|discriminate].
  destruct (PrimInt63.eqb (PrimInt63.land (wl ra) 1) 0) eqn:Q; [|discriminate]. injection H as <-. apply Uint63.eqb_correct in Q.
  split; [exact Q|]. exists ra. split; [reflexivity|]. split; [exact WT|]. split; [exact LT| reflexivity].
Qed.

Lemma fresh_ok_inv : forall st, fresh_ok st = true ->
  st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof.
  intros st H. unfold fresh_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. apply Uint63.ltb_spec in H2. apply Uint63.ltb_spec in H3. change (to_Z 0%uint63) with 0 in H2.
  change (to_Z 4611686018427387648%uint63) with (2 ^ 62 - 256) in H3. lia.
Qed.

Lemma minv_of_mem_inv : forall M, Lib.Mem.mem_inv segs M ->
  forall x b, M x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros M MI x b Hx seg Hs. pose proof (MI x b Hx) as X. unfold Lib.Mem.ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Lemma munch_frame : forall (m M' : word -> option byte) (D nZ : Z),
  munch [(D, D + nZ)] m M' -> forall a, 0 <= a < two64 -> ~ (D <= a < D + nZ) -> M' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros m M' D nZ MU a Ha NI. apply (MU (Z_to_bv 64 a)). cbn. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64 in *; lia).
  split; [exact NI| exact I].
Qed.

Lemma setr_fields : forall st r v,
  s_pc (setr st r v) = s_pc st /\ s_ff (setr st r v) = s_ff st /\ s_resv (setr st r v) = s_resv st /\ s_regs (setr st r v) = s_regs st /\
  s_facts (setr st r v) = s_facts st /\ s_ops (setr st r v) = s_ops st /\ s_priv (setr st r v) = s_priv st /\ s_next (setr st r v) = s_next st.
Proof. intros [] r v; destruct r; repeat split; reflexivity. Qed.
Lemma setpc_fields : forall st r,
  s_rf (setpc st r) = s_rf st /\ s_ff (setpc st r) = s_ff st /\ s_resv (setpc st r) = s_resv st /\ s_regs (setpc st r) = s_regs st /\
  s_facts (setpc st r) = s_facts st /\ s_ops (setpc st r) = s_ops st /\ s_priv (setpc st r) = s_priv st /\ s_next (setpc st r) = s_next st /\ s_pc (setpc st r) = r.
Proof. intros [] r; repeat split; reflexivity. Qed.
Lemma setregs_fields : forall st R,
  s_pc (setregs st R) = s_pc st /\ s_rf (setregs st R) = s_rf st /\ s_ff (setregs st R) = s_ff st /\ s_resv (setregs st R) = s_resv st /\ s_regs (setregs st R) = R /\
  s_facts (setregs st R) = s_facts st /\ s_ops (setregs st R) = s_ops st /\ s_priv (setregs st R) = s_priv st /\ s_next (setregs st R) = s_next st.
Proof. intros [] R; repeat split; reflexivity. Qed.
Lemma getr_setregs : forall st R x, getr (setregs st R) x = getr st x.
Proof. intros [] R x; reflexivity. Qed.
Lemma setregs_eq : forall st R, setregs st R = SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) R (s_facts st) (s_ops st) (s_priv st) (s_next st).
Proof. intros; reflexivity. Qed.

Lemma FOP_cons : forall {A} (Rr : A -> A -> Prop) a l, ForallOrdPairs Rr (a :: l) -> Forall (Rr a) l /\ ForallOrdPairs Rr l.
Proof. intros A Rr a l H. inversion H; subst; auto. Qed.

Lemma new_block_apart : forall E fs R (A : word) LB m model kN rN (NB : Z) ws (wN wT x : sv * sv * sv),
  facts_hold E fs -> regions_disjoint E R ->
  IMap.find kN R = Some rN -> PrimInt63.eqb kN 0%uint63 = false -> rg_lo rN = 0%uint63 -> hiZ E rN = NB -> 0 < NB -> rg_w rN = true ->
  aw_holds segs IMGX AW A LB (map (wden E) ws) m model -> In (bv_unsigned (ev E kN), NB) LB ->
  windows_wf (map (wden E) ws) LB (aw_ceiling segs IMGX AW model) ->
  kinds_lit ws = true -> other_blocks_ok fs R kN ws = true -> no_other_at kN wN ws = true -> sub_windows_ok R kN wT ws = true ->
  In wN ws -> wden E wN = Win (bv_unsigned (ev E kN)) NB HeapOp.K_BLOCK ->
  In x ws -> x <> wN -> x <> wT -> w_kind (wden E x) <> K_STACK ->
  forall a, in_iv (w_iv (wden E x)) a -> ~ (bv_unsigned (ev E kN) <= a < bv_unsigned (ev E kN) + NB).
Proof.
  intros E fs R A LB m model kN rN NB ws wN wT x Pfacts0 Pdisj0 FN KN0 LON HIN NBP WN HA NLB WF KL OBK NOA SWO INN WNE Hx' NxN NxT NS a Ha HN.
  set (Nz := bv_unsigned (ev E kN)) in *.
  pose proof (proj1 (forallb_forall _ _) KL x Hx') as KLx. cbn beta iota in KLx. destruct (kind_of x) as [kd|] eqn:KDx; [|discriminate KLx].
  pose proof (kind_of_sound E x kd KDx) as WK.
  destruct x as [[xlo xlen] xkd]. unfold kind_of in KDx. cbn [snd] in KDx.
  destruct xkd as [kw| | | | | | | | | |]; try discriminate KDx. destruct (wt kw) eqn:KWT; [discriminate KDx|]. injection KDx as <-.
  destruct (Z.eq_dec (to_Z (wl kw)) HeapOp.K_BLOCK) as [K1|NK1].
  -
    pose proof (proj1 (forallb_forall _ _) OBK _ Hx') as OB. cbn beta iota in OB. rewrite KWT in OB. cbn [orb] in OB.
    assert (KW1 : PrimInt63.eqb (wl kw) 1 = true) by (apply (proj2 (Uint63.eqb_spec _ _)); apply Uint63.to_Z_inj; rewrite K1; reflexivity).
    rewrite KW1 in OB. cbn [negb] in OB.
    destruct xlo as [|kx ox| | | | | | | | |]; try discriminate OB.
    destruct (PrimInt63.eqb kx kN) eqn:KXN.
    + apply Uint63.eqb_correct in KXN. subst kx. pose proof (proj1 (forallb_forall _ _) NOA _ Hx') as NO. cbn beta iota in NO. rewrite Uint63.eqb_refl in NO. cbn [negb orb] in NO.
      apply win3_eqb_eq in NO. exact (NxN NO).
    + cbn [orb] in OB. apply andb_prop in OB as [OB FND]. apply andb_prop in OB as [OX KX0]. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
      destruct (IMap.find kx R) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HX0].
      apply Uint63.eqb_correct in LOX. destruct (decide_ltu fs (VL wzero) (rg_hi rx)) as [[|]|] eqn:DH; try discriminate HX0.
      pose proof (decide_ltu_sound E fs Pfacts0 _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS. cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS.
      apply Uint63.eqb_false_correct in KXN.
      pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
      destruct WFx as (_ & _ & _ & [[KS _]|[[_ INx]|[KS _]]]);
        [rewrite WK in KS; unfold HeapOp.K_STACK, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia| | rewrite WK in KS; unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia].
      unfold w_iv, wden in INx. cbn [w_lo w_len] in INx. rewrite (den_VP0 E kx wzero (weqb_refl _)) in INx.
      unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E kx wzero (weqb_refl _)) in Ha.
      destruct (Z.eq_dec (bv_unsigned (ev E kx)) Nz) as [EQX|NEX].
      * apply (Pdisj0 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) Nz). unfold loZ. rewrite LOX, LON, HIN. unfold hiZ. rewrite EQX.
        change (keyZ 0%uint63) with 0. fold Nz. clear - HPOS NBP. lia.
      * exact (aw_blocks_disj segs IMGX AW _ LB _ m model _ _ a HA INx NLB ltac:(cbn [fst]; exact NEX) Ha ltac:(unfold in_iv; cbn [fst snd]; exact HN)).
  -
    pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
    assert (K2 : 2 <= to_Z (wl kw)).
    { rewrite WK in NS. destruct WFx as (_ & _ & _ & [[KS _]|[[KS _]|[KS _]]]); rewrite WK in KS;
        unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in NS, KS, NK1; clear - NS KS NK1; lia. }
    pose proof (proj1 (forallb_forall _ _) SWO _ Hx') as SW. cbn beta iota in SW. rewrite KWT in SW. cbn [orb] in SW.
    destruct (Z.ltb_spec (to_Z (wl kw)) 2); [lia|].
    destruct (Z.leb_spec 7 (to_Z (wl kw))) as [K7|K7].
    {
      pose proof (aw_ghost_apart segs IMGX AW _ LB _ m model HA) as GA.
      apply (GA _ _ (in_map (wden E) _ _ Hx') (in_map (wden E) _ _ INN)) with (a := a).
      - rewrite WK. unfold HeapOp.K_GHOST. exact K7.
      - rewrite WNE. reflexivity.
      - exact Ha.
      - rewrite WNE. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact HN. }
    cbn [orb] in SW.
    apply orb_prop in SW as [SW|SW]; [apply win3_eqb_eq in SW; exact (NxT SW)|].
    destruct xlo as [|kx ox| | | | | | | | |]; try discriminate SW.
    apply andb_prop in SW as [SW FND]. apply andb_prop in SW as [SW KX0]. apply andb_prop in SW as [KXN OX].
    apply negb_true_iff in KXN. apply Uint63.eqb_false_correct in KXN. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
    destruct (IMap.find kx R) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HXR]. apply Uint63.eqb_correct in LOX. apply sv_eqb_eq in HXR.
    unfold wden, w_iv, in_iv in Ha. rewrite (den_VP0 E kx wzero (weqb_refl _)) in Ha. cbn [w_lo w_len fst snd] in Ha.
    apply (Pdisj0 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) a). unfold loZ. rewrite LOX, LON, HIN. unfold hiZ. rewrite HXR.
    change (keyZ 0%uint63) with 0. fold Nz. alia.
Qed.

Lemma pelems_at_shift : forall es (bm bm' : bmem) a a',
  (forall i, 0 <= i < ELEM_SIZE * Z.of_nat (length es) -> bm' (a' + i) = bm (a + i)) -> pelems_at bm a es -> pelems_at bm' a' es.
Proof.
  induction es as [|e es IH]; intros bm bm' a a' H C; [exact I|]. cbn [pelems_at] in C |- *. destruct C as (C1 & C2 & C3 & C4 & C5).
  cbn [length] in H. rewrite Nat2Z.inj_succ in H. unfold ELEM_SIZE in *.
  split; [| split; [| split; [| split]]].
  - unfold u64_at in *. rewrite (rdZ_shift bm bm' 8 a a'); [exact C1|]. intros i Hi. apply H. lia.
  - unfold u64_at in *. rewrite (rdZ_shift bm bm' 8 (a + 8) (a' + 8)); [exact C2|]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
  - unfold u8_at in *. rewrite (rdZ_shift bm bm' 1 (a + 16) (a' + 16)); [exact C3|]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
  - unfold u8_at in *. rewrite (rdZ_shift bm bm' 1 (a + 17) (a' + 17)); [exact C4|]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
  - apply (IH bm bm' (a + 24) (a' + 24)); [| exact C5]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
Qed.

Lemma region48_ok : forall priv E m k c0 c1 c2 c3 c4 c5,
  PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + 48 < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + 48 -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  slot_ok segs E m (bv_unsigned (ev E k)) c0 -> slot_ok segs E m (bv_unsigned (ev E k) + 8) c1 -> slot_ok segs E m (bv_unsigned (ev E k) + 16) c2 ->
  slot_ok segs E m (bv_unsigned (ev E k) + 24) c3 -> slot_ok segs E m (bv_unsigned (ev E k) + 32) c4 -> slot_ok segs E m (bv_unsigned (ev E k) + 40) c5 ->
  region_ok segs priv E m k (region48 c0 c1 c2 c3 c4 c5).
Proof.
  intros priv E m k c0 c1 c2 c3 c4 c5 K R BY S0 S1 S2 S3 S4 S5. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  assert (HI : hiZ E (region48 c0 c1 c2 c3 c4 c5) = 48) by (unfold hiZ; cbn [region48 rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (LO : loZ (region48 c0 c1 c2 c3 c4 c5) = 0) by reflexivity.
  assert (CIN : forall base s c i, slot_ok segs E m base s -> In c s -> 0 <= i < to_Z (c_w c) -> 0 <= to_Z (c_idx c) + i < 8).
  { intros base s c i [_ FA] Hc Hi. pose proof (proj1 (Forall_forall _ _) FA c Hc) as (B1 & B2 & B3 & _). lia. }
  assert (B5 : IMap.bst (IMap.add 4%uint63 (Gran true c4) (IMap.add 3%uint63 (Gran true c3) (IMap.add 2%uint63 (Gran true c2) (IMap.add 1%uint63 (Gran true c1) (IMap.add 0%uint63 (Gran true c0) IMap.empty)))))).
  { repeat apply IMap.bst_add. exact I. }
  apply (region_ok_fresh segs priv E m k _ K).
  - cbn [region48 rg_cells]. apply IMap.bst_add. exact B5.
  - reflexivity.
  - rewrite LO. lia.
  - rewrite HI. lia.
  - intros a Ha. rewrite LO, HI in Ha. apply BY. lia.
  - intros g gr F. rewrite LO, HI. cbn [region48 rg_cells] in F.
    destruct (Uint63.eqb g 5) eqn:G5.
    { apply Uint63.eqb_correct in G5. subst g. rewrite IMap.find_add_same in F by (repeat apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 5%uint63) with 5. replace (bv_unsigned (ev E k) + 8 * 5) with (bv_unsigned (ev E k) + 40) by lia.
      split; [exact S5| intros c i Hc Hi; pose proof (CIN _ _ c i S5 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G5. rewrite IMap.find_add_other in F by (first [(repeat apply IMap.bst_add; exact I) | congruence]).
    destruct (Uint63.eqb g 4) eqn:G4.
    { apply Uint63.eqb_correct in G4. subst g. rewrite IMap.find_add_same in F by (repeat apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 4%uint63) with 4. replace (bv_unsigned (ev E k) + 8 * 4) with (bv_unsigned (ev E k) + 32) by lia.
      split; [exact S4| intros c i Hc Hi; pose proof (CIN _ _ c i S4 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G4. rewrite IMap.find_add_other in F by (first [(repeat apply IMap.bst_add; exact I) | congruence]).
    destruct (Uint63.eqb g 3) eqn:G3.
    { apply Uint63.eqb_correct in G3. subst g. rewrite IMap.find_add_same in F by (repeat apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 3%uint63) with 3. replace (bv_unsigned (ev E k) + 8 * 3) with (bv_unsigned (ev E k) + 24) by lia.
      split; [exact S3| intros c i Hc Hi; pose proof (CIN _ _ c i S3 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G3. rewrite IMap.find_add_other in F by (first [(repeat apply IMap.bst_add; exact I) | congruence]).
    destruct (Uint63.eqb g 2) eqn:G2.
    { apply Uint63.eqb_correct in G2. subst g. rewrite IMap.find_add_same in F by (repeat apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 2%uint63) with 2. replace (bv_unsigned (ev E k) + 8 * 2) with (bv_unsigned (ev E k) + 16) by lia.
      split; [exact S2| intros c i Hc Hi; pose proof (CIN _ _ c i S2 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G2. rewrite IMap.find_add_other in F by (first [(repeat apply IMap.bst_add; exact I) | congruence]).
    destruct (Uint63.eqb g 1) eqn:G1.
    { apply Uint63.eqb_correct in G1. subst g. rewrite IMap.find_add_same in F by (repeat apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 1%uint63) with 1. replace (bv_unsigned (ev E k) + 8 * 1) with (bv_unsigned (ev E k) + 8) by lia.
      split; [exact S1| intros c i Hc Hi; pose proof (CIN _ _ c i S1 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G1. rewrite IMap.find_add_other in F by (first [(repeat apply IMap.bst_add; exact I) | congruence]).
    destruct (Uint63.eqb g 0) eqn:G0.
    { apply Uint63.eqb_correct in G0. subst g. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
      change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r.
      split; [exact S0| intros c i Hc Hi; pose proof (CIN _ _ c i S0 Hc Hi); lia]. }
    apply Uint63.eqb_false_correct in G0. rewrite IMap.find_add_other in F by (first [exact I | congruence]). rewrite IMap.find_empty in F. discriminate F.
Qed.

Lemma regrow0_sound : forall st r aw ws ca c sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) -> call_pre st = Some r ->
  PkStack.parse_ca ca = Some c -> (exists b0, PkStack.c_eb c = VL b0 /\ weqb b0 wzero = true) ->
  regrow0 st r aw ws c = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r aw ws ca c sts K E ms model Hpc TO CP PCA (b0 & EB & B00) HAP HS0 HMP HPB Hk.
  apply (proj1 (weqb_ok _ _)) in B00. subst b0.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb] in EB. subst eb.
  unfold regrow0 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP.
  set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 0) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs st)) as [rN|] eqn:FN; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B]. apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [EE0 EC0].
  apply sv_eqb_eq in EE0. apply sv_eqb_eq in EC0. subst ee ecap.
  apply negb_true_iff in KN0. apply negb_true_iff in KN1. apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN.
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN.
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & ra & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.

  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pminv0].
  set (R := ms_regs ms). set (FR := ms_fregs ms). set (fc := ms_fcsr ms). set (m := ms_mem ms).
  assert (MSE : ms = MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)).
  { rewrite (MS_eta ms) at 1 by exact Psvc0. f_equal; [rewrite Ppc0, Hpc; reflexivity| rewrite RESV in Presv0; exact Presv0| exact Prom0]. }
  pose proof (MemFX.getr_R segs OPS E st ms model HS0) as GR.
  assert (HS0' : st_ok segs OPS E st (MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)) model) by (rewrite <- MSE; exact HS0).

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VL wzero; VL wzero; VL wzero; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  assert (VBn12 : sv_vars_below n0 n12 = true) by (subst n12; unfold getr; exact (rf_allb_get _ _ _ VBrf X12)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  pose proof HC as HCm. apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).
  assert (VB0 : v_begin (k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
  destruct VE as [(_ & VC0 & LS0)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)]. subst ls.
  set (Nz := bv_unsigned (ev E kN)) in *.
  set (bm := bmem_of segs m) in *.

  pose proof (Preg0 kN rN FN) as ROKN.
  assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
  assert (HIN' : hiZ E rN = 24) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr. rewrite LON', HIN' in RNr. fold Nz in RNr.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.

  assert (N12V : bv_unsigned (den E n12) = 0).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu den]. rewrite bv_sub_unsigned, wrap64, wbv_unsigned, wzero_ok. reflexivity.
    - apply sv_eqb_eq in LEN. rewrite LEN. replace (sv_alu ALU_SUB (VL wzero) (VL wzero)) with (VL wzero) by (vm_compute; reflexivity).
      cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? 0) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + 0 - 0) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }
  assert (R10 : PropExec.getr R 10%bv = Z_to_bv 64 Nz).
  { rewrite <- reg_of_X10. unfold R. rewrite (GR X10). fold dx. rewrite DXV. subst Nz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R11 : PropExec.getr R 11%bv = Z_to_bv 64 0).
  { rewrite <- reg_of_X11. unfold R. rewrite (GR X11), X11B. apply bv_eq. cbn [den]. rewrite wbv_unsigned. reflexivity. }
  assert (R12 : PropExec.getr R 12%bv = Z_to_bv 64 0).
  { rewrite <- reg_of_X12. unfold R. rewrite (GR X12). fold n12. rewrite <- N12V. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R1 : PropExec.getr R 1%bv = Z_to_bv 64 (to_Z (wl ra))).
  { rewrite <- reg_of_X1. unfold R. rewrite (GR X1), X1V. cbn [den]. unfold wbv. rewrite (w2Z_nowt ra RWT). reflexivity. }
  pose proof (int_range (wl ra)) as Rra. rewrite two63_eq in Rra.
  assert (EVENz : to_Z (wl ra) mod 2 = 0).
  { pose proof (land_mk (wl ra) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVEN in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  assert (RETPC : MState.ret_pc (PropExec.getr R 1%bv) = PropExec.getr R 1%bv) by (rewrite R1; apply ret_pc_even; [lia| exact EVENz]).

  assert (SRC : Lib.Mem.bytes_at segs m 0 []) by (split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia).
  destruct (MemFX.based_rw_cells segs (s_priv st) E m kN rN 0 0%nat ROKN KN0 WN ltac:(rewrite LON'; lia) ltac:(rewrite HIN'; cbn; lia)) as (junk & JLEN & DST).
  rewrite Z.add_0_r in DST. fold Nz in DST.
  pose proof (plain_mf _ _ OPS_plain Pmf0) as [MH ML].
  rewrite MSE.
  apply (MEMCPY R FR fc m model Nz 0 0 [] junk K R10 R11 R12 ltac:(alia) ltac:(alia) ltac:(alia) RETPC SRC eq_refl DST ltac:(left; alia)
           (MemFX.mem_inv_of_st_ok segs OPS E st ms model HS0) MH ML).
  intros R' M' KEPT A0' MU WM MI' RW' BA' OM.

  assert (MM : forall x, M' x = m x).
  { intros x. pose proof (bv_unsigned_in_range 64 x) as RX. rewrite bv_modulus_64 in RX.
    rewrite <- (Z_to_bv_bv_unsigned x). apply (munch_frame m M' Nz 0 MU); [unfold two64; exact RX| lia]. }

  set (Fv := fun i : Z => MemFX.cfv R' (Z_to_bv 64 0) i).
  set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
  set (E1 := env_above E n0 Fv Gv).
  assert (HX : env_ext n0 E E1) by (subst E1; apply env_above_ext).
  assert (TZ15 : to_Z (PrimInt63.add n0 15) = to_Z n0 + 15) by (rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia); reflexivity).
  assert (EVN1 : ev E1 kN = ev E kN) by (subst E1; apply ev_below; exact KN_LT).
  assert (DR1 : forall v, In v (op_args o) -> den E1 v = den E v) by (intros v Hv; exact (den_reval n0 E E1 HX v (VBo v Hv))).
  pose proof (st_ok_reval segs OPS n0 E E1 HX st ms model NPOS VB HS0) as HSE1.
  pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 _ Preg1 Pdisj1 _ Pfacts1 _ _ _ _].

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply (proj1 (r5_eqb_spec _ _)) in Q. subst x. rewrite reg_of_X10, A0', R10. reflexivity.
    - apply KEPT. assert (N10 : x <> X10) by (intros ->; rewrite (proj2 (r5_eqb_spec X10 X10) eq_refl) in Q; discriminate Q).
      destruct x; try discriminate CPx; try congruence; unfold kept_regs; cbn [In];
        repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end. }
  assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)).
  { intros x i Hc. subst Fv. cbn beta. apply MemFX.cfv_clob. exact Hc. }
  pose proof (MemFX.clobber_sound segs OPS E st R R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs) model Fv Gv HS0' VB NPOS N62 HF HKR) as HS1.
  fold n0 in HS1. change (env_above E n0 Fv Gv) with E1 in HS1.
  pose proof (clobber_fields st) as (Cpc & Cff & Crv & Creg & Cfs & Cops & Cpv & Cnx). fold n0 in Cnx.

  pose proof (MemFX.st_ok_mem_ext segs OPS E1 (clobber st) R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m M' (seg_rom segs) model MM HS1) as HS2.

  assert (DDX1 : den E1 dx = den E1 (VP kN wzero)).
  { rewrite (den_reval n0 E E1 HX dx VBdx), DXV. rewrite <- EVN1. apply bv_eq. symmetry. exact (den_VP0 E1 kN wzero (weqb_refl _)). }
  assert (G10 : getr (clobber st) X10 = dx) by (subst dx; rewrite getr_clobber; reflexivity).
  pose proof (setreg_sound segs OPS E1 (clobber st) _ model X10 (VP kN wzero) HS2 ltac:(discriminate) ltac:(rewrite G10; exact DDX1)) as HS3.
  pose proof (repl_regs_sound kept_r5 dx (VP kN wzero) E1 _ _ model HS3 ltac:(cbn; intuition discriminate) DDX1) as HS4.
  pose proof (MemFX.setpc_sound segs OPS E1 _ R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None M' (seg_rom segs) model (wl ra) HS4) as HS5.
  rewrite R1.
  apply (Hk st' (or_introl eq_refl) E1 _ model HX HMP).
  set (st5 := setpc (repl_regs kept_r5 dx (VP kN wzero) (setr (clobber st) X10 (VP kN wzero))) (wl ra)) in *.
  pose proof (repl_regs_fields kept_r5 dx (VP kN wzero) (setr (clobber st) X10 (VP kN wzero))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  pose proof (setr_fields (clobber st) X10 (VP kN wzero)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
  pose proof (setpc_fields (repl_regs kept_r5 dx (VP kN wzero) (setr (clobber st) X10 (VP kN wzero))) (wl ra)) as (P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59).
  assert (F5ops : s_ops st5 = opre ++ o :: opost) by (subst st5; rewrite P56, Q6, Y6, Cops; exact OPSEQ).
  assert (F5regs : s_regs st5 = s_regs st) by (subst st5; rewrite P54, Q4, Y4, Creg; reflexivity).
  assert (F5pv : s_priv st5 = s_priv st) by (subst st5; rewrite P57, Q7, Y7; exact Cpv).
  assert (F5fs : s_facts st5 = fs) by (subst st5; rewrite P55, Q5, Y5, Cfs; reflexivity).
  subst st'.
  change (setpc (repl_regs kept_r5 dx (VP kN wzero) (setr (clobber st) X10 (VP kN wzero))) (wl ra)) with st5.

  set (bm' := bmem_of segs M').
  assert (BMM : forall a, bm' a = bm a) by (intros a; subst bm bm'; unfold bmem_of, rb; rewrite (MM (Z_to_bv 64 a)); reflexivity).

  assert (WD1 : forall w, In w ws -> wden E1 w = wden E w).
  { intros [[w1 w2] w3] Hw. destruct (INW _ Hw) as (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3. unfold wden. rewrite (DR1 _ I1), (DR1 _ I2), (DR1 _ I3). reflexivity. }
  assert (MWD1 : map (wden E1) ws = map (wden E) ws) by (apply map_ext_in; exact WD1).
  set (wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz 24 HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity. }

  assert (NLB : In (Nz, 24) LB).
  { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite (WNd E eq_refl) in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
    - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
    - exact IN.
    - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 24 -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
  assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).

  assert (HA' : aw_holds segs IMGX AW (den E aw) LB (map (wden E) ws) M' model).
  { refine (proj1 (aw_frame segs IMGX AW _ LB _ m M' model HA _ (fun a _ Hm => OM _ Hm))). intros a Ha Hd. symmetry. apply MM. }

  set (wNT := top_win kN 24%uint63 ETOPk).
  set (ws' := map (fun w => if win3_eqb w wN then wNT else w) ws).
  set (ca' := [root; rootT; n1; P1; zh; c0; VP kN wzero; VP kN wzero; VP kN (wlit 24%uint63); tptr; trest; tmap; tkey; cf; fT; fN; fP]).
  assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN) \/ w = wNT).
  { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQx & Hx). destruct (win3_eqb x wN) eqn:Q.
    - right. symmetry. exact EQx.
    - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate Q. }
  assert (LENws' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; clear - WLEN; lia).
  assert (WNTd : wden E1 wNT = Win Nz 24 6) by (subst wNT; rewrite top_win_den, EVN1; reflexivity).
  assert (Db' : bv_unsigned (den E1 (VP kN wzero)) = Nz) by (rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
  assert (Dcap' : bv_unsigned (den E1 (VP kN (wlit 24%uint63))) = Nz + 24).
  { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, EVN1; fold Nz; change (to_Z 24%uint63) with 24; [reflexivity| alia]. }
  set (g' := PKG (k_tree g) (mkVec Nz 0 1 24) (k_zone g)).
  apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ model o HS5 opre opost F5ops OID OPOTH []
           [] (mk_args 3%uint63 aw ws' ca') _ (PrimInt63.add n0 15)).
  -   intros k [].
  -   constructor.
  -   intros k rr [].
  -   intros k rr [].
  -   intros k rr a [].
  -   intros k1 r1 k2 r2 a [].
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
    split; [apply mk_args_sound; exact LENws'|].
    assert (AWE : den E1 aw = den E aw) by (apply DR1; rewrite ARGS; right; left; reflexivity). rewrite AWE.
    split.
    { pose proof HA' as HA2. rewrite <- MWD1 in HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
      - intros x Hx. destruct (KEPTW x Hx) as [[Hx' _]| ->]; [left; exact Hx'| right; apply UOK.kind_new_sub; reflexivity].
      - intros x Hx. destruct (UOK.map_replace_old ws wN wNT x Hx) as [H1| ->]; [left; exact H1| right].
        rewrite (WNd E1 EVN1). split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
        exists (Nz, 24). split; [exact NLB|]. split; [unfold in_iv; cbn [fst snd w_lo]; clear; lia|]. left. unfold c24, C24_LO, C24_HI. cbn [snd]. clear. lia. }
    split.
    +
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPTW x Hx) as [[Hx' _]| ->].
      * rewrite (WD1 x Hx'). exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
      * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
        right; right. split; [unfold HeapOp.K_SUB; alia|]. exists (Nz, 24). split; [exact NLB|]. intros a Ha. exact Ha.
    +
      apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
      assert (DRC : forall v, In v [root; rootT; n1; P1; zh; c0; VL wzero; VL wzero; VL wzero; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> den E1 v = den E v)
        by (intros v Hv; apply DR1; apply INCA; exact Hv).
      assert (VNV : vec_valid (mkVec Nz 0 1 24)) by (unfold vec_valid; cbn [v_elt v_size v_cap v_begin]; split; [alia|]; split; [alia|]; split; [exact NZ0| exact NZ8]).
      assert (OWN' : owned g' = (Nz, 24) :: map chunk_block (z_chunks (k_zone g))).
      { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone v_begin]. rewrite (proj2 (Z.eqb_neq _ _) NZ0). reflexivity. }
      assert (OWNo : owned g = map chunk_block (z_chunks (k_zone g))).
      { unfold owned, evec_blocks. rewrite VB0. reflexivity. }
      exists g', []. split; [| split; [| split; [| split]]].
      *
        unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP last_opt rev].
        rewrite ?(DRC root), ?(DRC rootT), ?(DRC n1), ?(DRC P1), ?(DRC zh), ?(DRC c0), ?(DRC tptr), ?(DRC trest), ?(DRC tmap), ?(DRC tkey),
                ?(DRC cf), ?(DRC fT), ?(DRC fN), ?(DRC fP) by inlist.
        rewrite Db', Dcap'. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
        split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
        split; [reflexivity|]. split; [alia|]. split; [alia|].
        cbn [last_opt rev] in LTOP. split; [exact LTOP|].
        intros CF. destruct (LCF CF) as (X & _). exfalso. exact (X eq_refl).
      *
        unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone v_elt v_size v_cap v_begin]. unfold v_capend. cbn [v_begin v_elt v_cap].
        split; [exact LV|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; split; [exact VNV| split; [lia| split; [reflexivity| lia]]]|]. split; [alia| exact ZV].
      *
        unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF. split.
        -- intros b [<-|Hb]; [exact NLB| exact (OL b Hb)].
        -- constructor; [| exact OF]. apply Forall_forall. intros cb Hcb.
           pose proof (DISJN cb ltac:(rewrite OWNo; exact Hcb)) as D. unfold rdisj. cbn [fst snd].
           apply in_map_iff in Hcb as (ch & <- & Hch). unfold chunk_block. cbn [fst snd].
           destruct ZV as ((_ & _ & V3 & _) & _). destruct (V3 ch Hch) as (_ & _ & S3).
           destruct (Z_lt_le_dec (fst ch) (Nz + 24)) as [A1|A1]; [| left; exact A1].
           destruct (Z_lt_le_dec Nz (fst ch + (CHUNK_HDR + snd ch))) as [A2|A2]; [| right; exact A2].
           exfalso. destruct (Z_lt_le_dec (fst ch) Nz) as [A3|A3].
           ++ apply (D Nz ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
           ++ apply (D (fst ch) ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
      *
        unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
        rewrite OWN'.
        destruct (KEPTW x Hx) as [[Hx' NxN]| ->].
        -- rewrite (WD1 x Hx') in NS |- *.
           destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]]; [| destruct ET as (_ & NE0 & _); exfalso; exact (NE0 VB0)].
           left. split; [exact KDx|]. intros b [<-|Hb] a Ha Hb'.
           ++ unfold in_iv in Hb'. cbn [fst snd] in Hb'.
              exact (new_block_apart E fs (s_regs st) _ LB m model kN rN 24 ws wN wN x Pfacts0 Pdisj0 FN KN0 LON HIN' ltac:(lia) WN HA NLB WF KL OBK NOA SWO EXN (WNd E eq_refl)
                       Hx' NxN NxN NS a Ha Hb').
           ++ exact (DJ b ltac:(rewrite OWNo; exact Hb) a Ha Hb').
        -- right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
           unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
           split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia.
      *
        split.
        2: { split; [destruct GH as [SE EP]; split|].
             3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| cbn [a_cf]; rewrite (DRC cf ltac:(do 13 right; left; reflexivity)); reflexivity].
                  intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                  destruct (KEPTW x Hx) as [[Hx' _]| ->]; [rewrite (WD1 x Hx'); apply in_map; exact Hx'|].
                  exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
             - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
               destruct (KEPTW x Hx) as [[Hx' _]| ->]; [rewrite (WD1 x Hx'); apply in_map; exact Hx'|].
               exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
             - intros _. exists (wden E1 wNT). split.
               + apply in_map. subst ws'. apply in_map_iff. exists wN. rewrite win3_eqb_refl. split; [reflexivity| exact EXN].
               + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
                 split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia. }
        unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone v_begin]. fold bm'.
        destruct (PK.mem_frame segs _ g [] LB (map (wden E) ws) m M' P O Wk ltac:(intros a _ _ _; symmetry; exact (MM (Z_to_bv 64 a))) M) as (M1 & M2 & M3 & M4 & M5).
        split; [exact M1|]. split; [exact M2|]. split; [cbn [a_root] in M3 |- *; rewrite (DRC root) by inlist; exact M3|].
        split; [exact M4|]. intros _. cbn. exact I.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
    split; [| intros k rr []].
    left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))). rewrite MWD1.
    split; [exact RA0|]. split; [exact NI|]. intros IW. apply (proj1 (in_ws_map_iff E ws a)) in IW as (w & Hw & Hin).
    destruct (win3_eqb w wN) eqn:QN.
    + apply win3_eqb_eq in QN. subst w. apply (NWi wNT); [subst ws'; apply in_map_iff; exists wN; rewrite win3_eqb_refl; auto|].
      rewrite WNTd. rewrite (WNd E eq_refl) in Hin. exact Hin.
    + apply (NWi w); [subst ws'; apply in_map_iff; exists w; rewrite QN; auto|]. rewrite (WD1 w Hw). exact Hin.
  -   constructor.
Qed.

Lemma regrow1_sound : forall st r aw ws ca c kB kT oc sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) -> call_pre st = Some r ->
  PkStack.parse_ca ca = Some c -> PkStack.c_eb c = VP kB wzero -> PkStack.c_ee c = VP kT (wlit 24%uint63) -> PkStack.c_ecap c = VP kB oc ->
  regrow1 st r aw ws c kB kT oc = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r aw ws ca c kB kT oc sts K E ms model Hpc TO CP PCA EB EE EC HAP HS0 HMP HPB Hk.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb PkStack.c_ee PkStack.c_ecap] in EB, EE, EC. subst eb ee ecap.
  unfold regrow1 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs st)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  destruct (gcells rT 0%uint63) as [t0|] eqn:GT0; [|discriminate]. destruct (gcells rT 1%uint63) as [t1|] eqn:GT1; [|discriminate].
  destruct (gcells rT 2%uint63) as [t2|] eqn:GT2; [|discriminate].
  destruct (gcells rN (Uint63.of_Z (L / 8))) as [e0|] eqn:GN0; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 1%uint63)) as [e1|] eqn:GN1; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 2%uint63)) as [e2|] eqn:GN2; [|discriminate].
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND TKB].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [OCT L24].
  apply negb_true_iff in OCT. apply Z.leb_le in L24. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0. apply negb_true_iff in KN1.
  apply neqb_neq in NNT. apply neqb_neq in NNB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN. apply existsb_win_In in EXT.
  apply andb_prop in COND2 as [COND2 WT]. apply andb_prop in COND2 as [COND2 HIT]. apply andb_prop in COND2 as [COND2 LOT].
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN. apply Uint63.eqb_correct in LOT. apply sv_eqb_eq in HIT.
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & ra & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.

  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pminv0].
  set (R := ms_regs ms). set (FR := ms_fregs ms). set (fc := ms_fcsr ms). set (m := ms_mem ms).
  assert (MSE : ms = MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)).
  { rewrite (MS_eta ms) at 1 by exact Psvc0. f_equal; [rewrite Ppc0, Hpc; reflexivity| rewrite RESV in Presv0; exact Presv0| exact Prom0]. }
  pose proof (MemFX.getr_R segs OPS E st ms model HS0) as GR.
  assert (HS0' : st_ok segs OPS E st (MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)) model) by (rewrite <- MSE; exact HS0).

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (INb : In (VP kB wzero) (op_args o)) by (apply INCA; inlist).
  assert (INe : In (VP kT (wlit 24%uint63)) (op_args o)) by (apply INCA; inlist).
  assert (INcap : In (VP kB oc) (op_args o)) by (apply INCA; inlist).
  assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero INb).
  assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 24%uint63) INe).
  assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  assert (VBn12 : sv_vars_below n0 n12 = true) by (subst n12; unfold getr; exact (rf_allb_get _ _ _ VBrf X12)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  pose proof HC as HCm. apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & LK & P & O & Wk & M & GH & CO).
  pose proof LK as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & ICB & CH & PE).
  set (V := k_evec g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.
  set (bm := bmem_of segs m) in *.
  change (v_begin (k_evec g) = bv_unsigned (den E (VP kB wzero))) in Leb.
  change (v_end (k_evec g) = bv_unsigned (den E (VP kT (wlit 24%uint63)))) in Lee.
  change (v_capend (k_evec g) = bv_unsigned (den E (VP kB oc))) in Lecap.
  fold V in Leb, Lee, Lecap.
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in Leb. fold Bz in Leb.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.

  pose proof (Preg0 kN rN FN) as ROKN. pose proof (Preg0 kT rT FT) as ROKT.
  assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
  assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
  pose proof (w2Z_range oc) as ROC. fold L in ROC. unfold two40Z in L40.
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. alia. }
  assert (HIN' : hiZ E rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
  assert (HIT' : hiZ E rT = 24) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr. rewrite LON', HIN' in RNr. fold Nz in RNr.
  pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT' in RTr. fold Tz in RTr.

  assert (DVE : bv_unsigned (den E (VP kT (wlit 24%uint63))) = Tz + 24).
  { apply den_VP_nowrap. rewrite wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. clear - RTr. lia. }
  rewrite DVE in Lee.
  pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as IM1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as IM2.
  cbn [fact_holds] in IM1, IM2. rewrite DVE in IM1, IM2.
  assert (VCE : v_capend V = Bz + 24 * v_cap V) by (unfold v_capend; rewrite EL, Leb; reflexivity).
  assert (VEN : v_end V = Bz + 24 * v_size V) by (unfold v_end; rewrite EL, Leb; reflexivity).
  assert (VVAL : vec_valid V /\ ecap_ok (v_cap V)).
  { destruct VE as [(B0 & C0 & LS0)|VV]; [| exact VV]. exfalso.

    pose proof (bv_unsigned_in_range 64 (den E (VP kB oc))) as RC. rewrite bv_modulus_64 in RC.
    rewrite VCE, C0 in Lecap. rewrite VEN in Lee. subst ls. cbn [length Z.of_nat] in SZ. rewrite SZ in Lee. alia. }
  destruct VVAL as (VVAL & CPOS & CPOW). pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  pose proof (proj1 O _ (owned_evec g ltac:(fold V; rewrite Leb; fold V in VV3; rewrite Leb in VV3; exact VV3))) as VLB. fold V in VLB. rewrite Leb in VLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ m model _ HA VLB) as (Bb1 & Bb2 & Bb3 & Bb4 & _). cbn [fst snd] in Bb1, Bb2, Bb3.
  assert (VBY : v_bytes V = 24 * v_cap V) by (unfold v_bytes; rewrite EL; reflexivity).
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { assert (DM : bv_unsigned (den E (VP kB oc)) = (Bz + L) mod two64) by (cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wrap64; reflexivity).
    rewrite VBY in Bb3. rewrite VCE in Lecap. pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.
    destruct (Z_lt_le_dec (Bz + L) two64) as [LT2|GE2].
    - rewrite Z.mod_small in DM by (clear - LT2 RB ROC; lia). exact DM.
    - exfalso. rewrite <- (Z.mod_unique (Bz + L) two64 1 (Bz + L - two64)) in DM by (clear - GE2 RB ROC; unfold two64 in *; lia).
      clear - DM Lecap Bb3 CEIL ROC RB L40 Bb1 Bb2 CPOS. unfold two64 in *. lia. }
  rewrite DVC in Lecap, IM1, IM2.
  assert (LCAP : L = 24 * v_cap V) by alia.
  assert (SZC : v_size V = v_cap V) by alia.
  assert (CAP2 : 2 * v_cap V <= 1024).
  { apply (PKL.cap_double_ok (k_tree g) ls); [exact (proj1 CPOW)| exact LV| exact (proj2 ZV)| rewrite <- SZC; exact SZ]. }
  assert (TZ24 : Tz + 24 = Bz + L) by alia.

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + L - L) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }
  assert (R10 : PropExec.getr R 10%bv = Z_to_bv 64 Nz).
  { rewrite <- reg_of_X10. unfold R. rewrite (GR X10). fold dx. rewrite DXV. subst Nz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R11 : PropExec.getr R 11%bv = Z_to_bv 64 Bz).
  { rewrite <- reg_of_X11. unfold R. rewrite (GR X11), X11B. subst Bz. rewrite <- (den_VP0 E kB wzero (weqb_refl _)). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R12 : PropExec.getr R 12%bv = Z_to_bv 64 L).
  { rewrite <- reg_of_X12. unfold R. rewrite (GR X12). fold n12. rewrite <- N12V. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R1 : PropExec.getr R 1%bv = Z_to_bv 64 (to_Z (wl ra))).
  { rewrite <- reg_of_X1. unfold R. rewrite (GR X1), X1V. cbn [den]. unfold wbv. rewrite (w2Z_nowt ra RWT). reflexivity. }
  pose proof (int_range (wl ra)) as Rra. rewrite two63_eq in Rra.
  assert (EVENz : to_Z (wl ra) mod 2 = 0).
  { pose proof (land_mk (wl ra) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EVEN in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  assert (RETPC : MState.ret_pc (PropExec.getr R 1%bv) = PropExec.getr R 1%bv) by (rewrite R1; apply ret_pc_even; [lia| exact EVENz]).

  assert (UB : forall a, Bz <= a < Bz + L -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ m model _ a HA VLB). unfold in_iv. cbn [fst snd]. rewrite VBY. alia. }
  destruct (present_bytes m Bz (Z.to_nat L) ltac:(intros a Ha; apply UB; alia) ltac:(alia) ltac:(alia)) as (srcb & SLEN & SRC).
  destruct (MemFX.based_rw_cells segs (s_priv st) E m kN rN 0 (Z.to_nat L) ROKN KN0 WN ltac:(rewrite LON'; lia) ltac:(rewrite HIN'; alia)) as (junk & JLEN & DST).
  rewrite Z.add_0_r in DST. fold Nz in DST.

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz (2 * L) HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (VOWN : In (Bz, L) (owned g)) by (rewrite <- Leb, LCAP, <- VBY; apply owned_evec; fold V; rewrite Leb; alia).
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }
  pose proof (plain_mf _ _ OPS_plain Pmf0) as [MH ML].
  rewrite MSE.
  apply (MEMCPY R FR fc m model Nz Bz L srcb junk K R10 R11 R12 ltac:(alia) ltac:(alia) ltac:(alia) RETPC SRC
           ltac:(rewrite SLEN; reflexivity) DST SEP (MemFX.mem_inv_of_st_ok segs OPS E st ms model HS0) MH ML).
  intros R' M' KEPT A0' MU WM MI' RW' BA' OM.

  set (NT := Nz + L - 24).
  set (Fv := fun i : Z => if i =? 15 then Z_to_bv 64 NT else MemFX.cfv R' (Z_to_bv 64 0) i).
  set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
  set (E1 := env_above E n0 Fv Gv).
  assert (HX : env_ext n0 E E1) by (subst E1; apply env_above_ext).
  set (nT := PrimInt63.add n0 15) in *.
  assert (TZ15 : to_Z nT = to_Z n0 + 15) by (subst nT; rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia); reflexivity).
  assert (TZ16 : to_Z (PrimInt63.add n0 16) = to_Z n0 + 16) by (rewrite add_Z by (change (to_Z 16%uint63) with 16; rewrite wB_two63, two63_eq; alia); reflexivity).
  assert (ENT : ev E1 nT = Z_to_bv 64 NT).
  { subst E1. rewrite ev_above by alia. rewrite TZ15. replace (to_Z n0 + 15 - to_Z n0) with 15 by alia. reflexivity. }
  assert (EVN1 : ev E1 kN = ev E kN) by (subst E1; apply ev_below; exact KN_LT).
  assert (EVB1 : ev E1 kB = ev E kB) by (subst E1; apply ev_below; exact KB_LT).
  assert (EVT1 : ev E1 kT = ev E kT) by (subst E1; apply ev_below; exact KT_LT).
  assert (DR1 : forall v, In v (op_args o) -> den E1 v = den E v) by (intros v Hv; exact (den_reval n0 E E1 HX v (VBo v Hv))).
  assert (NTV : bv_unsigned (ev E1 nT) = NT).
  { rewrite ENT, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. subst NT. alia. }
  pose proof (st_ok_reval segs OPS n0 E E1 HX st ms model NPOS VB HS0) as HSE1.
  pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 _ Preg1 Pdisj1 _ Pfacts1 _ _ _ _].

  assert (HKR : forall x, x <> X0 -> clob_pos x = None -> PropExec.getr R' (reg_of_r5 x) = PropExec.getr R (reg_of_r5 x)).
  { intros x N0 CPx. destruct (r5_eqb x X10) eqn:Q.
    - apply (proj1 (r5_eqb_spec _ _)) in Q. subst x. rewrite reg_of_X10, A0', R10. reflexivity.
    - apply KEPT. assert (N10 : x <> X10) by (intros ->; rewrite (proj2 (r5_eqb_spec X10 X10) eq_refl) in Q; discriminate Q).
      destruct x; try discriminate CPx; try congruence; unfold kept_regs; cbn [In];
        repeat match goal with |- ?a = ?b \/ _ => first [left; apply bv_eq; reflexivity | right] | |- False => fail end. }
  assert (HF : forall x i, clob_pos x = Some i -> Fv (Z.of_nat i) = PropExec.getr R' (reg_of_r5 x)).
  { intros x i Hc. subst Fv. cbn beta.
    replace (Z.of_nat i =? 15) with false by (destruct x; cbn in Hc; try discriminate Hc; injection Hc as <-; reflexivity).
    apply MemFX.cfv_clob. exact Hc. }
  pose proof (MemFX.clobber_sound segs OPS E st R R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs) model Fv Gv HS0' VB NPOS N62 HF HKR) as HS1.
  fold n0 in HS1. change (env_above E n0 Fv Gv) with E1 in HS1.
  pose proof (clobber_fields st) as (Cpc & Cff & Crv & Creg & Cfs & Cops & Cpv & Cnx). fold n0 in Cnx.

  assert (BYN : forall a, Nz <= a < Nz + 2 * L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. destruct (bytes_of_region segs _ E m kN rN a ROKN KN0 ltac:(rewrite LON', HIN'; fold Nz; alia)) as [By1 By2].
    split; [exact (OM _ By1)| exact By2]. }
  destruct (empty_region_ok (s_priv st) E1 M' kN (2 * L) KN0 ltac:(unfold two62Z; alia) ltac:(rewrite EVN1; fold Nz; alia)
              ltac:(rewrite EVN1; fold Nz; exact BYN)) as (ROKNe & HINe & LONe).
  pose proof (MemFX.st_ok_based_write segs OPS E1 (clobber st) R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m M' (seg_rom segs) model kN rN (empty_region (2 * L))
                HS1 ltac:(rewrite Creg; exact FN) KN0 WN
                ltac:(intros a Ha NI; apply (munch_frame m M' Nz L MU a Ha); rewrite EVN1, LON' in NI; unfold hiZ in NI; rewrite HIN in NI;
                      cbn [den] in NI; rewrite wbv_unsigned, L2w in NI; fold Nz in NI; clear - NI ROC; lia)
                OM (minv_of_mem_inv M' MI') ltac:(rewrite Cpv; exact ROKNe)
                ltac:(rewrite LONe, LON'; apply Z.le_refl)
                ltac:(rewrite HINe; unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned, L2w; apply Z.le_refl)) as HS2.
  rewrite <- (setregs_eq (clobber st) (IMap.add kN (empty_region (2 * L)) (s_regs (clobber st)))) in HS2.
  set (st2 := setregs (clobber st) (IMap.add kN (empty_region (2 * L)) (s_regs (clobber st)))) in *.

  assert (DDX1 : den E1 dx = den E1 (VP kN wzero)).
  { rewrite (den_reval n0 E E1 HX dx VBdx), DXV. rewrite <- EVN1. apply bv_eq. symmetry. exact (den_VP0 E1 kN wzero (weqb_refl _)). }
  assert (G10 : getr st2 X10 = dx).
  { subst st2 dx. rewrite getr_setregs, getr_clobber. reflexivity. }
  pose proof (setreg_sound segs OPS E1 st2 _ model X10 (VP kN wzero) HS2 ltac:(discriminate) ltac:(rewrite G10; exact DDX1)) as HS3.
  pose proof (repl_regs_sound kept_r5 dx (VP kN wzero) E1 _ _ model HS3 ltac:(cbn; intuition discriminate) DDX1) as HS4.
  pose proof (MemFX.setpc_sound segs OPS E1 _ R' FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None M' (seg_rom segs) model (wl ra) HS4) as HS5.
  rewrite R1.
  apply (Hk st' (or_introl eq_refl) E1 _ model HX HMP).
  set (st5 := setpc (repl_regs kept_r5 dx (VP kN wzero) (setr st2 X10 (VP kN wzero))) (wl ra)) in *.

  pose proof (repl_regs_fields kept_r5 dx (VP kN wzero) (setr st2 X10 (VP kN wzero))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
  pose proof (setr_fields st2 X10 (VP kN wzero)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
  pose proof (setregs_fields (clobber st) (IMap.add kN (empty_region (2 * L)) (s_regs (clobber st)))) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  pose proof (setpc_fields (repl_regs kept_r5 dx (VP kN wzero) (setr st2 X10 (VP kN wzero))) (wl ra)) as (P51 & P52 & P53 & P54 & P55 & P56 & P57 & P58 & P59).
  assert (F5ops : s_ops st5 = opre ++ o :: opost).
  { subst st5. rewrite P56, Q6, Y6. subst st2. rewrite Z7, Cops. exact OPSEQ. }
  assert (F5regs : s_regs st5 = IMap.add kN (empty_region (2 * L)) (s_regs st)).
  { subst st5. rewrite P54, Q4, Y4. subst st2. rewrite Z5, Creg. reflexivity. }
  assert (F5pv : s_priv st5 = s_priv st).
  { subst st5. rewrite P57, Q7, Y7. subst st2. rewrite Z8. exact Cpv. }
  assert (F5fs : s_facts st5 = fs).
  { subst st5. rewrite P55, Q5, Y5. subst st2. rewrite Z6, Cfs. reflexivity. }
  subst st'.
  change (setpc (repl_regs kept_r5 dx (VP kN wzero) (setr (setregs (clobber st) (IMap.add kN (empty_region (2 * L)) (s_regs (clobber st)))) X10 (VP kN wzero))) (wl ra)) with st5.

  set (bm' := bmem_of segs M').

  assert (FRM : forall a, 0 <= a < two64 -> in_user LB a -> ~ in_ws (heap_ws (map (wden E) ws)) a -> m (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
  { intros a Ha _ NW. symmetry. apply (munch_frame m M' Nz L MU a Ha). intros IN. apply NW. unfold in_ws, heap_ws. apply in_ivs_In.
    exists (w_iv (wden E wN)). split.
    - apply in_map. apply filter_In. split; [apply in_map; exact EXN|]. rewrite (WNd E eq_refl). reflexivity.
    - rewrite (WNd E eq_refl). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. alia. }
  pose proof (PK.mem_frame segs _ g ls LB (map (wden E) ws) m M' P O Wk FRM M) as M2.
  pose proof M2 as (TW2 & KA2 & ICB2 & CH2 & PE2).

  assert (NLB : In (Nz, 2 * L) LB).
  { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite (WNd E eq_refl) in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
    - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
    - exact IN.
    - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
  destruct (aw_blocks_ok segs IMGX AW _ LB _ m model _ HA NLB) as (Nb1 & Nb2 & Nb3 & _). cbn [fst snd] in Nb1, Nb2, Nb3.

  destruct RW' as [[_ BAd] _]. cbn [cells_bytes cbytes] in BAd. rewrite app_nil_r in BAd.
  assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
  { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite !MemFX.rb_mrd.
    destruct BAd as (_ & _ & BD). destruct BA' as (_ & _ & BS).
    pose proof (BD (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X1. pose proof (BS (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X2.
    rewrite Z2Nat.id in X1, X2 by alia. rewrite X1, X2. reflexivity. }
  assert (SAME : forall a, 0 <= a < two64 -> ~ (Nz <= a < Nz + L) -> rb segs M' a = rb segs m a).
  { intros a Ha NI. unfold rb. rewrite (munch_frame m M' Nz L MU a Ha NI). reflexivity. }

  set (VN := mkVec Nz (v_size V) (2 * v_cap V) 24).
  set (g' := PKG (k_tree g) VN (k_zone g)).
  assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V /\ v_cap VN = 2 * v_cap V /\ v_elt VN = 24 /\ v_bytes VN = 2 * L /\
                v_end VN = NT + 24 /\ v_capend VN = Nz + 2 * L).
  { subst VN. unfold v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite SZC. subst NT. repeat split; alia. }
  destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
  assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
  assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
  assert (TZB : Tz = Bz + L - 24) by alia.
  assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
  assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

  assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
  { intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }

  assert (BYNT : forall a, NT <= a < NT + 48 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply BYN. subst NT. alia. }
  assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. destruct (UB a Ha) as [U1 U2]. split; [exact (OM _ U1)| exact U2]. }

  assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
  { intros i Hi. rewrite !MemFX.rb_mrd. destruct BAd as (_ & _ & BD). destruct BA' as (_ & _ & BS).
    pose proof (BD (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X1. pose proof (BS (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X2.
    rewrite Z2Nat.id in X1, X2 by alia. rewrite X1, X2. reflexivity. }

  assert (GCINV : forall rr gi cs, gcells rr gi = Some cs -> exists gr, IMap.find gi (rg_cells rr) = Some gr /\ cs = g_cells gr).
  { intros rr gi cs H. unfold gcells in H. destruct (IMap.find gi (rg_cells rr)) as [gr|]; [|discriminate]. injection H as <-. exists gr. auto. }
  assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
  { apply keyZ_of_Z. unfold two62Z. clear - L24 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
  assert (L8E : 8 * (L / 8) = L) by (clear - L8 L24; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
  assert (L8R : 0 <= L / 8 < 2 ^ 44) by (clear - L24 L40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (OFZ : forall d, 0 <= d <= 2 -> PrimInt63.add (Uint63.of_Z (L / 8)) (Uint63.of_Z d) = Uint63.of_Z (L / 8 + d)).
  { intros d Hd. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec. rewrite wB_two63, two63_eq. clear - Hd L8R.
    rewrite (Z.mod_small (L / 8)) by lia. rewrite (Z.mod_small d) by lia. rewrite ?(Z.mod_small (L / 8 + d)) by lia. first [reflexivity | symmetry; apply Z.mod_small; lia | apply Z.mod_small; lia]. }
  assert (KEYL1 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 1) = L / 8 + 1).
  { change 1%uint63 with (Uint63.of_Z 1). rewrite (OFZ 1) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
  assert (KEYL2 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 2) = L / 8 + 2).
  { change 2%uint63 with (Uint63.of_Z 2). rewrite (OFZ 2) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
  assert (SLOT : forall E0 rr kk gi cs, IMap.find kk (s_regs st) = Some rr -> st_ok segs OPS E0 st ms model -> gcells rr gi = Some cs ->
            slot_ok segs E0 m (bv_unsigned (ev E0 kk) + 8 * keyZ gi) cs).
  { intros E0 rr kk gi cs Hf HSx Hg. destruct (GCINV rr gi cs Hg) as (gr & Fgr & ->). exact (ro_cells _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HSx kk rr Hf) gi gr Fgr). }
  pose proof (SLOT E1 rT kT 0%uint63 t0 FT HSE1 GT0) as ST0. pose proof (SLOT E1 rT kT 1%uint63 t1 FT HSE1 GT1) as ST1.
  pose proof (SLOT E1 rT kT 2%uint63 t2 FT HSE1 GT2) as ST2.
  pose proof (SLOT E1 rN kN _ e0 FN HSE1 GN0) as SN0. pose proof (SLOT E1 rN kN _ e1 FN HSE1 GN1) as SN1. pose proof (SLOT E1 rN kN _ e2 FN HSE1 GN2) as SN2.
  rewrite EVT1 in ST0, ST1, ST2. fold Tz in ST0, ST1, ST2. change (keyZ 0%uint63) with 0 in ST0. change (keyZ 1%uint63) with 1 in ST1. change (keyZ 2%uint63) with 2 in ST2.
  rewrite EVN1 in SN0, SN1, SN2. fold Nz in SN0, SN1, SN2. rewrite KEYL in SN0. rewrite KEYL1 in SN1. rewrite KEYL2 in SN2.
  assert (SHIFT_T : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 m (Tz + 8 * j) cs -> slot_ok segs E1 M' (NT + 8 * j) cs).
  { intros j cs Hj S0. apply (slot_ok_shift E1 m M' (Tz + 8 * j) (NT + 8 * j) _ S0). intros i Hi. subst NT. rewrite TZB.
    replace (Nz + L - 24 + 8 * j + i) with (Nz + (L - 24 + 8 * j + i)) by alia. rewrite (RBC (L - 24 + 8 * j + i)) by alia.
    replace (Bz + (L - 24 + 8 * j + i)) with (Bz + L - 24 + 8 * j + i) by alia. apply SAME; [alia|]. clear - SEP Hi Hj L24 RNr Bb1. lia. }
  assert (SHIFT_N : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 m (Nz + 8 * (L / 8 + j)) cs -> slot_ok segs E1 M' (NT + 24 + 8 * j) cs).
  { intros j cs Hj S0. apply (slot_ok_shift E1 m M' (Nz + 8 * (L / 8 + j)) (NT + 24 + 8 * j) _ S0). intros i Hi. subst NT.
    replace (Nz + L - 24 + 24 + 8 * j + i) with (Nz + 8 * (L / 8 + j) + i) by alia. apply SAME; alia. }
  assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region48 t0 t1 t2 e0 e1 e2)).
  { apply (region48_ok (s_priv st) E1 M' nT _ _ _ _ _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| | | | | |].
    - replace NT with (NT + 8 * 0) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 0) with Tz by alia. rewrite Z.mul_0_r, Z.add_0_r in ST0. exact ST0.
    - replace (NT + 8) with (NT + 8 * 1) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 1) with (Tz + 8) by alia. exact ST1.
    - replace (NT + 16) with (NT + 8 * 2) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 2) with (Tz + 16) by alia. exact ST2.
    - replace (NT + 24) with (NT + 24 + 8 * 0) by alia. apply SHIFT_N; [lia|]. replace (L / 8 + 0) with (L / 8) by alia. exact SN0.
    - replace (NT + 32) with (NT + 24 + 8 * 1) by alia. apply SHIFT_N; [lia|]. exact SN1.
    - replace (NT + 40) with (NT + 24 + 8 * 2) by alia. apply SHIFT_N; [lia|]. exact SN2. }
  destruct (empty_region_ok (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
              ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).

  assert (WD1 : forall w, In w ws -> wden E1 w = wden E w).
  { intros [[w1 w2] w3] Hw. destruct (INW _ Hw) as (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3. unfold wden. rewrite (DR1 _ I1), (DR1 _ I2), (DR1 _ I3). reflexivity. }
  assert (MWD1 : map (wden E1) ws = map (wden E) ws) by (apply map_ext_in; exact WD1).
  set (wT := top_win kT 24%uint63 ETOPk) in *.
  assert (WTd : wden E wT = Win Tz 24 6) by (subst wT; rewrite top_win_den; reflexivity).

  assert (HA' : aw_holds segs IMGX AW (den E aw) LB (map (wden E) ws) M' model).
  { refine (proj1 (aw_frame segs IMGX AW _ LB _ m M' model HA _ (fun a _ Hm => OM _ Hm))).
    intros a Ha Hd. destruct (aw_dep_ok segs IMGX AW _ LB _ m model a HA Hd) as (_ & NU & _).
    symmetry. apply (munch_frame m M' Nz L MU a Ha). intros IN. apply NU. unfold in_user. apply in_ivs_In. exists (Nz, 2 * L). split; [exact NLB|].
    unfold in_iv. cbn [fst snd]. alia. }

  assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E) ws) a /\ ~ in_ivs IMGX a).
  { intros a Ha.
    assert (SF : PK.safe g (map (wden E) ws) a).
    { intros w Hw (K6 & NE0 & E1' & E2' & E3') Hin. fold V in E1', E2', E3'. rewrite VEN, SZC in E2'. unfold ELEM_SIZE in E2'.
      unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. clear - Ha Hin E2' TZB LCAP. lia. }
    destruct (pk_owned_byte_props segs IMGX AW _ LB m model g _ _ a HA WF O Wk VOWN ltac:(unfold in_iv; cbn [fst snd]; alia) SF) as (_ & NI & NW & _).
    split; [exact NW| exact NI]. }

  set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
  set (wNT := top_win nT 48%uint63 ETOPk).
  set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
  set (b' := VP kN wzero). set (e' := VP nT (wlit 24%uint63)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
  set (ca' := [root; rootT; n1; P1; zh; c0; b'; e'; cap'; tptr; trest; tmap; tkey; cf; fT; fN; fP]).
  assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
  { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
    apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
    split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
  assert (LENws' : Z.of_nat (length ws') < two63).
  { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
  assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
  { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
  assert (WNTd : wden E1 wNT = Win NT 48 6) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
  assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
  assert (De' : bv_unsigned (den E1 e') = NT + 24).
  { subst e'. rewrite (den_VP_nowrap E1 nT (wlit 24%uint63)); rewrite ?wlit_ok, NTV; change (to_Z 24%uint63) with 24; [reflexivity| subst NT; alia]. }
  assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
  { subst cap'. rewrite (den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }

  assert (DRC : forall v, In v [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> den E1 v = den E v)
    by (intros v Hv; apply DR1; apply INCA; exact Hv).

  assert (LSNE : ls <> []) by (intros X; rewrite X in SZ; cbn in SZ; alia).
  assert (RLEN : Z.of_nat (length (removelast ls)) = v_size V - 1).
  { rewrite (removelast_length _ LSNE). rewrite Nat2Z.inj_sub by (destruct ls; [exfalso; exact (LSNE eq_refl)| cbn; lia]). rewrite <- SZ. reflexivity. }
  apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ model o HS5 opre opost F5ops OID OPOTH [kN; kT]
           [(nT, region48 t0 t1 t2 e0 e1 e2); (kB, empty_region L)] (mk_args 3%uint63 aw ws' ca') _ (PrimInt63.add n0 16)).
  -   intros k [<-|[<-|[]]]; rewrite F5regs.
    + split; [exact KN0|]. exists (empty_region (2 * L)). rewrite IMap.find_add_same by exact Pbst0. split; reflexivity.
    + split; [exact KT0|]. exists rT. rewrite IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)]. split; [exact FT| exact WT].
  -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
  -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
  -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
  -   intros k rr a [H1|[H1|[]]] IR; injection H1 as <- <-.
    + right. exists kN, (empty_region (2 * L)). split; [left; reflexivity|]. rewrite F5regs, IMap.find_add_same by exact Pbst0. split; [reflexivity|].
      unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LONe, HINe. fold Nz.
      change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
      change (to_Z 48%uint63) with 48 in IR. subst NT. alia.
    + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
      destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
      * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))). rewrite MWD1.
        destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
      * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs, IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)].
        split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. alia.
  -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
      unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0;
      unfold hiZ; cbn [region48 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 48%uint63) with 48; intros [J1 J2].
    + apply (DISJ_BN a); subst NT; alia.
    + apply (DISJ_BN a); subst NT; alia.
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
    split; [apply mk_args_sound; exact LENws'|].
    assert (AWE : den E1 aw = den E aw) by (apply DR1; rewrite ARGS; right; left; reflexivity). rewrite AWE.
    split.
    { pose proof HA' as HA2. rewrite <- MWD1 in HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
      - intros x Hx. destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [left; exact Hx'| right| right; apply UOK.kind_new_sub; reflexivity].

        rewrite WB'd. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|].
        intros _ g0 Hg KG a Ha Hb. apply in_map_iff in Hg as (y & <- & Hy).
        destruct (KEPTW y Hy) as [(Hy' & _ & _)|[->| ->]].
        + rewrite (WD1 y Hy') in KG, Ha.
          destruct (proj1 (Forall_forall _ _) Wk (wden E y) (in_map _ _ _ Hy') ltac:(unfold K_STACK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
          * exact (DJ (Bz, L) VOWN a Ha Hb).
          * destruct ET as (K6 & _). unfold PK.K_ETOP, K_GHOST in *. lia.
        + rewrite WB'd in KG. cbn [w_kind] in KG. unfold K_GHOST, HeapOp.K_BLOCK in KG. lia.
        + rewrite WNTd in KG. cbn [w_kind] in KG. unfold K_GHOST in KG. lia.
      - intros x Hx. destruct (UOK.filter_old ws [wB'; wNT] (fun w => negb (win3_eqb w wN || win3_eqb w wT)) x Hx) as [H1|F]; [left; exact H1| right].
        apply negb_false_iff in F. apply orb_prop in F as [F|F]; apply win3_eqb_eq in F; subst x.
        +
          rewrite (WNd E1 EVN1). split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
          apply (block_keep_evidence LB _ Nz (2 * L) _ (wden E1 wNT) NLB).
          * cbn [w_lo]. alia.
          * apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
          * rewrite WNTd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
          * rewrite WNTd. cbn [w_len]. clear. lia.
          * rewrite WNTd. cbn [w_lo]. subst NT. alia.
        +
          rewrite (WD1 wT EXT), WTd. split; [unfold aw_tied, K_STACK, K_GHOST; cbn [w_kind]; clear; lia|]. intros _ _.
          apply (block_keep_evidence LB _ Bz L _ (wden E1 wB') (proj1 O _ VOWN)).
          * cbn [w_lo]. alia.
          * apply in_map. subst ws'. apply in_app_iff. right. left. reflexivity.
          * rewrite WB'd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
          * rewrite WB'd. cbn [w_len]. alia.
          * rewrite WB'd. cbn [w_lo]. alia. }
    split.
    +
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
      * rewrite (WD1 x Hx'). exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
      * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
        right; left. split; [reflexivity|]. unfold w_iv. cbn [w_lo w_len]. rewrite LCAP, <- VBY. exact VLB.
      * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
        right; right. split; [unfold HeapOp.K_SUB; alia|].
        exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L24. lia.
    +
      apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
      assert (VNV : vec_valid VN).
      { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, SZC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }

      assert (RDJ2 : forall b, In b (owned g) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
      { intros b0 Hb0. pose proof (PK.owned_pos g ls P b0 Hb0) as PO. unfold rdisj.
        destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
        destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
        exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
        - apply (DISJN b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
        - apply (DISJN b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }
      assert (OWNo : owned g = (Bz, L) :: map chunk_block (z_chunks (k_zone g))).
      { unfold owned, evec_blocks. fold V. rewrite Leb. replace (Bz =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite <- Leb; exact VV3). rewrite VBY, <- LCAP. reflexivity. }
      assert (OWN' : owned g' = (Nz, 2 * L) :: map chunk_block (z_chunks (k_zone g))).
      { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone]. rewrite VN1, VN5. replace (Nz =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ0). reflexivity. }
      exists g', ls. split; [| split; [| split; [| split]]].
      *
        unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
        rewrite ?(DRC root), ?(DRC rootT), ?(DRC n1), ?(DRC P1), ?(DRC zh), ?(DRC c0), ?(DRC tptr), ?(DRC trest), ?(DRC tmap), ?(DRC tkey),
                ?(DRC cf), ?(DRC fT), ?(DRC fN), ?(DRC fP) by inlist.
        rewrite Db', De', Dcap', VN1, VN6, VN7.
        split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact LTOP| exact LCF].
      *
        unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone]. rewrite VN1, VN2, VN3, VN4, VN7.
        split; [exact LV|]. split; [reflexivity|]. split; [exact SZ|]. split; [right; split; [exact VNV| split; [alia| split; [apply pow2_b_double; [exact (proj1 CPOW)| alia]| clear - CAP2; alia]]]|]. split; [alia| exact ZV].
      *
        unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF, RDJ2. split.
        -- intros b0 [<-|Hb0]; [exact NLB| apply OL; right; exact Hb0].
        -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
           apply Forall_forall. intros cb Hcb. apply (proj1 (RDJ2 _ ltac:(right; exact Hcb))).
      *
        unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx). rewrite OWN'.
        destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
        -- rewrite (WD1 x Hx') in NS |- *.
           destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]];
             [| exfalso; pose proof (only_kind_sound E 6 _ ws OKT x Hx' (proj1 ET)) as X; injection X as <-; exact (NxT eq_refl)].
           left. split; [exact KDx|]. intros b0 [<-|Hb0] a Ha Hb.
           ++ unfold in_iv in Hb. cbn [fst snd] in Hb.
              exact (new_block_apart E fs (s_regs st) _ LB m model kN rN (2 * L) ws wN wT x Pfacts0 Pdisj0 FN KN0 LON HIN' ltac:(alia) WN HA NLB WF KL OBK NOA SWO EXN (WNd E eq_refl)
                       Hx' NxN NxT NS a Ha Hb).
           ++ exact (DJ b0 ltac:(rewrite OWNo; right; exact Hb0) a Ha Hb).
        --
           left. rewrite WB'd. split; [left; reflexivity|]. intros b0 [<-|Hb0] a Ha Hb; unfold in_iv, w_iv in Ha; cbn [w_lo w_len fst snd] in Ha; unfold in_iv in Hb; cbn [fst snd] in Hb.
           ++ exact (DISJ_BN a Hb Ha).
           ++ destruct O as [OL OF]. rewrite OWNo in OF. destruct (FOP_cons _ _ _ OF) as [F1 _].
              pose proof (proj1 (Forall_forall _ _) F1 b0 Hb0) as D. unfold rdisj in D. cbn [fst snd] in D. clear - D Ha Hb. lia.
        --
           right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
           unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
           split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia.
      *
        split.
        2: { split; [destruct GH as [SE EP]; split|].
             3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| cbn [a_cf]; rewrite (DRC cf ltac:(do 13 right; left; reflexivity)); reflexivity].
                  intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                  destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [rewrite (WD1 x Hx'); apply in_map; exact Hx'| |].
                  - exfalso. apply NV. apply pku_val_none_kind. rewrite WB'd. cbn [w_kind]. unfold HeapOp.K_BLOCK. clear. lia.
                  - exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
             - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
               destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [rewrite (WD1 x Hx'); apply in_map; exact Hx'| |].
               + exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. clear - K9. lia.
               + exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
             - intros _. exists (wden E1 wNT). split.
               + apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
               + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
                 split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia. }
        unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone a_root]. rewrite VN1. fold bm'.
        split; [exact TW2|]. split; [exact KA2|]. split; [cbn [a_root] in ICB2; rewrite (DRC root) by inlist; exact ICB2|]. split; [exact CH2|].
        intros _. pose proof (PE2 ltac:(fold V; rewrite Leb; rewrite <- Leb; exact VV3)) as X. fold V in X. rewrite Leb in X.
        apply (pelems_at_shift _ bm' bm' Bz Nz); [| exact X].
        intros i Hi. apply COPY. rewrite length_map, RLEN in Hi. unfold ELEM_SIZE in Hi. clear - Hi SZC LCAP CPOS. lia.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
    split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IW|NIW].
      * right. apply (proj1 (in_ws_map_iff E ws a)) in IW as (w & Hw & Hin).
        destruct (win3_eqb w wN) eqn:QN; [| destruct (win3_eqb w wT) eqn:QT].
        -- apply win3_eqb_eq in QN. subst w. exists kN, (empty_region (2 * L)). split; [left; reflexivity|]. rewrite F5regs, IMap.find_add_same by exact Pbst0.
           split; [reflexivity|]. rewrite (WNd E eq_refl) in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. unfold inR. rewrite EVN1, LONe, HINe. fold Nz. clear - Hin. lia.
        -- apply win3_eqb_eq in QT. subst w. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs, IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)].
           split; [exact FT|]. rewrite WTd in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin.
           unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. clear - Hin. lia.
        -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
           rewrite (WD1 w Hw). exact Hin.
      * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))). rewrite MWD1. auto.
    + intros k rr [H1|[H1|[]]] IR; injection H1 as <- <-.
      * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite NTV in IR. change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR.
        rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 48%uint63) with 48 in IR. alia.
      * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
  -
    assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
    assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 24))))) = Nz + (L - 24)).
    { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
    constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
    constructor.
    { cbn [fact_holds]. rewrite Db', DnT0. subst NT. alia. }
    constructor.
    { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
    apply Forall_app. split.
    + apply (top_facts_sound E1 fs b' nT Pfacts1); rewrite Db', NTV; [subst NT; alia|].
      subst NT. replace (Nz + L - 24 - Nz) with (L - 24) by alia. apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 3). lia.
    + apply (anchor_facts_sound E1 fs kN (L - 24) (L - 24) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
Qed.

Theorem pkregrow_sound : contract_sound segs OPS MP PB pkregrow_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [pkregrow_contract c_apply c_pc] in HAP, Hpc.
  unfold pkregrow_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct (PkStack.parse_ca ca) as [c|] eqn:PCA; [|discriminate].
  destruct (PkStack.c_eb c) as [b0|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  - destruct (weqb b0 wzero) eqn:B00; [|discriminate].
    exact (regrow0_sound st r aw ws ca c sts K E ms model Hpc TO CP PCA (ex_intro _ b0 (conj EB B00)) HAP HS0 HMP HPB Hk).
  - destruct (PkStack.c_ee c) as [|kT oe| | | | | | | | |] eqn:EE; try discriminate.
    destruct (PkStack.c_ecap c) as [|kB' oc| | | | | | | | |] eqn:EC; try discriminate.
    destruct (PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63)) eqn:Q; [|discriminate].
    apply andb_prop in Q as [Q OE]. apply andb_prop in Q as [KBB OB]. apply Uint63.eqb_correct in KBB. subst kB'.
    apply (proj1 (weqb_ok _ _)) in OB. apply (proj1 (weqb_ok _ _)) in OE. subst ob oe.
    exact (regrow1_sound st r aw ws ca c kB kT oc sts K E ms model Hpc TO CP PCA EB EE EC HAP HS0 HMP HPB Hk).
Qed.

End Sound.
End WithPc.
End PkRegrow.
