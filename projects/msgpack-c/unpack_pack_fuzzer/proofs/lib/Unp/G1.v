(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G1.

Definition g1_hdr (R : IMap.t region) (ws : list (sv * sv * sv)) (D0 : bool) (root slot tD restD : sv)
           (kA kVT kC kZ k1 : int) (rC : region) : option (sv * sv * sv * int) :=
  if D0 then
    match root with
    | VP kR oR =>
        match okey oR, IMap.find kR R with
        | Some key, Some rR =>
            if negb (PrimInt63.eqb kR 0%uint63) && negb (PrimInt63.eqb kR kA) && negb (PrimInt63.eqb kR kVT)
               && negb (PrimInt63.eqb kR kC) && negb (PrimInt63.eqb kR kZ) && only_kind 4 None ws && Z.ltb (keyZ key + 24) two62Z
            then match cell_at rR (keyZ key) 4%uint63, cell_at rR (keyZ key + 8) 4%uint63, cell_at rR (keyZ key + 16) 8%uint63 with
                 | Some a, Some b, Some c => Some (a, b, c, 0%uint63)
                 | _, _, _ => None
                 end
            else None
        | _, _ => None
        end
    | _ => None
    end
  else
    match slot with
    | VP kS os =>
        if weqb os wzero && negb (PrimInt63.eqb kS 0%uint63) && negb (PrimInt63.eqb kS kA) && negb (PrimInt63.eqb kS kVT)
           && negb (PrimInt63.eqb kS kC) && negb (PrimInt63.eqb kS kZ) && negb (PrimInt63.eqb kS k1)
           && only_kind 4 (Some (slot_win kS)) ws && existsb (win3_eqb (slot_win kS)) ws
        then match IMap.find kS R with
             | Some rS =>
                 if PrimInt63.eqb (rg_lo rS) 0%uint63 && sv_eqb (rg_hi rS) (VL (wlit 24%uint63)) && rg_w rS then
                 match cell_at rS 0 4%uint63, cell_at rS 8 4%uint63, cell_at rS 16 8%uint63,
                       cell_at rC 0 4%uint63, cell_at rC 4 4%uint63 with
                 | Some a, Some b, Some c, Some tc0, Some rc0 =>
                     if same32 tc0 tD && same32 rc0 restD then Some (a, b, c, kS) else None
                 | _, _, _, _, _ => None
                 end
                 else None
             | None => None
             end
        else None
    | _ => None
    end.

Definition g1_count (fs : list fact) (nH nC : sv) : option sv :=
  match find_first (GFast.GFast.bounded_count_f fs) (nH :: nC :: zx_forms (core32 nH)) with
  | Some nsv => if same32 nsv nH then Some nsv else None
  | None => None
  end.

Fixpoint exists_lazy {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: t => if f a then true else exists_lazy f t end.
Lemma exists_lazy_eq : forall A (f : A -> bool) l, exists_lazy f l = existsb f l.
Proof. induction l as [|a t IH]; cbn [exists_lazy existsb]; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.

Definition size_mul (SZ : sv) (per : Z) (c : sv) : bool :=
  match SZ with
  | VMd M_MUL c' (VL k) => sv_eqb c' c && weqb k (wlit (if per =? 1 then 24%uint63 else 48%uint63))
  | _ => false
  end.

Definition g1_size (fs : list fact) (SZ : sv) (per : Z) (nsv nH : sv) : bool :=
  let cands := nsv :: zx_forms (core32 nH) in
  if exists_lazy (size_mul SZ per) cands then true
  else exists_lazy (fun c => match decide_eq_t fs SZ (size_sv per c) with Some true => true | _ => false end) cands.

Lemma size_mul_den : forall E SZ per c, (per = 1 \/ per = 2) -> size_mul SZ per c = true -> bv_unsigned (den E c) <= 1000 ->
  bv_unsigned (den E SZ) = OBJ_SIZE * per * bv_unsigned (den E c).
Proof.
  intros E SZ per c Hp H Hc. unfold size_mul in H.
  destruct SZ; try discriminate H.
  repeat match type of H with
  | (match ?x with _ => _ end) = true => destruct x; try discriminate H
  end.
  apply andb_prop in H as [H1 H2]. apply sv_eqb_eq in H1. apply (proj1 (weqb_ok _ _)) in H2. subst.
  pose proof (bv_unsigned_in_range _ (den E c)) as R. rewrite bv_modulus_64 in R.
  match goal with |- bv_unsigned (den E (VMd M_MUL ?a (VL ?k))) = _ => change (den E (VMd M_MUL a (VL k))) with (bv_mul (den E a) (den E (VL k))) end.
  rewrite bv_mul_unsigned, den_VL, wlit_ok. unfold bv_wrap. rewrite bv_modulus_64. unfold OBJ_SIZE.
  destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - change (to_Z 24%uint63) with 24. rewrite Z.mod_small by (unfold two64; lia). lia.
  - change (to_Z 48%uint63) with 48. rewrite Z.mod_small by (unfold two64; lia). lia.
Qed.

Definition depth_test (fs : list fact) (d : sv) : bool :=
  match decide_ltu fs d (VL (wlit 1001%uint63)) with Some true => true | _ => false end.

Definition depth_test_q (fs : list fact) (d : sv) : bool :=
  match decide_ltu (rel_facts (sv_vs d []) fs) d (VL (wlit 1001%uint63)) with Some true => true | _ => false end.
Definition depth_cands (base vb : sv) : list sv :=
  [sv_alu ALU_SRA (sv_alu ALU_SUB base vb) (VL (wlit 3%uint63)); sv_alu ALU_SRL (sv_alu ALU_SUB base vb) (VL (wlit 3%uint63))].

Definition depth_bases (fs : list fact) (ve : sv) : list sv :=
  match ve with VP k o => map (fun X => sv_alu ALU_ADD X (VL o)) (anchor_defs fs k) | _ => [ve] end.
Definition depth_all (fs : list fact) (ve vb : sv) : list sv := flat_map (fun base => depth_cands base vb) (depth_bases fs ve).
Definition g1_depth (fs : list fact) (ve vb : sv) : bool :=
  let cands := depth_all fs ve vb in
  if exists_lazy (depth_test_q fs) cands then true else exists_lazy (depth_test fs) cands.

Lemma g1_depth_unfold : forall fs ve vb,
  g1_depth fs ve vb = if exists_lazy (depth_test_q fs) (depth_all fs ve vb) then true else exists_lazy (depth_test fs) (depth_all fs ve vb).
Proof. reflexivity. Qed.

Lemma two_pass_inv : forall E fs (L : list sv), facts_hold E fs ->
  (if exists_lazy (depth_test_q fs) L then true else exists_lazy (depth_test fs) L) = true ->
  exists d, In d L /\ bv_ltu (den E d) (den E (VL (wlit 1001%uint63))) = true.
Proof.
  intros E fs L FH H. destruct (exists_lazy (depth_test_q fs) L) eqn:Q1.
  - rewrite exists_lazy_eq in Q1. apply existsb_exists in Q1 as (d & Hd & Q). exists d. split; [exact Hd|].
    unfold depth_test_q in Q. destruct (decide_ltu (rel_facts (sv_vs d []) fs) d (VL (wlit 1001%uint63))) as [[|]|] eqn:DL; try discriminate.
    exact (decide_ltu_sound E _ (rel_facts_hold E _ fs FH) _ _ _ DL).
  - rewrite exists_lazy_eq in H. apply existsb_exists in H as (d & Hd & Q). exists d. split; [exact Hd|].
    unfold depth_test in Q. destruct (decide_ltu fs d (VL (wlit 1001%uint63))) as [[|]|] eqn:DL; try discriminate.
    exact (decide_ltu_sound E fs FH _ _ _ DL).
Qed.

Lemma depth_all_in : forall fs k o vb d, In d (depth_all fs (VP k o) vb) -> exists X, In X (anchor_defs fs k) /\
  (d = sv_alu ALU_SRA (sv_alu ALU_SUB (sv_alu ALU_ADD X (VL o)) vb) (VL (wlit 3%uint63)) \/
   d = sv_alu ALU_SRL (sv_alu ALU_SUB (sv_alu ALU_ADD X (VL o)) vb) (VL (wlit 3%uint63))).
Proof.
  intros fs k o vb d Hd. unfold depth_all in Hd. apply in_flat_map in Hd as (base & Hbase & Hd).
  unfold depth_bases in Hbase. apply in_map_iff in Hbase as (X & <- & HXa). exists X. split; [exact HXa|].
  unfold depth_cands in Hd. destruct Hd as [<-|[<-|[]]]; [left| right]; reflexivity.
Qed.

Lemma g1_depth_inv : forall E fs k o vb, facts_hold E fs -> g1_depth fs (VP k o) vb = true ->
  exists X d, In X (anchor_defs fs k) /\
    (d = sv_alu ALU_SRA (sv_alu ALU_SUB (sv_alu ALU_ADD X (VL o)) vb) (VL (wlit 3%uint63)) \/
     d = sv_alu ALU_SRL (sv_alu ALU_SUB (sv_alu ALU_ADD X (VL o)) vb) (VL (wlit 3%uint63))) /\
    bv_ltu (den E d) (den E (VL (wlit 1001%uint63))) = true.
Proof.
  intros E fs k o vb FH H. rewrite g1_depth_unfold in H.
  destruct (two_pass_inv E fs _ FH H) as (d & Hd & LT). destruct (depth_all_in _ _ _ _ _ Hd) as (X & HXa & Hform).
  exists X, d. auto.
Qed.

Definition g1_zone (fs : list fact) (kA : int) (SZ zptr zfree zpS zfS : sv) : bool :=
  existsb (fun X => msame zpS (VAlu ALU_ADD X SZ)
                    && msame (VAlu ALU_ADD zpS zfS) (VAlu ALU_ADD (if sv_eqb zptr (VP kA wzero) then X else zptr) zfree))
          (anchor_defs fs kA).

Definition same_end (fs : list fact) (v t : sv) : bool :=
  sv_eqb v t
  || match v, t with
     | VP k o, VP kt ot => fact_lookup fs (is_FEq (VP kt wzero) (VP k (wsub o ot)))
     | _, _ => false
     end.

Lemma same_end_sound : forall E fs v t, facts_hold E fs -> same_end fs v t = true -> den E v = den E t.
Proof.
  intros E fs v t FH H. unfold same_end in H. apply orb_prop in H as [H|H].
  - apply sv_eqb_eq in H. subst v. reflexivity.
  - destruct v as [|k o| | | | | | | | |]; try discriminate. destruct t as [|kt ot| | | | | | | | |]; try discriminate.
    pose proof (proj2 (syntactic_eq_sound E fs FH (VP kt wzero) (VP k (wsub o ot))) H) as Hf. cbn [den] in Hf.
    apply bv_eq. apply (f_equal bv_unsigned) in Hf. rewrite !bv_add_unsigned, !wbv_unsigned in Hf. rewrite wsub_ok, wzero_ok in Hf.
    unfold bv_wrap in Hf. rewrite bv_modulus_64 in Hf. rewrite Z.add_0_r in Hf.
    pose proof (bv_unsigned_in_range _ (ev E kt)) as RK. rewrite bv_modulus_64 in RK. rewrite (Z.mod_small _ _ RK) in Hf.
    cbn [den]. rewrite !bv_add_unsigned, !wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. rewrite Hf.
    rewrite Zplus_mod_idemp_l.
    replace (bv_unsigned (ev E k) + (w2Z o - w2Z ot) mod two64 + w2Z ot) with ((bv_unsigned (ev E k) + w2Z ot) + (w2Z o - w2Z ot) mod two64) by lia.
    rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Section WithPc.
Variable PUSH_PC : int.

Definition g1_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
          let D0 := sv_eqb cb ce in
          match find_first is_carve ws, ve, ce, zh, root with
          | Some ((VP kA _, SZ, _) as wA), VP kVT ove, VP kC oc, VP kZ oz, VP k1 oR =>
              let wV := top_win kVT 16%uint63 3%uint63 in
              let ocl := wl oc in
              let wC := top_win kC (PrimInt63.add ocl 8%uint63) 2%uint63 in
              let wZ := top_win kZ 56%uint63 1%uint63 in

              if st_vars_below n0 st && PrimInt63.ltb 0%uint63 n0 && PrimInt63.ltb n0 (PrimInt63.sub bit62i 8%uint63)
                 && Z.ltb (Z.of_nat (length ws)) 4000
                 && weqb ove (wlit 8%uint63) && weqb oz wzero && negb (wt oc) && (if D0 then PrimInt63.eqb ocl 0%uint63 else PrimInt63.eqb ocl 8%uint63)
                 && negb (PrimInt63.eqb kVT 0%uint63) && negb (PrimInt63.eqb kC 0%uint63) && negb (PrimInt63.eqb kZ 0%uint63)
                 && negb (PrimInt63.eqb kA kVT) && negb (PrimInt63.eqb kA kC) && negb (PrimInt63.eqb kA kZ)
                 && negb (PrimInt63.eqb kVT kC) && negb (PrimInt63.eqb kVT kZ) && negb (PrimInt63.eqb kC kZ)
                 && negb (PrimInt63.eqb k1 0%uint63) && negb (PrimInt63.eqb k1 kA) && negb (PrimInt63.eqb k1 kVT)
                 && negb (PrimInt63.eqb k1 kC) && negb (PrimInt63.eqb k1 kZ)
                 && only_kind 5 (Some wA) ws && only_kind 3 (Some wV) ws && only_kind 2 (Some wC) ws
                 && existsb (win3_eqb wV) ws && existsb (win3_eqb wC) ws && existsb (win3_eqb wZ) ws
                 && (D0 || match decide_ltu_t fs cb ce with Some true => true | _ => false end)
                 && PrimInt63.leb 3%uint63 (find_align fs kA)
                 && implied_t fs (FULe zptr (VP kA wzero))
                 && implied_t fs (FULe (VAlu ALU_ADD (VP kA wzero) SZ) (VAlu ALU_ADD zptr zfree))
                 && g1_depth fs ve vb
              then
              match IMap.find kA R, IMap.find kVT R, IMap.find kC R, IMap.find kZ R, IMap.find k1 R with
              | Some rA, Some rV, Some rC, Some rZ, Some r1 =>
                  if rg_w r1 && PrimInt63.eqb (rg_lo rA) 0%uint63 && sv_eqb (rg_hi rA) SZ && rg_w rA && no_cells rA
                     && match rg_bg rA with BGNone => true | _ => false end
                     && PrimInt63.eqb (rg_lo rV) 0%uint63 && sv_eqb (rg_hi rV) (VL (wlit 16%uint63)) && rg_w rV
                     && PrimInt63.eqb (rg_lo rC) 0%uint63 && sv_eqb (rg_hi rC) (VL (wlit (PrimInt63.add ocl 8%uint63))) && rg_w rC
                     && PrimInt63.eqb (rg_lo rZ) 0%uint63 && sv_eqb (rg_hi rZ) (VL (wlit 56%uint63)) && rg_w rZ
                  then
                  match cell_at rV 0 8%uint63, cell_at rV 8 8%uint63,
                        cell_at rC (to_Z ocl) 4%uint63, cell_at rC (to_Z ocl + 4) 4%uint63,
                        gran8 rZ 1%uint63, gran8 rZ 2%uint63 with
                  | Some v0, Some v8, Some tsv, Some nC, Some (d1, zfS), Some (d2, zpS) =>
                      match lit tsv, g1_hdr R ws D0 root slot tD restD kA kVT kC kZ k1 rC with
                      | Some ti, Some (tyH, nH, pH, kS) =>
                          let t := to_Z ti in
                          match lit tyH, g1_count fs nH nC with
                          | Some tyi, Some nsv =>
                              let per := if t =? 0 then 1 else 2 in
                              if ((t =? 0) || (t =? 1)) && sv_eqb v8 (VP kA wzero) && sv_eqb v0 (if D0 then root else slot)
                                 && (to_Z tyi =? 7 + t) && sv_eqb pH (VP kA wzero) && same32 nH nC
                                 && g1_size fs SZ per nsv nH && g1_zone fs kA SZ zptr zfree zpS zfS
                              then
                                let nZP := n0 in let nZF := PrimInt63.add n0 1%uint63 in let nV := PrimInt63.add n0 2%uint63 in
                                let nCT := PrimInt63.add n0 3%uint63 in
                                let kC' := if D0 then kC else nCT in
                                let rZ' := set_cell8 (set_cell8 rZ 2%uint63 d2 (VP nZP wzero)) 1%uint63 d1 (VP nZF wzero) in
                                let rV' := region8 [Cell 0%uint63 8%uint63 (VP kA wzero)] in

                                let rC' := region8 [Cell 0%uint63 4%uint63 tsv; Cell 4%uint63 4%uint63 nsv] in
                                let KS := [kA; kVT; kZ; kC] ++ (if D0 then [] else [kS]) in
                                let NR := [(kA, region24); (nV, rV'); (kZ, rZ'); (kC', rC')] in
                                let dead (w : sv * sv * sv) := win3_eqb w wA || win3_eqb w wV || win3_eqb w wC || (negb D0 && win3_eqb w (slot_win kS)) in
                                let ws' := List.filter (fun w => negb (dead w)) ws ++ [top_win kC' 8%uint63 2%uint63; top_win nV 8%uint63 3%uint63; slot_win kA] in
                                let ca' := [root; cb; VP kC' (wlit 8%uint63); ccap; vb; VP nV (wlit 8%uint63); vcap; VP nZP wzero; VP nZF wzero; c0;
                                            VP kA wzero; tsv; nsv; (if D0 then tyH else rootT); (if D0 then sv_ext_c false 0%uint63 4%uint63 nH else n1); (if D0 then VP kA wzero else P1); VP kZ oz] in
                                let nf := [FEq (VP nV wzero) (VP kVT (wlit 8%uint63)); FULt cb (VP kC' (wlit 8%uint63)); FAlign nZP 3%uint63;
                                           FULe (VP kC' (wlit 8%uint63)) ccap; FULe (VP nV (wlit 8%uint63)) vcap]
                                          ++ (if D0 then [] else FEq (VP nCT wzero) (VP kC (wlit 8%uint63)) :: top_facts fs cb nCT)
                                          ++ top_facts fs vb nV ++ zp_facts fs kA nZP ++ zf_facts fs zfree nZF in
                                let f (v : sv) := if same_end fs v (VP kC (wadd oc (wlit 8%uint63))) then VP kC' (wlit 8%uint63)
                                                  else if same_end fs v (VP kVT (wlit 16%uint63)) then VP nV (wlit 8%uint63) else v in

                                match GPot.GPot.pot_scan_c fs aw ws with
                                | Some sc =>
                                if GPot.GPot.pot_pre fs aw sc then
                                let nP := PrimInt63.add n0 4%uint63 in
                                let st1 := surg st KS NR (mk_args 1%uint63 aw (GPot.GPot.pot_sym sc nP ws') ca')
                                                (GPot.GPot.pot_facts_push fs sc nP SZ ++ nf) (GPot.GPot.pot_next sc (PrimInt63.add n0 4%uint63)) in
                                Some [setregs st1 (IMap.add k1 (subst_cells f r1) (s_regs st1))]
                                else None
                                | None => None
                                end
                              else None
                          | _, _ => None
                          end
                      | _, _ => None
                      end
                  | _, _, _, _, _, _ => None
                  end
                  else None
              | _, _, _, _, _ => None
              end
              else None
          | _, _, _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g1_contract : contract := Contract PUSH_PC g1_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

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

Definition hide (P : Prop) : Prop := P.

Lemma den_VAlu : forall E op a b, den E (VAlu op a b) = alu64 op (den E a) (den E b).
Proof. reflexivity. Qed.

Lemma lit_val : forall E v i, lit v = Some i -> bv_unsigned (den E v) = to_Z i.
Proof. intros. apply lit_sound. assumption. Qed.

Ltac is_arith T :=
  lazymatch T with
  | hide _ => fail
  | (@eq Z _ _) => idtac | (not (@eq Z _ _)) => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | (_ /\ _) => idtac | (_ \/ _) => idtac
  | _ => fail
  end.
Ltac clear_nonarith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then fail else clear H
         end.

Ltac revert_arith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then revert H else fail
         end.
Ltac alia := revert_arith; let K := fresh "aliaK" in pose proof I as K; clear - K; intros; lia.

Lemma g1_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> g1_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP. unfold g1_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  destruct (find_first is_carve ws) as [[[a1 SZ] a3]|] eqn:FCV; [|discriminate].
  destruct a1 as [|kA oA| | | | | | | | |]; try discriminate.
  destruct ve as [|kVT ove| | | | | | | | |]; try discriminate.
  destruct ce as [|kC oc| | | | | | | | |]; try discriminate.
  destruct zh as [|kZ oz| | | | | | | | |]; try discriminate.
  destruct root as [|k1 oR| | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kA (s_regs st)) as [rA|] eqn:FA; [|discriminate].
  destruct (IMap.find kVT (s_regs st)) as [rV|] eqn:FV; [|discriminate].
  destruct (IMap.find kC (s_regs st)) as [rC|] eqn:FC; [|discriminate].
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  destruct (IMap.find k1 (s_regs st)) as [r1|] eqn:F1; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  destruct (cell_at rV 0 8) as [v0|] eqn:CV0; [|discriminate].
  destruct (cell_at rV 8 8) as [v8|] eqn:CV8; [|discriminate].
  destruct (cell_at rC (to_Z (wl oc)) 4) as [tsv|] eqn:CT; [|discriminate].
  destruct (cell_at rC (to_Z (wl oc) + 4) 4) as [nC|] eqn:CN; [|discriminate].
  destruct (gran8 rZ 1) as [[d1 zfS]|] eqn:GZF; [|discriminate].
  destruct (gran8 rZ 2) as [[d2 zpS]|] eqn:GZP; [|discriminate].
  destruct (lit tsv) as [ti|] eqn:LT; [|discriminate].
  destruct (g1_hdr (s_regs st) ws (sv_eqb cb (VP kC oc)) (VP k1 oR) slot tD restD kA kVT kC kZ k1 rC) as [[[[tyH nH] pH] kS]|] eqn:HDR; [|discriminate].
  destruct (lit tyH) as [tyi|] eqn:LTY; [|discriminate].
  destruct (g1_count (s_facts st) nH nC) as [nsv|] eqn:CNT; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND3; [|discriminate] end.
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [sc|] eqn:SCAN; [|discriminate].
  destruct (GPot.GPot.pot_pre (s_facts st) aw sc) eqn:PRE; [|discriminate].
  injection AP as <-.
  set (n0 := s_next st) in *. set (D0b := sv_eqb cb (VP kC oc)) in *. set (fs := s_facts st) in *.
  set (t := to_Z ti) in *.

  apply andb_prop in COND as [COND DEPTH]. apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1].
  apply andb_prop in COND as [COND ALA]. apply andb_prop in COND as [COND DDEC].
  apply andb_prop in COND as [COND EXZ]. apply andb_prop in COND as [COND EXC]. apply andb_prop in COND as [COND EXV].
  apply andb_prop in COND as [COND OK2]. apply andb_prop in COND as [COND OK3]. apply andb_prop in COND as [COND OK5].
  apply andb_prop in COND as [COND N1Z]. apply andb_prop in COND as [COND N1C]. apply andb_prop in COND as [COND N1V]. apply andb_prop in COND as [COND N1A]. apply andb_prop in COND as [COND K10].
  apply andb_prop in COND as [COND NCZ]. apply andb_prop in COND as [COND NVZ]. apply andb_prop in COND as [COND NVC].
  apply andb_prop in COND as [COND NAZ]. apply andb_prop in COND as [COND NAC]. apply andb_prop in COND as [COND NAV].
  apply andb_prop in COND as [COND KZ0]. apply andb_prop in COND as [COND KC0]. apply andb_prop in COND as [COND KV0].
  apply andb_prop in COND as [COND OCL]. apply andb_prop in COND as [COND OCT]. apply andb_prop in COND as [COND OZ].
  apply andb_prop in COND as [COND OVE]. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND N62].
  apply andb_prop in COND as [VB NPOS].
  apply neqb_neq in NCZ. apply neqb_neq in NVZ. apply neqb_neq in NVC. apply neqb_neq in NAZ. apply neqb_neq in NAC. apply neqb_neq in NAV.
  apply neqb_neq in N1Z. apply neqb_neq in N1C. apply neqb_neq in N1V. apply neqb_neq in N1A. apply negb_true_iff in K10.
  apply negb_true_iff in KZ0. apply negb_true_iff in KC0. apply negb_true_iff in KV0.
  apply (proj1 (weqb_ok _ _)) in OZ. subst oz. apply (proj1 (weqb_ok _ _)) in OVE. subst ove. apply negb_true_iff in OCT.
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  apply Uint63.ltb_spec in N62. replace (to_Z (PrimInt63.sub bit62i 8%uint63)) with (to_Z bit62i - 8) in N62 by (vm_compute; reflexivity).
  apply existsb_win_In in EXZ. apply existsb_win_In in EXC. apply existsb_win_In in EXV.
  apply andb_prop in COND2 as [COND2 WZ]. apply andb_prop in COND2 as [COND2 HIZ56]. apply andb_prop in COND2 as [COND2 LOZ]. apply andb_prop in COND2 as [COND2 WC].
  apply sv_eqb_eq in HIZ56.
  apply andb_prop in COND2 as [COND2 HIC]. apply andb_prop in COND2 as [COND2 LOC]. apply andb_prop in COND2 as [COND2 WV].
  apply andb_prop in COND2 as [COND2 HIV]. apply andb_prop in COND2 as [COND2 LOV]. apply andb_prop in COND2 as [COND2 BGA].
  apply andb_prop in COND2 as [COND2 NCA]. apply andb_prop in COND2 as [COND2 WA]. apply andb_prop in COND2 as [COND2 HIA]. apply andb_prop in COND2 as [W1 LOA].
  apply Uint63.eqb_correct in LOZ. apply Uint63.eqb_correct in LOC. apply Uint63.eqb_correct in LOV. apply Uint63.eqb_correct in LOA.
  apply sv_eqb_eq in HIC. apply sv_eqb_eq in HIV. apply sv_eqb_eq in HIA.
  apply andb_prop in COND3 as [COND3 ZONE]. apply andb_prop in COND3 as [COND3 SIZE]. apply andb_prop in COND3 as [COND3 S32HC].
  apply andb_prop in COND3 as [COND3 PH]. apply andb_prop in COND3 as [COND3 TYI]. apply andb_prop in COND3 as [COND3 V0].
  apply andb_prop in COND3 as [T01 V8].
  apply sv_eqb_eq in PH. subst pH. apply sv_eqb_eq in V8. subst v8. apply sv_eqb_eq in V0. apply Z.eqb_eq in TYI.

  destruct (find_first_some _ is_carve ws _ FCV) as [INA ISC]. unfold is_carve in ISC.
  destruct a3 as [k5| | | | | | | | | |]; try discriminate.
  apply andb_prop in ISC as [ISC K5]. apply andb_prop in ISC as [ISC NT5]. apply andb_prop in ISC as [OA0 KA0].
  apply (proj1 (weqb_ok _ _)) in OA0. subst oA. apply negb_true_iff in KA0. apply negb_true_iff in NT5. apply Uint63.eqb_correct in K5.
  assert (K5E : k5 = wlit 5%uint63) by (destruct k5 as [kt kl]; cbn [wt wl] in NT5, K5; subst; reflexivity). subst k5.

  assert (TZ1 : to_Z (PrimInt63.add n0 1) = to_Z n0 + 1) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 1%uint63) with 1; alia]).
  assert (TZ2 : to_Z (PrimInt63.add n0 2) = to_Z n0 + 2) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 2%uint63) with 2; alia]).
  assert (TZ3 : to_Z (PrimInt63.add n0 3) = to_Z n0 + 3) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 3%uint63) with 3; alia]).
  assert (TZ4 : to_Z (PrimInt63.add n0 4) = to_Z n0 + 4) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 4%uint63) with 4; alia]).
  set (nZF := PrimInt63.add n0 1) in *. set (nV := PrimInt63.add n0 2) in *. set (nCT := PrimInt63.add n0 3) in *. set (nP := PrimInt63.add n0 4) in *.

  pose proof HS0 as [_ _ _ _ _ _ _ _ _ Pbst0 Preg0 _ _ _ _ _ _ _].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [VP k1 oR; cb; VP kC oc; ccap; vb; VP kVT (wlit 8); vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; VP kZ wzero] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hk. pose proof (VBo _ Hk) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (KA_LT : to_Z kA < to_Z n0) by exact (LTn kA wzero (proj1 (INW _ INA))).
  assert (KVT_LT : to_Z kVT < to_Z n0) by exact (LTn kVT (wlit 8) (INCA _ ltac:(do 5 right; left; reflexivity))).
  assert (KC_LT : to_Z kC < to_Z n0) by exact (LTn kC oc (INCA _ ltac:(do 2 right; left; reflexivity))).
  assert (KZ_LT : to_Z kZ < to_Z n0) by exact (LTn kZ wzero (INCA _ ltac:(do 16 right; left; reflexivity))).
  assert (K1_LT : to_Z k1 < to_Z n0) by exact (LTn k1 oR (INCA _ ltac:(left; reflexivity))).
  pose proof (ro_bst _ _ _ _ _ _ (Preg0 kZ rZ FZ)) as BRZ.
  assert (VBzpS : sv_vars_below n0 zpS = true) by exact (gran8_vars_below n0 st kZ rZ 2%uint63 d2 zpS VB Pbst0 BRZ FZ GZP).
  assert (VBzfS : sv_vars_below n0 zfS = true) by exact (gran8_vars_below n0 st kZ rZ 1%uint63 d1 zfS VB Pbst0 BRZ FZ GZF).

  set (wZP := den E zpS). set (wZF := den E zfS).
  set (wV := Z_to_bv 64 (bv_unsigned (ev E kVT) + 8)). set (wCT := Z_to_bv 64 (bv_unsigned (ev E kC) + 8)).
  set (wP := Z_to_bv 64 (GPot.GPot.pot_word E sc + (88 - 2 * bv_unsigned (den E SZ)))).
  set (E' := env_upd (env_upd (env_upd (env_upd (env_upd E n0 wZP) nZF wZF) nV wV) nCT wCT) nP wP).
  assert (HX : env_ext n0 E E').
  { subst E'. eapply (env_ext_trans n0 nP); [alia| | apply env_upd_ext]. eapply (env_ext_trans n0 nCT); [alia| | apply env_upd_ext].
    eapply (env_ext_trans n0 nV); [alia| | apply env_upd_ext].
    eapply (env_ext_trans n0 nZF); [alia| | apply env_upd_ext]. apply env_upd_ext. }
  assert (EZP : ev E' n0 = wZP).
  { subst E'. rewrite (ev_upd_other _ nP) by alia. rewrite (ev_upd_other _ nCT) by alia. rewrite (ev_upd_other _ nV) by alia. rewrite (ev_upd_other _ nZF) by alia. apply env_upd_same. }
  assert (EZF : ev E' nZF = wZF).
  { subst E'. rewrite (ev_upd_other _ nP) by alia. rewrite (ev_upd_other _ nCT) by alia. rewrite (ev_upd_other _ nV) by alia. apply env_upd_same. }
  assert (EV : ev E' nV = wV).
  { subst E'. rewrite (ev_upd_other _ nP) by alia. rewrite (ev_upd_other _ nCT) by alia. apply env_upd_same. }
  assert (ECT : ev E' nCT = wCT) by (subst E'; rewrite (ev_upd_other _ nP) by alia; apply env_upd_same).
  assert (EP : ev E' nP = wP) by (subst E'; apply env_upd_same).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n0 E E' HX v (VBo v Hv))).
  assert (EVkVT : ev E' kVT = ev E kVT) by exact (ev_reval n0 E E' HX kVT ltac:(apply Uint63.ltb_spec; exact KVT_LT)).
  assert (EVkC : ev E' kC = ev E kC) by exact (ev_reval n0 E E' HX kC ltac:(apply Uint63.ltb_spec; exact KC_LT)).
  assert (DzpS : den E' zpS = wZP) by exact (den_reval n0 E E' HX zpS VBzpS).
  assert (DzfS : den E' zfS = wZF) by exact (den_reval n0 E E' HX zfS VBzfS).
  clearbody E'.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n0 E E' HX st ms model NPOS VB HS0).
  clear HS0 Pbst0 Preg0 BRZ.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E') as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & [AX PTU] & SE). clear CS0.
  pose proof (GPot.GPot.pot_scan_c_ok E' fs aw ws sc Pfacts SCAN) as SCOK.
  destruct (PTU eq_refl) as (S0 & KP0 & PA0). clear PTU.
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  assert (Lce' : v_end (u_cstk g) = bv_unsigned (den E' (VP kC oc))) by exact Lce.
  assert (Lve' : v_end (u_vstk g) = bv_unsigned (den E' (VP kVT (wlit 8)))) by exact Lve.
  assert (Lroot' : u_root g = bv_unsigned (den E' (VP k1 oR))) by exact Lroot. clear Lce Lve Lroot. rename Lroot' into Lroot.
  pose proof (pf g P) as (VC & EC & SC & VV & EV8 & SV' & LV & LA & ZV).
  pose proof ZV as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  pose proof VC as (VC1 & VC2 & VC3 & VC4). pose proof VV as (VV1 & VV2 & VV3 & VV4).
  pose proof P as (_ & _ & _ & CC & _ & _ & _ & CV & _ & DLIM & _ & _).
  destruct (head_chunk g P) as (h & hr & EH & HH1 & HH2 & HH3).
  assert (Hh : In h (z_chunks (u_zone g))) by (rewrite EH; left; reflexivity).
  pose proof (owned_chunk g h Hh) as OWNh.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block h) HA (proj1 O _ OWNh)) as (Bh1 & Bh2 & Bh3 & Bh4 & _).
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.
  unfold chunk_block in Bh1, Bh2, Bh3. cbn [fst snd] in Bh1, Bh2, Bh3. unfold CHUNK_HDR in Bh2, Bh3.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (cstk_block g) HA (proj1 O _ (owned_cstk g))) as (Bc1 & Bc2 & Bc3 & _ & _).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (vstk_block g) HA (proj1 O _ (owned_vstk g))) as (Bv1 & Bv2 & Bv3 & _ & _).
  unfold cstk_block, vstk_block, v_bytes in Bc1, Bc2, Bc3, Bv1, Bv2, Bv3. cbn [fst snd] in Bc1, Bc2, Bc3, Bv1, Bv2, Bv3.
  rewrite EC in Bc2, Bc3. rewrite EV8 in Bv2, Bv3.
  assert (CAP32 : forall c, cap32_b c = true -> 32 <= c).
  { intros c Hc. unfold cap32_b in Hc. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.leb_le in Hc. unfold EMBED_STACK in Hc. exact Hc. }
  pose proof (CAP32 _ CC) as CC32. pose proof (CAP32 _ CV) as CV32.
  assert (DLEN : u_D g = Z.of_nat (length (u_levels g))) by reflexivity.

  pose proof (Preg kA rA FA) as ROA. pose proof (Preg kVT rV FV) as ROV. pose proof (Preg kC rC FC) as ROC. pose proof (Preg kZ rZ FZ) as ROZ.

  set (P_ := bv_unsigned (ev E' kA)) in *. set (B1 := bv_unsigned (ev E' kVT)) in *. set (BC := bv_unsigned (ev E' kC)) in *.
  set (ZB := bv_unsigned (ev E' kZ)) in *.
  set (bm := bmem_of segs (ms_mem ms)) in *.
  set (zp := z_ptr (u_zone g)) in *. set (zf := z_free (u_zone g)) in *. set (ls := u_levels g) in *.
  set (SZd := bv_unsigned (den E' SZ)) in *.
  assert (HIA' : hiZ E' rA = SZd) by (unfold hiZ; rewrite HIA; reflexivity).
  assert (HIV' : hiZ E' rV = 16) by (unfold hiZ; rewrite HIV; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (OCLV : to_Z (wl oc) = (if D0b then 0 else 8)).
  { destruct D0b; apply Uint63.eqb_correct in OCL; rewrite OCL; reflexivity. }
  set (ocl := to_Z (wl oc)) in *.
  assert (OCW : w2Z oc = ocl) by (unfold w2Z; rewrite OCT; subst ocl; alia).
  assert (HIC' : hiZ E' rC = ocl + 8).
  { unfold hiZ. rewrite HIC. cbn [den]. rewrite wbv_unsigned, wlit_ok, to_Z_add_small; [subst ocl; reflexivity| |change (to_Z 8%uint63) with 8; alia].
    pose proof (int_range (wl oc)). rewrite to_Z_bit62i. destruct D0b; subst ocl; alia. }
  assert (LOA' : loZ rA = 0) by (unfold loZ; rewrite LOA; reflexivity).
  assert (LOV' : loZ rV = 0) by (unfold loZ; rewrite LOV; reflexivity).
  assert (LOC' : loZ rC = 0) by (unfold loZ; rewrite LOC; reflexivity).
  assert (LOZ' : loZ rZ = 0) by (unfold loZ; rewrite LOZ; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROA KA0) as RA. rewrite LOA', HIA' in RA. fold P_ in RA.
  pose proof (ro_range _ _ _ _ _ _ ROV KV0) as RVr. rewrite LOV', HIV' in RVr. fold B1 in RVr.
  pose proof (ro_range _ _ _ _ _ _ ROC KC0) as RCr. rewrite LOC', HIC' in RCr. fold BC in RCr.
  pose proof (ro_range _ _ _ _ _ _ ROZ KZ0) as RZr. rewrite LOZ' in RZr. fold ZB in RZr.

  destruct (cell_at_u64 segs _ E' (ms_mem ms) kVT rV 0 v0 ROV KV0 ltac:(alia) ltac:(unfold two62Z; alia) CV0) as (AV0 & _ & _).
  destruct (cell_at_u64 segs _ E' (ms_mem ms) kVT rV 8 _ ROV KV0 ltac:(alia) ltac:(unfold two62Z; alia) CV8) as (AV8 & _ & _).
  rewrite (den_VP0 E' kA wzero (weqb_refl _)) in AV8. fold P_ B1 bm in AV0, AV8. rewrite Z.add_0_r in AV0.
  destruct (cell_at_u32 segs _ E' (ms_mem ms) kC rC ocl tsv ROC KC0 ltac:(destruct D0b; subst ocl; alia) ltac:(unfold two62Z; destruct D0b; subst ocl; alia) CT) as (AT & _ & _).
  destruct (cell_at_u32 segs _ E' (ms_mem ms) kC rC (ocl + 4) nC ROC KC0 ltac:(destruct D0b; subst ocl; alia) ltac:(unfold two62Z; destruct D0b; subst ocl; alia) CN) as (AN & _ & _).
  fold BC bm in AT, AN. rewrite Z.add_assoc in AN.
  destruct (gran8_u64 segs _ E' (ms_mem ms) kZ rZ 1%uint63 d1 zfS ROZ KZ0 GZF ltac:(change (keyZ 1%uint63) with 1; alia) ltac:(change (keyZ 1%uint63) with 1; unfold two62Z; alia)) as (AZF & _ & HZ1).
  destruct (gran8_u64 segs _ E' (ms_mem ms) kZ rZ 2%uint63 d2 zpS ROZ KZ0 GZP ltac:(change (keyZ 2%uint63) with 2; alia) ltac:(change (keyZ 2%uint63) with 2; unfold two62Z; alia)) as (AZP & _ & HZ2).
  change (keyZ 1%uint63) with 1 in AZF, HZ1. change (keyZ 2%uint63) with 2 in AZP, HZ2. fold ZB bm in AZF, AZP. rewrite DzpS in AZP. rewrite DzfS in AZF.

  pose proof (lit_val E' tsv ti LT) as TSV. fold t in TSV.
  assert (T01' : t = 0 \/ t = 1) by (apply orb_prop in T01; destruct T01 as [X|X]; apply Z.eqb_eq in X; alia).
  pose proof (lit_val E' tyH tyi LTY) as TYV. rewrite TYI in TYV.
  unfold g1_count in CNT. destruct (find_first (GFast.GFast.bounded_count_f fs) (nH :: nC :: zx_forms (core32 nH))) as [nsv'|] eqn:FF; [|discriminate].
  destruct (same32 nsv' nH) eqn:S32; [|discriminate]. injection CNT as ->.
  destruct (find_first_some _ _ _ _ FF) as [_ BND].
  rewrite GFast.GFast.bounded_count_f_eq in BND. pose proof (bounded_count_sound E' fs nsv Pfacts BND) as NB. set (n := bv_unsigned (den E' nsv)) in *.
  assert (NH32 : bv_unsigned (den E' nH) mod 2 ^ 32 = n).
  { rewrite <- (same32_sound E' nsv nH S32). apply Z.mod_small. alia. }
  assert (NC32 : bv_unsigned (den E' nC) mod 2 ^ 32 = n).
  { rewrite <- (same32_sound E' nH nC S32HC). exact NH32. }
  rewrite NC32 in AN.
  assert (TSV32 : bv_unsigned (den E' tsv) mod 2 ^ 32 = t) by (rewrite TSV; apply Z.mod_small; alia).
  rewrite TSV32 in AT.
  assert (NH32h : hide (bv_unsigned (den E' nH) mod 2 ^ 32 = n)) by exact NH32.
  assert (NC32h : hide (bv_unsigned (den E' nC) mod 2 ^ 32 = n)) by exact NC32.
  assert (TSV32h : hide (bv_unsigned (den E' tsv) mod 2 ^ 32 = t)) by exact TSV32. clear NH32 NC32 TSV32.
  set (ct := if t =? 0 then CT_ARRAY_ITEM else CT_MAP_KEY).
  assert (CTc : ctype_code ct = t) by (subst ct; destruct T01' as [-> | ->]; reflexivity).
  assert (CTt : container_type ct = 7 + t) by (subst ct; destruct T01' as [-> | ->]; reflexivity).
  assert (CTp : per ct = (if t =? 0 then 1 else 2)) by (subst ct; destruct T01' as [-> | ->]; reflexivity).
  assert (CTnv : ct <> CT_MAP_VALUE) by (subst ct; destruct T01' as [-> | ->]; discriminate).
  assert (PER12 : per ct = 1 \/ per ct = 2) by (rewrite CTp; destruct (t =? 0); alia).

  assert (SZV : SZd = OBJ_SIZE * per ct * n).
  { unfold g1_size in SIZE. cbv zeta in SIZE.
    assert (DCof : forall c, In c (nsv :: zx_forms (core32 nH)) -> bv_unsigned (den E' c) = n).
    { intros c Hc. destruct Hc as [<-|Hc]; [reflexivity|]. rewrite (zx_forms_den E' (core32 nH) c Hc).
      rewrite (core32_den E' nH). exact NH32h. }
    destruct (exists_lazy (size_mul SZ (if t =? 0 then 1 else 2)) (nsv :: zx_forms (core32 nH))) eqn:SM.
    - rewrite exists_lazy_eq in SM. apply existsb_exists in SM as (c & Hc & Q). pose proof (DCof c Hc) as DC.
      rewrite <- CTp in Q. subst SZd. rewrite (size_mul_den E' SZ (per ct) c PER12 Q ltac:(rewrite DC; alia)), DC. reflexivity.
    - rewrite exists_lazy_eq in SIZE. apply existsb_exists in SIZE as (c & Hc & Q).
      destruct (decide_eq_t fs SZ (size_sv (if t =? 0 then 1 else 2) c)) as [[|]|] eqn:DQ; try discriminate.
      pose proof (decide_eq_t_sound E' fs Pfacts _ _ _ DQ) as EQ. apply (proj1 (eqb_iff _ _ true)) in EQ.
      pose proof (DCof c Hc) as DC.
      subst SZd. rewrite EQ, <- CTp, (size_sv_den E' (per ct) c PER12 ltac:(rewrite DC; alia)), DC. reflexivity. }
  assert (SZ24 : 24 <= SZd) by (rewrite SZV; unfold OBJ_SIZE; destruct PER12 as [X|X]; rewrite X; alia).

  assert (LCE' : v_end (u_cstk g) = BC + ocl).
  { rewrite Lce'. subst BC ocl. rewrite <- OCW. apply den_VP_nowrap. rewrite OCW. destruct D0b; alia. }
  assert (LVE' : v_end (u_vstk g) = B1 + 8).
  { rewrite Lve'. subst B1. rewrite (den_VP_nowrap E' kVT (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; alia).
    rewrite wlit_ok. reflexivity. }
  assert (VEND : v_end (u_vstk g) = v_begin (u_vstk g) + 8 * (u_D g + 1)) by (unfold v_end; rewrite EV8, SV'; alia).
  assert (CEND : v_end (u_cstk g) = v_begin (u_cstk g) + 8 * u_D g) by (unfold v_end; rewrite EC, SC; alia).
  assert (DZ : D0b = true -> ls = []).
  { intros HD. subst D0b. apply sv_eqb_eq in HD.
    assert (X : v_begin (u_cstk g) = v_end (u_cstk g)) by (rewrite Lcb, Lce', HD; reflexivity).
    rewrite CEND in X. subst ls. destruct (u_levels g); [reflexivity|]. exfalso. rewrite DLEN in X. cbn [length] in X. alia. }
  assert (DNZ : D0b = false -> ls <> []).
  { intros HD NIL. rewrite HD in DDEC. cbn [orb] in DDEC. destruct (decide_ltu_t fs cb (VP kC oc)) as [[|]|] eqn:DL; try discriminate.
    pose proof (decide_ltu_t_sound E' fs Pfacts _ _ _ DL) as LTU. apply (proj1 (ltu_iff _ _ true)) in LTU.
    rewrite <- Lcb, <- Lce', CEND, DLEN in LTU. subst ls. rewrite NIL in LTU. cbn [length] in LTU. alia. }
  assert (OCLD : ocl = (if D0b then 0 else 8)) by exact OCLV.
  assert (DVAL : BC + ocl = v_begin (u_cstk g) + 8 * u_D g) by (rewrite <- LCE'; exact CEND).
  assert (D0ls : if D0b then ls = [] else ls <> []) by (destruct D0b; [exact (DZ eq_refl)| exact (DNZ eq_refl)]).
  assert (OCL0 : 0 <= ocl <= 8) by (rewrite OCLD; destruct D0b; alia).

  assert (WINC : sub_ok 1 g (wden E' (top_win kC (PrimInt63.add (wl oc) 8) 2)) /\ to_Z (PrimInt63.add (wl oc) 8%uint63) = ocl + 8).
  { assert (L8 : to_Z (PrimInt63.add (wl oc) 8%uint63) = ocl + 8).
    { rewrite to_Z_add_small; [subst ocl; reflexivity| |change (to_Z 8%uint63) with 8; alia]. rewrite to_Z_bit62i. destruct D0b; subst ocl; alia. }
    split; [| exact L8].
    pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXC)) as WW. rewrite top_win_den in WW |- *. rewrite L8 in WW |- *. fold BC in WW |- *.
    change (to_Z 2%uint63) with 2 in WW |- *.
    cbn [w_kind w_lo w_len] in WW. destruct (WW ltac:(unfold K_STACK; alia)) as [[_ DJ]|[_ SO]]; [| exact SO].
    exfalso. refine (DJ (cstk_block g) (owned_cstk g) BC _ _).
    - unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. alia.
    - unfold in_iv, cstk_block, v_bytes. cbn [fst snd]. rewrite EC. destruct D0b; [pose proof (DZ eq_refl) as NIL| pose proof (DNZ eq_refl) as NN].
      + rewrite DLEN, NIL in DVAL. cbn [length] in DVAL. rewrite OCLD in DVAL. clear - DVAL CC32. alia.
      + assert (1 <= u_D g) by (rewrite DLEN; destruct ls; [contradiction| cbn [length]; alia]). rewrite OCLD in DVAL.
        pose proof VC2 as X. rewrite SC in X. clear - X H DVAL CC32. alia. }
  destruct WINC as [WINC L8].
  assert (CROOM : v_begin (u_cstk g) <= BC /\ BC + ocl + 8 <= v_capend (u_cstk g)).
  { unfold sub_ok in WINC. cbv zeta in WINC. rewrite top_win_den, L8 in WINC. change (to_Z 2%uint63) with 2 in WINC. cbn [w_kind w_lo w_len] in WINC. fold BC in WINC.
    destruct WINC as [(_ & I1 & I2 & I3)|[(KD & _)|[(KD & _)|(KD & _)]]]; [alia| discriminate KD..]. }
  assert (WINV : sub_ok 1 g (wden E' (top_win kVT 16 3))).
  { pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXV)) as WW. rewrite top_win_den in WW |- *. fold B1 in WW |- *.
    cbn [w_kind w_lo w_len] in WW. change (to_Z 16%uint63) with 16 in WW |- *. change (to_Z 3%uint63) with 3 in WW |- *.
    destruct (WW ltac:(unfold K_STACK; alia)) as [[_ DJ]|[_ SO]]; [| exact SO].
    exfalso. refine (DJ (vstk_block g) (owned_vstk g) B1 _ _).
    - unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. alia.
    - unfold in_iv, vstk_block, v_bytes. cbn [fst snd]. rewrite EV8. pose proof VV2 as X. rewrite SV' in X.
      pose proof VEND as Y. rewrite LVE' in Y. clear - X Y DLEN. alia. }
  assert (VROOM : v_begin (u_vstk g) <= B1 /\ B1 + 16 <= v_capend (u_vstk g)).
  { unfold sub_ok in WINV. cbv zeta in WINV. rewrite top_win_den in WINV. cbn [w_kind w_lo w_len] in WINV.
    change (to_Z 16%uint63) with 16 in WINV. change (to_Z 3%uint63) with 3 in WINV. fold B1 in WINV.
    destruct WINV as [(KD & _)|[(_ & I1 & I2 & I3)|[(KD & _)|(KD & _)]]]; [discriminate KD| alia| discriminate KD..]. }

  assert (CURSLOT : u_cur_slot g = (if D0b then bv_unsigned (den E' (VP k1 oR)) else bv_unsigned (den E' slot))).
  { destruct D0b.
    - pose proof (DZ eq_refl) as NIL. unfold u_cur_slot. subst ls. rewrite NIL. cbn [cur_slot rev]. exact Lroot.
    - pose proof (DNZ eq_refl) as NN. exact (proj1 (LD NN)). }
  assert (HDRS : u32_at bm (u_cur_slot g) (7 + t) /\ u32_at bm (u_cur_slot g + 8) n /\ u64_at bm (u_cur_slot g + 16) P_ /\
                 (D0b = true -> only_kind 4 None ws = true) /\
                 (D0b = false -> exists rS, slot = VP kS wzero /\ IMap.find kS (s_regs st) = Some rS /\ rg_lo rS = 0%uint63 /\ rg_hi rS = VL (wlit 24%uint63)
                                   /\ rg_w rS = true /\ In (slot_win kS) ws /\ only_kind 4 (Some (slot_win kS)) ws = true
                                   /\ kS <> 0%uint63 /\ kS <> kA /\ kS <> kVT /\ kS <> kC /\ kS <> kZ /\ kS <> k1
                                   /\ u32_at bm BC (bv_unsigned (den E' tD) mod 2 ^ 32) /\ u32_at bm (BC + 4) (bv_unsigned (den E' restD) mod 2 ^ 32))).
  { unfold g1_hdr in HDR. rewrite CURSLOT. destruct D0b.
    - destruct (okey oR) as [key|] eqn:OK; [|discriminate]. rewrite F1 in HDR.
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR; [|discriminate] end.
      destruct (cell_at r1 (keyZ key) 4) as [a|] eqn:C1; [|discriminate]. destruct (cell_at r1 (keyZ key + 8) 4) as [b|] eqn:C2; [|discriminate].
      destruct (cell_at r1 (keyZ key + 16) 8) as [c|] eqn:C3; [|discriminate]. injection HDR as E1 E2 E3 E4. subst a b c. subst kS.
      apply andb_prop in CR as [CR K62]. apply Z.ltb_lt in K62.
      apply andb_prop in CR as [CR OK4]. apply andb_prop in CR as [CR _]. apply andb_prop in CR as [CR _]. apply andb_prop in CR as [CR _]. apply andb_prop in CR as [KR0 _].
      clear KR0. pose proof K10 as KR0. pose proof (Preg k1 r1 F1) as ROR.
      pose proof (okey_sound oR key OK) as [KEY KR]. clear KR. pose proof (keyZ_range key) as KRR. unfold two62Z in K62.
      assert (ADDR : bv_unsigned (den E' (VP k1 oR)) = bv_unsigned (ev E' k1) + keyZ key).
      { destruct (cell_at_ok_s segs _ E' (ms_mem ms) k1 r1 (keyZ key) 4%uint63 tyH ROR ltac:(unfold two62Z; alia) ltac:(unfold two62Z; alia) C1) as (_ & _ & IN).
        pose proof (IN KR0 0 ltac:(change (to_Z 4%uint63) with 4; alia)) as IN0. pose proof (ro_range _ _ _ _ _ _ ROR KR0) as [R1 R2].
        rewrite (den_VP_addr E' k1 oR key OK) by (unfold addrZ; alia). rewrite Z_to_bv_unsigned. unfold addrZ, bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. alia. }
      rewrite ADDR.
      destruct (cell_at_u32_s segs _ E' (ms_mem ms) k1 r1 (keyZ key) tyH ROR KR0 ltac:(unfold two62Z; alia) ltac:(unfold two62Z; alia) C1) as (X1 & _ & _).
      destruct (cell_at_u32_s segs _ E' (ms_mem ms) k1 r1 (keyZ key + 8) nH ROR KR0 ltac:(unfold two62Z; alia) ltac:(unfold two62Z; alia) C2) as (X2 & _ & _).
      destruct (cell_at_u64_s segs _ E' (ms_mem ms) k1 r1 (keyZ key + 16) _ ROR KR0 ltac:(unfold two62Z; alia) ltac:(unfold two62Z; alia) C3) as (X3 & _ & _).
      fold bm in X1, X2, X3. rewrite TYV, Z.mod_small in X1 by (clear - T01'; alia). rewrite (NH32h : bv_unsigned (den E' nH) mod 2 ^ 32 = n) in X2. rewrite (den_VP0 E' kA wzero (weqb_refl _)) in X3. fold P_ in X3.
      rewrite !Z.add_assoc in X2, X3.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [intros _; exact OK4| intros X; discriminate X].
    - destruct slot as [|kS0 os| | | | | | | | |]; try discriminate.
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR; [|discriminate] end.
      destruct (IMap.find kS0 (s_regs st)) as [rS|] eqn:FS; [|discriminate].
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR2; [|discriminate] end.
      destruct (cell_at rS 0 4) as [a|] eqn:C1; [|discriminate]. destruct (cell_at rS 8 4) as [b|] eqn:C2; [|discriminate].
      destruct (cell_at rS 16 8) as [c|] eqn:C3; [|discriminate].
      destruct (cell_at rC 0 4) as [tc0|] eqn:C4; [|discriminate]. destruct (cell_at rC 4 4) as [rc0|] eqn:C5; [|discriminate].
      destruct (same32 tc0 tD && same32 rc0 restD) eqn:S2; [|discriminate]. injection HDR as E1 E2 E3 E4. subst a b c. subst kS0.
      apply andb_prop in S2 as [S2a S2b].
      apply andb_prop in CR as [CR EXS]. apply andb_prop in CR as [CR OK4]. apply andb_prop in CR as [CR NS1]. apply andb_prop in CR as [CR NSZ]. apply andb_prop in CR as [CR NSC].
      apply andb_prop in CR as [CR NSV]. apply andb_prop in CR as [CR NSA]. apply andb_prop in CR as [OS KS0'].
      apply (proj1 (weqb_ok _ _)) in OS. subst os. apply negb_true_iff in KS0'.
      apply neqb_neq in NSZ. apply neqb_neq in NSC. apply neqb_neq in NSV. apply neqb_neq in NSA. apply neqb_neq in NS1. apply existsb_win_In in EXS.
      apply andb_prop in CR2 as [CR2 WS]. apply andb_prop in CR2 as [LOS HIS]. apply Uint63.eqb_correct in LOS. apply sv_eqb_eq in HIS.
      pose proof (Preg kS rS FS) as ROS.
      rewrite (den_VP0 E' kS wzero (weqb_refl _)).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kS rS 0 tyH ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C1) as (X1 & _ & _).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kS rS 8 nH ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C2) as (X2 & _ & _).
      destruct (cell_at_u64 segs _ E' (ms_mem ms) kS rS 16 _ ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C3) as (X3 & _ & _).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kC rC 0 tc0 ROC KC0 ltac:(alia) ltac:(unfold two62Z; alia) C4) as (X4 & _ & _).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kC rC 4 rc0 ROC KC0 ltac:(alia) ltac:(unfold two62Z; alia) C5) as (X5 & _ & _).
      fold bm BC in X1, X2, X3, X4, X5. rewrite Z.add_0_r in X1, X4.
      rewrite TYV, Z.mod_small in X1 by (clear - T01'; alia). rewrite (NH32h : bv_unsigned (den E' nH) mod 2 ^ 32 = n) in X2. rewrite (den_VP0 E' kA wzero (weqb_refl _)) in X3. fold P_ in X3.
      rewrite (same32_sound E' tc0 tD S2a) in X4. rewrite (same32_sound E' rc0 restD S2b) in X5.
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [intros X; discriminate X|]. intros _.
      exists rS. split; [reflexivity|]. split; [exact FS|]. split; [exact LOS|]. split; [exact HIS|]. split; [exact WS|]. split; [exact EXS|]. split; [exact OK4|].
      split; [exact (Uint63.eqb_false_correct _ _ KS0')|]. split; [exact NSA|]. split; [exact NSV|]. split; [exact NSC|]. split; [exact NSZ|]. split; [exact NS1|]. split; [exact X4| exact X5]. }
  destruct HDRS as (HTY & HN & HP & HD0 & HD1).

  assert (ZPV : bv_unsigned (den E' zptr) = zp) by (symmetry; exact Lzp).
  assert (ZFV : bv_unsigned (den E' zfree) = zf) by (symmetry; exact Lzf).
  assert (CHI : chunk_hi h = zp + zf) by (subst zp zf; alia).
  assert (B1' : 0 <= P_ + SZd < two64) by (clear - RA SZ24; lia).
  assert (B2' : 0 <= zp + zf < two64) by (clear - Bh1 Bh2 Bh3 Bh4 CHI; rewrite <- CHI; unfold chunk_hi, CHUNK_HDR in *; lia).
  assert (ZLE : zp <= P_).
  { pose proof (implied_t_sound E' fs _ Pz Pfacts IMP1) as IF1. cbn [fact_holds] in IF1. rewrite ZPV, (den_VP0 E' kA wzero (weqb_refl _)) in IF1. exact IF1. }
  assert (ZHI : P_ + SZd <= zp + zf).
  { pose proof (implied_t_sound E' fs _ Pz Pfacts IMP2) as IF2. cbn [fact_holds] in IF2. rewrite !den_VAlu in IF2. cbn [alu64 alu] in IF2.
    rewrite !bv_add_unsigned, (den_VP0 E' kA wzero (weqb_refl _)), ZPV, ZFV, !wrap64 in IF2. fold SZd in IF2. fold P_ in IF2.
    rewrite (Z.mod_small _ _ B1'), (Z.mod_small _ _ B2') in IF2. exact IF2. }
  set (zp' := bv_unsigned (den E' zpS)) in *. set (zf' := bv_unsigned (den E' zfS)) in *.
  assert (ZPS : zp' = P_ + SZd /\ zp' + zf' = zp + zf).
  { unfold g1_zone in ZONE. apply existsb_exists in ZONE as (X & HX0 & Q). apply andb_prop in Q as [Q1 Q2].
    pose proof (anchor_defs_sound E' fs kA X Pfacts HX0) as DX.
    pose proof (msame_sound E' _ _ Q1) as M1. pose proof (msame_sound E' _ _ Q2) as M2.
    assert (M1' : zp' = (P_ + SZd) mod two64).
    { subst zp'. rewrite M1, den_VAlu. cbn [alu64 alu]. rewrite bv_add_unsigned, DX, (den_VP0 E' kA wzero (weqb_refl _)), wrap64. reflexivity. }
    rewrite Z.mod_small in M1' by exact B1'.
    assert (M2' : (zp' + zf') mod two64 = zp + zf).
    { apply (f_equal bv_unsigned) in M2. rewrite !den_VAlu in M2. cbn [alu64 alu] in M2. rewrite !bv_add_unsigned, !wrap64 in M2. fold zp' zf' in M2.
      replace (bv_unsigned (den E' (if sv_eqb zptr (VP kA wzero) then X else zptr))) with zp in M2.
      2:{ destruct (sv_eqb zptr (VP kA wzero)) eqn:QZ; [| symmetry; exact ZPV]. apply sv_eqb_eq in QZ. rewrite DX, <- QZ. symmetry. exact ZPV. }
      rewrite ZFV in M2. rewrite M2. apply Z.mod_small. exact B2'. }
    pose proof (bv_unsigned_in_range _ (den E' zfS)) as RF. rewrite bv_modulus_64 in RF. fold zf' in RF.
    pose proof (bv_unsigned_in_range _ (den E' zpS)) as RP. rewrite bv_modulus_64 in RP. fold zp' in RP.
    split; [exact M1'|].
    destruct (mod_ex (zp' + zf')) as [q Hq]. rewrite Hq in M2'. unfold two64 in *. alia. }
  destruct ZPS as [ZP1 ZP2].
  pose proof (bv_unsigned_in_range _ (den E' zfS)) as RF. rewrite bv_modulus_64 in RF. fold zf' in RF.

  assert (DEP : u_D g + 1 <= LIMIT).
  { destruct (g1_depth_inv E' _ _ _ _ Pfacts DEPTH) as (X & d & HXa & Hd & LTU).
    pose proof (anchor_defs_sound E' fs kVT X Pfacts HXa) as XD.
    assert (BASE : den E' (sv_alu ALU_ADD X (VL (wlit 8))) = den E' (VP kVT (wlit 8))).
    { rewrite den_sv_alu. cbn [alu64 alu]. rewrite XD. apply bv_eq. rewrite bv_add_unsigned, (den_VP0 E' kVT wzero (weqb_refl _)), den_VPu. cbn [den].
      rewrite wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
    apply (proj1 (ltu_iff _ _ true)) in LTU.
    replace (bv_unsigned (den E' (VL (wlit 1001)))) with 1001 in LTU by (cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    assert (SUBV : bv_unsigned (den E' (sv_alu ALU_SUB (sv_alu ALU_ADD X (VL (wlit 8))) vb)) = 8 * (u_D g + 1)).
    { rewrite den_sv_alu. cbn [alu64 alu]. rewrite BASE. rewrite bv_sub_unsigned, wrap64. rewrite <- Lve', <- Lvb, VEND. unfold LIMIT in DLIM.
      replace (v_begin (u_vstk g) + 8 * (u_D g + 1) - v_begin (u_vstk g)) with (8 * (u_D g + 1)) by alia.
      apply Z.mod_small. unfold two64. rewrite DLEN. alia. }
    assert (SH : forall w : word, bv_unsigned w = 8 * (u_D g + 1) ->
              bv_unsigned (alu64 ALU_SRA w (den E' (VL (wlit 3)))) = u_D g + 1 /\ bv_unsigned (alu64 ALU_SRL w (den E' (VL (wlit 3)))) = u_D g + 1).
    { intros w Hw. cbn [den alu64 alu]. rewrite bv_ashiftr_unsigned, bv_shiftr_unsigned, !shamt6_bv. change (to_Z (shamt6 (wlit 3))) with 3.
      rewrite !Z.shiftr_div_pow2 by alia. change (2 ^ 3) with 8.
      assert (SG : bv_signed w = bv_unsigned w).
      { unfold bv_signed. apply bv_swrap_small. rewrite Hw. unfold bv_half_modulus. rewrite bv_modulus_64. replace (two64 / 2) with 9223372036854775808 by (vm_compute; reflexivity). rewrite DLEN in *. unfold LIMIT in DLIM. alia. }
      rewrite SG, Hw, wrap64. replace (8 * (u_D g + 1)) with ((u_D g + 1) * 8) by alia. rewrite Z.div_mul by alia.
      split; [| reflexivity]. apply Z.mod_small. unfold two64. rewrite DLEN in *. unfold LIMIT in DLIM. alia. }
    destruct (SH _ SUBV) as [S1 S2].
    destruct Hd as [->| ->]; rewrite den_sv_alu in LTU; [rewrite S1 in LTU| rewrite S2 in LTU]; unfold LIMIT; alia. }

  set (nl := new_level ct n P_).
  set (z' := zone_bump (u_zone g) (zp' - zp)).
  set (g' := mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) (push_level ls ct n P_) (vec_push (u_cstk g)) (vec_push (u_vstk g)) z').
  assert (ZG : zone_grows (u_zone g) z') by (apply zone_grows_bump; alia).
  assert (ZV' : zone_valid z').
  { subst z'. unfold zone_bump, zone_valid. cbn [z_chunks z_addr z_ptr z_free]. fold zp zf.
    split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. rewrite EH in *. cbn [hd] in *. unfold chunk_lo, chunk_hi, CHUNK_HDR in *.
    split; [alia|]. split; [alia|]. split; [alia|]. exact Z7. }
  assert (ZC' : z_chunks z' = z_chunks (u_zone g) /\ z_ptr z' = zp' /\ z_free z' = zf' /\ z_addr z' = z_addr (u_zone g) /\ z_head z' = z_head (u_zone g)).
  { subst z'. unfold zone_bump. cbn. fold zp zf. repeat split; alia. }
  destruct ZC' as (ZCc & ZCp & ZCf & ZCa & ZCh).
  assert (HH1' : fst h + 8 <= zp) by (unfold chunk_lo, CHUNK_HDR in HH1; exact HH1).
  assert (P0 : P_ <> 0) by (clear - HH1' Bh1 ZLE; lia).
  assert (P8 : P_ mod 8 = 0) by exact (mod8_of_align E' fs kA Pfacts ALA).
  assert (FRESH : forall a k, 0 <= k -> in_alloc (u_zone g) a k -> rdisj a k P_ (lv_bytes nl)).
  { intros a k Hk Ha. apply (in_alloc_fresh_disj (u_zone g) a k P_ (lv_bytes nl) ZV Hk Ha); [fold zp; alia|].
    rewrite EH. cbn [hd]. rewrite CHI. subst nl. unfold lv_bytes, new_level. cbn [lv_t lv_n]. rewrite <- SZV. alia. }
  assert (BYTES : lv_bytes nl = SZd) by (subst nl; unfold lv_bytes, new_level; cbn [lv_t lv_n]; rewrite SZV; reflexivity).
  pose proof (push_ok bm (u_zone g) (u_root g) ls ct n P_ CTnv ltac:(unfold LIMIT; alia) P0 P8 LV LA (completed_ok_wf _ _ _ (proj2 (proj2 (proj2 (proj2 (proj2 M)))))) FRESH)
    as (LV' & LA' & _ & CONT' & CUR' & LK' & LSLOT' & CONTS').
  assert (P8h : hide (P_ mod 8 = 0)) by exact P8. clear P8.
  pose proof (vec_push_end (u_cstk g)) as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  pose proof (vec_push_end (u_vstk g)) as (PV1 & PV2 & PV3 & PV4 & PV5 & PV6 & PV7).
  assert (OWN' : owned g' = owned g) by (subst g'; unfold owned, cstk_block, vstk_block; cbn [u_cstk u_vstk u_zone]; rewrite PC2, PC4, PV2, PV4, ZCc; reflexivity).
  assert (PURE' : pure_ok g').
  { subst g'. unfold pure_ok. cbn [u_cstk u_vstk u_levels u_zone]. unfold u_D. cbn [u_levels]. rewrite push_level_length, Nat2Z.inj_succ. fold ls. rewrite <- DLEN.
    destruct (vec_push_valid (u_cstk g) VC ltac:(unfold v_end, v_capend in *; rewrite EC in *; alia)) as [VCP _].
    destruct (vec_push_valid (u_vstk g) VV ltac:(unfold v_end, v_capend in *; rewrite EV8 in *; alia)) as [VVP _].
    rewrite PC5, PC6, PC7, PV5, PV6, PV7.
    split; [exact VCP|]. split; [exact EC|]. split; [rewrite SC; alia|]. split; [exact CC|].
    split; [exact VVP|]. split; [exact EV8|]. split; [rewrite SV'; alia|]. split; [exact CV|].
    split; [exact LV'|]. split; [alia|]. split; [| exact ZV'].
    pose proof BYTES as BY. unfold nl in BY.
    apply LA'; [exact ZG|]. unfold in_alloc. rewrite ZCp, ZCc, ?BYTES, ?BY, EH. right. cbn [hd]. unfold chunk_lo, CHUNK_HDR. alia. }
  assert (OWNOK' : own_ok g' LB) by (unfold own_ok; rewrite OWN'; exact O).

  assert (LAST' : last_opt (push_level ls ct n P_) = Some nl) by (unfold push_level; apply last_opt_snoc).
  assert (SLOTnl : lv_slot nl = P_) by exact LSLOT'.
  assert (UNFnl : lv_unfilled nl = SZd) by (unfold lv_unfilled; rewrite SLOTnl, BYTES; subst nl; cbn [new_level lv_P]; alia).

  assert (SUBS : sub_ok 1 g' (Win P_ 24 K_SLOT)).
  { unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; right; left. split; [reflexivity|]. exists nl. subst g'. cbn [u_levels]. split; [exact LAST'|].
    cbn [Z.eqb CM_CONS Pos.eqb]. rewrite SLOTnl, UNFnl. alia. }
  assert (SUBC : sub_ok 1 g' (Win (BC + ocl) 8 K_CTOP)).
  { unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. left. split; [reflexivity|]. subst g'. cbn [u_cstk]. rewrite PC1, PC2, PC3, EC, LCE'. alia. }
  assert (SUBV : sub_ok 1 g' (Win (B1 + 8) 8 K_VTOP)).
  { unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; left. split; [reflexivity|]. subst g'. cbn [u_vstk]. rewrite PV1, PV2, PV3, EV8, LVE'. alia. }

  assert (BYA : forall a, P_ <= a < P_ + SZd -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (bytes_of_region segs _ E' (ms_mem ms) kA rA a ROA KA0). rewrite LOA', HIA'. fold P_. alia. }
  assert (BYV : forall a, B1 <= a < B1 + 16 -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (bytes_of_region segs _ E' (ms_mem ms) kVT rV a ROV KV0). rewrite LOV', HIV'. fold B1. alia. }
  assert (BYC : forall a, BC <= a < BC + ocl + 8 -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (bytes_of_region segs _ E' (ms_mem ms) kC rC a ROC KC0). rewrite LOC', HIC'. fold BC. alia. }

  set (kC' := if D0b then kC else nCT) in *.
  assert (EkC' : bv_unsigned (ev E' kC') = BC + ocl).
  { subst kC'. destruct D0b.
    - change (ocl = 0) in OCLD. rewrite OCLD. subst BC. clear; lia.
    - change (ocl = 8) in OCLD. rewrite OCLD, ECT. unfold wCT. rewrite Z_to_bv_unsigned, <- EVkC. fold BC. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small.
      clear - RCr OCLD. lia. }
  assert (EnV : bv_unsigned (ev E' nV) = B1 + 8).
  { rewrite EV. unfold wV. rewrite Z_to_bv_unsigned, <- EVkVT. fold B1. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. alia. }
  assert (EnCT : bv_unsigned (ev E' nCT) = BC + 8).
  { rewrite ECT. unfold wCT. rewrite Z_to_bv_unsigned, <- EVkC. fold BC. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. clear - RCr OCL0. lia. }
  assert (EnZP : bv_unsigned (ev E' n0) = zp') by (rewrite EZP, <- DzpS; reflexivity).
  assert (EnZF : bv_unsigned (ev E' nZF) = zf') by (rewrite EZF, <- DzfS; reflexivity).
  assert (NZP0 : PrimInt63.eqb n0 0%uint63 = false) by (apply neq_eqb; intros X; assert (X' := f_equal to_Z X); change (to_Z 0%uint63) with 0 in X'; subst n0; alia).
  assert (NV0 : PrimInt63.eqb nV 0%uint63 = false) by (apply neq_eqb; intros X; assert (X' := f_equal to_Z X); change (to_Z 0%uint63) with 0 in X'; alia).
  assert (NCT0 : PrimInt63.eqb nCT 0%uint63 = false) by (apply neq_eqb; intros X; assert (X' := f_equal to_Z X); change (to_Z 0%uint63) with 0 in X'; alia).
  assert (KC'0 : PrimInt63.eqb kC' 0%uint63 = false) by (subst kC'; destruct D0b; [exact KC0| exact NCT0]).

  set (rZ' := set_cell8 (set_cell8 rZ 2 d2 (VP n0 wzero)) 1 d1 (VP nZF wzero)) in *.
  set (rV' := region8 [Cell 0%uint63 8%uint63 (VP kA wzero)]) in *.
  set (rC' := region8 [Cell 0%uint63 4%uint63 tsv; Cell 4%uint63 4%uint63 nsv]) in *.
  assert (NSV32 : bv_unsigned (den E' nsv) mod 2 ^ 32 = n) by (apply Z.mod_small; alia).
  assert (ROKA : region_ok segs (s_priv st) E' (ms_mem ms) kA region24).
  { apply (region24_ok segs _ E' (ms_mem ms) kA KA0); fold P_; [alia|]. intros a Ha. apply BYA. alia. }
  assert (ROKV : region_ok segs (s_priv st) E' (ms_mem ms) nV rV').
  { apply (region8_u64_ok segs _ E' (ms_mem ms) nV (VP kA wzero) P_ NV0); rewrite ?EnV; [alia| intros a Ha; apply BYV; alia| exact AV8| exact (den_VP0 E' kA wzero (weqb_refl _))]. }
  assert (ROKC : region_ok segs (s_priv st) E' (ms_mem ms) kC' rC').
  { apply (region8_u32x2_ok segs _ E' (ms_mem ms) kC' tsv t nsv n KC'0); rewrite ?EkC'; [alia| intros a Ha; apply BYC; alia| exact AT| exact TSV32h| exact AN| exact NSV32]. }
  assert (ROKZ : region_ok segs (s_priv st) E' (ms_mem ms) kZ rZ').
  { subst rZ'. apply (region_ok_set_cell8 segs (s_priv st) E' (ms_mem ms) kZ _ 1%uint63 d1 zfS).
    - apply (region_ok_set_cell8 segs (s_priv st) E' (ms_mem ms) kZ rZ 2%uint63 d2 zpS); [exact ROZ| exact (gran8_find _ _ _ _ GZP)|].
      apply bv_eq. rewrite (den_VP0 E' n0 wzero (weqb_refl _)), EnZP. reflexivity.
    - cbn [set_cell8 rg_cells]. rewrite IMap.find_add_other; [exact (gran8_find _ _ _ _ GZF)| exact (ro_bst _ _ _ _ _ _ ROZ)| intros X; discriminate X].
    - apply bv_eq. rewrite (den_VP0 E' nZF wzero (weqb_refl _)), EnZF. reflexivity. }
  assert (HIZ' : hiZ E' rZ' = hiZ E' rZ /\ loZ rZ' = loZ rZ) by (subst rZ'; split; reflexivity).
  destruct HIZ' as [HIZ' LOZ''].

  assert (INRA : forall a, inR E' kA region24 a -> inR E' kA rA a).
  { intros a Ha. unfold inR in Ha |- *. rewrite LOA', HIA'. change (loZ region24) with 0 in Ha. unfold hiZ in Ha. cbn [region24 rg_hi den] in Ha.
    rewrite wbv_unsigned, wlit_ok in Ha. change (to_Z 24%uint63) with 24 in Ha. fold P_ in Ha |- *. alia. }
  assert (HIV8 : hiZ E' rV' = 8 /\ loZ rV' = 0) by (split; [unfold hiZ; cbn [rV' region8 rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity| reflexivity]).
  assert (HIC8 : hiZ E' rC' = 8 /\ loZ rC' = 0) by (split; [unfold hiZ; cbn [rC' region8 rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity| reflexivity]).
  destruct HIV8 as [HIV8 LOV8]. destruct HIC8 as [HIC8 LOC8].
  assert (INRV : forall a, inR E' nV rV' a -> inR E' kVT rV a).
  { intros a Ha. unfold inR in Ha |- *. rewrite HIV8, LOV8, EnV in Ha. rewrite LOV', HIV'. fold B1. alia. }
  assert (INRC : forall a, inR E' kC' rC' a -> inR E' kC rC a).
  { intros a Ha. unfold inR in Ha |- *. rewrite HIC8, LOC8, EkC' in Ha. rewrite LOC', HIC'. fold BC. alia. }
  assert (INRZ : forall a, inR E' kZ rZ' a -> inR E' kZ rZ a).
  { intros a Ha. unfold inR in Ha |- *. rewrite HIZ', LOZ'' in Ha. exact Ha. }

  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E') ws) a -> FP OPS E' (op_args o) a).
  { intros a RA0 NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E') ws) _ a DEC)). auto. }

  set (vP0 := Pot.Pot.pot_val ls S0 0) in *.
  assert (PVP : Pot.Pot.pot_val (push_level ls ct n P_) S0 0 = vP0 + (88 - 2 * SZd)).
  { rewrite (Pot.Pot.pot_val_push ls ct n P_ S0 CTnv). fold vP0. unfold Pot.Pot.UNIT, Pot.Pot.objs_of. rewrite SZV. unfold OBJ_SIZE. clear. lia. }
  assert (V1 : 0 <= vP0 + (88 - 2 * SZd)).
  { rewrite <- PVP. pose proof PURE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & DL1 & _ & _).
    apply Pot.Pot.pot_val_nonneg; [exact LV'| exact DL1| exact (Pot.Pot.kids_pk_nonneg _ _ _ _ KP0)| clear; lia]. }
  assert (POTW : match sc with
                 | Some lo => bv_unsigned (ev E' nP) = vP0 + (88 - 2 * SZd) /\ vP0 + (88 - 2 * SZd) <= 2 ^ 41 /\
                              POT_BASE <= bv_unsigned (den E' lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 /\ bv_unsigned (den E' lo) = POT_BASE + vP0
                 | None => True end).
  { destruct sc as [lo|]; [| exact I].
    assert (INlo : In lo (op_args o)) by (destruct SCOK as (INP & _); exact (proj1 (INW _ INP))).
    apply (GPot.GPot.sym_word E' E fs aw ws lo nP vP0 (88 - 2 * SZd) Pfacts SCOK PRE PA0 (DR lo INlo)); [| exact V1| clear - SZ24; lia].
    rewrite EP. subst wP SZd. rewrite (DR SZ (proj1 (proj2 (INW _ INA)))). reflexivity. }
  assert (SZM : SZd <= 2 ^ 20) by (rewrite SZV; unfold OBJ_SIZE; destruct PER12 as [X|X]; rewrite X; clear - NB; lia).
  pose proof (GPot.GPot.scan_oldb E' ws sc SCOK) as OLDB.
  assert (NEWB : match sc with Some _ => POT_BASE <= bv_unsigned (den E' (VP nP GPot.GPot.POT_BASEw)) | None => True end).
  { destruct sc as [lo|]; [| exact I]. destruct POTW as (EVP & VM & _). apply (GPot.GPot.sym_newb E' (Some lo) nP). rewrite EVP. exact VM. }

  assert (NEQ1 : nV <> kA /\ nV <> kZ /\ nV <> kC' /\ kA <> kC' /\ kZ <> kC' /\ nV <> kVT /\ nCT <> kC).
  { assert (TC : to_Z kC' = to_Z kC \/ to_Z kC' = to_Z n0 + 3) by (subst kC'; destruct D0b; [left; reflexivity| right; exact TZ3]).
    assert (NACz : to_Z kA <> to_Z kC) by (intros Y; apply NAC; apply Uint63.to_Z_inj; exact Y).
    assert (NCZz : to_Z kC <> to_Z kZ) by (intros Y; apply NCZ; apply Uint63.to_Z_inj; exact Y).
    clear - TC NACz NCZz TZ2 TZ3 KA_LT KZ_LT KC_LT KVT_LT.
    repeat split; intros X; apply (f_equal to_Z) in X; lia. }
  set (KS := [kA; kVT; kZ; kC] ++ (if D0b then [] else [kS])) in *.
  set (NR := [(kA, region24); (nV, rV'); (kZ, rZ'); (kC', rC')]) in *.
  assert (NRcases : forall k r, In (k, r) NR -> (k = kA /\ r = region24) \/ (k = nV /\ r = rV') \/ (k = kZ /\ r = rZ') \/ (k = kC' /\ r = rC')).
  { intros k r Hin. subst NR. destruct Hin as [H1|[H1|[H1|[H1|[]]]]]; injection H1 as <- <-; auto. }
  assert (PARENT : forall k r, In (k, r) NR -> exists k0 r0, In k0 KS /\ IMap.find k0 (s_regs st) = Some r0 /\ PrimInt63.eqb k0 0%uint63 = false /\ rg_w r0 = true /\
            (forall a, inR E' k r a -> inR E' k0 r0 a) /\
            (k = kA -> k0 = kA) /\ (k = nV -> k0 = kVT) /\ (k = kZ -> k0 = kZ) /\ (k = kC' -> k0 = kC)).
  { intros k r Hin. destruct (NRcases k r Hin) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
    - exists kA, rA. subst KS. split; [left; reflexivity|]. split; [exact FA|]. split; [exact KA0|]. split; [exact WA|]. split; [exact INRA|].
      repeat split; intros X; try reflexivity; exfalso; [apply (proj1 NEQ1); symmetry; exact X| apply NAZ; exact X| apply (proj1 (proj2 (proj2 (proj2 NEQ1)))); exact X].
    - exists kVT, rV. subst KS. split; [right; left; reflexivity|]. split; [exact FV|]. split; [exact KV0|]. split; [exact WV|]. split; [exact INRV|].
      repeat split; intros X; try reflexivity; exfalso; [apply (proj1 NEQ1); exact X| apply (proj1 (proj2 NEQ1)); exact X| apply (proj1 (proj2 (proj2 NEQ1))); exact X].
    - exists kZ, rZ. subst KS. split; [right; right; left; reflexivity|]. split; [exact FZ|]. split; [exact KZ0|]. split; [exact WZ|]. split; [exact INRZ|].
      repeat split; intros X; try reflexivity; exfalso; [apply NAZ; symmetry; exact X| apply (proj1 (proj2 NEQ1)); symmetry; exact X| apply (proj1 (proj2 (proj2 (proj2 (proj2 NEQ1))))); exact X].
    - exists kC, rC. subst KS. split; [right; right; right; left; reflexivity|]. split; [exact FC|]. split; [exact KC0|]. split; [exact WC|]. split; [exact INRC|].
      repeat split; intros X; try reflexivity; exfalso; [apply (proj1 (proj2 (proj2 (proj2 NEQ1)))); symmetry; exact X| apply (proj1 (proj2 (proj2 NEQ1))); symmetry; exact X| apply (proj1 (proj2 (proj2 (proj2 (proj2 NEQ1))))); symmetry; exact X]. }
  assert (LENws' : Z.of_nat (length (List.filter (fun w => negb (win3_eqb w (VP kA wzero, SZ, VL (wlit 5)) || win3_eqb w (top_win kVT 16 3) || win3_eqb w (top_win kC (PrimInt63.add (wl oc) 8) 2) || negb D0b && win3_eqb w (slot_win kS))) ws
                                  ++ [top_win kC' 8 2; top_win nV 8 3; slot_win kA])) < two63).
  { rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w (VP kA wzero, SZ, VL (wlit 5)) || win3_eqb w (top_win kVT 16 3) || win3_eqb w (top_win kC (PrimInt63.add (wl oc) 8) 2) || negb D0b && win3_eqb w (slot_win kS))) ws) as FL.
    unfold two63. clear - FL WLEN. lia. }

  match goal with |- st_ok _ _ _ (setregs _ (IMap.add _ (subst_cells ?F _) _)) _ _ => set (fsub := F) in * end.
  assert (FDEN : forall v, den E' (fsub v) = den E' v).
  { assert (T1 : den E' (VP kC' (wlit 8)) = den E' (VP kC (wadd oc (wlit 8)))).
    { apply bv_eq.
      rewrite (den_VP_nowrap E' kC' (wlit 8)) by (rewrite wlit_ok, EkC'; change (to_Z 8%uint63) with 8; clear - RCr OCL0 CROOM Bc3 CEIL; lia).
      assert (W8 : w2Z (wadd oc (wlit 8)) = ocl + 8).
      { rewrite wadd_ok, wlit_ok, OCW. change (to_Z 8%uint63) with 8. apply Z.mod_small. clear - OCL0. unfold two64. lia. }
      rewrite (den_VP_nowrap E' kC (wadd oc (wlit 8))) by (rewrite W8; fold BC; clear - RCr OCL0; lia).
      rewrite EkC', W8, wlit_ok. fold BC. change (to_Z 8%uint63) with 8. clear. lia. }
    assert (T2 : den E' (VP nV (wlit 8)) = den E' (VP kVT (wlit 16))).
    { apply bv_eq.
      rewrite (den_VP_nowrap E' nV (wlit 8)) by (rewrite wlit_ok, EnV; change (to_Z 8%uint63) with 8; clear - RVr; lia).
      rewrite (den_VP_nowrap E' kVT (wlit 16)) by (rewrite wlit_ok; change (to_Z 16%uint63) with 16; fold B1; clear - RVr; lia).
      rewrite EnV, !wlit_ok. fold B1. change (to_Z 8%uint63) with 8. change (to_Z 16%uint63) with 16. clear; lia. }
    intros v. subst fsub. cbn beta.
    destruct (same_end fs v (VP kC (wadd oc (wlit 8)))) eqn:Q1.
    - rewrite T1. symmetry. exact (same_end_sound E' fs v _ Pfacts Q1).
    - destruct (same_end fs v (VP kVT (wlit 16))) eqn:Q2; [|reflexivity].
      rewrite T2. symmetry. exact (same_end_sound E' fs v _ Pfacts Q2). }
  assert (HNDUP : List.NoDup (map fst NR)).
  { subst NR. cbn [map fst]. destruct NEQ1 as (M1' & M2' & M3' & M4' & M5' & _).
    constructor; [| constructor; [| constructor; [| constructor; [intros []| constructor]]]].
    + intros [X|[X|[X|[]]]]; [exact (M1' X)| exact (NAZ (eq_sym X))| exact (M4' (eq_sym X))].
    + intros [X|[X|[]]]; [exact (M2' (eq_sym X))| exact (M3' (eq_sym X))].
    + intros [X|[]]. exact (M5' (eq_sym X)). }
  match goal with |- st_ok _ _ _ (setregs ?S1 (IMap.add _ _ ?R)) _ _ => change R with (s_regs S1) end.
  apply (st_ok_subst_cells segs OPS E' _ ms model k1 r1 fsub); [| | exact K10| exact FDEN].
  2:{ cbn [surg s_regs]. apply (proj2 (find_add_regions _ _ k1 r1 (remove_keys_bst _ _ Pbst) HNDUP)).
      right. split.
      - unfold NR. cbn [map fst In]. intros [X|[X|[X|[X|[]]]]]; [exact (N1A (eq_sym X))| | exact (N1Z (eq_sym X))|].
        + assert (X' := f_equal to_Z X). clear - X' K1_LT TZ2. lia.
        + subst kC'. destruct D0b; [exact (N1C (eq_sym X))|]. assert (X' := f_equal to_Z X). clear - X' K1_LT TZ3. lia.
      - apply (proj2 (find_remove_keys _ _ k1 r1 Pbst)). split; [| exact F1].
        unfold KS. intros X. cbn [app] in X. destruct X as [X|[X|[X|[X|X]]]]; [exact (N1A (eq_sym X))| exact (N1V (eq_sym X))| exact (N1Z (eq_sym X))| exact (N1C (eq_sym X))|].
        destruct D0b; [destruct X|]. destruct X as [X|[]]. destruct (HD1 eq_refl) as (rS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NS1 & _). exact (NS1 X). }
  match goal with |- st_ok _ _ _ (surg _ _ _ (mk_args _ _ ?W ?CA) ?NF _) _ _ => set (ws' := W) in *; set (ca' := CA) in *; set (nf := NF) in * end.

  subst ws' nf. match goal with |- st_ok _ _ _ (surg _ _ _ (mk_args _ _ (GPot.GPot.pot_sym _ _ ?W) _) (_ ++ ?NF) _) _ _ => set (ws' := W) in *; set (nf := NF) in * end.
  assert (LENP : Z.of_nat (length (GPot.GPot.pot_sym sc nP ws')) < two63) by (unfold GPot.GPot.pot_sym; rewrite GPot.GPot.pot_set_length; exact LENws').

  assert (KEPT : forall w, In w ws' -> (In w ws /\ w <> (VP kA wzero, SZ, VL (wlit 5)) /\ w <> top_win kVT 16 3 /\ w <> top_win kC (PrimInt63.add (wl oc) 8) 2 /\ (D0b = false -> w <> slot_win kS))
                                     \/ In w [slot_win kA; top_win kC' 8 2; top_win nV 8 3]).
  { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|Hw]; [left| right; destruct Hw as [<-|[<-|[<-|[]]]]; cbn [In]; auto].
    apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q.
    apply orb_false_iff in Q as [Q Q4]. apply orb_false_iff in Q as [Q Q3]. apply orb_false_iff in Q as [Q1 Q2].
    split; [exact Hw|]. split; [intros X; subst w; rewrite win3_eqb_refl in Q1; discriminate Q1|].
    split; [intros X; subst w; rewrite win3_eqb_refl in Q2; discriminate Q2|].
    split; [intros X; subst w; rewrite win3_eqb_refl in Q3; discriminate Q3|].
    intros XD X; subst w. rewrite XD in Q4. cbn [negb andb] in Q4. rewrite win3_eqb_refl in Q4. discriminate Q4. }
  assert (M5' : ls <> [] -> conts_at bm (tl (containers (u_root g) ls)) (tl ls) ->
                conts_at bm (tl (containers (u_root g) (ls ++ [nl]))) (tl (ls ++ [nl]))).
  { intros NN M5. pose proof HTY as X1. pose proof HN as X2. pose proof HP as X3. unfold u_cur_slot in X1, X2, X3. fold ls in X1, X2, X3.
    pose proof CTt as CT'. clear - NN M5 X1 X2 X3 CT'. clearbody ls. destruct ls as [|l1 ls1]; [exfalso; exact (NN eq_refl)|].
    cbn [app containers tl]. rewrite containers_app. cbn [containers]. cbn [containers tl] in M5.
    apply (proj2 (conts_at_app bm _ _ ls1 [nl] (containers_length _ _))). split; [exact M5|]. cbn [conts_at].
    rewrite <- (cur_slot_cons (u_root g) l1 ls1). subst nl. cbn [new_level lv_t lv_n lv_P]. rewrite CT'.
    split; [exact X1| split; [exact X2| split; [exact X3| exact I]]]. }
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH KS NR _ (GPot.GPot.pot_facts_push fs sc nP SZ ++ nf) (GPot.GPot.pot_next sc (PrimInt63.add n0 4))).
  -   intros k Hk. subst KS. apply in_app_iff in Hk as [Hk|Hk].
    + destruct Hk as [<-|[<-|[<-|[<-|[]]]]]; [split; [exact KA0| exists rA; auto]| split; [exact KV0| exists rV; auto]| split; [exact KZ0| exists rZ; auto]| split; [exact KC0| exists rC; auto]].
    + destruct D0b; [destruct Hk|]. destruct Hk as [<-|[]]. destruct (HD1 eq_refl) as (rS & _ & FS & _ & _ & WS & _ & _ & KS0 & _).
      split; [apply neq_eqb; exact KS0| exists rS; auto].
  -   exact HNDUP.
  -   intros k r Hin. destruct (NRcases k r Hin) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; [exact KA0| exact NV0| exact KZ0| exact KC'0].
  -   intros k r Hin. destruct (NRcases k r Hin) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; [exact ROKA| exact ROKV| exact ROKZ| exact ROKC].
  -   intros k r a Hin IR. destruct (PARENT k r Hin) as (k0 & r0 & I0 & F0 & _ & _ & SUB & _). right. exists k0, r0. auto.
  -   intros q1 u1 q2 u2 a H1 H2 NE12 [I1 I2].
    destruct (NRcases q1 u1 H1) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
    destruct (NRcases q2 u2 H2) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; try (exfalso; exact (NE12 eq_refl)).
    + exact (Pdisj kA rA kVT rV FA FV NAV KA0 KV0 (or_introl WA) a (conj (INRA a I1) (INRV a I2))).
    + exact (Pdisj kA rA kZ rZ FA FZ NAZ KA0 KZ0 (or_introl WA) a (conj (INRA a I1) (INRZ a I2))).
    + exact (Pdisj kA rA kC rC FA FC NAC KA0 KC0 (or_introl WA) a (conj (INRA a I1) (INRC a I2))).
    + exact (Pdisj kVT rV kA rA FV FA (fun X => NAV (eq_sym X)) KV0 KA0 (or_introl WV) a (conj (INRV a I1) (INRA a I2))).
    + exact (Pdisj kVT rV kZ rZ FV FZ NVZ KV0 KZ0 (or_introl WV) a (conj (INRV a I1) (INRZ a I2))).
    + exact (Pdisj kVT rV kC rC FV FC NVC KV0 KC0 (or_introl WV) a (conj (INRV a I1) (INRC a I2))).
    + exact (Pdisj kZ rZ kA rA FZ FA (fun X => NAZ (eq_sym X)) KZ0 KA0 (or_introl WZ) a (conj (INRZ a I1) (INRA a I2))).
    + exact (Pdisj kZ rZ kVT rV FZ FV (fun X => NVZ (eq_sym X)) KZ0 KV0 (or_introl WZ) a (conj (INRZ a I1) (INRV a I2))).
    + exact (Pdisj kZ rZ kC rC FZ FC (fun X => NCZ (eq_sym X)) KZ0 KC0 (or_introl WZ) a (conj (INRZ a I1) (INRC a I2))).
    + exact (Pdisj kC rC kA rA FC FA (fun X => NAC (eq_sym X)) KC0 KA0 (or_introl WC) a (conj (INRC a I1) (INRA a I2))).
    + exact (Pdisj kC rC kVT rV FC FV (fun X => NVC (eq_sym X)) KC0 KV0 (or_introl WC) a (conj (INRC a I1) (INRV a I2))).
    + exact (Pdisj kC rC kZ rZ FC FZ NCZ KC0 KZ0 (or_introl WC) a (conj (INRC a I1) (INRZ a I2))).
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E' aw), (map (wden E') (GPot.GPot.pot_sym sc nP ws')), (map (den E') ca'), LB.
    split; [apply mk_args_sound; exact LENP|].

    split; [apply (aw_keep segs IMGX AW _ _ (map (wden E') ws')); [| exact (GPot.GPot.wins_keep_pot_set E' sc _ _ OLDB NEWB LB)];
            apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E' 1 g LB ws ws' P O Wk);
            [intros x Hx; destruct (KEPT x Hx) as [(Hx' & _)|Hnew]; [left; exact Hx'| right; left];
             destruct Hnew as [<-|[<-|[<-|[]]]]; apply UOK.kind_sub; vm_compute; reflexivity
            |intros x Hx; destruct (win3_eqb x (VP kA wzero, SZ, VL (wlit 5))) eqn:Q1;
             [right; left; apply win3_eqb_eq in Q1; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             destruct (win3_eqb x (top_win kVT 16 3)) eqn:Q2;
             [right; left; apply win3_eqb_eq in Q2; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             destruct (win3_eqb x (top_win kC (PrimInt63.add (wl oc) 8) 2)) eqn:Q3;
             [right; left; apply win3_eqb_eq in Q3; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             destruct (win3_eqb x (slot_win kS)) eqn:Q4;
             [right; left; apply win3_eqb_eq in Q4; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             left; subst ws'; apply in_or_app; left; apply filter_In; split; [exact Hx|]; cbv beta; rewrite Q1, Q2, Q3, Q4; rewrite andb_false_r; reflexivity]|]. split.
    +
      apply (GPot.GPot.windows_wf_pot_set E' sc _ _ OLDB NEWB LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPT x Hx) as [(Hx' & _)|Hnew]; [exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx'))|].
      destruct Hnew as [<-|[<-|[<-|[]]]].
      * rewrite slot_win_top, top_win_den. fold P_. change (to_Z 24%uint63) with 24. change (to_Z 4%uint63) with 4.
        unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [unfold chunk_lo, chunk_hi, CHUNK_HDR in *; alia|].
        right; right. split; [unfold K_SUB; alia|]. exists (chunk_block h). split; [exact (proj1 O _ OWNh)|].
        intros a Ha. unfold in_iv, chunk_block, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold chunk_lo, chunk_hi, CHUNK_HDR in *. alia.
      * rewrite top_win_den, EkC'. change (to_Z 8%uint63) with 8. change (to_Z 2%uint63) with 2.
        unfold window_wf. cbn [w_lo w_len w_kind w_iv]. unfold v_capend in CROOM. rewrite EC in CROOM.
        split; [alia|]. split; [alia|]. split; [alia|].
        right; right. split; [unfold K_SUB; alia|]. exists (cstk_block g). split; [exact (proj1 O _ (owned_cstk g))|].
        intros a Ha. unfold in_iv, cstk_block, v_bytes, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. rewrite EC. alia.
      * rewrite top_win_den, EnV. change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3.
        unfold window_wf. cbn [w_lo w_len w_kind w_iv]. unfold v_capend in VROOM. rewrite EV8 in VROOM.
        split; [alia|]. split; [alia|]. split; [alia|].
        right; right. split; [unfold K_SUB; alia|]. exists (vstk_block g). split; [exact (proj1 O _ (owned_vstk g))|].
        intros a Ha. unfold in_iv, vstk_block, v_bytes, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. rewrite EV8. alia.
    +
      cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. subst ca'. cbn [map decode_uc].
      exists g'. split; [| split; [exact PURE'| split; [exact OWNOK'| split; [| split]]]].
      *
        enough (LINK' : link (UC (bv_unsigned (den E' (VP k1 oR))) (bv_unsigned (den E' cb)) (bv_unsigned (den E' (VP kC' (wlit 8)))) (bv_unsigned (den E' ccap))
                                (bv_unsigned (den E' vb)) (bv_unsigned (den E' (VP nV (wlit 8)))) (bv_unsigned (den E' vcap))
                                (bv_unsigned (den E' (VP n0 wzero))) (bv_unsigned (den E' (VP nZF wzero))) (bv_unsigned (den E' c0))
                                (bv_unsigned (den E' (VP kA wzero))) (bv_unsigned (den E' tsv)) (bv_unsigned (den E' nsv))
                                (bv_unsigned (den E' (if D0b then tyH else rootT))) (bv_unsigned (den E' (if D0b then sv_ext_c false 0%uint63 4%uint63 nH else n1)))
                                (bv_unsigned (den E' (if D0b then VP kA wzero else P1)))) g') by exact LINK'.
        unfold link. subst g'. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels u_cur_slot c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
        rewrite PC1, PC2, PC3, PV1, PV2, PV3, ZCp, ZCf, ZCh.
        split; [exact Lroot|]. split; [exact Lcb|]. split; [rewrite LCE', (den_VP_nowrap E' kC' (wlit 8)) by (rewrite wlit_ok, EkC'; change (to_Z 8%uint63) with 8; unfold v_capend in CROOM; alia); rewrite wlit_ok, EkC'; change (to_Z 8%uint63) with 8; alia|].
        split; [exact Lccap|]. split; [exact Lvb|].
        split; [rewrite LVE', (den_VP_nowrap E' nV (wlit 8)) by (rewrite wlit_ok, EnV; change (to_Z 8%uint63) with 8; unfold v_capend in VROOM; alia); rewrite wlit_ok, EnV; change (to_Z 8%uint63) with 8; alia|].
        split; [exact Lvcap|]. split; [symmetry; rewrite (den_VP0 E' n0 wzero (weqb_refl _)); exact EnZP|].
        split; [symmetry; rewrite (den_VP0 E' nZF wzero (weqb_refl _)); exact EnZF|]. split; [exact Lc0|].
        intros _. split; [unfold u_cur_slot; cbn [u_root u_vis u_levels]; rewrite push_level_cur_slot, (den_VP0 E' kA wzero (weqb_refl _)) by exact CTnv; reflexivity|].
        split; [exists nl; split; [exact LAST'| split; [subst nl; cbn [new_level lv_t]; rewrite CTc, TSV; reflexivity| subst nl; cbn [new_level lv_rest]; reflexivity]]|].
        destruct D0b.
        -- pose proof (DZ eq_refl) as NIL. exists nl, []. rewrite NIL. split; [reflexivity|]. subst nl. cbn [new_level lv_t lv_n lv_P].
           rewrite CTt, TYV, (den_VP0 E' kA wzero (weqb_refl _)), den_sv_ext_c, zx_ext_den. repeat split; try reflexivity. symmetry. exact NH32h.
        -- pose proof (DNZ eq_refl) as NN. destruct (LD NN) as (_ & _ & l1 & ls1 & EL & R1 & R2 & R3). exists l1, (ls1 ++ [nl]).
           unfold push_level. fold ls. rewrite EL. split; [reflexivity|]. auto.
      *
        apply GPot.GPot.wins_ok_pot_set.
        unfold wins_ok. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). intros NK.
        destruct (KEPT x Hx) as [(Hx' & NA & NVW & NCW & NSW)|Hnew].
        -- pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hx') NK) as [DJ|[NB1 SO]].
           ++ left. rewrite OWN'. exact DJ.
           ++ exfalso.
              unfold sub_ok in SO. cbv zeta in SO. destruct SO as [(KD & _)|[(KD & _)|[(KD & _)|(KD & _)]]].
              ** pose proof (only_kind_sound E' 2 _ ws OK2 x Hx' KD) as X. injection X as <-. exact (NCW eq_refl).
              ** pose proof (only_kind_sound E' 3 _ ws OK3 x Hx' KD) as X. injection X as <-. exact (NVW eq_refl).
              ** destruct D0b; [pose proof (only_kind_sound E' 4 _ ws (HD0 eq_refl) x Hx' KD) as X; discriminate X|].
                 destruct (HD1 eq_refl) as (rS & _ & _ & _ & _ & _ & _ & OK4 & _). pose proof (only_kind_sound E' 4 _ ws OK4 x Hx' KD) as X. injection X as <-. exact (NSW eq_refl eq_refl).
              ** pose proof (only_kind_sound E' 5 _ ws OK5 x Hx' KD) as X. injection X as <-. exact (NA eq_refl).
        -- right. destruct Hnew as [<-|[<-|[<-|[]]]].
           ++ rewrite slot_win_top, top_win_den. fold P_. change (to_Z 24%uint63) with 24. change (to_Z 4%uint63) with 4. cbn [w_kind]. split; [unfold K_BLOCK; alia| exact SUBS].
           ++ rewrite top_win_den, EkC'. change (to_Z 8%uint63) with 8. change (to_Z 2%uint63) with 2. cbn [w_kind]. split; [unfold K_BLOCK; alia| exact SUBC].
           ++ rewrite top_win_den, EnV. change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3. cbn [w_kind]. split; [unfold K_BLOCK; alia| exact SUBV].
      *
        destruct M as (M1 & M2 & M3 & M4 & M5 & M6). fold bm ls in M1, M2, M3, M4, M5, M6.
        unfold mem_ok. subst g'. cbn [u_levels u_cstk u_vstk u_zone u_root u_vis]. fold bm. rewrite PC2, PV2, ZCc.
        split; [| split; [| split; [| split; [exact M4| split]]]].
        --
           unfold push_level. rewrite removelast_snoc.
           destruct D0b; [rewrite (DZ eq_refl); exact I|].
           pose proof (DNZ eq_refl) as NN. destruct (LD NN) as (_ & (lD & HLD & TD1 & TD2) & _).
           destruct (top_level g lD HLD) as (ls0 & ELS & RL & _). fold ls in ELS, RL. rewrite ELS. apply (proj2 (cstk_at_app bm _ ls0 [lD])).
           rewrite <- RL. split; [exact M1|]. cbn [cstk_at]. rewrite RL.
           assert (LEN0 : v_begin (u_cstk g) + 8 * Z.of_nat (length ls0) = BC).
           { assert (LL : Z.of_nat (length ls) = Z.of_nat (length ls0) + 1) by (clear - ELS; rewrite ELS, length_app; cbn [length]; lia).
             change (ocl = 8) in OCLD. clear - DVAL DLEN LL OCLD. lia. }
           rewrite LEN0. destruct (HD1 eq_refl) as (rS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X4 & X5).
           pose proof (proj1 (Forall_forall _ _) LV lD ltac:(fold ls; rewrite ELS; apply in_app_iff; right; left; reflexivity)) as (LV1 & LV2 & LV3 & _).
           rewrite <- TD1, Z.mod_small in X4 by (clear; destruct (lv_t lD); cbn; lia).
           rewrite <- TD2, Z.mod_small in X5 by (unfold LIMIT in LV3; clear - LV1 LV2 LV3; lia).
           split; [exact X4| split; [exact X5| exact I]].
        --
           intros _. destruct D0b.
           ++ pose proof (DZ eq_refl) as NIL. rewrite V0 in AV0.
              assert (VB1 : v_begin (u_vstk g) = B1) by (pose proof VEND as X; rewrite LVE', DLEN, NIL in X; cbn [length] in X; alia).
              rewrite VB1. rewrite <- Lroot in AV0. exact AV0.
           ++ exact (M2 (DNZ eq_refl)).
        --
           unfold push_level. rewrite removelast_snoc.
           destruct D0b; [rewrite (DZ eq_refl); exact I|].
           pose proof (DNZ eq_refl) as NN. destruct (LD NN) as (SL & (lD & HLD & _) & _).
           destruct (top_level g lD HLD) as (ls0 & ELS & RL & _). fold ls in ELS, RL. rewrite ELS. apply (proj2 (vstk_at_app bm _ ls0 [lD])).
           rewrite <- RL. split; [exact M3|]. cbn [vstk_at]. rewrite RL.
           assert (LEN0 : v_begin (u_vstk g) + 8 + 8 * Z.of_nat (length ls0) = B1).
           { assert (LL : Z.of_nat (length ls) = Z.of_nat (length ls0) + 1) by (clear - ELS; rewrite ELS, length_app; cbn [length]; lia).
             pose proof VEND as X. rewrite LVE', DLEN in X. clear - X LL. lia. }
           rewrite LEN0. split; [| exact I]. rewrite V0 in AV0.
           replace (lv_slot lD) with (u_cur_slot g) by (unfold u_cur_slot; fold ls; rewrite ELS; apply cur_slot_snoc). rewrite SL. exact AV0.
        --
           unfold push_level. destruct D0b.
           ++ rewrite (DZ eq_refl). cbn. exact I.
           ++ exact (M5' (DNZ eq_refl) M5).
        --
           exact (completed_ok_push bm (u_zone g) z' ls ct n P_ CTnv ZG FRESH M6).
      *
        split; [intros X; discriminate X|].
        destruct AX as (X & A). split.
        { split.
          { exists (X + 1). subst g'. cbn [u_levels u_zone]. unfold push_level.
            pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PDL & _ & _).
            apply Acct.acct_push; [| exact (new_level_k ct n P_ CTnv)| exact (Acct.u_D_length g PDL)].
            eapply Acct.acct_frame; [| exact A]. intros l i ox Hl Hi T.
            eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T]. }

          intros _. exists S0. subst g'. cbn [u_levels u_zone]. split.
          - unfold push_level. apply Pot.Pot.kids_pk_push; [| exact (new_level_k ct n P_ CTnv)].
            apply (Pot.Pot.kids_pk_frame bm bm (u_zone g) z' ls S0); [| exact KP0]. intros l i ox Hl Hi T.
            eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T].
          - apply (GPot.GPot.pot_at_set E' ws ws' sc _ _ SCOK).
            + intros x Hx. destruct (KEPT x Hx) as [(Hx' & _)|Hnew]; [left; exact Hx'| right].
              destruct Hnew as [<-|[<-|[<-|[]]]]; apply kind_ne; vm_compute; reflexivity.
            + destruct sc as [lo|]; [| exact I]. destruct POTW as (EVP & VM & _).
              rewrite (GPot.GPot.pw_den_lo E' nP ltac:(rewrite EVP; exact VM)), EVP, PVP. reflexivity. }

        apply GPot.GPot.seal_ok_pot_set.
        replace (z_chunks (u_zone g')) with (z_chunks (u_zone g)) by (subst g'; cbn [u_zone]; symmetry; exact ZCc).
        apply (SealX.seal_ok_map _ _ _ _ _ SE). intros x Hx.
        destruct (KEPT x Hx) as [(Hx' & _)|Hnew]; [left; exact Hx'| right].
        destruct Hnew as [<-|[<-|[<-|[]]]]; apply kind_ne; vm_compute; reflexivity.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') (GPot.GPot.pot_sym sc nP ws')) _ a (mk_args_sound E' 1%uint63 aw _ _ LENP))) in FPa as (RA0 & NI & NW).
    assert (NW' : ~ in_ws (map (wden E') ws') a) by (intros X; apply NW; apply GPot.GPot.in_ws_pot_set; exact X). clear NW. rename NW' into NW.
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E' w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E' ws' a)). exists w. auto. }
    split.
    + destruct (in_ws_dec (map (wden E') ws) a) as [IW|NIW]; [| left; exact (FPold a RA0 NI NIW)].
      right. apply (proj1 (in_ws_map_iff E' ws a)) in IW as (w & Hw & Hin).

      assert (DEAD : w = (VP kA wzero, SZ, VL (wlit 5)) \/ w = top_win kVT 16 3 \/ w = top_win kC (PrimInt63.add (wl oc) 8) 2 \/ (D0b = false /\ w = slot_win kS)).
      { destruct (win3_eqb w (VP kA wzero, SZ, VL (wlit 5))) eqn:Q1; [left; exact (win3_eqb_eq _ _ Q1)|].
        destruct (win3_eqb w (top_win kVT 16 3)) eqn:Q2; [right; left; exact (win3_eqb_eq _ _ Q2)|].
        destruct (win3_eqb w (top_win kC (PrimInt63.add (wl oc) 8) 2)) eqn:Q3; [right; right; left; exact (win3_eqb_eq _ _ Q3)|].
        destruct (negb D0b && win3_eqb w (slot_win kS)) eqn:Q4.
        - apply andb_prop in Q4 as [Q4 Q5]. right; right; right. split; [destruct D0b; [discriminate Q4| reflexivity]| exact (win3_eqb_eq _ _ Q5)].
        - exfalso. apply (NWi w); [| exact Hin]. subst ws'. apply in_app_iff. left. apply filter_In. split; [exact Hw|]. rewrite Q1, Q2, Q3, Q4. reflexivity. }
      destruct DEAD as [->|[->|[->|[HD ->]]]].
      *
        exists kA, rA. split; [subst KS; left; reflexivity|]. split; [exact FA|].
        unfold wden, w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. rewrite (den_VP0 E' kA wzero (weqb_refl _)) in Hin. fold P_ SZd in Hin.
        unfold inR. rewrite LOA', HIA'. fold P_. alia.
      * exists kVT, rV. split; [subst KS; right; left; reflexivity|]. split; [exact FV|].
        rewrite top_win_den in Hin. unfold w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. fold B1 in Hin. change (to_Z 16%uint63) with 16 in Hin.
        unfold inR. rewrite LOV', HIV'. fold B1. alia.
      * exists kC, rC. split; [subst KS; right; right; right; left; reflexivity|]. split; [exact FC|].
        rewrite top_win_den, L8 in Hin. unfold w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. fold BC in Hin.
        unfold inR. rewrite LOC', HIC'. fold BC. alia.
      * destruct (HD1 HD) as (rS & SL & FS & LOS & HIS & _). exists kS, rS. split; [subst KS; rewrite HD; apply in_app_iff; right; left; reflexivity|]. split; [exact FS|].
        rewrite slot_win_top, top_win_den in Hin. unfold w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. change (to_Z 24%uint63) with 24 in Hin.
        unfold inR, loZ, hiZ. rewrite LOS, HIS. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. change (keyZ 0%uint63) with 0. alia.
    + intros k r Hin IR. destruct (NRcases k r Hin) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
      * apply (NWi (slot_win kA)); [subst ws'; apply in_app_iff; right; do 2 right; left; reflexivity|].
        rewrite slot_win_top, top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold P_. change (to_Z 24%uint63) with 24.
        unfold inR in IR. change (loZ region24) with 0 in IR. unfold hiZ in IR. cbn [region24 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 24%uint63) with 24 in IR. fold P_ in IR. alia.
      * apply (NWi (top_win nV 8 3)); [subst ws'; apply in_app_iff; right; right; left; reflexivity|].
        rewrite top_win_den, EnV. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. change (to_Z 8%uint63) with 8.
        unfold inR in IR. rewrite HIV8, LOV8, EnV in IR. alia.
      *
        apply (NWi (top_win kZ 56 1)).
        -- subst ws'. apply in_app_iff. left. apply filter_In. split; [exact EXZ|].
           rewrite (win3_eqb_kind_false (top_win kZ 56 1) (VP kA wzero, SZ, VL (wlit 5)) 1 5 eq_refl eq_refl ltac:(alia)).
           rewrite (win3_eqb_kind_false (top_win kZ 56 1) (top_win kVT 16 3) 1 3 eq_refl eq_refl ltac:(alia)).
           rewrite (win3_eqb_kind_false (top_win kZ 56 1) (top_win kC (PrimInt63.add (wl oc) 8) 2) 1 2 eq_refl eq_refl ltac:(alia)).
           rewrite (win3_eqb_kind_false (top_win kZ 56 1) (slot_win kS) 1 4 eq_refl eq_refl ltac:(alia)).
           rewrite andb_false_r. reflexivity.
        -- rewrite top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold ZB. change (to_Z 56%uint63) with 56.
           unfold inR in IR. rewrite HIZ', LOZ'', LOZ' in IR. fold ZB in IR. unfold hiZ in IR. rewrite HIZ56 in IR. cbn [den] in IR.
           rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 56%uint63) with 56 in IR. alia.
      * apply (NWi (top_win kC' 8 2)); [subst ws'; apply in_app_iff; right; left; reflexivity|].
        rewrite top_win_den, EkC'. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. change (to_Z 8%uint63) with 8.
        unfold inR in IR. rewrite HIC8, LOC8, EkC' in IR. alia.
  -
    assert (CE8 : BC + ocl + 8 <= v_capend (u_cstk g)) by alia.
    assert (CAPC : v_capend (u_cstk g) <= two62Z) by (unfold v_capend; rewrite EC; unfold two62Z; alia).
    assert (CAPV : v_capend (u_vstk g) <= two62Z) by (unfold v_capend; rewrite EV8; unfold two62Z; alia).
    assert (CHI62 : zp + zf <= two62Z) by (rewrite <- CHI; unfold chunk_hi, CHUNK_HDR, two62Z; alia).
    apply Forall_app. split.
    {
      destruct sc as [lo|]; [| constructor]. destruct POTW as (EVP & VM & B & VLO).
      apply (GPot.GPot.pot_facts_push_hold E' lo nP SZ (vP0 + (88 - 2 * SZd)) B EVP); [clear - V1 VM; lia| fold SZd; clear - SZ24 SZM; lia| fold SZd; rewrite VLO; clear; lia| exact Pfacts]. }
    subst nf. constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' nV wzero (weqb_refl _)), EnV, (den_VP_nowrap E' kVT (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; alia).
      rewrite wlit_ok. reflexivity. }
    constructor.
    { cbn [fact_holds]. rewrite <- Lcb, (den_VP_nowrap E' kC' (wlit 8)) by (rewrite wlit_ok, EkC'; change (to_Z 8%uint63) with 8; unfold two62Z in CAPC; alia).
      rewrite wlit_ok, EkC'. change (to_Z 8%uint63) with 8. pose proof CROOM. rewrite LCE', CEND in *. pose proof VC2. alia. }
    constructor.
    { cbn [fact_holds]. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. rewrite EnZP, ZP1, SZV.
      rewrite Z.add_mod, (P8h : P_ mod 8 = 0) by alia. unfold OBJ_SIZE. replace (24 * per ct * n) with ((3 * per ct * n) * 8) by alia. rewrite Z_mod_mult. reflexivity. }
    constructor.
    { cbn [fact_holds]. rewrite <- Lccap, (den_VP_nowrap E' kC' (wlit 8)) by (rewrite wlit_ok, EkC'; change (to_Z 8%uint63) with 8; unfold two62Z in CAPC; clear - RCr OCL0 CROOM CAPC; lia).
      rewrite wlit_ok, EkC'. change (to_Z 8%uint63) with 8. clear - CROOM. lia. }
    constructor.
    { cbn [fact_holds]. rewrite <- Lvcap, (den_VP_nowrap E' nV (wlit 8)) by (rewrite wlit_ok, EnV; change (to_Z 8%uint63) with 8; unfold two62Z in CAPV; clear - RVr VROOM CAPV; lia).
      rewrite wlit_ok, EnV. change (to_Z 8%uint63) with 8. clear - VROOM. lia. }
    apply Forall_app. split.
    { destruct D0b; [constructor|]. change (ocl = 8) in OCLD. constructor.
      - cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' nCT wzero (weqb_refl _)), EnCT, (den_VP_nowrap E' kC (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; clear - RCr OCL0; lia).
        rewrite wlit_ok. reflexivity.
      - apply (top_facts_sound E' fs cb nCT Pfacts); rewrite EnCT, <- Lcb.
        + pose proof DVAL as DV. rewrite OCLD in DV. pose proof CROOM as CR. rewrite OCLD in CR. pose proof VC2 as X. rewrite SC in X.
          clear - DV CR CAPC X DLEN. unfold two62Z in *. lia.
        + replace (BC + 8 - v_begin (u_cstk g)) with (u_D g * 8) by (clear - DVAL OCLD; rewrite OCLD in DVAL; lia). apply Z_mod_mult. }
    apply Forall_app. split.
    { apply (top_facts_sound E' fs vb nV Pfacts); rewrite EnV, <- Lvb.
      - clear - LVE' VEND VROOM CAPV DLEN. unfold two62Z in *. lia.
      - replace (B1 + 8 - v_begin (u_vstk g)) with ((u_D g + 1) * 8) by (clear - LVE' VEND; lia). apply Z_mod_mult. }
    apply Forall_app. split.
    { apply (zp_facts_sound E' fs kA n0 Pfacts). rewrite EnZP, ZP1. fold P_. clear - SZ24 ZHI CHI62. unfold two62Z in *. lia. }
    apply (zf_facts_sound E' fs zfree nZF Pfacts). rewrite EnZF, ZFV. clear - ZP1 ZP2 ZLE SZ24 RF. lia.
Qed.

Theorem g1_sound : contract_sound segs OPS MP PB g1_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g1_contract c_apply] in HAP.
  destruct (g1_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold g1_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HAP as <-. destruct (g1_sound_main E st ms model st' HS AP) as (E' & HX & HS').
    exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS').
  - exfalso. unfold g1_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G1.
