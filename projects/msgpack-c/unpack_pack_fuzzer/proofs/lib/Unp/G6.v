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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin G4 G1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G6.

Definition two40Z : Z := 1099511627776.

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

Definition region16 (c0 c1 : slot) : region :=
  Region 0%uint63 (VL (wlit 16%uint63)) true BGNone (IMap.add 1%uint63 (Gran false c1) (IMap.add 0%uint63 (Gran false c0) IMap.empty)).
Definition empty_region (L : Z) : region := Region 0%uint63 (VL (wlit (Uint63.of_Z L))) true BGNone IMap.empty.

Definition elem_cells (isV : bool) (r : region) (g : int) : option slot :=
  match IMap.find g (rg_cells r) with
  | Some gr =>
      match isV, g_cells gr with
      | true, [Cell i w p] =>
          if PrimInt63.eqb i 0%uint63 && PrimInt63.eqb w 8%uint63 then Some (g_cells gr) else None
      | false, [Cell i1 w1 t; Cell i2 w2 n] =>
          if PrimInt63.eqb i1 0%uint63 && PrimInt63.eqb w1 4%uint63 && PrimInt63.eqb i2 4%uint63 && PrimInt63.eqb w2 4%uint63
          then Some (g_cells gr) else None
      | _, _ => None
      end
  | None => None
  end.

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
                        if wt kd || Z.ltb (to_Z (wl kd)) 2 then true else
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

Section WithPc.
Variable MEMCPY_PC : int.
Variable isV : bool.

Definition KD : int := if isV then 3%uint63 else 2%uint63.

Definition g6_apply (st : sstate) : option (list sstate) :=
  match the_op st, call_pre st with
  | Some (md, aw, ws, ca), Some r =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
          let b := if isV then vb else cb in let e := if isV then ve else ce in let cap := if isV then vcap else ccap in
          match b, e, cap with
          | VP kB ob, VP kT oe, VP kB' oc =>
              let L := w2Z oc in let dx := getr st X10 in let n12 := getr st X12 in
              match dst_anchor dx n12 L with
              | Some kN =>
                  let wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63)) in
                  let wT := top_win kT 8%uint63 KD in
                  if PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 8%uint63) && negb (wt oc)
                     && (16 <=? L) && (L mod 8 =? 0) && (L <? two40Z)
                     && negb (PrimInt63.eqb kB 0%uint63) && negb (PrimInt63.eqb kT 0%uint63) && negb (PrimInt63.eqb kN 0%uint63)
                     && negb (PrimInt63.eqb kT kB) && negb (PrimInt63.eqb kN kB) && negb (PrimInt63.eqb kN kT)
                     && Z.ltb (Z.of_nat (length ws)) 4000
                     && sv_eqb (getr st X11) b && len_ok n12 e b L
                     && implied fs (FULe e cap) && implied fs (FULe cap e)
                     && existsb (win3_eqb wN) ws && G4.no_other_at kN wN ws
                     && existsb (win3_eqb wT) ws && only_kind (to_Z KD) (Some wT) ws
                     && PrimInt63.leb 3%uint63 (find_align fs kN) && G4.range_nz fs kN
                     && match IMap.find kB R with None => true | Some _ => false end
                     && G4.kinds_lit ws && other_blocks_ok fs R kN ws && sub_windows_ok R kN wT ws
                  then
                  match IMap.find kN R, IMap.find kT R with
                  | Some rN, Some rT =>
                      if PrimInt63.eqb (rg_lo rN) 0%uint63 && sv_eqb (rg_hi rN) (VL (wlit (Uint63.of_Z (2 * L)))) && rg_w rN
                         && match rg_bg rN with BGNone | BGUnk => true | _ => false end
                         && PrimInt63.eqb (rg_lo rT) 0%uint63 && sv_eqb (rg_hi rT) (VL (wlit 8%uint63)) && rg_w rT
                      then
                      match elem_cells isV rT 0%uint63, elem_cells isV rN (Uint63.of_Z (L / 8)) with
                      | Some topc, Some newc =>
                          let nT := PrimInt63.add n0 15%uint63 in
                          let st1 := clobber st in

                          let st1' := setregs st1 (IMap.add kN (empty_region (2 * L)) (s_regs st1)) in
                          let st2 := repl_regs kept_r5 dx (VP kN wzero) (setr st1' X10 (VP kN wzero)) in
                          let st3 := setpc st2 r in
                          let rT' := region16 topc newc in
                          let rB' := empty_region L in
                          let ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws
                                     ++ [(VP kB wzero, VL oc, VL (wlit 1%uint63)); top_win nT 16%uint63 KD] in
                          let b' := VP kN wzero in let e' := VP nT (wlit 8%uint63) in let cap' := VP kN (wlit (Uint63.of_Z (2 * L))) in
                          let ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
                                     else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] in
                          let nf := [FEq (VP nT wzero) (VP kN (wlit (Uint63.of_Z (L - 8)))); FULt b' e'; FULe e' cap';
                                     FEq (VAlu ALU_SUB e' b') (VAlu ALU_SUB e b)]
                                    ++ G4.anchor_facts fs kN (L - 8) (L - 8) nT
                                    ++ (if PrimInt63.leb 3%uint63 (find_align fs kN) then [FAlign nT 3%uint63] else []) in
                          Some [surg st3 [kN; kT] [(nT, rT'); (kB, rB')] (mk_args 1%uint63 aw ws' ca') nf (PrimInt63.add n0 16%uint63)]
                      | _, _ => None
                      end
                      else None
                  | _, _ => None
                  end
                  else None
              | None => None
              end
          | _, _, _ => None
          end
      | _ => None
      end
      else None
  | _, _ => None
  end.

Definition g6_contract : contract := Contract MEMCPY_PC g6_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
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

Lemma cstk_at_shift : forall ls (bm bm' : bmem) a a',
  (forall i, 0 <= i < 8 * Z.of_nat (length ls) -> bm' (a' + i) = bm (a + i)) -> cstk_at bm a ls -> cstk_at bm' a' ls.
Proof.
  induction ls as [|l ls IH]; intros bm bm' a a' H C; [exact I|]. cbn [cstk_at] in C |- *. destruct C as (C1 & C2 & C3).
  cbn [length] in H. rewrite Nat2Z.inj_succ in H.
  split; [| split].
  - unfold u32_at in *. rewrite (rdZ_shift bm bm' 4 a a'); [exact C1|]. intros i Hi. apply H. lia.
  - unfold u32_at in *. rewrite (rdZ_shift bm bm' 4 (a + 4) (a' + 4)); [exact C2|]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
  - apply (IH bm bm' (a + 8) (a' + 8)); [| exact C3]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
Qed.

Lemma vstk_at_shift : forall ls (bm bm' : bmem) a a',
  (forall i, 0 <= i < 8 * Z.of_nat (length ls) -> bm' (a' + i) = bm (a + i)) -> vstk_at bm a ls -> vstk_at bm' a' ls.
Proof.
  induction ls as [|l ls IH]; intros bm bm' a a' H C; [exact I|]. cbn [vstk_at] in C |- *. destruct C as (C1 & C2).
  cbn [length] in H. rewrite Nat2Z.inj_succ in H.
  split.
  - unfold u64_at in *. rewrite (rdZ_shift bm bm' 8 a a'); [exact C1|]. intros i Hi. apply H. lia.
  - apply (IH bm bm' (a + 8) (a' + 8)); [| exact C2]. intros i Hi. rewrite <- !Z.add_assoc. apply H. lia.
Qed.

Lemma slot_ok_shift : forall E (m m' : word -> option byte) A A' cs,
  slot_ok segs E m A cs -> (forall i, 0 <= i < 8 -> rb segs m' (A' + i) = rb segs m (A + i)) -> slot_ok segs E m' A' cs.
Proof.
  intros E m m' A A' cs [SS FA] RB. split; [exact SS|]. apply Forall_forall. intros c Hc.
  pose proof (proj1 (Forall_forall _ _) FA c Hc) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [exact B3|].
  intros i Hi. rewrite <- Z.add_assoc, (RB (to_Z (c_idx c) + i)) by lia. rewrite Z.add_assoc. exact (B4 i Hi).
Qed.

Lemma region16_ok : forall priv E m k c0 c1,
  PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + 16 < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + 16 -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  slot_ok segs E m (bv_unsigned (ev E k)) c0 -> slot_ok segs E m (bv_unsigned (ev E k) + 8) c1 ->
  region_ok segs priv E m k (region16 c0 c1).
Proof.
  intros priv E m k c0 c1 K R BY S0 S1. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  assert (HI : hiZ E (region16 c0 c1) = 16) by (unfold hiZ; cbn [region16 rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (LO : loZ (region16 c0 c1) = 0) by reflexivity.
  assert (CIN : forall base s c i, slot_ok segs E m base s -> In c s -> 0 <= i < to_Z (c_w c) -> 0 <= to_Z (c_idx c) + i < 8).
  { intros base s c i [_ FA] Hc Hi. pose proof (proj1 (Forall_forall _ _) FA c Hc) as (B1 & B2 & B3 & _). lia. }
  apply (region_ok_fresh segs priv E m k _ K).
  - cbn [region16 rg_cells]. apply IMap.bst_add. apply IMap.bst_add. exact I.
  - reflexivity.
  - rewrite LO. lia.
  - rewrite HI. lia.
  - intros a Ha. rewrite LO, HI in Ha. apply BY. lia.
  - intros g gr F. cbn [region16 rg_cells] in F.
    destruct (Uint63.eqb g 1) eqn:G1.
    + apply Uint63.eqb_correct in G1. subst g. rewrite IMap.find_add_same in F by (apply IMap.bst_add; exact I). injection F as <-. cbn [g_cells].
      change (keyZ 1%uint63) with 1. replace (bv_unsigned (ev E k) + 8 * 1) with (bv_unsigned (ev E k) + 8) by lia. split; [exact S1|].
      intros c i Hc Hi. pose proof (CIN _ _ c i S1 Hc Hi). rewrite LO, HI. lia.
    + apply Uint63.eqb_false_correct in G1. rewrite IMap.find_add_other in F by (first [apply IMap.bst_add; exact I | congruence]).
      destruct (Uint63.eqb g 0) eqn:G0.
      * apply Uint63.eqb_correct in G0. subst g. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
        change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split; [exact S0|].
        intros c i Hc Hi. pose proof (CIN _ _ c i S0 Hc Hi). rewrite LO, HI. lia.
      * apply Uint63.eqb_false_correct in G0. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma range_nz_sound : forall E fs k, facts_hold E fs -> G4.range_nz fs k = true -> bv_unsigned (ev E k) <> 0.
Proof.
  intros E fs k FH H. unfold G4.range_nz in H. destruct (find_range fs k) as [[lo hi]|] eqn:FR; [|discriminate].
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

Theorem g6_sound : contract_sound segs OPS MP PB g6_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [g6_contract c_apply c_pc] in HAP, Hpc.
  unfold g6_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (call_pre st) as [r|] eqn:CP; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in HAP.
  remember (if isV then vb else cb) as b eqn:EB in HAP. remember (if isV then ve else ce) as e eqn:EE in HAP.
  remember (if isV then vcap else ccap) as cap eqn:ECAP in HAP.
  destruct b as [|kB ob| | | | | | | | |]; try discriminate.
  destruct e as [|kT oe| | | | | | | | |]; try discriminate.
  destruct cap as [|kB' oc| | | | | | | | |]; try discriminate.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs st)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs st)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  destruct (elem_cells isV rT 0) as [topc|] eqn:ETOP; [|discriminate].
  destruct (elem_cells isV rN (Uint63.of_Z (L / 8))) as [newc|] eqn:ENEW; [|discriminate].

  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL]. apply andb_prop in COND as [COND NOB].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB]. apply andb_prop in COND as [COND NTB].
  apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [COND L16].
  apply andb_prop in COND as [COND OCT]. apply andb_prop in COND as [COND OE8]. apply andb_prop in COND as [KBB OB0].
  apply Uint63.eqb_correct in KBB. subst kB'.
  apply (proj1 (weqb_ok _ _)) in OB0. subst ob. apply (proj1 (weqb_ok _ _)) in OE8. subst oe. apply negb_true_iff in OCT.
  apply Z.leb_le in L16. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0.
  apply G1.neqb_neq in NNT. apply G1.neqb_neq in NNB. apply G1.neqb_neq in NTB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply G1.existsb_win_In in EXN. apply G1.existsb_win_In in EXT.
  apply andb_prop in COND2 as [COND2 WT]. apply andb_prop in COND2 as [COND2 HIT]. apply andb_prop in COND2 as [COND2 LOT].
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN. apply Uint63.eqb_correct in LOT. apply sv_eqb_eq in HIT.
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & ra & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.

  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pminv0].
  set (R := ms_regs ms). set (FR := ms_fregs ms). set (fc := ms_fcsr ms). set (m := ms_mem ms).
  assert (MSE : ms = MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)).
  { rewrite (MS_eta ms) at 1 by exact Psvc0. f_equal.
    - rewrite Ppc0, Hpc. reflexivity.
    - rewrite RESV in Presv0. exact Presv0.
    - exact Prom0. }
  pose proof (MemFX.getr_R segs OPS E st ms model HS0) as GR.
  assert (HS0' : st_ok segs OPS E st (MS R FR (Z_to_bv 64 (to_Z MEMCPY_PC)) fc None m (seg_rom segs)) model) by (rewrite <- MSE; exact HS0).

  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (INb : In (VP kB wzero) (op_args o)) by (rewrite EB; destruct isV; apply INCA; inlist).
  assert (INe : In (VP kT (wlit 8)) (op_args o)) by (rewrite EE; destruct isV; apply INCA; inlist).
  assert (INcap : In (VP kB oc) (op_args o)) by (rewrite ECAP; destruct isV; apply INCA; inlist).
  assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero INb).
  assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 8) INe).
  assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  assert (VBn12 : sv_vars_below n0 n12 = true) by (subst n12; unfold getr; exact (rf_allb_get _ _ _ VBrf X12)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. pose proof HC as HCm.
  unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & LK & P & O & Wk & M & CS0). clear CS0.
  pose proof LK as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof (pf g P) as (VC & EC & SC & VV & EV8 & SV' & LV & LA & ZV).
  pose proof P as (_ & _ & _ & CC & _ & _ & _ & CV & _ & DLIM & _ & _).
  set (V := if isV then u_vstk g else u_cstk g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.
  set (bm := bmem_of segs m) in *.

  assert (VFACTS : vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\
                   v_begin V = bv_unsigned (den E (VP kB wzero)) /\ v_end V = bv_unsigned (den E (VP kT (wlit 8))) /\ v_capend V = bv_unsigned (den E (VP kB oc)) /\
                   In (v_begin V, v_bytes V) (owned g)).
  { subst V. destruct isV.
    - rewrite <- EB in Lvb. rewrite <- EE in Lve. rewrite <- ECAP in Lvcap.
      split; [exact VV|]. split; [exact EV8|]. split; [exact CV|]. split; [exact Lvb|]. split; [exact Lve|]. split; [exact Lvcap|]. exact (owned_vstk g).
    - rewrite <- EB in Lcb. rewrite <- EE in Lce. rewrite <- ECAP in Lccap.
      split; [exact VC|]. split; [exact EC|]. split; [exact CC|]. split; [exact Lcb|]. split; [exact Lce|]. split; [exact Lccap|]. exact (owned_cstk g). }
  destruct VFACTS as (VVAL & VELT & VCAP & LVB & LVE & LVC & VOWN).
  pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  pose proof (proj1 O _ VOWN) as VLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ m model _ HA VLB) as (Bb1 & Bb2 & Bb3 & Bb4 & _). cbn [fst snd] in Bb1, Bb2, Bb3.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in LVB. fold Bz in LVB.
  assert (VBY : v_bytes V = 8 * v_cap V) by (unfold v_bytes; rewrite VELT; reflexivity).
  assert (VCE : v_capend V = Bz + 8 * v_cap V) by (unfold v_capend; rewrite VELT, LVB; reflexivity).
  assert (VEN : v_end V = Bz + 8 * v_size V) by (unfold v_end; rewrite VELT, LVB; reflexivity).

  pose proof (Preg0 kN rN FN) as ROKN. pose proof (Preg0 kT rT FT) as ROKT.
  assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
  assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. unfold two40Z in L40. pose proof (w2Z_range oc). alia. }
  assert (HIN' : hiZ E rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
  assert (HIT' : hiZ E rT = 8) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr. rewrite LON', HIN' in RNr. fold Nz in RNr.
  pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT' in RTr. fold Tz in RTr.
  pose proof (w2Z_range oc) as ROC. fold L in ROC.

  unfold two40Z in L40.
  assert (DVE : bv_unsigned (den E (VP kT (wlit 8))) = Tz + 8).
  { apply G1.den_VP_nowrap. rewrite wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. clear - RTr. lia. }
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { apply G1.den_VP_nowrap. fold L Bz. clear - L40 Bb1 Bb2 Bb3 CEIL LVB ROC. unfold two64. lia. }
  rewrite DVE in LVE. rewrite DVC in LVC.
  assert (LCAP : L = 8 * v_cap V) by alia.
  assert (SZC : v_size V = v_cap V).
  { pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as I1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as I2.
    cbn [fact_holds] in I1, I2. rewrite DVE, DVC in I1, I2. alia. }
  assert (TZ8 : Tz + 8 = Bz + L) by alia.
  assert (CAP32 : 32 <= v_cap V) by (pose proof (cap32_pos _ VCAP) as X; unfold EMBED_STACK in X; exact X).

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (G1.den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
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

  assert (WNd : wden E (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1)) = Win Nz (2 * L) HeapOp.K_BLOCK).
  { unfold wden. rewrite (den_VP0 E kN wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite WNd in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) (v_bytes V) L); [| alia| alia| rewrite VBY; alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. rewrite LVB. exact Hb. }
  pose proof (plain_mf _ _ OPS_plain Pmf0) as [MH ML].
  rewrite MSE.
  apply (MEMCPY R FR fc m model Nz Bz L srcb junk K R10 R11 R12 ltac:(alia) ltac:(alia) ltac:(unfold two40Z in L40; alia) RETPC SRC
           ltac:(rewrite SLEN; reflexivity) DST SEP (MemFX.mem_inv_of_st_ok segs OPS E st ms model HS0) MH ML).
  intros R' M' KEPT A0' MU WM MI' RW' BA' OM.

  set (NT := Nz + L - 8).
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
    exists (w_iv (wden E (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1)))). split.
    - apply in_map. apply filter_In. split; [apply in_map; exact EXN|]. rewrite WNd. reflexivity.
    - rewrite WNd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. alia. }
  pose proof (cw_unp_frame segs XW 1 _ LB _ m M' HCm FRM) as CW'.
  unfold cw_unp_holds in CW'. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in CW'. cbn [map decode_uc] in CW'.
  destruct CW' as (g2 & LK2 & P2 & O2 & Wk2 & M2 & _ & AX2).
  pose proof LK2 as (L2root & L2cb & L2ce & L2ccap & L2vb & L2ve & L2vcap & L2zp & L2zf & L2c0 & L2D).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in L2root, L2cb, L2ce, L2ccap, L2vb, L2ve, L2vcap, L2zp, L2zf, L2c0, L2D.
  pose proof (pf g2 P2) as (VC' & EC' & SC' & VV' & EV8' & SV'' & LV' & LA' & ZV').
  pose proof P2 as (_ & _ & _ & CC' & _ & _ & _ & CV' & _ & DLIM' & _ & _).
  set (V2 := if isV then u_vstk g2 else u_cstk g2) in *.
  assert (VF2 : vec_valid V2 /\ v_elt V2 = 8 /\ cap32_b (v_cap V2) = true /\
                v_begin V2 = Bz /\ v_end V2 = Tz + 8 /\ v_capend V2 = Bz + L /\ In (v_begin V2, v_bytes V2) (owned g2) /\
                v_size V2 = (if isV then u_D g2 + 1 else u_D g2)).
  { subst V2. destruct isV.
    - rewrite <- EB, (den_VP0 E kB wzero (weqb_refl _)) in L2vb. rewrite <- EE, DVE in L2ve. rewrite <- ECAP, DVC in L2vcap.
      split; [exact VV'|]. split; [exact EV8'|]. split; [exact CV'|]. split; [exact L2vb|]. split; [exact L2ve|]. split; [exact L2vcap|]. split; [exact (owned_vstk g2)| exact SV''].
    - rewrite <- EB, (den_VP0 E kB wzero (weqb_refl _)) in L2cb. rewrite <- EE, DVE in L2ce. rewrite <- ECAP, DVC in L2ccap.
      split; [exact VC'|]. split; [exact EC'|]. split; [exact CC'|]. split; [exact L2cb|]. split; [exact L2ce|]. split; [exact L2ccap|]. split; [exact (owned_cstk g2)| exact SC']. }
  destruct VF2 as (V2VAL & V2ELT & V2CAP & V2B & V2E & V2C & V2OWN & V2SZ).
  pose proof V2VAL as (W1 & W2 & W3 & W4).
  assert (V2BY : v_bytes V2 = L) by (unfold v_bytes; rewrite V2ELT; unfold v_capend in V2C; rewrite V2ELT, V2B in V2C; alia).
  assert (V2SC : v_size V2 = v_cap V2) by (unfold v_end, v_capend in V2E, V2C; rewrite V2ELT, V2B in V2E, V2C; alia).
  assert (LCAP2 : L = 8 * v_cap V2) by (unfold v_capend in V2C; rewrite V2ELT, V2B in V2C; alia).
  pose proof (proj1 O2 _ V2OWN) as V2LB. rewrite V2BY in V2LB, V2OWN.

  assert (NLB : In (Nz, 2 * L) LB).
  { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
    - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
    - exact IN.
    - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }

  destruct RW' as [[_ BAd] _]. cbn [cells_bytes cbytes] in BAd. rewrite app_nil_r in BAd.
  assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
  { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite !MemFX.rb_mrd.
    destruct BAd as (_ & _ & BD). destruct BA' as (_ & _ & BS).
    pose proof (BD (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X1. pose proof (BS (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X2.
    rewrite Z2Nat.id in X1, X2 by alia. rewrite X1, X2. reflexivity. }

  assert (SAME : forall a, 0 <= a < two64 -> ~ (Nz <= a < Nz + L) -> rb segs M' a = rb segs m a).
  { intros a Ha NI. unfold rb. rewrite (munch_frame m M' Nz L MU a Ha NI). reflexivity. }
  assert (SAMEb : forall a, 0 <= a < two64 -> ~ (Nz <= a < Nz + L) -> bm' a = bm a).
  { intros a Ha NI. subst bm bm'. rewrite !bmem_of_in by exact Ha. rewrite (SAME a Ha NI). reflexivity. }

  set (VN := vec_regrow V2 Nz).
  set (g' := mkUnp (u_ctx g2) (u_vis g2) (u_data g2) (u_len g2) (u_levels g2) (if isV then u_cstk g2 else VN) (if isV then VN else u_vstk g2) (u_zone g2)).
  assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V2 /\ v_cap VN = 2 * v_cap V2 /\ v_elt VN = 8 /\ v_bytes VN = 2 * L /\
                v_end VN = NT + 8 /\ v_capend VN = Nz + 2 * L).
  { subst VN. unfold vec_regrow, v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite V2ELT, V2SC. subst NT. repeat split; alia. }
  destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
  assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
  assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
  assert (TZB : Tz = Bz + L - 8) by alia.
  assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply G1.neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
  assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

  assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
  { intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. rewrite LVB, VBY, <- LCAP. exact Hb. }

  assert (BYNT : forall a, NT <= a < NT + 16 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply BYN. subst NT. alia. }
  assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. destruct (UB a Ha) as [U1 U2]. split; [exact (OM _ U1)| exact U2]. }

  assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
  { intros i Hi. rewrite !MemFX.rb_mrd. destruct BAd as (_ & _ & BD). destruct BA' as (_ & _ & BS).
    pose proof (BD (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X1. pose proof (BS (Z.to_nat i) ltac:(rewrite SLEN; apply Z2Nat.inj_lt; lia)) as X2.
    rewrite Z2Nat.id in X1, X2 by alia. rewrite X1, X2. reflexivity. }

  assert (ECINV : forall r gi cs, elem_cells isV r gi = Some cs -> exists gr, IMap.find gi (rg_cells r) = Some gr /\ cs = g_cells gr).
  { intros r gi cs H. unfold elem_cells in H. destruct (IMap.find gi (rg_cells r)) as [gr|]; [|discriminate]. exists gr. split; [reflexivity|].
    destruct isV; destruct (g_cells gr) as [|[i1 w1 v1] [|[i2 w2 v2] [|? ?]]]; try discriminate H;
      match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; reflexivity| discriminate H] end. }
  destruct (ECINV rT 0%uint63 topc ETOP) as (grT & FgrT & ->).
  destruct (ECINV rN (Uint63.of_Z (L / 8)) newc ENEW) as (grN & FgrN & ->).
  assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
  { apply keyZ_of_Z. unfold two62Z. clear - L16 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
  assert (L8E : 8 * (L / 8) = L) by (clear - L8 L16; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
  assert (STOP : slot_ok segs E1 m Tz (g_cells grT)).
  { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kT rT FT) 0%uint63 grT FgrT) as X. rewrite EVT1 in X. fold Tz in X. change (keyZ 0%uint63) with 0 in X.
    rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
  assert (SNEW : slot_ok segs E1 m (Nz + L) (g_cells grN)).
  { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kN rN FN) _ grN FgrN) as X. rewrite EVN1, KEYL, L8E in X. fold Nz in X. exact X. }
  assert (STOP' : slot_ok segs E1 M' NT (g_cells grT)).
  { apply (slot_ok_shift E1 m M' Tz NT _ STOP). intros i Hi. subst NT. rewrite TZB.
    replace (Nz + L - 8 + i) with (Nz + (L - 8 + i)) by alia. rewrite (RBC (L - 8 + i)) by alia.
    replace (Bz + (L - 8 + i)) with (Bz + L - 8 + i) by alia. apply SAME; [alia|]. clear - SEP Hi L16 RNr Bb1 LVB. lia. }
  assert (SNEW' : slot_ok segs E1 M' (NT + 8) (g_cells grN)).
  { apply (slot_ok_shift E1 m M' (Nz + L) (NT + 8) _ SNEW). intros i Hi. subst NT. replace (Nz + L - 8 + 8 + i) with (Nz + L + i) by alia.
    apply SAME; alia. }
  assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region16 (g_cells grT) (g_cells grN))).
  { apply (region16_ok (s_priv st) E1 M' nT _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| exact STOP'| exact SNEW']. }
  destruct (empty_region_ok (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
              ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).

  assert (WD1 : forall w, In w ws -> wden E1 w = wden E w).
  { intros [[w1 w2] w3] Hw. destruct (INW _ Hw) as (I1 & I2 & I3). cbn [fst snd] in I1, I2, I3. unfold wden. rewrite (DR1 _ I1), (DR1 _ I2), (DR1 _ I3). reflexivity. }
  assert (MWD1 : map (wden E1) ws = map (wden E) ws) by (apply map_ext_in; exact WD1).
  assert (WTd : wden E (top_win kT 8 KD) = Win Tz 8 (to_Z KD)) by (rewrite top_win_den; reflexivity).
  assert (KDv : to_Z KD = (if isV then K_VTOP else K_CTOP)) by (unfold KD; destruct isV; reflexivity).

  assert (HA' : aw_holds segs IMGX AW (den E aw) LB (map (wden E) ws) M' model).
  { refine (proj1 (aw_frame segs IMGX AW _ LB _ m M' model HA _ (fun a _ Hm => OM _ Hm))).
    intros a Ha Hd. destruct (aw_dep_ok segs IMGX AW _ LB _ m model a HA Hd) as (_ & NU & _).
    symmetry. apply (munch_frame m M' Nz L MU a Ha). intros IN. apply NU. unfold in_user. apply in_ivs_In. exists (Nz, 2 * L). split; [exact NLB|].
    unfold in_iv. cbn [fst snd]. alia. }

  assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E) ws) a /\ ~ in_ivs IMGX a).
  { intros a Ha.
    assert (SF : safe 1 g2 (map (wden E) ws) a).
    { clear - V2B V2E P2 O2 Ha TZB. subst V2. destruct isV; [apply (safe_vstk 1 g2 LB _ P2 O2)| apply (safe_cstk 1 g2 LB _ P2 O2)]; rewrite V2B, V2E; lia. }
    destruct (owned_byte_props segs IMGX AW _ LB M' model 1 g2 _ _ a HA' WF O2 Wk2 V2OWN ltac:(unfold in_iv; cbn [fst snd]; rewrite V2B; alia) SF) as (_ & NI & NW & _).
    split; [exact NW| exact NI]. }

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  set (wT := top_win kT 8 KD) in *.
  set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
  set (wNT := top_win nT 16 KD).
  set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
  set (b' := VP kN wzero). set (e' := VP nT (wlit 8)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
  set (ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
              else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]).
  assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
  { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
    apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
    split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
  assert (LENws' : Z.of_nat (length ws') < two63).
  { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
  assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
  { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
  assert (WNTd : wden E1 wNT = Win NT 16 (to_Z KD)) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
  assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
  assert (De' : bv_unsigned (den E1 e') = NT + 8).
  { subst e'. rewrite (G1.den_VP_nowrap E1 nT (wlit 8)); rewrite ?wlit_ok, NTV; change (to_Z 8%uint63) with 8; [reflexivity| subst NT; alia]. }
  assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
  { subst cap'. rewrite (G1.den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }
  apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ model o HS5 opre opost F5ops OID OPOTH [kN; kT]
           [(nT, region16 (g_cells grT) (g_cells grN)); (kB, empty_region L)] (mk_args 1%uint63 aw ws' ca') _ (PrimInt63.add n0 16)).
  -   intros k [<-|[<-|[]]]; rewrite F5regs.
    + split; [exact KN0|]. exists (empty_region (2 * L)). rewrite IMap.find_add_same by exact Pbst0. split; reflexivity.
    + split; [exact KT0|]. exists rT. rewrite IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)]. split; [exact FT| exact WT].
  -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
  -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
  -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
  -   intros k r a [H1|[H1|[]]] IR; injection H1 as <- <-.
    + right. exists kN, (empty_region (2 * L)). split; [left; reflexivity|]. rewrite F5regs, IMap.find_add_same by exact Pbst0. split; [reflexivity|].
      unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LONe, HINe. fold Nz.
      change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
      change (to_Z 16%uint63) with 16 in IR. subst NT. alia.
    + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
      destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
      * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))). rewrite MWD1.
        destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
      * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs, IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)].
        split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. alia.
  -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
      unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region16 (g_cells grT) (g_cells grN))) with 0;
      unfold hiZ; cbn [region16 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 16%uint63) with 16; intros [I1 I2].
    + apply (DISJ_BN a); subst NT; alia.
    + apply (DISJ_BN a); subst NT; alia.
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
    split; [apply mk_args_sound; exact LENws'|].
    assert (AWE : den E1 aw = den E aw) by (apply DR1; rewrite ARGS; right; left; reflexivity). rewrite AWE.

    assert (N24 : ~ c24 (2 * L)).
    { destruct (OpsTwin.UOT.cap32_bytes _ VCAP) as (k2 & Hk2 & E2). unfold c24, C24_LO, C24_HI.
      replace (2 * L) with (256 * 2 ^ (k2 + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
      exact (OpsTwin.UOT.pow2_not_c24 (k2 + 1) ltac:(lia)). }
    assert (WkE1 : wins_ok 1 g (map (wden E1) ws)) by (rewrite MWD1; exact Wk).
    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ (eq_ind_r (fun l => aw_holds segs IMGX AW (den E aw) LB l M' model) HA' MWD1));
            apply (UOK.unp_wins_keep_map E1 1 g LB ws ws' P O WkE1);
            [intros x Hx; destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]];
             [left; exact Hx'
             |right; right; rewrite WB'd; unfold w_iv; cbn [w_kind w_lo w_len]; split; [reflexivity|];
              replace (Bz, L) with (v_begin V, v_bytes V) by (f_equal; [exact LVB| rewrite VBY, LCAP; reflexivity]); exact VOWN
             |right; left; subst wNT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]
            |intros x Hx; destruct (win3_eqb x wN) eqn:QK1;
             [right; right; apply win3_eqb_eq in QK1; subst x; rewrite (WD1 wN EXN); subst wN; rewrite WNd; cbn [w_kind w_iv w_lo w_len];
              split; [reflexivity|]; split; [exact NLB| exact N24]|];
             destruct (win3_eqb x wT) eqn:QK2;
             [right; left; apply win3_eqb_eq in QK2; subst x; subst wT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity|];
             left; subst ws'; apply in_or_app; left; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1, QK2; reflexivity]|]. split.
    +
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
      * rewrite (WD1 x Hx'). exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
      * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
        right; left. split; [reflexivity|]. rewrite <- V2B. exact V2LB.
      * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
        right; right. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_SUB; alia|].
        exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L16. lia.
    +
      cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb].
      assert (CA' : ca' = [root; (if isV then cb else b'); (if isV then ce else e'); (if isV then ccap else cap');
                           (if isV then b' else vb); (if isV then e' else ve); (if isV then cap' else vcap); zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh])
        by (subst ca'; destruct isV; reflexivity).
      rewrite CA'. cbn [map decode_uc].
      assert (VNV : vec_valid VN).
      { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, V2SC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }
      assert (VNC : cap32_b (v_cap VN) = true).
      { rewrite VN3. unfold cap32_b. apply cap32_double; [exact V2CAP| alia]. }

      assert (DJ2 : forall b, In b (owned g2) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv b a).
      { intros b0 Hb0 a Ha. pose proof (proj1 (Forall_forall _ _) Wk2 _ (in_map _ _ _ EXN)) as WW. rewrite WNd in WW.
        destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
        apply (DJ b0 Hb0 a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
      assert (RDJ2 : forall b, In b (owned g2) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
      { intros b0 Hb0. pose proof (owned_pos g2 P2 b0 Hb0) as PO. unfold rdisj.
        destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
        destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
        exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
        - apply (DJ2 b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
        - apply (DJ2 b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }

      assert (VNB : (v_begin VN, v_bytes VN) = (Nz, 2 * L)) by (rewrite VN1, VN5; reflexivity).
      assert (V2Bb : (v_begin V2, v_bytes V2) = (Bz, L)) by (rewrite V2B, V2BY; reflexivity).

      assert (DRC : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] -> den E1 v = den E v)
        by (intros v Hv; apply DR1; apply INCA; exact Hv).

      assert (DLEN2 : u_D g2 = Z.of_nat (length (u_levels g2))) by reflexivity.
      assert (DPOS : 1 <= u_D g2) by (clear - V2SZ V2SC CAP32 LCAP LCAP2 DLEN2; destruct isV; lia).
      assert (LNE : u_levels g2 <> []) by (intros X; rewrite X in DLEN2; cbn in DLEN2; alia).
      assert (RLEN : Z.of_nat (length (removelast (u_levels g2))) = u_D g2 - 1).
      { rewrite (removelast_length _ LNE). rewrite Nat2Z.inj_sub by (destruct (u_levels g2); [exfalso; exact (LNE eq_refl)| cbn; lia]). rewrite <- DLEN2. reflexivity. }
      exists g'. split; [| split; [| split; [| split; [| split]]]].
      *
        unfold link. subst g'. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels u_cur_slot c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
        destruct isV; cbn [u_cstk u_vstk];
          rewrite ?(DRC root), ?(DRC cb), ?(DRC ce), ?(DRC ccap), ?(DRC vb), ?(DRC ve), ?(DRC vcap), ?(DRC zptr), ?(DRC zfree), ?(DRC c0),
                  ?(DRC slot), ?(DRC tD), ?(DRC restD), ?(DRC rootT), ?(DRC n1), ?(DRC P1) by inlist;
          rewrite ?Db', ?De', ?Dcap', ?VN1, ?VN6, ?VN7.
        -- split; [exact L2root|]. split; [exact L2cb|]. split; [exact L2ce|]. split; [exact L2ccap|].
           split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
        -- split; [exact L2root|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
           split; [exact L2vb|]. split; [exact L2ve|]. split; [exact L2vcap|].
           split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
      *
        unfold pure_ok. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. unfold u_D. cbn [u_levels]. change (Z.of_nat (length (u_levels g2))) with (u_D g2).
        pose proof P2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
        clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 VNV VNC VN2 VN4 V2SZ V2.
        destruct isV; subst V2; cbn in V2SZ.
        -- split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact VNV|]. split; [exact VN4|].
           split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
        -- split; [exact VNV|]. split; [exact VN4|]. split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|].
           split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
      *

        assert (TIE' : blocks_tied (owned g')).
        { pose proof (own_tied g2 LB O2) as OT.
          pose proof P2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _).
          pose proof (cap32_pos _ B4) as C32c. pose proof (cap32_pos _ B8) as C32v. unfold EMBED_STACK in C32c, C32v.
          destruct B1 as (_ & SZc & _). destruct B5 as (_ & SZv & _).
          subst g'. unfold blocks_tied, owned, cstk_block, vstk_block. cbn [u_cstk u_vstk u_zone snd].
          unfold v_bytes in OT |- *. rewrite B2, B6 in OT.
          clear - OT B2 B3 B6 B7 C32c C32v SZc SZv V2SZ V2SC LCAP2 VN5 V2.
          unfold v_bytes in VN5. subst V2. destruct isV; cbn [u_cstk u_vstk]; rewrite ?B2, ?B6; unfold v_bytes in VN5; lia. }
        destruct O2 as [OL [OF _]]. unfold own_ok. unfold owned, cstk_block, vstk_block in OL, OF, RDJ2. unfold owned, cstk_block, vstk_block in TIE' |- *.
        subst g'. cbn [u_cstk u_vstk u_zone] in TIE' |- *. subst V2. destruct isV; cbn [u_cstk u_vstk u_zone] in TIE' |- *; rewrite VNB in TIE' |- *; rewrite V2Bb in OL, OF, RDJ2;
          (split; [| split; [| exact TIE']]).
        -- intros b0 [<-|[<-|Hb0]]; [apply OL; left; reflexivity| exact NLB| apply OL; right; right; exact Hb0].
        -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. destruct (FOP_cons _ _ _ F2) as [F3 F4].
              constructor; [| constructor; [| exact F4]].
              ** constructor; [apply (proj2 (RDJ2 _ ltac:(left; reflexivity)))|]. exact (Forall_inv_tail F1).
              ** apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; right; exact Hc))).
        -- intros b0 [<-|[<-|Hb0]]; [exact NLB| apply OL; right; left; reflexivity| apply OL; right; right; exact Hb0].
        -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
              apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; exact Hc))).
      *
        unfold wins_ok. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
        assert (OWN' : forall b0, In b0 (owned g') -> b0 = (Nz, 2 * L) \/ In b0 (owned g2)).
        { intros b0 Hb0. subst g'. unfold owned, cstk_block, vstk_block in Hb0 |- *. cbn [u_cstk u_vstk u_zone] in Hb0 |- *.
          clear - Hb0 VNB. destruct isV; rewrite VNB in Hb0; cbn [In] in Hb0 |- *;
            destruct Hb0 as [X|[X|X]]; (try (left; symmetry; exact X)); right; tauto. }
        destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
        -- rewrite (WD1 x Hx') in NS |- *.
           pose proof (proj1 (forallb_forall _ _) KL x Hx') as KLx. cbn beta iota in KLx. destruct (kind_of x) as [kd|] eqn:KDx; [|discriminate KLx].
           pose proof (kind_of_sound E x kd KDx) as WK.

           assert (XN : forall a, in_iv (w_iv (wden E x)) a -> ~ (Nz <= a < Nz + 2 * L)).
           { intros a Ha HN. destruct x as [[xlo xlen] xkd]. unfold kind_of in KDx. cbn [snd] in KDx.
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
                 destruct (IMap.find kx (s_regs st)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HX0].
                 apply Uint63.eqb_correct in LOX. destruct (decide_ltu fs (VL wzero) (rg_hi rx)) as [[|]|] eqn:DH; try discriminate HX0.
                 pose proof (decide_ltu_sound E fs Pfacts0 _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS. cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS.
                 apply Uint63.eqb_false_correct in KXN.

                 pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
                 destruct WFx as (_ & _ & _ & [[KS _]|[[_ INx]|[KS _]]]);
                   [rewrite WK in KS; unfold HeapOp.K_STACK, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia| | rewrite WK in KS; unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia].
                 unfold w_iv, wden in INx. cbn [w_lo w_len] in INx. rewrite (den_VP0 E kx wzero (weqb_refl _)) in INx.
                 unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E kx wzero (weqb_refl _)) in Ha.
                 destruct (Z.eq_dec (bv_unsigned (ev E kx)) Nz) as [EQX|NEX].
                 * apply (Pdisj0 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) Nz). unfold loZ, hiZ. rewrite LOX, EQX, LON, HIN. cbn [den]. rewrite wbv_unsigned, L2w.
                   change (keyZ 0%uint63) with 0. fold Nz. clear - HPOS L16. lia.
                 * exact (aw_blocks_disj segs IMGX AW _ LB _ m model _ _ a HA INx NLB ltac:(cbn [fst]; exact NEX) Ha ltac:(unfold in_iv; cbn [fst snd]; exact HN)).
             -
               pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
               assert (K2 : 2 <= to_Z (wl kw)).
               { rewrite WK in NS. destruct WFx as (_ & _ & _ & [[KS _]|[[KS _]|[KS _]]]); rewrite WK in KS;
                   unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in NS, KS, NK1; clear - NS KS NK1; lia. }
               pose proof (proj1 (forallb_forall _ _) SWO _ Hx') as SW. cbn beta iota in SW. rewrite KWT in SW. cbn [orb] in SW.
               destruct (Z.ltb_spec (to_Z (wl kw)) 2); [lia|].
               apply orb_prop in SW as [SW|SW]; [apply win3_eqb_eq in SW; exact (NxT SW)|].
               destruct xlo as [|kx ox| | | | | | | | |]; try discriminate SW.
               apply andb_prop in SW as [SW FND]. apply andb_prop in SW as [SW KX0]. apply andb_prop in SW as [KXN OX].
               apply negb_true_iff in KXN. apply Uint63.eqb_false_correct in KXN. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
               destruct (IMap.find kx (s_regs st)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HXR]. apply Uint63.eqb_correct in LOX. apply sv_eqb_eq in HXR.
               unfold wden, w_iv, in_iv in Ha. rewrite (den_VP0 E kx wzero (weqb_refl _)) in Ha. cbn [w_lo w_len fst snd] in Ha.
               apply (Pdisj0 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) a). unfold loZ, hiZ. rewrite LOX, HXR, LON, HIN.
               change (den E (VL (wlit (Uint63.of_Z (2 * L))))) with (wbv (wlit (Uint63.of_Z (2 * L)))). rewrite wbv_unsigned, L2w.
               change (keyZ 0%uint63) with 0. fold Nz. alia. }
           destruct (proj1 (Forall_forall _ _) Wk2 (wden E x) (in_map _ _ _ Hx') NS) as [[KDJ DJ]|[NB SO]].
           ++ left. split; [exact KDJ|]. intros b0 Hb0 a Ha Hb. destruct (OWN' b0 Hb0) as [->|Hb2]; [| exact (DJ b0 Hb2 a Ha Hb)].
              apply (XN a Ha). unfold in_iv in Hb. cbn [fst snd] in Hb. exact Hb.
           ++ right. split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *. subst g'. cbn [u_cstk u_vstk u_levels u_zone].
              destruct SO as [(KK & A)|[(KK & A)|[A|A]]]; [| | right; right; left; exact A| right; right; right; exact A].
              **
                 destruct isV; [left; split; [exact KK| exact A]|].
                 exfalso. pose proof (only_kind_sound E (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
              ** destruct isV; [| right; left; split; [exact KK| exact A]].
                 exfalso. pose proof (only_kind_sound E (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
        --
           left. rewrite WB'd. split; [left; reflexivity|]. intros b0 Hb0 a Ha Hb. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha. unfold in_iv in Hb.
           subst g'. unfold owned, cstk_block, vstk_block in Hb0. cbn [u_cstk u_vstk u_zone] in Hb0.
           pose proof (disj_cv g2 LB O2) as DCV. unfold rdisj in DCV.
           pose proof ZV' as (_ & _ & Z3' & _).
           subst V2. destruct isV; cbn [u_cstk u_vstk] in Hb0; rewrite VNB in Hb0; injection V2Bb as VB1 VB2; rewrite VB1, VB2 in DCV;
             destruct Hb0 as [<-|[<-|Hc]]; cbn [fst snd] in Hb.
           ++ clear - DCV Ha Hb. lia.
           ++ exact (DISJ_BN a Hb Ha).
           ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_vc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
              unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
           ++ exact (DISJ_BN a Hb Ha).
           ++ clear - DCV Ha Hb. lia.
           ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_cc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
              unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
        --
           right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_BLOCK; clear; lia|].
           unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. rewrite KDv.
           destruct isV; [right; left| left]; (split; [reflexivity|]); rewrite VN1, VN6, VN7; subst NT; clear - L16; lia.
      *
        destruct M2 as (M21 & M22 & M23 & M24 & M25 & M26). unfold mem_ok. subst g'. cbn [MS ms_mem u_levels u_cstk u_vstk u_zone u_root u_vis]. fold bm'.
        unfold V2 in V2B. unfold V2 in V2SZ.
        split; [| split; [| split; [| split; [exact M24| split; [exact M25| exact M26]]]]].
        -- destruct isV; [exact M21|]. cbn in V2B. rewrite VN1. apply (cstk_at_shift _ bm' bm' Bz Nz); [| rewrite <- V2B; exact M21].
           intros i Hi. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
        -- intros NN. destruct isV; [| exact (M22 NN)]. cbn in V2B. rewrite VN1. pose proof (M22 NN) as X. rewrite V2B in X. unfold u64_at in X |- *.
           rewrite (rdZ_shift bm' bm' 8 Bz Nz); [exact X|]. intros i Hi. apply COPY. clear - Hi L16. lia.
        -- destruct isV; [| exact M23]. cbn in V2B. rewrite VN1. apply (vstk_at_shift _ bm' bm' (Bz + 8) (Nz + 8)); [| rewrite <- V2B; exact M23].
           intros i Hi. rewrite <- !Z.add_assoc. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
      *
        split; [intros X; discriminate X|]. destruct AX2 as [AX2 SE2].
        assert (NP : forall w, In w (map (wden E1) ws') -> pot_win w -> In w (map (wden E) ws)).
        { intros w Hw (K0 & _). apply in_map_iff in Hw as (x & <- & Hx). destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
          - rewrite (WD1 x Hx'). apply in_map. exact Hx'.
          - exfalso. rewrite WB'd in K0. cbn [w_kind] in K0. unfold HeapOp.K_BLOCK, K_STACK in K0. lia.
          - exfalso. rewrite WNTd in K0. cbn [w_kind] in K0. unfold KD, K_STACK in K0.
            destruct isV; [change (to_Z 3%uint63) with 3 in K0| change (to_Z 2%uint63) with 2 in K0]; lia. }
        split; [exact (acct_pot_ws _ _ _ _ _ AX2 NP)|].

        change (u_zone g') with (u_zone g2).
        apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SE2|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
        -- rewrite (WD1 x Hx'). apply in_map. exact Hx'.
        -- exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. lia.
        -- exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold KD, Seal.K_TWIN in K9.
           destruct isV; [change (to_Z 3%uint63) with 3 in K9| change (to_Z 2%uint63) with 2 in K9]; lia.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws') _ a (mk_args_sound E1 1%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
    split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IW|NIW].
      * right. apply (proj1 (in_ws_map_iff E ws a)) in IW as (w & Hw & Hin).
        destruct (win3_eqb w wN) eqn:QN; [| destruct (win3_eqb w wT) eqn:QT].
        -- apply win3_eqb_eq in QN. subst w. exists kN, (empty_region (2 * L)). split; [left; reflexivity|]. rewrite F5regs, IMap.find_add_same by exact Pbst0.
           split; [reflexivity|]. rewrite WNd in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. unfold inR. rewrite EVN1, LONe, HINe. fold Nz. clear - Hin. lia.
        -- apply win3_eqb_eq in QT. subst w. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs, IMap.find_add_other; [| exact Pbst0| exact (fun X => NNT X)].
           split; [exact FT|]. subst wT. rewrite WTd in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin.
           unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. clear - Hin. lia.
        -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
           rewrite (WD1 w Hw). exact Hin.
      * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))). rewrite MWD1. auto.
    + intros k r [H1|[H1|[]]] IR; injection H1 as <- <-.
      * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite NTV in IR. change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR.
        rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 16%uint63) with 16 in IR. alia.
      * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
  -
    assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
    assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 8))))) = Nz + (L - 8)).
    { rewrite (G1.den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
    constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
    constructor.
    { cbn [fact_holds]. rewrite Db', De'. subst NT. alia. }
    constructor.
    { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
    constructor.
    {
      cbn [fact_holds]. apply bv_eq. rewrite !G1.den_VAlu. cbn [alu64 alu]. rewrite !bv_sub_unsigned, !wrap64, De', Db'.
      assert (DVE1 : bv_unsigned (den E1 (VP kT (wlit 8))) = Tz + 8).
      { rewrite (G1.den_VP_nowrap E1 kT (wlit 8)); rewrite EVT1, wlit_ok; change (to_Z 8%uint63) with 8; fold Tz; [reflexivity| exact (proj2 RTr)]. }
      rewrite DVE1, (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. fold Bz. subst NT. f_equal. alia. }
    apply Forall_app. split.
    + apply (G4.anchor_facts_sound E1 fs kN (L - 8) (L - 8) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
    + rewrite ALN. constructor; [| constructor]. cbn [fact_holds]. rewrite NTV. change (2 ^ to_Z 3%uint63) with 8. subst NT.
      replace (Nz + L - 8) with (Nz + (L - 8)) by alia. rewrite Z.add_mod, NZ8, Z.add_0_l, Z.mod_mod by lia.
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 1). lia.
Qed.

End Sound.
End WithPc.
End G6.
