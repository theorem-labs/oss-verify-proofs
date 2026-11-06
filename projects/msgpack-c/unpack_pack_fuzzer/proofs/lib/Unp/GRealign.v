(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRegroup.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module GRealign.

Definition MASK32 : w64 := wnot (wlit 31%uint63).

Definition is_def (n : int) (f : fact) : option (int * w64) :=
  match f with
  | FEq (VP n' z) (VAlu ALU_AND (VP k o) (VL mask)) =>
      if PrimInt63.eqb n' n && weqb z wzero && weqb mask MASK32 then Some (k, o) else None
  | _ => None
  end.
Fixpoint find_def (fs : list fact) (n : int) : option (int * w64) :=
  match fs with
  | [] => None
  | f :: fs' => match is_def n f with Some r => Some r | None => find_def fs' n end
  end.

Section WithPc.
Variable S_PC : int.
Variable L : int.

Definition zkey (z : Z) : int := Uint63.of_Z z.

Definition negw (i : int) : w64 := W64 true i.

Definition TOP47w : w64 := wlit 140737488355328%uint63.
Definition pad_hi (k : int) (o : w64) (n : int) : sv := VAlu ALU_SUB (VP k o) (VP n wzero).
Definition sliver_hi (k : int) (lo : int) (n : int) (room8 : Z) : sv := VAlu ALU_SUB (VP n (negw (zkey (- room8)))) (VP k (negw lo)).

Definition grealign_apply (st : sstate) : option (list sstate) :=
  match getr st X2 with
  | VP n z =>
      match find_def (s_facts st) n with
      | Some (k, o) =>
          match IMap.find k (s_regs st), IMap.find n (s_regs st), find_range (s_facts st) k with
          | Some r, None, Some (rlo, rhi) =>
              match rg_hi r, rg_bg r with
              | VL hi, BGNone =>
                  let oz := w2Zs o in let loz := keyZ (rg_lo r) in let Lz := to_Z L in
                  let room8 := 8 * ((oz - 16 - loz) / 8) in
                  let o16 := wsub o (wlit 16%uint63) in
                  let np := s_next st in let nb := PrimInt63.add np 1%uint63 in
                  if weqb z wzero && negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb n 0%uint63) && rg_w r
                     && PrimInt63.leb 4%uint63 (find_align (s_facts st) k)
                     && Z.eqb (oz mod 16) 0 && Z.eqb (Lz mod 8) 0 && Z.leb 0 Lz && Z.leb Lz 2040
                     && Z.ltb (oz + Lz) 0 && Z.leb (- 2 ^ 61) (oz - 64) && Z.leb 8 room8 && Z.ltb (oz + Lz) (w2Z hi) && negb (wt hi)
                     && nowrap rlo rhi o && nowrap rlo rhi o16
                     && Z.ltb loz 0 && st_vars_below np st && PrimInt63.ltb 0%uint63 np && PrimInt63.ltb np bit62i
                     && PrimInt63.ltb n np && PrimInt63.ltb k np
                  then
                    let rk := Region (zkey (oz + Lz)) (rg_hi r) true BGNone (IMap.remove_range bit62i (zkey ((oz + Lz) / 8)) (rg_cells r)) in
                    let rn := Region (zkey (- room8)) (VL (wlit L)) true BGNone IMap.empty in
                    let rp := Region 0%uint63 (pad_hi k o n) true BGNone IMap.empty in
                    let rb := Region 0%uint63 (sliver_hi k (rg_lo r) n room8) true BGNone IMap.empty in
                    let nf := [FEq (VP np wzero) (VP n (wlit L)); FEq (VP nb wzero) (VP k (negw (rg_lo r)));
                               FAlign n 5%uint63; FRange n (wadd rlo o16) (wadd rhi o);
                               FULe (VP n wzero) (VP k o); FULe (VP k o16) (VP n wzero)]

                              ++ [FULe (VP n wzero) (VP np wzero)]
                              ++ (if Z.leb (w2Z rhi + oz + Lz) (2 ^ 47) then [FULe (VAlu ALU_ADD (VP np wzero) (pad_hi k o n)) (VL TOP47w)] else []) in
                    Some [GRegroup.regroup st [k] [(k, rk); (n, rn); (np, rp); (nb, rb)] nf (PrimInt63.add np 2%uint63)]
                  else None
              | _, _ => None
              end
          | _, _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition grealign_contract : contract := Contract S_PC grealign_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma find_def_holds : forall E fs n k o, Forall (fact_holds E) fs -> find_def fs n = Some (k, o) ->
  den E (VP n wzero) = den E (VAlu ALU_AND (VP k o) (VL MASK32)).
Proof.
  induction fs as [|f fs IH]; intros n k o HF H; cbn [find_def] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct (is_def n f) as [[k' o']|] eqn:D; [|exact (IH n k o HF' H)]. injection H as <- <-.
  unfold is_def in D. destruct f as [| | | |x y| | |]; try discriminate D.
  destruct x as [|n' z| | | | | | | | |]; try discriminate D.
  destruct y as [| |op y1 y2| | | | | | | |]; try discriminate D. destruct op; try discriminate D.
  destruct y1 as [|k2 o2| | | | | | | | |]; try discriminate D. destruct y2 as [mask| | | | | | | | | |]; try discriminate D.
  destruct (PrimInt63.eqb n' n && weqb z wzero && weqb mask MASK32) eqn:C; [|discriminate D]. injection D as <- <-.
  apply andb_prop in C as [C M]. apply andb_prop in C as [N Z0].
  apply Uint63.eqb_correct in N. apply weqb_eq in Z0. apply weqb_eq in M. subst n' z mask. exact Hf.
Qed.

Lemma w2Zs_wsub_small : forall a b, - two63 <= w2Zs a - w2Zs b < two63 -> w2Zs (wsub a b) = w2Zs a - w2Zs b.
Proof.
  intros a b H. rewrite (w2Zs_eq (wsub a b)), w2Z_wt, wsub_ok.
  rewrite (w2Zs_eq a), (w2Zs_eq b), (w2Z_wt a), (w2Z_wt b) in H |- *.
  pose proof (w2Z_range a) as Ra. pose proof (w2Z_range b) as Rb. unfold two63, two64 in *.
  destruct (Z.leb_spec 9223372036854775808 (w2Z a)), (Z.leb_spec 9223372036854775808 (w2Z b));
  destruct (Z_lt_le_dec (w2Z a - w2Z b) 0);
  try (replace (w2Z a - w2Z b) with ((w2Z a - w2Z b + 18446744073709551616) + (-1) * 18446744073709551616) by lia;
       rewrite Z.mod_add, Z.mod_small by lia;
       destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b + 18446744073709551616)); lia);
  try (rewrite (Z.mod_small (w2Z a - w2Z b)) by lia; destruct (Z.leb_spec 9223372036854775808 (w2Z a - w2Z b)); lia).
Qed.

Lemma mask32_val : w2Z MASK32 = two64 - 2 ^ 5.
Proof. reflexivity. Qed.

Lemma realign_val : forall v, 0 <= v < two64 -> v mod 16 = 0 ->
  let N := Z.land v (two64 - 2 ^ 5) in N mod 32 = 0 /\ v - 16 <= N <= v.
Proof.
  intros v R M N. subst N. rewrite land_negpow2 by lia. change (2 ^ 5) with 32.
  pose proof (Z.div_mod v 16 ltac:(lia)) as D16. rewrite M in D16.
  pose proof (Z.div_mod v 32 ltac:(lia)) as D32. pose proof (Z.mod_pos_bound v 32 ltac:(lia)) as B.
  set (a := v / 16) in *. set (q := v / 32) in *. set (r := v mod 32) in *.
  assert (V : r = 0 \/ r = 16) by lia.
  split; [| lia].
  replace (v - r) with (q * 32) by lia. apply Z.mod_mul. lia.
Qed.

Lemma w2Zs_negw : forall i, keyZ i < 0 -> w2Zs (negw i) = keyZ i.
Proof.
  intros i H. destruct (keyZ_cases i) as [[G1 G2]|[G1 G2]]; rewrite G2 in *; [exfalso; clear - G1 H; lia|].
  unfold negw, w2Zs, w2Z. cbn [wt wl]. unfold two64, two63. clear. lia.
Qed.

Lemma st_vars_below_region : forall n st j rx, IMap.bst (s_regs st) -> st_vars_below n st = true -> IMap.find j (s_regs st) = Some rx -> PrimInt63.ltb j n = true.
Proof.
  intros n st j rx B H F. unfold st_vars_below in H.
  repeat match type of H with (_ && _)%bool = true => let X := fresh "H" in apply andb_prop in H as [H X] end.
  match goal with Hx : IMap.forallb _ (s_regs st) = true |- _ => pose proof (proj1 (IMap.forallb_spec _ _ B) Hx j rx F) as P end.
  cbn beta in P. apply andb_prop in P as [P _]. exact P.
Qed.

Theorem grealign_sound : contract_sound segs OPS MP PB grealign_contract.
Proof.
  intros st sts Hpc HA K E0 ms model HS0 HMP HPB Hk. cbn [grealign_contract c_apply] in HA. unfold grealign_apply in HA.
  destruct (getr st X2) as [|n z| | | | | | | | |] eqn:SP; try discriminate HA.
  destruct (find_def (s_facts st) n) as [[k o]|] eqn:FD; [|discriminate HA].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate HA].
  destruct (IMap.find n (s_regs st)) eqn:Hn; [discriminate HA|].
  destruct (find_range (s_facts st) k) as [[rlo rhi]|] eqn:FR; [|discriminate HA].
  destruct (rg_hi r) as [hi| | | | | | | | | |] eqn:HI; try discriminate HA.
  destruct (rg_bg r) eqn:BG; try discriminate HA.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate HA] end.
  injection HA as <-.
  apply andb_prop in C as [C W6]. apply andb_prop in C as [C W5]. apply andb_prop in C as [C W4]. apply andb_prop in C as [C W3].
  apply andb_prop in C as [C W2]. apply andb_prop in C as [C W1].
  repeat match type of C with (_ && _)%bool = true => let X := fresh "C" in apply andb_prop in C as [C X] end.
  apply weqb_eq in C. subst z. apply negb_true_iff in C14, C13, C2.
  apply Uint63.leb_spec in C11. change (to_Z 4%uint63) with 4 in C11.
  apply Z.eqb_eq in C10, C9. apply Z.leb_le in C8, C7, C5, C4. apply Z.ltb_lt in C6, C3, W1.
  apply Uint63.ltb_spec in W3, W4, W5, W6. change (to_Z 0%uint63) with 0 in W3. rewrite to_Z_bit62i in W4.

  set (np := s_next st) in *. set (nb := PrimInt63.add np 1%uint63) in *.
  assert (NB1 : to_Z nb = to_Z np + 1) by (unfold nb; rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; rewrite Z.mod_small; [reflexivity| rewrite wB_two63; unfold two63; lia]).
  set (E1 := env_upd E0 np (den E0 (VP n (wlit L)))).
  set (E := env_upd E1 nb (den E0 (VP k (negw (rg_lo r))))).
  assert (HX : env_ext np E0 E).
  { apply (env_ext_trans np nb E0 E1 E); [lia| apply env_upd_ext| apply env_upd_ext]. }
  assert (HS : st_ok segs OPS E st ms model) by exact (st_ok_reval segs OPS np E0 E HX st ms model W3 W2 HS0).
  assert (EVo : forall j, to_Z j < to_Z np -> ev E j = ev E0 j) by (intros j Hj; exact (proj1 (proj2 HX j Hj))).
  assert (EVnp : ev E np = den E0 (VP n (wlit L))).
  { unfold E, E1. cbn [env_upd ev]. destruct (eqbP np nb) as [X|_]; [lia|]. rewrite Uint63.eqb_refl. reflexivity. }
  assert (EVnb : ev E nb = den E0 (VP k (negw (rg_lo r)))) by (unfold E; apply env_upd_same).
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  set (oz := w2Zs o) in *. set (Lz := to_Z L) in *. set (loz := keyZ (rg_lo r)) in *.
  set (room8 := 8 * ((oz - 16 - loz) / 8)) in *.
  pose proof (find_range_sound E _ FH k rlo rhi FR) as RK.
  pose proof (nowrap_sound _ _ _ C1) as NW1. pose proof (nowrap_sound _ _ _ C0) as NW0.
  assert (O16 : w2Zs (wsub o (wlit 16%uint63)) = oz - 16).
  { rewrite w2Zs_wsub_small; [reflexivity|]. change (w2Zs (wlit 16%uint63)) with 16. fold oz. unfold two63. lia. }
  rewrite O16 in NW0.
  set (K0 := bv_unsigned (ev E k)) in *.
  pose proof (find_def_holds E _ n k o FH FD) as DEF.

  assert (DK : bv_unsigned (den E (VP k o)) = K0 + oz).
  { rewrite den_VP. apply Z.mod_small. fold K0 oz. lia. }
  assert (K16 : K0 mod 16 = 0).
  { pose proof (find_align_sound E _ FH k) as ALG. pose proof (int_range (find_align (s_facts st) k)) as RA.
    destruct (Z_lt_ge_dec (to_Z (find_align (s_facts st) k)) 64) as [LT|GE].
    - change 16 with (2 ^ 4). apply (align_weaken _ 4 (to_Z (find_align (s_facts st) k))); [lia| exact ALG].
    - pose proof (bv_unsigned_in_range 64 (ev E k)) as R. rewrite bv_modulus_64 in R.
      assert (P : two64 <= 2 ^ to_Z (find_align (s_facts st) k)) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
      rewrite Z.mod_small in ALG by lia. unfold K0. rewrite ALG. reflexivity. }
  assert (V16 : (K0 + oz) mod 16 = 0) by (rewrite Z.add_mod, K16, C10 by lia; reflexivity).
  set (N0 := bv_unsigned (ev E n)).
  assert (NV : N0 mod 32 = 0 /\ K0 + oz - 16 <= N0 <= K0 + oz).
  { assert (NE : N0 = Z.land (K0 + oz) (two64 - 2 ^ 5)).
    { apply (f_equal bv_unsigned) in DEF. cbn [den alu64 alu] in DEF.
      rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r, bv_wrap_small in DEF by apply bv_unsigned_in_range.
      fold N0 in DEF. rewrite DEF, bv_and_unsigned, wbv_unsigned, mask32_val.
      change (bv_unsigned (ev E k + wbv o)) with (bv_unsigned (den E (VP k o))). rewrite DK. reflexivity. }
    rewrite NE. apply realign_val; [lia| exact V16]. }
  destruct NV as [N32 NB].

  pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  destruct RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  specialize (Rrange C14). specialize (Rvalid C14).
  assert (HZ : hiZ E r = w2Z hi) by (unfold hiZ; rewrite HI; cbn [den]; apply wbv_unsigned).
  unfold loZ in Rrange, Rvalid. fold loz in Rrange, Rvalid. rewrite HZ in Rrange, Rvalid. fold K0 in Rrange, Rvalid.
  pose proof (keyZ_range (rg_lo r)) as RLO. fold loz in RLO.
  assert (RM : 8 <= room8 <= oz - 16 - loz).
  { split; [exact C4|]. unfold room8. pose proof (Z.mul_div_le (oz - 16 - loz) 8 ltac:(lia)). lia. }
  assert (KC : keyZ (zkey (oz + Lz)) = oz + Lz) by (apply GW.keyZ_of_Z; unfold Mem.two62Z; lia).
  assert (KN : keyZ (zkey (- room8)) = - room8) by (apply GW.keyZ_of_Z; unfold Mem.two62Z; lia).
  assert (CUT8 : (oz + Lz) mod 8 = 0).
  { rewrite Z.add_mod, C9 by lia. assert (Q : oz mod 8 = 0).
    { pose proof (Z.div_mod oz 16 ltac:(lia)) as D. rewrite C10 in D. rewrite D. replace (16 * (oz / 16) + 0) with ((2 * (oz / 16)) * 8) by lia. apply Z.mod_mul. lia. }
    rewrite Q. reflexivity. }
  set (rk := Region (zkey (oz + Lz)) (VL hi) true BGNone (IMap.remove_range bit62i (zkey ((oz + Lz) / 8)) (rg_cells r))) in *.
  set (rn := Region (zkey (- room8)) (VL (wlit L)) true BGNone IMap.empty) in *.
  assert (NKne : n <> k) by (intros ->; rewrite Hr in Hn; discriminate Hn).
  assert (N0ne : PrimInt63.eqb n 0%uint63 = false) by exact C13.
  assert (HLZ : hiZ E rn = Lz) by (unfold hiZ, rn; cbn [rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (HKZ : hiZ E rk = w2Z hi) by (unfold hiZ, rk; cbn [rg_hi den]; apply wbv_unsigned).

  assert (SUBN : forall a, N0 + loZ rn <= a < N0 + hiZ E rn -> K0 + loz <= a < K0 + w2Z hi).
  { intros a Ha. unfold loZ in Ha. cbn [rg_lo rn] in Ha. rewrite KN, HLZ in Ha. lia. }
  assert (SUBK : forall a, K0 + loZ rk <= a < K0 + hiZ E rk -> K0 + loz <= a < K0 + w2Z hi).
  { intros a Ha. unfold loZ in Ha. cbn [rg_lo rk] in Ha. rewrite KC, HKZ in Ha. lia. }
  assert (WO : w2Z o = oz + two64).
  { pose proof (w2Zs_eq o) as X. fold oz in X. pose proof (w2Z_range o) as RW. destruct (wt o); lia. }
  assert (WO16 : w2Z (wsub o (wlit 16%uint63)) = oz - 16 + two64).
  { pose proof (w2Zs_eq (wsub o (wlit 16%uint63))) as X. rewrite O16 in X. pose proof (w2Z_range (wsub o (wlit 16%uint63))) as RW.
    destruct (wt (wsub o (wlit 16%uint63))); lia. }

  assert (LOZ : w2Zs (negw (rg_lo r)) = loz) by (apply w2Zs_negw; fold loz; lia).
  assert (RMZ : w2Zs (negw (zkey (- room8))) = - room8) by (rewrite w2Zs_negw; rewrite KN; lia).
  assert (EN0 : ev E0 n = ev E n) by (symmetry; apply EVo; lia).
  assert (EK0 : ev E0 k = ev E k) by (symmetry; apply EVo; lia).
  assert (LW : w2Zs (wlit L) = Lz) by (unfold w2Zs; cbn [wlit wt]; apply wlit_ok).
  assert (VNP : bv_unsigned (ev E np) = N0 + Lz).
  { rewrite EVnp, den_VP, EN0, LW. fold N0. apply Z.mod_small. lia. }
  assert (VNB : bv_unsigned (ev E nb) = K0 + loz).
  { rewrite EVnb, den_VP, EK0, LOZ. fold K0. apply Z.mod_small. lia. }
  assert (DN0 : bv_unsigned (den E (VP n wzero)) = N0).
  { rewrite den_VP. change (w2Zs wzero) with 0. fold N0. rewrite Z.add_0_r. apply Z.mod_small.
    pose proof (bv_unsigned_in_range 64 (ev E n)) as X. rewrite bv_modulus_64 in X. exact X. }
  set (rp := Region 0%uint63 (pad_hi k o n) true BGNone IMap.empty) in *.
  set (rb := Region 0%uint63 (sliver_hi k (rg_lo r) n room8) true BGNone IMap.empty) in *.
  assert (HPZ : hiZ E rp = K0 + oz - N0).
  { unfold hiZ, rp, pad_hi. cbn [rg_hi den alu64 alu]. rewrite bv_sub_unsigned. fold (den E (VP k o)) (den E (VP n wzero)). rewrite DK, DN0.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. lia. }
  assert (HBZ : hiZ E rb = N0 - room8 - (K0 + loz)).
  { unfold hiZ, rb, sliver_hi. cbn [rg_hi den alu64 alu]. rewrite bv_sub_unsigned.
    fold (den E (VP n (negw (zkey (- room8))))) (den E (VP k (negw (rg_lo r)))). rewrite !den_VP, RMZ, LOZ. fold N0 K0.
    rewrite (Z.mod_small (N0 + - room8)) by lia. rewrite (Z.mod_small (K0 + loz)) by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. lia. }
  assert (LZ0 : forall rr, rg_lo rr = 0%uint63 -> loZ rr = 0) by (intros rr X; unfold loZ; rewrite X; reflexivity).
  refine (Hk _ (or_introl eq_refl) E ms model HX HMP _).
  apply (GRegroup.regroup_sound segs OPS E st ms model [k] _ _ _ HS).
  -
    cbn [map fst].
    assert (D1 : n <> np) by (intros X; rewrite X in W5; clear - W5; lia).
    assert (D2 : n <> nb) by (intros X; rewrite X in W5; clear - W5 NB1; lia).
    assert (D3 : k <> np) by (intros X; rewrite X in W6; clear - W6; lia).
    assert (D4 : k <> nb) by (intros X; rewrite X in W6; clear - W6 NB1; lia).
    assert (D5 : np <> nb) by (intros X; rewrite <- X in NB1; clear - NB1; lia).
    constructor; [cbn [In]; intros [X|[X|[X|[]]]]; [exact (NKne X)| exact (D3 (eq_sym X))| exact (D4 (eq_sym X))]|].
    constructor; [cbn [In]; intros [X|[X|[]]]; [exact (D1 (eq_sym X))| exact (D2 (eq_sym X))]|].
    constructor; [cbn [In]; intros [X|[]]; exact (D5 (eq_sym X))|]. constructor; [intros []| constructor].
  -
    intros j rj IN. cbn [In] in IN. destruct IN as [X|[X|[X|[X|[]]]]]; injection X as <- <-.
    + split; [exact C14| left; left; reflexivity].
    + split; [exact C13| right; exact Hn].
    + split; [destruct (eqbP np 0%uint63) as [X|_]; [change (to_Z 0%uint63) with 0 in X; lia| reflexivity]|]. right.
      destruct (IMap.find np (s_regs st)) as [rx|] eqn:FX; [| reflexivity]. exfalso.
      apply (st_vars_below_region np st np rx (so_bst _ _ _ _ _ _ HS) W2) in FX. apply Uint63.ltb_spec in FX. lia.
    + split; [destruct (eqbP nb 0%uint63) as [X|_]; [change (to_Z 0%uint63) with 0 in X; lia| reflexivity]|]. right.
      destruct (IMap.find nb (s_regs st)) as [rx|] eqn:FX; [| reflexivity]. exfalso.
      apply (st_vars_below_region np st nb rx (so_bst _ _ _ _ _ _ HS) W2) in FX. apply Uint63.ltb_spec in FX. lia.
  - intros k' [<-|[]]. exact C14.
  -
    intros j rj IN. cbn [In] in IN. destruct IN as [X|[X|[X|[X|[]]]]]; injection X as <- <-.
    +
      assert (SUBF : forall g gr, IMap.find g (rg_cells rk) = Some gr ->
                IMap.find g (rg_cells r) = Some gr /\ ~ (to_Z bit62i <= to_Z g < to_Z (zkey ((oz + Lz) / 8)))).
      { intros g gr F1. cbn [rg_cells rk] in F1. rewrite IMap.find_remove_range in F1 by exact Rbst.
        destruct (lebP bit62i g) as [A|A]; destruct (ltbP g (zkey ((oz + Lz) / 8))) as [B|B]; cbn in F1; try discriminate F1; split; try exact F1; lia. }
      constructor.
      * cbn [rg_cells rk]. apply IMap.remove_range_bst. exact Rbst.
      * intros _. fold K0. unfold loZ. cbn [rg_lo rk]. rewrite KC, HKZ. lia.
      * intros _ a Ha. fold K0 in Ha. destruct (Rvalid a (SUBK a Ha)) as (V1 & V2 & V3).
        split; [exact V1| split; [intros _; apply V2; exact C12| exact V3]].
      * intros g gr F1. apply Rcells. exact (proj1 (SUBF g gr F1)).
      * intros g gr c i F1 IC Hi. destruct (SUBF g gr F1) as [F0 NR].
        destruct (Rin g gr c i F0 IC Hi) as [P1 P2]. cbv zeta in P1, P2 |- *. split; [|intros X; rewrite C14 in X; discriminate X].
        intros _. specialize (P1 C14). unfold loZ in P1. fold loz in P1. rewrite HZ in P1. unfold loZ. cbn [rg_lo rk]. rewrite KC, HKZ.
        split; [|lia].
        pose proof (to_Z_bounded (c_idx c)) as RI.
        destruct (keyZ_cases g) as [[G1 G2]|[G1 G2]]; rewrite G2.
        -- lia.
        -- rewrite to_Z_bit62i in NR.
           assert (QK : keyZ (zkey ((oz + Lz) / 8)) = (oz + Lz) / 8).
           { apply GW.keyZ_of_Z. unfold Mem.two62Z. pose proof (Z.div_mod (oz + Lz) 8 ltac:(lia)) as D. rewrite CUT8 in D. lia. }
           destruct (keyZ_cases (zkey ((oz + Lz) / 8))) as [[H1 H2]|[H1 H2]]; rewrite QK in H2.
           ++ pose proof (Z.div_mod (oz + Lz) 8 ltac:(lia)) as D. rewrite CUT8 in D. lia.
           ++ pose proof (Z.div_mod (oz + Lz) 8 ltac:(lia)) as D. rewrite CUT8 in D. unfold two63 in *. lia.
      * intros o' H1 H2 U. unfold bg_byte. cbn [rg_bg rk]. exact I.
    +
      constructor.
      * cbn [rg_cells rn]. apply IMap.bst_empty.
      * intros _. fold N0. unfold loZ. cbn [rg_lo rn]. rewrite KN, HLZ. lia.
      * intros _ a Ha. fold N0 in Ha. destruct (Rvalid a (SUBN a Ha)) as (V1 & V2 & V3).
        split; [exact V1| split; [intros _; apply V2; exact C12| exact V3]].
      * intros g gr F1. cbn [rg_cells rn] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros g gr c i F1. cbn [rg_cells rn] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros o' H1 H2 U. unfold bg_byte. cbn [rg_bg rn]. exact I.
    +
      constructor.
      * cbn [rg_cells rp]. apply IMap.bst_empty.
      * intros _. rewrite VNP, (LZ0 rp eq_refl), HPZ. lia.
      * intros _ a Ha. rewrite VNP, (LZ0 rp eq_refl), HPZ in Ha. destruct (Rvalid a ltac:(lia)) as (V1' & V2' & V3').
        split; [exact V1'| split; [intros _; apply V2'; exact C12| exact V3']].
      * intros g gr F1. cbn [rg_cells rp] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros g gr c i F1. cbn [rg_cells rp] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros o' H1 H2 U. unfold bg_byte. cbn [rg_bg rp]. exact I.
    +
      constructor.
      * cbn [rg_cells rb]. apply IMap.bst_empty.
      * intros _. rewrite VNB, (LZ0 rb eq_refl), HBZ. lia.
      * intros _ a Ha. rewrite VNB, (LZ0 rb eq_refl), HBZ in Ha. destruct (Rvalid a ltac:(lia)) as (V1' & V2' & V3').
        split; [exact V1'| split; [intros _; apply V2'; exact C12| exact V3']].
      * intros g gr F1. cbn [rg_cells rb] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros g gr c i F1. cbn [rg_cells rb] in F1. rewrite IMap.find_empty in F1. discriminate F1.
      * intros o' H1 H2 U. unfold bg_byte. cbn [rg_bg rb]. exact I.
  -
    intros j rj a IN Ha. exists k, r. split; [left; reflexivity|]. split; [exact Hr|]. split; [| intros _; exact C12].
    unfold GRegroup.rng in *. fold K0. unfold loZ at 1. fold loz. rewrite HZ.
    cbn [In] in IN. destruct IN as [X|[X|[X|[X|[]]]]]; injection X as <- <-.
    + fold K0 in Ha. exact (SUBK a Ha).
    + fold N0 in Ha. exact (SUBN a Ha).
    + rewrite VNP, (LZ0 rp eq_refl), HPZ in Ha. lia.
    + rewrite VNB, (LZ0 rb eq_refl), HBZ in Ha. lia.
  -
    intros j1 r1 j2 r2 a IN1 IN2 NE [A1 A2]. unfold GRegroup.rng in A1, A2.
    assert (RK' : forall a0, K0 + loZ rk <= a0 < K0 + hiZ E rk -> K0 + oz + Lz <= a0) by (intros a0 H0; unfold loZ in H0; cbn [rg_lo rk] in H0; rewrite KC in H0; lia).
    assert (RN' : forall a0, N0 + loZ rn <= a0 < N0 + hiZ E rn -> N0 - room8 <= a0 < N0 + Lz) by (intros a0 H0; unfold loZ in H0; cbn [rg_lo rn] in H0; rewrite KN, HLZ in H0; lia).
    cbn [In] in IN1, IN2.
    destruct IN1 as [X|[X|[X|[X|[]]]]]; injection X as <- <-; destruct IN2 as [Y|[Y|[Y|[Y|[]]]]]; injection Y as <- <-;
      try (apply NE; reflexivity);
      try (fold K0 in A1); try (fold K0 in A2); try (fold N0 in A1); try (fold N0 in A2);
      try rewrite VNP, (LZ0 rp eq_refl), HPZ in A1; try rewrite VNP, (LZ0 rp eq_refl), HPZ in A2;
      try rewrite VNB, (LZ0 rb eq_refl), HBZ in A1; try rewrite VNB, (LZ0 rb eq_refl), HBZ in A2;
      try (apply RK' in A1); try (apply RK' in A2); try (apply RN' in A1); try (apply RN' in A2); lia.
  -
    cbn [app]. repeat apply Forall_cons; [| | | | | | |]; cbn [fact_holds].
    8: { match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:TOPC end; [| constructor]. constructor; [| constructor]. cbn [fact_holds].
         apply Z.leb_le in TOPC.
         change (den E (VAlu ALU_ADD (VP np wzero) (pad_hi k o n))) with (alu64 ALU_ADD (den E (VP np wzero)) (den E (pad_hi k o n))).
         cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (den E (pad_hi k o n))) with (hiZ E rp). rewrite HPZ.
         rewrite (den_VP E np), VNP. change (w2Zs wzero) with 0. rewrite Z.add_0_r, (Z.mod_small (N0 + Lz)) by lia.
         unfold bv_wrap. rewrite bv_modulus_64, Z.mod_small by (unfold two64 in *; lia). cbn [den]. rewrite wbv_unsigned. change (w2Z TOP47w) with (2 ^ 47). lia. }
    7: { rewrite DN0, (den_VP E np), VNP. change (w2Zs wzero) with 0. rewrite Z.add_0_r, Z.mod_small by lia. lia. }
    + apply bv_eq. rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r, VNP, den_VP, LW. fold N0.
      rewrite !Z.mod_small by lia. reflexivity.
    + apply bv_eq. rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r, VNB, den_VP, LOZ. fold K0.
      rewrite !Z.mod_small by lia. reflexivity.
    + change (to_Z 5%uint63) with 5. change (2 ^ 5) with 32. exact N32.
    + rewrite !wadd_ok, WO, WO16. fold N0.
      replace (w2Z rlo + (oz - 16 + two64)) with ((w2Z rlo + (oz - 16)) + 1 * two64) by lia.
      replace (w2Z rhi + (oz + two64)) with ((w2Z rhi + oz) + 1 * two64) by lia.
      rewrite !Z.mod_add, !Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite DK. rewrite den_VP, (Z.mod_small _ two64) by (change (w2Zs wzero) with 0; fold N0; pose proof (bv_unsigned_in_range 64 (ev E n)) as X; rewrite bv_modulus_64 in X; lia).
      change (w2Zs wzero) with 0. fold N0. lia.
    + rewrite (den_VP E k), O16, (Z.mod_small _ two64) by (fold K0; lia).
      rewrite den_VP, (Z.mod_small _ two64) by (change (w2Zs wzero) with 0; fold N0; pose proof (bv_unsigned_in_range 64 (ev E n)) as X; rewrite bv_modulus_64 in X; lia).
      change (w2Zs wzero) with 0. fold K0 N0. lia.
Qed.
End Sound.
End WithPc.
End GRealign.
