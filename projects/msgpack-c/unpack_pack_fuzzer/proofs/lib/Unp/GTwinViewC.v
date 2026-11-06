(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Arguments Uint63.to_Z : simpl never.

Module GTwinViewC.

Definition vec_hi (n : int) (oA : w64) (k : int) : sv :=
  VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).
Definition is_vec_hi (h : sv) (n k : int) : option w64 :=
  match h with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n' oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some oA else None
  | _ => None
  end.

Definition is_lbk (n : int) (f : fact) : option (int * w64) :=
  match f with
  | FULe (VP k o) (VP n' z) => if PrimInt63.eqb n' n && weqb z wzero then Some (k, o) else None
  | FEq (VP n' z) (VP k o) => if PrimInt63.eqb n' n && weqb z wzero then Some (k, o) else None
  | _ => None
  end.
Fixpoint find_lbk (fs0 fs : list fact) (n : int) (S : w64) : option (int * w64) :=
  match fs with
  | [] => None
  | f :: fs' => match is_lbk n f with
                | Some (k, o) => match find_link fs0 k S with Some _ => Some (k, o) | None => find_lbk fs0 fs' n S end
                | None => find_lbk fs0 fs' n S
                end
  end.
Definition zkey (z : Z) : int := Uint63.of_Z z.

Section WithPc.
Variable S_PC : int.
Variable SEL : sstate -> option int.
Variable S : w64.

Definition gtwinviewc_apply (st : sstate) : option (list sstate) :=
  match SEL st with
  | Some n =>
      match find_lbk (s_facts st) (s_facts st) n S with
      | Some (k, o2) =>
          match find_link (s_facts st) k S with
          | Some sh =>
              match IMap.find n (s_regs st), IMap.find sh (s_regs st) with
              | Some rn, Some rs =>
                  match rg_hi rn, is_vec_hi (rg_hi rs) n k, rg_bg rs, rg_cells rs with
                  | VL hn, Some oA, BGZero, IMap.Leaf =>
                      let lon := keyZ (rg_lo rn) in let hin := w2Z hn in let los := keyZ (rg_lo rs) in
                      let oAz := w2Zs oA in let o2z := w2Zs o2 in
                      let lo' := lon / 8 in let hi' := (hin + 7) / 8 in
                      let nx := s_next st in
                      if negb (PrimInt63.eqb n 0%uint63) && negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb sh 0%uint63)
                         && negb (rg_w rs)
                         && PrimInt63.leb 3%uint63 (find_align (s_facts st) n) && PrimInt63.leb 3%uint63 (find_align (s_facts st) k)
                         && Z.eqb (oAz mod 8) 0 && Z.eqb (o2z mod 8) 0
                         && nowrap_kb (s_facts st) n oA && nowrap_kb (s_facts st) k o2
                         && negb (wt S) && negb (wt hn)
                         && Z.leb 0 o2z && Z.leb 0 oAz
                         && Z.leb los (o2z / 8 + lo') && Z.leb hi' (oAz / 8) && Z.ltb lo' hi'
                         && Z.leb (- 2 ^ 60) lo' && Z.ltb hi' (2 ^ 60)
                         && st_vars_below nx st && PrimInt63.ltb 0%uint63 nx && PrimInt63.ltb nx bit62i
                      then
                        let rt := Region (zkey lo') (VL (wlit (Uint63.of_Z hi'))) false BGZero IMap.empty in
                        let lk := FEq (VP nx wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP n wzero) (VL (wlit 3%uint63))) (VL S)) in
                        Some [SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add nx rt (s_regs st)) (lk :: s_facts st)
                                 (s_ops st) (s_priv st) (PrimInt63.add nx 1%uint63)]
                      else None
                  | _, _, _, _ => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition gtwinviewc_contract : contract := Contract S_PC gtwinviewc_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma find_lbk_holds : forall E fs0 fs n S k o, Forall (fact_holds E) fs -> find_lbk fs0 fs n S = Some (k, o) ->
  bv_unsigned (den E (VP k o)) <= bv_unsigned (den E (VP n wzero)).
Proof.
  induction fs as [|f fs IH]; intros n S0 k o HF H; cbn [find_lbk] in H; [discriminate|].
  inversion HF as [|f' l Hf HF']; subst.
  destruct (is_lbk n f) as [[k' o']|] eqn:D; [|exact (IH n S0 k o HF' H)].
  destruct (find_link fs0 k' S0) as [sh|]; [|exact (IH n S0 k o HF' H)]. injection H as <- <-.
  unfold is_lbk in D. destruct f as [| | |x y|x y| | |]; try discriminate D.
  - destruct x as [|k2 o2| | | | | | | | |]; try discriminate D. destruct y as [|n' z| | | | | | | | |]; try discriminate D.
    destruct (PrimInt63.eqb n' n && weqb z wzero) eqn:C; [|discriminate D]. injection D as <- <-.
    apply andb_prop in C as [N Z0]. apply Uint63.eqb_correct in N. apply weqb_eq in Z0. subst n' z. exact Hf.
  - destruct x as [|n' z| | | | | | | | |]; try discriminate D. destruct y as [|k2 o2| | | | | | | | |]; try discriminate D.
    destruct (PrimInt63.eqb n' n && weqb z wzero) eqn:C; [|discriminate D]. injection D as <- <-.
    apply andb_prop in C as [N Z0]. apply Uint63.eqb_correct in N. apply weqb_eq in Z0. subst n' z.
    cbn [fact_holds] in Hf. rewrite Hf. lia.
Qed.

Lemma is_vec_hi_eq : forall h n k oA, is_vec_hi h n k = Some oA -> h = vec_hi n oA k.
Proof.
  intros h n k oA H. unfold is_vec_hi in H.
  destruct h as [| |op a b| | | | | | | |]; try discriminate H.
  destruct op; try discriminate H.
  destruct a as [| |op2 a1 a2| | | | | | | |]; try discriminate H.
  destruct op2; try discriminate H.
  destruct a1 as [|n' oA'| | | | | | | | |]; try discriminate H.
  destruct a2 as [|k' z| | | | | | | | |]; try discriminate H.
  destruct b as [c| | | | | | | | | |]; try discriminate H.
  destruct (PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63)) eqn:C; [|discriminate H].
  injection H as <-.
  apply andb_prop in C as [C C3]. apply andb_prop in C as [C Cz]. apply andb_prop in C as [Cn Ck].
  apply Uint63.eqb_correct in Cn, Ck. apply weqb_eq in Cz, C3. subst. reflexivity.
Qed.

Lemma keyZ_of_Z : forall z, - 2 ^ 62 <= z < 2 ^ 62 -> keyZ (Uint63.of_Z z) = z.
Proof.
  intros z Hz. destruct (Z.lt_ge_cases z 0) as [NEG|NN].
  2: { destruct (keyZ_cases (Uint63.of_Z z)) as [[R K]|[R K]]; rewrite Uint63.of_Z_spec, wB_two63, Z.mod_small in * by (unfold two63; lia); [exact K| lia]. }
  destruct (keyZ_cases (Uint63.of_Z z)) as [[R K]|[R K]]; rewrite Uint63.of_Z_spec, wB_two63 in *.
  - exfalso. replace z with ((z + two63) + (-1) * two63) in R by lia. rewrite Z_mod_plus_full, Z.mod_small in R by (unfold two63; lia). unfold two63 in R. lia.
  - rewrite K. replace z with ((z + two63) + (-1) * two63) at 1 by lia. rewrite Z_mod_plus_full, Z.mod_small by (unfold two63; lia). unfold two63. lia.
Qed.

Lemma mod8_of_align : forall E fs k, facts_hold E fs -> PrimInt63.leb 3%uint63 (find_align fs k) = true -> bv_unsigned (ev E k) mod 8 = 0.
Proof.
  intros E fs k FH AL. apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL.
  pose proof (find_align_sound E fs FH k) as ALG. pose proof (int_range (find_align fs k)) as RA.
  destruct (Z_lt_ge_dec (to_Z (find_align fs k)) 64) as [LT|GE].
  - change 8 with (2 ^ 3). apply (align_weaken _ 3 (to_Z (find_align fs k))); [lia| exact ALG].
  - pose proof (bv_unsigned_in_range 64 (ev E k)) as R. rewrite bv_modulus_64 in R.
    assert (P : two64 <= 2 ^ to_Z (find_align fs k)) by (rewrite two64_eq; apply Z.pow_le_mono_r; lia).
    rewrite Z.mod_small in ALG by lia. rewrite ALG. reflexivity.
Qed.

Theorem gtwinviewc_sound : contract_sound segs OPS MP PB gtwinviewc_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gtwinviewc_contract c_apply] in HA. unfold gtwinviewc_apply in HA.
  destruct (SEL st) as [n|] eqn:SP; [|discriminate HA].
  destruct (find_lbk (s_facts st) (s_facts st) n S) as [[k o2]|] eqn:FL; [|discriminate HA].
  destruct (find_link (s_facts st) k S) as [sh|] eqn:FK; [|discriminate HA].
  destruct (IMap.find n (s_regs st)) as [rn|] eqn:Hn; [|discriminate HA].
  destruct (IMap.find sh (s_regs st)) as [rs|] eqn:Hs; [|discriminate HA].
  destruct (rg_hi rn) as [hn| | | | | | | | | |] eqn:HIN; try discriminate HA.
  destruct (is_vec_hi (rg_hi rs) n k) as [oA|] eqn:HIS; [|discriminate HA].
  apply is_vec_hi_eq in HIS.
  destruct (rg_bg rs) eqn:BGS; try discriminate HA.
  destruct (rg_cells rs) eqn:CLS; try discriminate HA.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate HA] end.
  injection HA as <-.
  repeat match type of C with (_ && _)%bool = true => let X := fresh "C" in apply andb_prop in C as [C X] end.

  apply negb_true_iff in C, C20, C19, C18, C11, C10.
  apply Z.eqb_eq in C15, C14. apply Z.leb_le in C9, C8, C7, C6, C4. apply Z.ltb_lt in C5, C3.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH. pose proof (so_bst _ _ _ _ _ _ HS) as BST.
  set (nx := s_next st) in *.
  set (oAz := w2Zs oA) in *. set (o2z := w2Zs o2) in *.
  set (lon := keyZ (rg_lo rn)) in *. set (los := keyZ (rg_lo rs)) in *.
  set (lo' := lon / 8) in *. set (hi' := (w2Z hn + 7) / 8) in *.
  set (K0 := bv_unsigned (ev E k)). set (N0 := bv_unsigned (ev E n)). set (SH0 := bv_unsigned (ev E sh)).
  pose proof (bv_unsigned_in_range 64 (ev E k)) as RK. rewrite bv_modulus_64 in RK. fold K0 in RK.
  pose proof (bv_unsigned_in_range 64 (ev E n)) as RN. rewrite bv_modulus_64 in RN. fold N0 in RN.
  pose proof (mod8_of_align E _ k FH C16) as K8. fold K0 in K8.
  pose proof (mod8_of_align E _ n FH C17) as N8. fold N0 in N8.
  destruct (nowrap_kb_sound E _ FH n oA C13) as [_ D1]. destruct (nowrap_kb_sound E _ FH k o2 C12) as [_ D2]. fold N0 oAz in D1. fold K0 o2z in D2.
  pose proof (find_lbk_holds E _ _ n S k o2 FH FL) as LB.
  assert (DN : bv_unsigned (den E (VP n wzero)) = N0).
  { rewrite den_VP. change (w2Zs wzero) with 0. rewrite Z.add_0_r. apply Z.mod_small. exact RN. }
  rewrite DN, D2 in LB.
  pose proof (bv_unsigned_in_range 64 (den E (VP n oA))) as RNA. rewrite bv_modulus_64, D1 in RNA.

  destruct (find_link_holds E _ k S sh FH FK) as (c' & SH3' & LK). apply Uint63.eqb_correct in SH3'.
  pose proof (w2Z_range S) as RS0. pose proof (w2Z_wt S) as WS. rewrite C11 in WS.
  assert (SZ : 0 <= w2Z S < two63) by (unfold two63 in *; destruct (Z.leb_spec 9223372036854775808 (w2Z S)); [discriminate WS| lia]).
  assert (SHV : SH0 = K0 / 8 + w2Z S).
  { apply (f_equal bv_unsigned) in LK. cbn [den alu64 alu] in LK.
    assert (X0 : forall y : bv 64, bv_unsigned (y + wbv wzero)%bv = bv_unsigned y).
    { intros y. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. }
    rewrite X0, bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv, SH3', X0, wbv_unsigned in LK.
    change (to_Z 3%uint63) with 3 in LK. rewrite Z.shiftr_div_pow2 in LK by lia. change (2 ^ 3) with 8 in LK. fold K0 SH0 in LK.
    rewrite LK. apply bv_wrap_small. rewrite bv_modulus_64.
    assert (0 <= K0 / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; unfold two64 in *; lia]).
    unfold two63, two64 in *. lia. }

  set (w := den E (VAlu ALU_ADD (VAlu ALU_SRL (VP n wzero) (VL (wlit 3%uint63))) (VL S))).
  assert (WV : bv_unsigned w = N0 / 8 + w2Z S).
  { subst w. cbn [den alu64 alu].
    rewrite bv_add_unsigned, bv_shiftr_unsigned, shamt6_bv, wbv_unsigned.
    change (to_Z (shamt6 (wlit 3%uint63))) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (ev E n + wbv wzero)%bv with (den E (VP n wzero)). rewrite DN.
    apply bv_wrap_small. rewrite bv_modulus_64.
    assert (0 <= N0 / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; unfold two64 in *; lia]).
    unfold two63, two64 in *. lia. }
  assert (DD : o2z / 8 <= N0 / 8 - K0 / 8 /\ (N0 + oAz - K0) / 8 = N0 / 8 - K0 / 8 + oAz / 8).
  { pose proof (Z.div_mod K0 8 ltac:(lia)) as EK. rewrite K8 in EK. pose proof (Z.div_mod N0 8 ltac:(lia)) as EN. rewrite N8 in EN.
    pose proof (Z.div_mod oAz 8 ltac:(lia)) as E1. rewrite C15 in E1. pose proof (Z.div_mod o2z 8 ltac:(lia)) as E2. rewrite C14 in E2.
    split; [lia|].
    replace (N0 + oAz - K0) with ((N0 / 8 - K0 / 8 + oAz / 8) * 8) by lia. apply Z.div_mul. lia. }
  destruct DD as [DD DH].
  set (E' := env_upd E nx w).
  pose proof (env_upd_ext E nx w) as EXT. fold E' in EXT.
  assert (NPOS : 0 < to_Z nx) by (apply ltb_spec in C1; change (to_Z 0%uint63) with 0 in C1; exact C1).
  pose proof (st_ok_reval segs OPS nx E E' EXT st ms model NPOS C2 HS) as HS1.

  assert (KEYLT : forall j rj, IMap.find j (s_regs st) = Some rj -> to_Z j < to_Z nx).
  { intros j rj F. unfold st_vars_below in C2. do 2 (apply andb_prop in C2; destruct C2 as [C2 ?]). apply andb_prop in C2 as [_ HR].
    pose proof (proj1 (IMap.forallb_spec _ _ BST) HR j rj F) as P. cbn beta in P. apply andb_prop in P as [P _]. apply ltb_spec in P. exact P. }
  assert (SHne : sh <> nx) by (intros X; pose proof (KEYLT sh rs Hs) as Y; rewrite X in Y; lia).
  assert (NXnone : IMap.find nx (s_regs st) = None).
  { destruct (IMap.find nx (s_regs st)) as [rx|] eqn:F; [|reflexivity]. pose proof (KEYLT nx rx F). lia. }
  assert (ESH : ev E' sh = ev E sh).
  { subst E'. cbn [env_upd ev]. destruct (PrimInt63.eqb sh nx) eqn:Q; [apply Uint63.eqb_correct in Q; contradiction| reflexivity]. }
  assert (ENX : ev E' nx = w) by (subst E'; apply env_upd_same).
  set (SH1 := bv_unsigned w) in *.
  set (rt := Region (zkey lo') (VL (wlit (Uint63.of_Z hi'))) false BGZero IMap.empty).
  assert (HI0 : 0 <= hi') by (unfold hi'; apply Z.div_pos; [pose proof (w2Z_range hn); lia| lia]).
  assert (KT : keyZ (zkey lo') = lo') by (apply keyZ_of_Z; lia).
  assert (HT : hiZ E' rt = hi').
  { unfold hiZ, rt. cbn [rg_hi den]. rewrite wbv_unsigned, wlit_ok, Uint63.of_Z_spec, wB_two63. apply Z.mod_small. unfold two63. lia. }
  pose proof (so_reg _ _ _ _ _ _ HS1 sh rs Hs) as ROS. destruct ROS as [Sbst Srange Svalid Scells Sin Sbg].
  specialize (Srange C19). specialize (Svalid C19).
  set (HH := (N0 + oAz - K0) / 8).
  assert (HZS : hiZ E' rs = HH).
  { unfold hiZ. rewrite HIS.
    assert (VB : vars_below nx (vec_hi n oA k) = true).
    { assert (HR : IMap.forallb (fun k0 r0 => PrimInt63.ltb k0 nx && region_vars_below nx r0) (s_regs st) = true).
      { unfold st_vars_below in C2. do 2 (apply andb_prop in C2; destruct C2 as [C2 ?]). apply andb_prop in C2 as [_ HR]. exact HR. }
      pose proof (proj1 (IMap.forallb_spec _ _ BST) HR sh rs Hs) as P. cbn beta in P. apply andb_prop in P as [_ P].
      unfold region_vars_below in P. apply andb_prop in P as [P _]. rewrite HIS in P. exact P. }
    rewrite (den_env_ext nx E E' _ EXT VB). unfold vec_hi. cbn [den alu64 alu].
    rewrite bv_shiftr_unsigned, shamt6_bv, bv_sub_unsigned. change (to_Z (shamt6 (wlit 3%uint63))) with 3.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    change (ev E n + wbv oA)%bv with (den E (VP n oA)). rewrite D1.
    assert (DK : bv_unsigned (ev E k + wbv wzero)%bv = K0).
    { rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_small. rewrite bv_modulus_64. exact RK. }
    rewrite DK. unfold HH. f_equal. apply bv_wrap_small. rewrite bv_modulus_64. lia. }
  unfold loZ in Srange, Svalid. fold los in Srange, Svalid. rewrite ESH, HZS in Srange, Svalid. fold SH0 in Srange, Svalid.
  assert (SUBT : forall a, SH1 + lo' <= a < SH1 + hi' -> SH0 + los <= a < SH0 + HH) by (intros a Ha; lia).
  assert (NXne0 : PrimInt63.eqb nx 0%uint63 = false).
  { destruct (PrimInt63.eqb nx 0%uint63) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. rewrite Q in NPOS. change (to_Z 0%uint63) with 0 in NPOS. lia. }
  assert (FIND : forall j rj, IMap.find j (IMap.add nx rt (s_regs st)) = Some rj -> (j = nx /\ rj = rt) \/ (j <> nx /\ IMap.find j (s_regs st) = Some rj)).
  { intros j rj F. destruct (eqbP nx j) as [X|X].
    - apply to_Z_inj in X. subst j. rewrite IMap.find_add_same in F by exact BST. injection F as <-. left; auto.
    - assert (NJ : nx <> j) by (intros Y; apply X; rewrite Y; reflexivity).
      rewrite IMap.find_add_other in F by assumption. right. split; [congruence| exact F]. }
  assert (RNG : forall a, bv_unsigned (ev E' nx) + loZ rt <= a < bv_unsigned (ev E' nx) + hiZ E' rt -> SH0 + los <= a < SH0 + HH).
  { intros a Ha. rewrite ENX, HT in Ha. unfold loZ in Ha. cbn [rg_lo rt] in Ha. rewrite KT in Ha. fold SH1 in Ha. apply SUBT. exact Ha. }
  assert (INB : forall a, in_based E' (IMap.add nx rt (s_regs st)) a -> in_based E' (s_regs st) a).
  { intros a (j & rj & F & J0 & Ha). destruct (FIND j rj F) as [[-> ->]|[NJ F0]].
    - exists sh, rs. split; [exact Hs|]. split; [exact C19|]. unfold loZ. fold los. rewrite ESH, HZS. fold SH0. apply RNG. exact Ha.
    - exists j, rj. auto. }
  refine (Hk _ (or_introl eq_refl) E' ms model EXT HMP _).
  destruct HS1 as [Qpc Qx0 Qregs Qfregs Qsvc Qresv Qfcsr Qrom Qz Qbst Qreg Qdisj Qpub Qfacts Qops Qapart Qmf Qcov Qminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Qbst.
  - intros j rj F. destruct (FIND j rj F) as [[-> ->]|[NJ F0]]; [|exact (Qreg j rj F0)].
    constructor.
    + cbn [rg_cells rt]. apply IMap.bst_empty.
    + intros _. rewrite ENX, HT. unfold loZ. cbn [rg_lo rt]. rewrite KT. fold SH1. lia.
    + intros _ a Ha. destruct (Svalid a (RNG a Ha)) as (V1 & V2 & V3).
      split; [exact V1| split; [intros X; cbn [rg_w rt] in X; discriminate X| exact V3]].
    + intros g gr F1. cbn [rg_cells rt] in F1. rewrite IMap.find_empty in F1. discriminate F1.
    + intros g gr c i F1. cbn [rg_cells rt] in F1. rewrite IMap.find_empty in F1. discriminate F1.
    + intros o' H1 H2 U. specialize (H1 NXne0). rewrite HT in H1. unfold loZ in H1. cbn [rg_lo rt] in H1. rewrite KT in H1.
      unfold bg_byte. cbn [rg_bg rt]. rewrite ENX. fold SH1.
      pose proof (Sbg (o' + (SH1 - SH0))) as G.
      assert (G1 : PrimInt63.eqb sh 0%uint63 = false -> loZ rs <= o' + (SH1 - SH0) < hiZ E' rs).
      { intros _. unfold loZ. fold los. rewrite HZS. lia. }
      assert (G2 : PrimInt63.eqb sh 0%uint63 = true -> 0 <= o' + (SH1 - SH0) < two63 / 2 /\
                   (exists bs, memory_read segs (Z_to_bv 64 (o' + (SH1 - SH0))) 1 = Some bs) /\ ~ in_priv (s_priv st) (o' + (SH1 - SH0))).
      { intros X. rewrite C19 in X. discriminate X. }
      assert (G3 : uncovered rs (o' + (SH1 - SH0))).
      { intros g gr _ F1. rewrite CLS in F1. cbn in F1. discriminate F1. }
      specialize (G G1 G2 G3). unfold bg_byte in G. rewrite BGS in G. rewrite ESH in G. fold SH0 in G.
      replace (SH1 + o') with (SH0 + (o' + (SH1 - SH0))) by lia. exact G.
  -
    intros k1 r1 k2 r2 F1 F2 NE Z1 Z2 W a [A1 A2].
    destruct (FIND k1 r1 F1) as [[-> ->]|[NJ1 G1]]; destruct (FIND k2 r2 F2) as [[-> ->]|[NJ2 G2]].
    + apply NE; reflexivity.
    + destruct W as [W|W]; [cbn [rg_w rt] in W; discriminate W|].
      assert (SK : sh <> k2) by (intros X; subst k2; rewrite Hs in G2; injection G2 as <-; rewrite C18 in W; discriminate W).
      apply (Qdisj sh rs k2 r2 Hs G2 SK C19 Z2 (or_intror W) a). split; [|exact A2].
      unfold loZ. fold los. rewrite ESH, HZS. fold SH0. apply RNG. exact A1.
    + destruct W as [W|W]; [|cbn [rg_w rt] in W; discriminate W].
      assert (SK : k1 <> sh) by (intros X; subst k1; rewrite Hs in G1; injection G1 as <-; rewrite C18 in W; discriminate W).
      apply (Qdisj k1 r1 sh rs G1 Hs SK Z1 C19 (or_introl W) a). split; [exact A1|].
      unfold loZ. fold los. rewrite ESH, HZS. fold SH0. apply RNG. exact A2.
    + exact (Qdisj k1 r1 k2 r2 G1 G2 NE Z1 Z2 W a (conj A1 A2)).
  - intros r0 g gr c F0. apply (Qpub r0 g gr c).
    rewrite IMap.find_add_other in F0 by (try exact Qbst; intros X; rewrite X in NXne0; discriminate NXne0). exact F0.
  - apply Forall_cons; [|exact Qfacts]. cbn [fact_holds].
    assert (VB : vars_below nx (VAlu ALU_ADD (VAlu ALU_SRL (VP n wzero) (VL (wlit 3%uint63))) (VL S)) = true).
    { cbn [vars_below]. rewrite !andb_true_r. apply ltb_spec. exact (KEYLT n rn Hn). }
    rewrite (den_env_ext nx E E' _ EXT VB). fold w. cbn [den]. rewrite ENX.
    apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
  - unfold ops_apart in *. apply (Forall_impl _ (P := fun o0 => forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o0) (map (den E') (op_args o0))) ->
                             ~ in_based E' (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a))); [|exact Qapart].
    intros o0 H a Ex. destruct (H a Ex) as [NBa P]. split; [intros IB; apply NBa, INB; exact IB| exact P].
  - intros a FA. apply Qcov. destruct FA as [IB|SEG]; [left; apply INB; exact IB| right; exact SEG].
Qed.
End Sound.
End WithPc.

Definition sel_reg (r : r5) (st : sstate) : option int := match getr st r with VP n _ => Some n | _ => None end.
Definition sel_carg (i : nat) (st : sstate) : option int :=
  match UG.the_op st with
  | Some (_, _, _, ca) => match nth_error ca i with Some (VP n _) => Some n | _ => None end
  | None => None
  end.
Definition gtvc_reg (pc : int) (r : r5) (S : w64) : contract := gtwinviewc_contract pc (sel_reg r) S.
Definition gtvc_carg (pc : int) (i : nat) (S : w64) : contract := gtwinviewc_contract pc (sel_carg i) S.

End GTwinViewC.
