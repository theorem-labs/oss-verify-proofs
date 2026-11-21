(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees FillWinModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section WalkFB.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation pend := (ds_pending ds).
Local Abbreviation bv := (ds_bi_valid ds).
Local Abbreviation bb := (ds_bi_buf ds).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
Hypothesis HBR0 : BR6u F mem0 S p PBL mem ds.
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_flush_bits ds) <= PBL.
Hypothesis HUB : UBT S p.

Definition bC : cfg := CFG [] [] [EVar 1%nat] [] [].
Definition VB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | rewrite ?szwrap_small by lia; lia
            | change (2 ^ 3) with 8 in *; zcond_close
            | symex_read_auto ].

Local Ltac run fuel dirs rds pins pv rv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs bC fuel dirs rdv pinsv vbv NoRegions pv rv F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac br_finish Hms P1 Hfr :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HBR0 M;
      lazymatch goal with
      | HB : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [rewrite <- P1; exact Hms|];
          split; [eapply BR_eqst; [exact HB|] | fr_weak Hfr]
      end
  end.

Lemma cell2_hi : forall segs m a v,
  cell segs m a 2 v -> 0 <= v < 65536 -> 0 <= a -> a + 2 <= 2 ^ 64 ->
  exists bs, rdn segs m (zw (a + 1)) 1 = Some bs /\ bytes_le_to_Z bs = v / 256.
Proof.
  intros segs m a v Hc Hv Ha Ha2. unfold cell in Hc.
  pose proof (rdn_skipn segs m 2 (zw a) _ 1 Hc ltac:(lia)) as H1. cbn [skipn Z_to_le_bytes Nat.sub] in H1.
  replace (a + 1) with (a + Z.of_nat 1) by lia. rewrite zw_add_nat.
  exists [Z_to_bv 8 (Z.shiftr v 8)]. split; [exact H1|]. rewrite bytes_le_single, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8%N) with 256.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma w8_land255 : forall b, wrap8 (Z.land b 255) = wrap8 b.
Proof. intros b. unfold wrap8. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Lemma w8_hi16 : forall b, 0 <= b < 65536 -> wrap8 (Z.shiftr (wrap16 b) 8) = wrap8 (b / 256).
Proof.
  intros b Hb. rewrite wrap16_mod', (Z.mod_small b) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma shr8_div : forall b, 0 <= b -> Z.shiftr b 8 = b / 256.
Proof. intros b Hb. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Theorem tr_flush_bits_run : forall regs,
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bd28 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (tr_flush_bits ds)
    /\ (forall r : reg, reg_in r FB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  pose proof Hbinv as (Hbv & Hbb & Hpend).
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HBR0) as (C40 & C16 & C5936 & C5940 & Cpb).
  pose proof (cell2_hi _ _ _ _ C5936 ltac:(lia) ltac:(lia) ltac:(lia)) as Rhi.
  replace (S + 5936 + 1) with (S + 5937) in Rhi by lia.
  assert (Hlo : 0 <= bb mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hhi : 0 <= bb / 256 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold tr_flush_bits in *.
  destruct (Z.eq_dec bv 16) as [C1|C1].
  - pose proof Hroom as HR'. rewrite bi_flush_eq16 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
    run 80%nat [false; false; false; false; false; false; false; false; false]
        [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RFresh]
        [(10, EVar 32)] [S; PB; pend; bb; bv] [bb / 256].
    br_finish Hms P1 Hfr. st_eq.
    + f_equal; [f_equal; [lia | symmetry; apply w8_land255] | lia | symmetry; apply w8_hi16; lia].
    + lia.
    + reflexivity.
    + reflexivity.
  - destruct (Z_le_gt_dec 8 bv) as [C2|C2].
    + pose proof Hroom as HR'. rewrite bi_flush_eq8 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
      run 80%nat [false; false; true; false; false; false; false; false]
          [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RFresh]
          [(10, EVar 32)] [S; PB; pend; bb; bv] [bb / 256].
      br_finish Hms P1 Hfr. st_eq.
      * f_equal. lia.
      * reflexivity.
      * rewrite shr8_div by lia. apply Z.mod_small. lia.
      * rewrite szwrap32_small by lia. lia.
    + rewrite bi_flush_eq0 by lia. rewrite upd4_self.
      run 80%nat [false; false; true; true] [RVal (EVar 36)] [(10, EVar 32)] [S; 0; pend; bb; bv] NoVals.
      exists R, mem. split; [rewrite <- P1; exact Hms|]. split; [exact HBR0 | fr_weak Hfr].
Qed.

End WalkFB.

Theorem tr_flush_bits_run6u_ok : tr_flush_bits_run6u.
Proof.
  unfold tr_flush_bits_run6u, A6U_TR_FLUSH_BITS. intros F mem0 mem S p PBL ds ra regs HL Hret HB HI HR HU P10 P1.
  replace (zw 0x1bd28) with (0x1bd28%bv : word) by (apply bv_eq; reflexivity).
  exact (tr_flush_bits_run F mem0 mem S p PBL ds ra Hret HL HB HI HR HU regs P10 P1).
Qed.

Definition BW_CLOB6u : list reg := [10; 11; 12; 13; 14; 15; 16]%bv.
Definition A6U_BI_WINDUP' : Z := 0x1bc44.

Definition bi_windup_run6u : Prop :=
  forall (F : franges) (mem0 mem : word -> option byte) (S : Z) (p : ds_ptrs) (PBL : Z)
         (ds : deflate_state) (ra : word) (regs : bvmap 5 word),
    BRH F S p PBL -> sub_franges F (S + 5944) 4 -> ret_ok ra -> BR6u F mem0 S p PBL mem ds -> BINV PBL ds ->
    ds_pending (bi_windup ds) <= PBL -> UBT S p ->
    getr regs 10 = zw S -> getr regs 1 = ra ->
    exists R m',
      msteps s6u_segs (mkst regs (zw A6U_BI_WINDUP') mem s6u_rom) (mkst R ra m' s6u_rom)
      /\ BR6u F mem0 S p PBL m' (bi_windup ds)
      /\ (forall r : reg, reg_in r BW_CLOB6u = false -> getr R r = getr regs r).

Section WalkBW.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation pend := (ds_pending ds).
Local Abbreviation bv := (ds_bi_valid ds).
Local Abbreviation bb := (ds_bi_buf ds).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
(* 1.4: bi_windup now stores bi_used (`sw a0,8(a1)` at 0x1bcbc, S + 5944), a junk
   range of the layout that BRH's frame does not name; BitsLib.BR_st_bi_used keeps BR across it *)
Hypothesis Hbu : sub_franges F (S + 5944) 4.
Hypothesis HBR0 : BR6u F mem0 S p PBL mem ds.
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (bi_windup ds) <= PBL.
Hypothesis HUB : UBT S p.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | rewrite ?szwrap_small by lia; lia
            | change (2 ^ 3) with 8 in *; zcond_close
            | symex_read_auto ].

Local Ltac run fuel dirs rds pins pv rv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs bC fuel dirs rdv pinsv vbv NoRegions pv rv F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac br_finish Hms P1 Hfr :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd HBR0 M;
      lazymatch goal with
      | HB : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [rewrite <- P1; exact Hms|];
          split; [eapply BR_eqst; [exact HB|] | fr_weak Hfr]
      end
  end.

(* 1.4: the last store is bi_used (S + 5944); cross it with BR_st_bi_used, the rest with br_fwd *)
Local Ltac bw_finish Hms P1 Hfr :=
  try replace (S + 5936 + 8) with (S + 5944) in Hms by lia;
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ (wbytes ?M1 (zw (S + 5944)) (Z_to_le_bytes 4 ?v)) _) =>
      br_fwd HBR0 M1;
      lazymatch goal with
      | H1 : BR _ _ _ _ _ _ _ _ _ M1 ?s1 |- _ =>
          let H2 := fresh "HBR" in
          assert (H2 : BR _ _ _ _ _ _ _ _ _ (wbytes M1 (zw (S + 5944)) (Z_to_le_bytes 4 v)) s1)
            by (eapply BR_st_bi_used; eauto);
          exists R, (wbytes M1 (zw (S + 5944)) (Z_to_le_bytes 4 v)); split; [rewrite <- P1; exact Hms|];
          split; [eapply BR_eqst; [exact H2|] | fr_weak Hfr]
      end
  end.

Theorem bi_windup_run : forall regs,
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bc44 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (bi_windup ds)
    /\ (forall r : reg, reg_in r BW_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  pose proof Hbinv as (Hbv & Hbb & Hpend).
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HBR0) as (C40 & C16 & C5936 & C5940 & Cpb).
  pose proof (cell2_hi _ _ _ _ C5936 ltac:(lia) ltac:(lia) ltac:(lia)) as Rhi.
  replace (S + 5936 + 1) with (S + 5937) in Rhi by lia.
  assert (Hhi : 0 <= bb / 256 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  destruct (Z_lt_le_dec 8 bv) as [C1|C1].
  - pose proof Hroom as HR'. rewrite bi_windup_eq2 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
    run 80%nat [false; false; false; false; false; false; true; false; false]
        [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RFresh; RVal (EVar 36)]
        [(10, EVar 32)] [S; PB; pend; bb; bv] [bb / 256].
    bw_finish Hms P1 Hfr. st_eq.
    + f_equal; [f_equal; [lia | symmetry; apply w8_land255] | lia | symmetry; apply w8_hi16; lia].
    + lia.
    + reflexivity.
    + reflexivity.
  - destruct (Z_lt_le_dec 0 bv) as [C2|C2].
    + pose proof Hroom as HR'. rewrite bi_windup_eq1 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
      run 80%nat [false; true; false; false; false; false; false]
          [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RVal (EVar 35); RVal (EVar 36)]
          [(10, EVar 32)] [S; PB; pend; bb; bv] NoVals.
      bw_finish Hms P1 Hfr. st_eq; [f_equal; lia | reflexivity | reflexivity | reflexivity].
    + rewrite bi_windup_eq0 by lia.
      run 80%nat [false; true; true; false] [RVal (EVar 36); RVal (EVar 36)] [(10, EVar 32)] [S; 0; pend; bb; bv] NoVals.
      bw_finish Hms P1 Hfr. st_eq; reflexivity.
Qed.

End WalkBW.

Theorem bi_windup_run6u_ok : bi_windup_run6u.
Proof.
  unfold bi_windup_run6u, A6U_BI_WINDUP'. intros F mem0 mem S p PBL ds ra regs HL Hbu Hret HB HI HR HU P10 P1.
  replace (zw 0x1bc44) with (0x1bc44%bv : word) by (apply bv_eq; reflexivity).
  exact (bi_windup_run F mem0 mem S p PBL ds ra Hret HL Hbu HB HI HR HU regs P10 P1).
Qed.

Lemma arr_fill_nat_S : forall {A} k (a : parr A) ofs v,
  arr_fill_nat a ofs (S k) v = arr_set (arr_fill_nat a ofs k v) (ofs + Z.of_nat k) v.
Proof.
  induction k as [|k IH]; intros a ofs v.
  - cbn [arr_fill_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [arr_fill_nat] in *. rewrite (IH (arr_set a ofs v) (ofs + 1) v). f_equal. lia.
Qed.

Definition zst (s : deflate_state) (t : tree_id) (k : nat) : deflate_state :=
  set_tree_fc s t (arr_fill_nat (tree_fc s t) 0 k 0).

Lemma zst_0 : forall s t, zst s t 0 = s.
Proof. intros s [| |]; destruct s; reflexivity. Qed.

Lemma zst_S : forall s t k,
  set_tree_fc (zst s t k) t (arr_set (tree_fc (zst s t k) t) (Z.of_nat k) (wrap16 0)) = zst s t (S k).
Proof.
  intros s t k. unfold zst. rewrite tree_fc_set_tree_fc, set_tree_fc_twice.
  rewrite arr_fill_nat_S. change (wrap16 0) with 0. rewrite Z.add_0_l. reflexivity.
Qed.

Lemma zst_S' : forall s t k i, i = Z.of_nat k ->
  set_tree_fc (zst s t k) t (arr_set (tree_fc (zst s t k) t) i (wrap16 0)) = zst s t (S k).
Proof. intros s t k i ->. apply zst_S. Qed.

Lemma set_sym_next_tree_fc : forall s v a,
  set_tree_fc (set_sym_next s v) TL a = set_sym_next (set_tree_fc s TL a) v.
Proof. intros. destruct s; reflexivity. Qed.
Lemma tree_fc_set_sym_next : forall s v t, tree_fc (set_sym_next s v) t = tree_fc s t.
Proof. intros s v [| |]; reflexivity. Qed.
Lemma set_sym_next_opt_len : forall s a b,
  set_opt_len (set_sym_next s a) b = set_sym_next (set_opt_len s b) a.
Proof. intros. destruct s; reflexivity. Qed.
Lemma set_sym_next_static_len : forall s a b,
  set_static_len (set_sym_next s a) b = set_sym_next (set_static_len s b) a.
Proof. intros. destruct s; reflexivity. Qed.


Lemma init_block_eq6u : forall s,
  init_block s =
    let s3 := zst (zst (zst s TL 286) TD 30) TB 19 in
    set_matches (set_static_len (set_opt_len (set_sym_next
      (set_tree_fc s3 TL (arr_set (tree_fc s3 TL) 256 (wrap16 1))) 0) 0) 0) 0.
Proof.
  intros s. cbv zeta.
  rewrite set_sym_next_opt_len, set_sym_next_static_len.
  unfold init_block, set_Freq, zst, arr_fill. cbn [set_tree_fc tree_fc].
  change (Z.to_nat L_CODES) with 286%nat. change (Z.to_nat D_CODES) with 30%nat.
  change (Z.to_nat BL_CODES) with 19%nat. change END_BLOCK with 256.
  match goal with |- ?a = ?b => constr_eq a b end.
  reflexivity.
Qed.

Lemma tr_init_eq6 : forall s, tr_init s = init_block (set_bi_valid (set_bi_buf s 0) 0).
Proof. intros s. unfold tr_init. cbv zeta. match goal with |- ?a = ?b => constr_eq a b end. reflexivity. Qed.

Section WalkIB.
Variables (F : franges) (mem0 : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ra : word).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation BRm := (BR6u F mem0 S p PBL).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
Hypothesis HFS : sub_franges F S dsl_SIZE.
Hypothesis HUB : UBT S p.

Definition iC : cfg := CFG [] [] [EVar 1%nat] [0x1b768; 0x1b77c] [].
Definition iVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 600)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption | lia
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ => rewrite H; f_equal; lia end
            | change (2 ^ 3) with 8 in *; zcond_close
            | symex_read_auto ].

Local Ltac irun fuel pins dirs pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in iVB in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs iC fuel dirs NoReads pinsv vbv NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Definition IREGS (R : bvmap 5 word) : Prop :=
  getr R 10 = zw S /\ getr R 11 = zw (S + 5900) /\ getr R 12 = zw (S + 212) /\ getr R 13 = zw (S + 2504)
  /\ getr R 15 = zw (Z.lxor (S + 212) (-1)) /\ getr R 16 = zw 1144 /\ getr R 1 = ra.
Definition IPINS : list (Z * expr) :=
  [(10, EVar 32); (11, EAdd (EVar 32) (ELit 5900)); (12, EAdd (EVar 32) (ELit 212)); (13, EAdd (EVar 32) (ELit 2504));
   (15, EXor (EAdd (EVar 32) (ELit 212)) (ELit (-1))); (16, ELit 1144)].

Local Ltac lreg HR :=
  let A := fresh "A" in
  lazymatch goal with |- getr ?R ?r = _ =>
    symex_reg HR r as A; rewrite A; first [reflexivity | assumption | f_equal; lia | rewrite zw_u; reflexivity]
  end.
Local Ltac ltregs HR := unfold IREGS; repeat split; lreg HR.

Local Ltac kof o :=
  lazymatch o with
  | 2904 => constr:(37%nat) | 2920 => constr:(39%nat) | 2928 => constr:(40%nat)
  | 2944 => constr:(42%nat) | 2952 => constr:(43%nat) | 2968 => constr:(45%nat)
  | 5936 => constr:(56%nat) | 5940 => constr:(57%nat)
  end.

Local Ltac fw_tower Hf M :=
  lazymatch M with
  | wbytes ?M1 (zw (S + 5944)) (Z_to_le_bytes 4 ?v) =>
      (* 1.4: _tr_init zeroes bi_used (`sw zero,8(a1)`, S + 5944), a gap of dsl_layout *)
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6u_segs M1 S dsl_layout ?vs |- _ =>
          let H2 := fresh "HF" in
          pose proof (DSLayout.fields_write_gap s6u_segs M1 S dsl_layout vs dsl_SIZE 5944 (Z_to_le_bytes 4 v) H1
                        dsl_layout_within ltac:(rewrite length_Z_to_le_bytes; vm_compute; reflexivity)
                        ltac:(lia) ltac:(unfold dsl_SIZE; lia) ltac:(lia)
                        ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)) as H2;
          clear H1
      end
  | wbytes ?M1 (zw (S + ?o)) (Z_to_le_bytes ?w ?v) =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6u_segs M1 S dsl_layout ?vs |- _ =>
          let k := kof o in
          let H2 := fresh "HF" in
          pose proof (fields_write_field s6u_segs M1 S dsl_layout vs dsl_SIZE k o w v H1 eq_refl
                        ltac:(vm_compute; reflexivity) dsl_layout_within ltac:(lia) ltac:(unfold dsl_SIZE; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HF" in pose proof Hf as H
  end.

Lemma ti_pro : forall regs m ds,
  BRi6u F mem0 S p PBL m ds ->
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m1,
    msteps s6u_segs (mkst regs (0x1b6d0 : word) m s6u_rom) (mkst R (0x1b768 : word) m1 s6u_rom)
    /\ BRm m1 (set_bi_valid (set_bi_buf ds 0) 0)
    /\ IREGS R /\ getr R 14 = zw 0
    /\ (forall r : reg, reg_in r TI_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m ds HBI P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  open_ubt HUB.
  destruct HBI as ((d & Hf) & Harr & HLn & Cpb & Hlen & Hag & HmS & HmP & Hgr).
  pose proof HmS as MS. unfold mapped, dsl_SIZE in MS.
  irun 60%nat [(10, EVar 32)] [false; false; false] [S; 0].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      exists R, M; split; [exact Hms|]; clear Hms;
      split; [| split; [ltregs HR | split; [lreg HR | fr_weak Hfr]]];
      fw_tower Hf M
  end.
  lazymatch goal with |- BR _ _ _ _ _ _ _ _ _ ?M2 ?s1 =>
    lazymatch goal with H1 : fields s6u_segs M2 S dsl_layout ?vs |- _ =>
    assert (Ev : vs = dsR_vals6u s1 p S)
      by (destruct d as [[[[[d1 d2] d3] d4] d5] d6]; unfold dvals6u, dsl_vals; cbn [list_upd]; dsred; reflexivity);
    rewrite Ev in H1; rename H1 into HFt
    end
  end.
  unfold BR. split; [exact HFt|].
  split.
  { change (dsl_arrays s6u_segs ?M S (set_bi_valid (set_bi_buf ds 0) 0)) with (dsl_arrays s6u_segs M S ds).
    repeat (apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; [| lia | lia | lia | cbn; lia | cbn; lia]).
    exact Harr. }
  split; [unfold tree_lens in *; dsred; exact HLn|].
  split.
  { dsred. repeat (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]).
    exact Cpb. }
  split; [dsred; exact Hlen|].
  split.
  { repeat (apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; [| lia | cbn; lia | intros x Hx; apply HFS; unfold dsl_SIZE; cbn in Hx; lia]).
    exact Hag. }
  split; [repeat apply mapped_wbytes; exact HmS|]. split; [repeat apply mapped_wbytes; exact HmP|].
  intros x Hx. repeat apply wbytes_grows. exact (Hgr x Hx).
Qed.

Lemma ib_pro : forall regs m,
  mapped m S dsl_SIZE ->
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R,
    msteps s6u_segs (mkst regs (0x1b73c : word) m s6u_rom) (mkst R (0x1b768 : word) m s6u_rom)
    /\ IREGS R /\ getr R 14 = zw 0
    /\ (forall r : reg, reg_in r IB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m MS P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & _). unfold dsl_SIZE in HS'. unfold mapped, dsl_SIZE in MS.
  open_ubt HUB.
  irun 30%nat [(10, EVar 32)] [false] [S; 0].
  exists R. split; [exact Hms|]. split; [ltregs HR|]. split; [lreg HR|]. fr_weak Hfr.
Qed.

Lemma zstep1 : forall regs m s (k : nat),
  BRm m s -> Z.of_nat k < 286 -> IREGS regs -> getr regs 14 = zw (4 * Z.of_nat k) ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b768 : word) m s6u_rom)
           (mkst R (if Z.of_nat k + 1 =? 286 then (0x1b77c : word) else (0x1b768 : word)) m' s6u_rom)
    /\ BRm m' (set_tree_fc s TL (arr_set (tree_fc s TL) (Z.of_nat k) (wrap16 0)))
    /\ IREGS R /\ getr R 14 = zw (4 * (Z.of_nat k + 1))
    /\ (forall r : reg, reg_in r [14; 17]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m s k HB Hk HI P14. pose proof HI as (P10 & P11 & P12 & P13 & P15 & P16 & P1).
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _). unfold mapped, dsl_SIZE in MS.
  assert (FIN : forall R (pc : word) a,
    msteps s6u_segs (mkst regs (0x1b768 : word) m s6u_rom) (mkst R pc (wbytes m (zw a) (Z_to_le_bytes 2 0)) s6u_rom) ->
    a = S + 212 + 4 * Z.of_nat k ->
    IREGS R -> getr R 14 = zw (4 * (Z.of_nat k + 1)) -> (forall r : reg, reg_in r [14; 17]%bv = false -> getr R r = getr regs r) ->
    exists R' m',
      msteps s6u_segs (mkst regs (0x1b768 : word) m s6u_rom) (mkst R' pc m' s6u_rom)
      /\ BRm m' (set_tree_fc s TL (arr_set (tree_fc s TL) (Z.of_nat k) (wrap16 0)))
      /\ IREGS R' /\ getr R' 14 = zw (4 * (Z.of_nat k + 1))
      /\ (forall r : reg, reg_in r [14; 17]%bv = false -> getr R' r = getr regs r)).
  { intros R pc a Hms -> QI Q14 Hfr. exists R, (wbytes m (zw (S + 212 + 4 * Z.of_nat k)) (Z_to_le_bytes 2 0)).
    split; [exact Hms|]. split; [| split; [exact QI | split; [exact Q14 | exact Hfr]]].
    change (S + 212) with (S + toff TL). apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); [exact HB | cbn; lia]. }
  destruct (Z.eqb_spec (Z.of_nat k + 1) 286) as [E|NE].
  - irun 20%nat (IPINS ++ [(14, EShl (EVar 33) 2)]) [false; false] [S; Z.of_nat k].
    lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes _ (zw ?a) _) _) =>
      apply (FIN R _ a Hms); [lia | ltregs HR | lreg HR | fr_weak Hfr] end.
  - irun 20%nat (IPINS ++ [(14, EShl (EVar 33) 2)]) [false; true] [S; Z.of_nat k].
    lazymatch type of Hms with msteps _ _ (mkst _ _ (wbytes _ (zw ?a) _) _) =>
      apply (FIN R _ a Hms); [lia | ltregs HR | lreg HR | fr_weak Hfr] end.
Qed.

Lemma zloop : forall j (k : nat) regs m s,
    (Z.of_nat k + Z.of_nat j = 286)%Z -> (0 < j)%nat ->
    BRm m (zst s TL k) -> IREGS regs -> getr regs 14 = zw (4 * Z.of_nat k) ->
    exists R m',
      msteps s6u_segs (mkst regs (0x1b768 : word) m s6u_rom) (mkst R (0x1b77c : word) m' s6u_rom)
      /\ BRm m' (zst s TL (k + j))
      /\ IREGS R
      /\ (forall r : reg, reg_in r [14; 17]%bv = false -> getr R r = getr regs r).
Proof.
  induction j as [|j IH]; intros k regs m s Hkj Hj HB HI P14; [lia|].
  destruct (zstep1 regs m (zst s TL k) k HB ltac:(lia) HI P14) as (R1 & m1 & Hms1 & HB1 & HI1 & Q14 & Hfr1).
  rewrite zst_S in HB1.
  destruct (Z.eqb_spec (Z.of_nat k + 1) 286) as [E|NE].
  - exists R1, m1. split; [exact Hms1|]. split; [|split; [exact HI1 | exact Hfr1]].
    replace (k + Datatypes.S j)%nat with (Datatypes.S k) by lia. exact HB1.
  - destruct (IH (Datatypes.S k) R1 m1 s ltac:(lia) ltac:(lia) HB1 HI1
                ltac:(rewrite Q14; f_equal; lia)) as (R2 & m2 & Hms2 & HB2 & HI2 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [replace (k + Datatypes.S j)%nat with (Datatypes.S k + j)%nat by lia; exact HB2|].
    split; [exact HI2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
Qed.

Lemma BR_st_fc_at : forall m s t i v a,
  BRm m s -> 0 <= i < tsize t -> a = S + toff t + 4 * i ->
  BRm (wbytes m (zw a) (Z_to_le_bytes 2 v)) (set_tree_fc s t (arr_set (tree_fc s t) i (wrap16 v))).
Proof. intros m s t i v a HB Hi ->. apply (BR_st_fc _ _ _ _ F mem0 S p PBL HLb HFS); assumption. Qed.

Ltac ib_zero_step M1 t c base :=
  lazymatch goal with
  | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
      lazymatch s1 with
      | zst _ t _ => idtac
      | _ => rewrite <- (zst_0 s1 t) in H1
      end
  end;
  lazymatch goal with
  | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
      lazymatch s1 with
      | zst ?b t ?k =>
          let H2 := fresh "HBR" in
          let i := eval vm_compute in ((c - base) / 4)%Z in
          lazymatch goal with
          | |- context [wbytes M1 (zw ?a) (Z_to_le_bytes 2 ?v)] =>
              pose proof (BR_st_fc_at M1 s1 t i v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          | H : context [wbytes M1 (zw ?a) (Z_to_le_bytes 2 ?v)] |- _ =>
              pose proof (BR_st_fc_at M1 s1 t i v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          end;
          rewrite (zst_S' b t k i ltac:(reflexivity)) in H2; clear H1
      end
  end.

Ltac ib_fwd HB M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      ib_fwd HB M1;
      let c := lazymatch a with S + ?c1 + ?c2 => eval vm_compute in (c1 + c2)%Z | S + ?c1 => c1 end in
      let cz := eval vm_compute in (Z.leb 2504 c && Z.ltb c 2624)%bool in
      lazymatch cz with
      | true => ib_zero_step M1 TD c 2504%Z
      | false =>
      let cb := eval vm_compute in (Z.leb 2748 c && Z.ltb c 2824)%bool in
      lazymatch cb with
      | true => ib_zero_step M1 TB c 2748%Z
      | false =>
      lazymatch goal with
      | H1 : BR _ _ _ _ ?F ?mem0 ?S ?p ?PBL M1 ?s1 |- _ =>
          let H2 := fresh "HBR" in
          lazymatch c with
          | 5900 => pose proof (BR_st_sym_next _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 1236 => pose proof (BR_st_fc_at M1 s1 TL 256 v a H1 ltac:(cbn; lia) ltac:(cbn [toff]; lia)) as H2
          | 5912 => pose proof (BR_st_opt_len _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 5920 => pose proof (BR_st_static_len _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          | 5928 => pose proof (BR_st_matches _ _ _ _ F mem0 S p PBL HLb HFS M1 s1 v H1) as H2
          end;
          clear H1
      end end end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Definition IB_DIRS : list bool := repeat false 48.

Lemma ib_tail : forall regs m s,
  BRm m s -> IREGS regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b77c : word) m s6u_rom) (mkst R ra m' s6u_rom)
    /\ BRm m' (let s3 := zst (zst s TD 30) TB 19 in
               set_matches (set_static_len (set_opt_len (set_sym_next
                 (set_tree_fc s3 TL (arr_set (tree_fc s3 TL) 256 (wrap16 1))) 0) 0) 0) 0)
    /\ (forall r : reg, reg_in r IB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m s HB (P10 & P11 & P12 & P13 & P15 & P16 & P1).
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _). unfold mapped, dsl_SIZE in MS.
  irun 200%nat IPINS IB_DIRS [S; 0].
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      ib_fwd HB M; exists R, M; split; [rewrite <- P1; exact Hms|]; clear Hms;
      split; [cbv zeta; lazymatch goal with H : BR _ _ _ _ _ _ _ _ _ M _ |- _ => exact H end | fr_weak Hfr]
  end.
Qed.

Theorem init_block_run : forall regs m s,
  BRm m s -> getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b73c : word) m s6u_rom) (mkst R ra m' s6u_rom)
    /\ BRm m' (init_block s)
    /\ (forall r : reg, reg_in r IB_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m s HB P10 P1.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & _ & _ & MS & _ & _).
  destruct (ib_pro regs m MS P10 P1) as (R1 & Hms1 & HI1 & A14 & Hfr1).
  rewrite <- (zst_0 s TL) in HB.
  destruct (zloop 286%nat 0%nat R1 m s ltac:(lia) ltac:(lia) HB HI1 ltac:(rewrite A14; f_equal; lia))
    as (R2 & m2 & Hms2 & HB2 & HI2 & Hfr2).
  cbn [Nat.add] in HB2.
  destruct (ib_tail R2 m2 _ HB2 HI2) as (R3 & m3 & Hms3 & HB3 & Hfr3).
  exists R3, m3. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
  split; [rewrite init_block_eq6u; exact HB3|].
  intros r Hr. rewrite (Hfr3 r Hr). rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity). exact (Hfr1 r Hr).
Qed.

Theorem tr_init_run : forall regs m ds,
  BRi6u F mem0 S p PBL m ds -> getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b6d0 : word) m s6u_rom) (mkst R ra m' s6u_rom)
    /\ BRm m' (tr_init ds)
    /\ (forall r : reg, reg_in r TI_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs m ds HBI P10 P1.
  destruct (ti_pro regs m ds HBI P10 P1) as (R1 & m1 & Hms1 & HB1 & HI1 & A14 & Hfr1).
  set (s0 := set_bi_valid (set_bi_buf ds 0) 0) in HB1.
  rewrite <- (zst_0 s0 TL) in HB1.
  destruct (zloop 286%nat 0%nat R1 m1 s0 ltac:(lia) ltac:(lia) HB1 HI1 ltac:(rewrite A14; f_equal; lia))
    as (R2 & m2 & Hms2 & HB2 & HI2 & Hfr2).
  cbn [Nat.add] in HB2.
  destruct (ib_tail R2 m2 _ HB2 HI2) as (R3 & m3 & Hms3 & HB3 & Hfr3).
  exists R3, m3. split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
  split; [rewrite tr_init_eq6, init_block_eq6u; exact HB3|].
  intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity). exact (Hfr1 r Hr).
Qed.

End WalkIB.

Theorem init_block_run6u_ok : init_block_run6u.
Proof.
  unfold init_block_run6u, A6U_INIT_BLOCK. intros F mem0 mem S p PBL ds ra regs HL HFS Hret HB HU P10 P1.
  replace (zw 0x1b73c) with (0x1b73c%bv : word) by (apply bv_eq; reflexivity).
  exact (init_block_run F mem0 S p PBL ra Hret HL HFS HU regs mem ds HB P10 P1).
Qed.

Theorem tr_init_run6u_ok : tr_init_run6u.
Proof.
  unfold tr_init_run6u, A6U_TR_INIT. intros F mem0 mem S p PBL ds ra regs HL HFS Hret HB HU P10 P1.
  replace (zw 0x1b6d0) with (0x1b6d0%bv : word) by (apply bv_eq; reflexivity).
  exact (tr_init_run F mem0 S p PBL ra Hret HL HFS HU regs mem ds HB P10 P1).
Qed.
End FXG.
