(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState Trees TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 TreesRod6 Callee6 TreesApi6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation pend := (ds_pending ds).
Local Abbreviation bv := (ds_bi_valid ds).
Local Abbreviation bb := (ds_bi_buf ds).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
Hypothesis HBR0 : BR6 F mem0 S p PBL mem ds.
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_flush_bits ds) <= PBL.

Definition bC : cfg := CFG [] [] [EVar 1%nat] [] [].
Definition VB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17)].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | rewrite ?szwrap_small by lia; lia
            | symex_read_auto ].

Local Ltac run fuel dirs rds pins pv rv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in VB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6_rom] =>
    symex s6_segs bC fuel dirs rdv pinsv vbv NoRegions pv rv F0 F0' (mkst regs pc m s6_rom) R HR Hfr Hms
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

Lemma cell2_lo : forall segs m a v,
  cell segs m a 2 v -> 0 <= v < 65536 ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = v mod 256.
Proof.
  intros segs m a v Hc Hv. unfold cell in Hc.
  pose proof (rdn_firstn segs m 2 (zw a) _ 1 Hc ltac:(lia)) as H1. cbn [firstn Z_to_le_bytes] in H1.
  exists [Z_to_bv 8 v]. split; [exact H1|]. rewrite bytes_le_single, Z_to_bv_unsigned. change (bv_modulus 8%N) with 256. reflexivity.
Qed.

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

Theorem tr_flush_bits_run : forall regs,
  getr regs 10 = zw S -> getr regs 1 = ra ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ad94 : word) mem s6_rom) (mkst R ra m' s6_rom)
    /\ BR6 F mem0 S p PBL m' (tr_flush_bits ds)
    /\ (forall r : reg, reg_in r FB_CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P1.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  pose proof Hbinv as (Hbv & Hbb & Hpend).
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HBR0) as (C40 & C16 & C5936 & C5940 & Cpb).
  pose proof (cell2_lo _ _ _ _ C5936 ltac:(lia)) as Rlo.
  pose proof (cell2_hi _ _ _ _ C5936 ltac:(lia) ltac:(lia) ltac:(lia)) as Rhi.
  replace (S + 5936 + 1) with (S + 5937) in Rhi by lia.
  assert (Hlo : 0 <= bb mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hhi : 0 <= bb / 256 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold tr_flush_bits in *.
  destruct (Z.eq_dec bv 16) as [C1|C1].
  - pose proof Hroom as HR'. rewrite bi_flush_eq16 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
    run 60%nat [false] [RVal (EVar 36); RVal (EVar 33); RVal (EVar 34); RFresh; RFresh]
        [(10, EVar 32)] [S; PB; pend; bb; bv] [bb mod 256; bb / 256].
    br_finish Hms P1 Hfr. st_eq.
    + f_equal; [f_equal; [lia | f_equal; change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity] | lia |].
      f_equal. rewrite wrap16_mod', (Z.mod_small bb) by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
    + lia.
    + reflexivity.
    + reflexivity.
  - destruct (Z_le_gt_dec 8 bv) as [C2|C2].
    + pose proof Hroom as HR'. rewrite bi_flush_eq8 in HR' |- * by lia. unfold upd4 in HR'. cbn in HR'.
      run 60%nat [true; false] [RVal (EVar 36); RVal (EVar 34); RVal (EVar 33); RFresh; RFresh]
          [(10, EVar 32)] [S; PB; pend; bb; bv] [bb mod 256; bb / 256].
      br_finish Hms P1 Hfr. st_eq.
      * f_equal; [lia|]. rewrite !wrap8_mod'. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
      * reflexivity.
      * rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply Z.mod_small. lia.
      * lia.
    + rewrite bi_flush_eq0 by lia. rewrite upd4_self.
      run 60%nat [true; true] [RVal (EVar 36)] [(10, EVar 32)] [S; 0; pend; bb; bv] NoVals.
      exists R, mem. split; [rewrite <- P1; exact Hms|]. split; [exact HBR0 | fr_weak Hfr].
Qed.

End Walk.

Theorem tr_flush_bits_run6_ok : tr_flush_bits_run6.
Proof.
  unfold tr_flush_bits_run6, A6_TR_FLUSH_BITS. intros F mem0 mem S p PBL ds ra regs HL Hret HB HI HR P10 P1.
  replace (zw 0x1ad94) with (0x1ad94%bv : word) by (apply bv_eq; reflexivity).
  exact (tr_flush_bits_run F mem0 mem S p PBL ds ra Hret HL HB HI HR regs P10 P1).
Qed.
End FXG.
