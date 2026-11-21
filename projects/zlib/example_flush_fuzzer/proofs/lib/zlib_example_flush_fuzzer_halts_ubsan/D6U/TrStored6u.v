(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout FillWinMem TreeMem BitsModel BitsModel2 BitsLib TrSmallModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees FillWinModel TreeModel SendModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u TreesRod6u Callee6u TreesApi6u TrApi6u TrSmall6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition Fmin (S PB PBL sp K : Z) : franges := [(S, dsl_SIZE); (PB, PBL); (sp - K, K)].

Lemma BRH_min : forall F S p PBL sp K, BRH F S p PBL -> BRH (Fmin S (p_pending_buf p) PBL sp K) S p PBL.
Proof.
  intros F S p PBL sp K (H1 & H2 & H3 & _ & _ & _ & _). unfold BRH, Fmin.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply sub_franges_here; unfold dsl_SIZE; lia|].
  split; [apply sub_franges_here; unfold dsl_SIZE; lia|].
  split; [apply sub_franges_here; unfold dsl_SIZE; lia|].
  apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma Fmin_S : forall S PB PBL sp K, sub_franges (Fmin S PB PBL sp K) S dsl_SIZE.
Proof. intros. unfold Fmin. apply sub_franges_here; lia. Qed.

Lemma BR_self : forall F Fc mem0 S p PBL m s,
  BR6u F mem0 S p PBL m s -> BR6u Fc m S p PBL m s.
Proof.
  intros F Fc mem0 S p PBL m s (A & B & C & D & E & G & H & I & J). unfold BR.
  repeat (split; [assumption|]). split; [apply agree_out_refl|]. split; [exact H|]. split; [exact I|]. intros x Hx; exact Hx.
Qed.

Lemma BR_back : forall F Fc mem0 S p PBL m m' s0 s,
  BR6u F mem0 S p PBL m s0 -> BR6u Fc m S p PBL m' s -> (forall x, in_franges Fc x -> in_franges F x) ->
  BR6u F mem0 S p PBL m' s /\ agree_out Fc m m'.
Proof.
  intros F Fc mem0 S p PBL m m' s0 s HB HB' HFc.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  split; [| exact Hag].
  eapply BR_rebase; [exact HB|]. eapply BR_weaken; [exact HB' | exact HFc].
Qed.

Section Walk.
Variables (F : franges) (mem0 mem : word -> option byte).
Variables (S : Z) (p : ds_ptrs) (PBL : Z) (ds : deflate_state) (ra : word).
Variables (sp : Z) (buf : option Z) (bufp len last : Z).
Hypothesis MEMCPY : memcpy_run6u.
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation W := (p_window p).
Local Abbreviation WL := (arr_len (ds_window ds)).
Local Abbreviation pend := (ds_pending ds).
Local Abbreviation bv := (ds_bi_valid ds).
Local Abbreviation bb := (ds_bi_buf ds).
Local Abbreviation nb := (sb_nb ds last).
Local Abbreviation SP := (sp - 48).

Hypothesis Hret : ret_ok ra.
Hypothesis HLb : BRH F S p PBL.
(* 1.4: the called bi_windup stores bi_used (S + 5944) *)
Hypothesis Hbu : sub_franges F (S + 5944) 4.
Hypothesis HBR0 : BR6u F mem0 S p PBL mem ds.
Hypothesis Hbinv : BINV PBL ds.
Hypothesis Hroom : ds_pending (tr_stored_block ds buf len last) <= PBL.
Hypothesis Hlast : 0 <= last <= 1.
Hypothesis Hlen : 0 <= len < 2 ^ 32.
Hypothesis Hfr48 : call_frame F mem S PB PBL sp 48.
Hypothesis Hsrc : tsb_src6u F mem p ds buf bufp len.
Hypothesis HUB : UBT S p.

Definition CLOB : list reg := SB_CLOB6u.

Lemma HR1 : tsb_hP ds + 1 + 1 + 1 + 1 + len <= PBL.
Proof.
  pose proof Hroom as H. pose proof Hbinv as (Hbv & Hbb & _).
  rewrite tr_stored_block_eq, tsb_tail_pending in H by assumption. exact H.
Qed.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Lemma srl_check0 : forall l b, 0 <= l < 2 -> 14 <= b <= 16 -> zaluw ALU_SRL l (Z.lxor b (-1)) = 0.
Proof.
  intros l b Hl Hb.
  assert (El : l = 0 \/ l = 1) by lia. assert (Eb : b = 14 \/ b = 15 \/ b = 16) by lia.
  destruct El as [-> | ->]; destruct Eb as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

Local Ltac side_closer :=
  try solve [ assumption
            | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia); lia
            | change (2 ^ 3) with 8 in *; zcond_close
            | apply srl_check0; lia
            | symex_read_auto ].

Ltac br_fwd2 HB M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) (Z_to_le_bytes ?w ?v) =>
      br_fwd2 HB M1;
      lazymatch goal with
      | H1 : BR ?sg ?AL ?AD ?AB ?F ?mem0 ?S ?p ?PBL M1 ?s1, HL : BRH ?F ?S ?p ?PBL |- _ =>
          let H2 := fresh "HBR" in
          lazymatch a with
          | S + 40 => pose proof (BR_st_pending sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5936 => pose proof (BR_st_bi_buf sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5940 => pose proof (BR_st_bi_valid sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | S + 5936 + 4 => pose proof (BR_st_bi_valid sg AL AD AB F mem0 S p PBL HL M1 s1 v H1) as H2
          | _ =>
              first
                [ let Hi := fresh in
                  let ty := constr:(0 <= a - p_pending_buf p < PBL) in
                  assert (Hi : ty) by lia;
                  pose proof (BR_st_pb sg AL AD AB F mem0 S p PBL HL M1 s1 a (a - p_pending_buf p) v H1 ltac:(lia) Hi) as H2;
                  clear Hi
                | pose proof (BR_st_other sg AL AD AB F mem0 S p PBL HL M1 s1 a (Z_to_le_bytes w v) H1
                    ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes; unfold dsl_SIZE; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes; cbn; lia)
                    ltac:(rewrite length_Z_to_le_bytes;
                          solve [eapply sub_franges_mono; [eassumption | cbn; lia | cbn; lia]])) as H2 ]
          end;
          clear H1
      end
  | _ => let H := fresh "HBR" in pose proof HB as H
  end.

Definition hC : cfg := CFG [] [] [EVar 1%nat] [0x1bc44] [].
Definition hVB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 65536); (36%nat, 17);
   (37%nat, 2); (38%nat, 2 ^ 32); (39%nat, 2 ^ 63)].
Definition hPINS : list (Z * expr) :=
  [(10, EVar 32); (12, EVar 38); (13, EVar 37); (2, EAdd (EVar 39) (ELit 48))].

Definition TREGS (regs R : bvmap 5 word) : Prop :=
  getr R 9 = zw S /\ getr R 8 = zw len /\ getr R 18 = getr regs 11 /\ getr R 19 = zw 65535 /\ getr R 2 = zw (sp - 48).
Definition FRM (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  cell s6u_segs m (sp - 48 + 40) 8 (bv_unsigned ra) /\ cell s6u_segs m (sp - 48 + 32) 8 (bv_unsigned (getr regs 8))
  /\ cell s6u_segs m (sp - 48 + 24) 8 (bv_unsigned (getr regs 9)) /\ cell s6u_segs m (sp - 48 + 16) 8 (bv_unsigned (getr regs 18))
  /\ cell s6u_segs m (sp - 48 + 8) 8 (bv_unsigned (getr regs 19)).

Local Ltac hrun dirs rds pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in hPINS in
  let vbv := eval vm_compute in hVB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs hC 120%nat dirs rdv pinsv vbv NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Lemma E16 : 0 <= bv < 32 -> 0 <= bb < 2 ^ 16 -> (Z.lor (szwrap 16 bb) (zaluw ALU_SLL last bv)) mod 2 ^ 16 = nb.
Proof. intros H H'. unfold sb_nb. apply nb_eqm2; [exact H | rewrite szwrap_eqm by lia; apply Z.mod_small; exact H' | reflexivity]. Qed.

Lemma div_mod_byte1 : forall e, (e / 2 ^ 8) mod 2 ^ 8 = (e mod 2 ^ 16) / 2 ^ 8.
Proof.
  intros e. rewrite <- !Z.shiftr_div_pow2, <- !Z.land_ones by lia.
  apply Z.bits_inj'; intros n Hn.
  rewrite Z.land_spec, Z.shiftr_spec, Z.shiftr_spec, Z.land_spec, !Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec n 8), (Z.ltb_spec (n + 8) 16); try lia; reflexivity.
Qed.

Lemma byte1_eq6 : forall e nb, e mod 2 ^ 16 = nb -> wrap8 ((e / 2 ^ 8) mod 2 ^ 8) = wrap8 (Z.shiftr (wrap16 nb) 8).
Proof. intros e nb E. rewrite div_mod_byte1. apply byte1_eq. exact E. Qed.

Lemma srl_eq_exact6u : forall l b, 0 <= l < 2 -> 14 <= b <= 16 ->
  zaluw ALU_SRL l (0 - b + 16) mod 2 ^ 16 = Z.shiftr (wrap16 l) (Buf_size - b).
Proof.
  intros l b Hl Hbv. rewrite zaluw_srl_small by lia. rewrite wrap16_mod', (Z.mod_small l) by lia.
  rewrite Z.shiftr_div_pow2 by (unfold Buf_size; lia). unfold Buf_size. replace (0 - b + 16) with (16 - b) by lia.
  assert (Hp : 1 <= 2 ^ (16 - b)) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (H0 : 0 <= l / 2 ^ (16 - b)) by (apply Z.div_pos; lia).
  assert (H1 : l / 2 ^ (16 - b) <= l) by (apply Z.div_le_upper_bound; [lia|]; nia).
  apply Z.mod_small. lia.
Qed.

Definition HCLOB : list reg := (1 :: 2 :: 8 :: 9 :: 18 :: 19 :: SB_CLOB6u)%bv.

Lemma cell_write_same_at : forall M a b (w : nat) v,
  b = a -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
  cell s6u_segs (wbytes M (zw b) (Z_to_le_bytes w v)) a w v.
Proof. intros M a b w v -> Ha Hw. apply cell_write_same; assumption. Qed.

Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.

Local Ltac tregs HR Hfr :=
  let A := fresh "A" in
  unfold TREGS;
  repeat match goal with
  | |- _ /\ _ => split
  | |- getr ?R ?r = _ =>
      first [ rewrite (Hfr r) by reflexivity; first [reflexivity | assumption]
            | symex_reg HR r as A; rewrite A; first [reflexivity | assumption | f_equal; lia | rewrite zw_u; reflexivity] ]
  end.

Local Ltac hfin Hms HR Hfr P1 :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd2 HBR0 M;
      lazymatch goal with
      | HB : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [eapply BR_eqst; [exact HB|]; clear HB
                | split; [unfold FRM; rewrite <- P1; repeat match goal with |- _ /\ _ => split end; frame_cells
                         | split; [tregs HR Hfr | split; [tregs HR Hfr | split; [tregs HR Hfr | fr_weak Hfr]]]]]
      end
  end.

Lemma head_run : forall regs,
  getr regs 10 = zw S -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m1,
    msteps s6u_segs (mkst regs (0x1b9e4 : word) mem s6u_rom) (mkst R (0x1bc44 : word) m1 s6u_rom)
    /\ BR6u F mem0 S p PBL m1 (send_bits ds last 3)
    /\ FRM regs m1
    /\ TREGS regs R /\ getr R 10 = zw S /\ getr R 1 = zw 0x1bb1c
    /\ (forall r : reg, reg_in r HCLOB = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P12 P13 P2 P1.
  pose proof Hfr48 as (Hsp & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS. unfold mapped in Hmf.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  pose proof Hbinv as (Hbv & Hbb & Hpend).
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HBR0) as (C40 & C16 & C5936 & C5940 & Cpb).
  pose proof HR1 as HRm. pose proof (tsb_hP_range ds) as HPr. clear Hroom.
  assert (P2' : getr regs 2 = zw (sp - 48 + 48)) by (rewrite P2; f_equal; lia).
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19.
  pose proof (sb_nb_range ds last) as Hnb.
  destruct (Z.leb_spec bv 13) as [C1|C1].
  - rewrite send_bits_keep_eq by (unfold Buf_size; lia).
    hrun [false; false; true; false] [RVal (EVar 36); RVal (EVar 35)] [S; PB; pend; bb; bv; last; len; sp - 48].
    pose proof (E16 ltac:(lia) ltac:(lia)) as E.
    hfin Hms HR Hfr P1. st_eq; [reflexivity | reflexivity | exact E | reflexivity].
  - rewrite send_bits_flush_eq by (unfold Buf_size; lia).
    hrun [false; false; false; false; false; false; false; false; false; false; false; false; false; true]
         [RVal (EVar 36); RVal (EVar 35); RVal (EVar 34); RVal (EVar 33)] [S; PB; pend; bb; bv; last; len; sp - 48].
    pose proof (E16 ltac:(lia) ltac:(lia)) as E.
    hfin Hms HR Hfr P1. st_eq.
    + f_equal; [f_equal; [lia | exact (byte0_eq _ nb E)] | lia | apply byte1_eq6; exact E].
    + lia.
    + apply srl_eq_exact6u; lia.
    + rewrite szwrap32_small by lia. unfold Buf_size. lia.
Qed.

Definition Fbw : franges := [(S + 40, 8); (S + 5936, 2); (S + 5940, 4); (PB, PBL); (S + 5944, 4)].
(* 1.4: (S + 5944, 4) = bi_used, stored by bi_windup; kept last so BRH_bw's four positions are unchanged *)

Lemma Fbw_bu : sub_franges Fbw (S + 5944) 4.
Proof.
  unfold Fbw. apply sub_franges_later. apply sub_franges_later. apply sub_franges_later. apply sub_franges_later.
  apply sub_franges_here; lia.
Qed.

Lemma BRH_bw : BRH Fbw S p PBL.
Proof.
  pose proof HLb as (H1 & H2 & H3 & _ & _ & _ & _). unfold BRH, Fbw.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [apply sub_franges_here; lia|].
  split; [apply sub_franges_later; apply sub_franges_here; lia|].
  split; [apply sub_franges_later; apply sub_franges_later; apply sub_franges_here; lia|].
  apply sub_franges_later. apply sub_franges_later. apply sub_franges_later. apply sub_franges_here; lia.
Qed.

Lemma Fbw_sub : forall x, in_franges Fbw x -> in_franges F x.
Proof.
  pose proof HLb as (_ & _ & _ & H40 & H36 & H44 & HP). unfold Fbw.
  intros x [Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]; cbn in Hx.
  - apply H40. lia.
  - apply H36. lia.
  - apply H44. lia.
  - apply HP. exact Hx.
  - apply Hbu. lia.
Qed.

Lemma ret_ok_zw' : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (zw z).
Proof. intros z Hz H2. apply ret_ok_even. rewrite u_zw_small by lia. exact H2. Qed.

Lemma call_bw : forall regs (regs0 : bvmap 5 word) m1 X,
  BR6u F mem0 S p PBL m1 X -> BINV PBL X -> ds_pending (bi_windup X) <= PBL ->
  FRM regs0 m1 -> getr regs 10 = zw S -> getr regs 1 = zw 0x1bb1c ->
  exists R m2,
    msteps s6u_segs (mkst regs (0x1bc44 : word) m1 s6u_rom) (mkst R (0x1bb1c : word) m2 s6u_rom)
    /\ BR6u F mem0 S p PBL m2 (bi_windup X)
    /\ FRM regs0 m2
    /\ (forall r : reg, reg_in r BW_CLOB6u = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 X HB1 HBI Hroom' HF P10 P1.
  pose proof Hfr48 as (Hsp & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  pose proof (bi_windup_run6u_ok Fbw m1 m1 S p PBL X (zw 0x1bb1c) regs BRH_bw Fbw_bu
                (ret_ok_zw' 0x1bb1c ltac:(lia) eq_refl) (BR_self F Fbw mem0 S p PBL m1 X HB1) HBI Hroom' HUB P10 P1)
    as (R & m2 & Hms & HB' & Hfr).
  unfold A6U_BI_WINDUP' in Hms.
  replace (zw 0x1bc44) with (0x1bc44%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x1bb1c) with (0x1bb1c%bv : word) in Hms by (apply bv_eq; reflexivity).
  destruct (BR_back F Fbw mem0 S p PBL m1 m2 X _ HB1 HB' Fbw_sub) as [HB2 Hag].
  exists R, m2. split; [exact Hms|]. split; [exact HB2|]. split; [|exact Hfr].
  assert (FC : forall a v, cell s6u_segs m1 a 8 v -> SP <= a -> a + 8 <= sp -> cell s6u_segs m2 a 8 v).
  { intros a v Hc Ha1 Ha2. apply (cell_agree_out s6u_segs Fbw m1 m2 a 8 v Hag); [| lia | change (Z.of_nat 8) with 8; lia | exact Hc].
    unfold Fbw. intros x Hx [Hin|[Hin|[Hin|[Hin|[Hin|[]]]]]]; cbn in Hin; change (Z.of_nat 8) with 8 in Hx; lia. }
  destruct HF as (C40 & C32 & C24 & C16 & C8).
  unfold FRM. repeat split; (apply FC; [assumption | lia | lia]).
Qed.

Definition tC : cfg := CFG [] [] [EVar 37%nat] [0x2a824] [].
Definition tVB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 32); (36%nat, 2 ^ 63); (37%nat, 2 ^ 64);
   (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64)].
Definition tPINS : list (Z * expr) := [(9, EVar 32); (8, EVar 35); (2, EVar 36); (19, ELit 65535)].
Definition tPINS2 : list (Z * expr) := [(9, EVar 32); (8, EVar 35); (2, EVar 36)].

Local Ltac trun C rds pins dirs pv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vbv := eval vm_compute in tVB in
  let rdv := eval vm_compute in rds in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs C 120%nat dirs rdv pinsv vbv NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac bits8 :=
  rewrite ?wrap8_mod', ?wrap16_mod'; rewrite <- ?Z.shiftr_div_pow2 by lia; rewrite <- ?Z.land_ones by lia;
  change 65535 with (Z.ones 16);
  apply Z.bits_inj'; intros n Hn;
  repeat first [ rewrite Z.land_spec | rewrite Z.lxor_spec | rewrite Z.shiftr_spec by lia | rewrite Z.lnot_spec by lia
               | rewrite Z.testbit_ones_nonneg by lia ];
  repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia end;
  rewrite ?Bool.andb_true_r, ?Bool.andb_false_r, ?Bool.xorb_true_r, ?Bool.xorb_false_r; try reflexivity.

Lemma s6_b0 : forall l, wrap8 l = wrap8 (Z.land (wrap16 l) 255).
Proof. intros l. change 255 with (Z.ones 8). bits8. Qed.
Lemma s6_b1 : forall l, wrap8 (l / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 (wrap16 l)) 8).
Proof. intros l. bits8. Qed.
Lemma s6_b2 : forall l, wrap8 (Z.lxor l 65535) = wrap8 (Z.land (wrap16 (Z.lnot l)) 255).
Proof. intros l. change 255 with (Z.ones 8). bits8. Qed.
Lemma s6_b3 : forall l, wrap8 (Z.lxor l 65535 / 2 ^ 8) = wrap8 (Z.shiftr (wrap16 (wrap16 (Z.lnot l))) 8).
Proof. intros l. bits8. Qed.

Local Ltac len_bytes :=
  rewrite ?upd4_pending_buf;
  repeat first [ apply s6_b0 | apply s6_b1 | apply s6_b2 | apply s6_b3 | reflexivity | lia | f_equal ].

Local Ltac tfin Hms HB1 :=
  lazymatch type of Hms with
  | msteps _ _ (mkst ?R _ ?M _) =>
      br_fwd2 HB1 M;
      lazymatch goal with
      | HB : BR _ _ _ _ _ _ _ _ _ M ?s1 |- _ =>
          exists R, M; split; [exact Hms|]; clear Hms;
          split; [eapply BR_eqst; [exact HB|]; clear HB | ]
      end
  end.

Definition T0_DIRS : list bool := repeat false 12 ++ [true].

Lemma tail0_run : forall regs (regs0 : bvmap 5 word) m1 A1 P1,
  BR6u F mem0 S p PBL m1 (upd4 ds A1 P1 0 0) ->
  0 <= P1 -> P1 + 1 + 1 + 1 + 1 + len <= PBL -> len = 0 ->
  FRM regs0 m1 -> TREGS regs0 regs ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bb1c : word) m1 s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (tsb_tail ds A1 P1 buf len)
    /\ getr R 2 = zw sp /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9
    /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19 /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r (1 :: 2 :: 8 :: 9 :: 18 :: 19 :: CLOB)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 A1 P1 HB1 HP0 HP1 Hl0 (C40f & C32f & C24f & C16f & C8f) (P9 & P8 & P18 & P19 & P2).
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB1) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB1) as (C40 & C16 & _ & _ & Cpb). cbn [upd4 ds_pending set_bi_valid set_bi_buf set_pending set_pending_buf] in C40.
  pose proof Hfr48 as (Hsp & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS. clear Hroom.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof Hret as Hret'. rewrite <- (zw_u ra) in Hret'. unfold ret_ok in Hret'.
  trun tC [RVal (EVar 34); RVal (EVar 33); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41)] tPINS T0_DIRS
       [S; PB; P1; len; sp - 48; bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9);
        bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19)].
  tfin Hms HB1.
  { unfold tsb_tail, tsb_lenA. replace (negb (len =? 0)) with false by (subst len; reflexivity).
    st_eq; [len_bytes | lia | reflexivity | reflexivity]. }
  symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9.
  symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19. symex_reg HR (1%bv : reg) as A1r.
  split; [rewrite A2; f_equal; lia|]. split; [exact A8|]. split; [exact A9|]. split; [exact A18|]. split; [exact A19|].
  split; [exact A1r|]. fr_weak Hfr.
Qed.

Definition T1_DIRS : list bool := repeat false 12 ++ [false; false; false].

Lemma t1_blk : forall regs (regs0 : bvmap 5 word) m1 A1 P1,
  BR6u F mem0 S p PBL m1 (upd4 ds A1 P1 0 0) ->
  0 <= P1 -> P1 + 1 + 1 + 1 + 1 + len <= PBL -> len <> 0 ->
  FRM regs0 m1 -> TREGS regs0 regs ->
  exists R m2,
    msteps s6u_segs (mkst regs (0x1bb1c : word) m1 s6u_rom) (mkst R (0x2a824 : word) m2 s6u_rom)
    /\ BR6u F mem0 S p PBL m2 (upd4 ds (tsb_lenA A1 P1 len) (P1 + 1 + 1 + 1 + 1) 0 0)
    /\ FRM regs0 m2
    /\ getr R 10 = zw (PB + (P1 + 1 + 1 + 1 + 1)) /\ getr R 11 = getr regs0 11 /\ getr R 12 = zw len
    /\ getr R 1 = zw 0x1bc18 /\ getr R 2 = zw (sp - 48) /\ getr R 9 = zw S /\ getr R 8 = zw len
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 A1 P1 HB1 HP0 HP1 Hl0 (C40f & C32f & C24f & C16f & C8f) (P9 & P8 & P18 & P19 & P2).
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB1) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB1) as (C40 & C16 & _ & _ & Cpb). cbn [upd4 ds_pending set_bi_valid set_bi_buf set_pending set_pending_buf] in C40.
  pose proof Hfr48 as (Hsp & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS. clear Hroom.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  trun tC [RVal (EVar 34); RVal (EVar 33)] tPINS T1_DIRS
       [S; PB; P1; len; sp - 48; bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9);
        bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19)].
  tfin Hms HB1.
  { unfold tsb_lenA. st_eq; [len_bytes | lia | reflexivity | reflexivity]. }
  split; [unfold FRM; repeat match goal with |- _ /\ _ => split end; frame_cells|].
  symex_reg HR (10%bv : reg) as A10. symex_reg HR (12%bv : reg) as A12.
  symex_reg HR (1%bv : reg) as A1r. symex_reg HR (2%bv : reg) as A2. symex_reg HR (9%bv : reg) as A9. symex_reg HR (8%bv : reg) as A8.
  symex_reg HR (11%bv : reg) as A11.
  split; [rewrite A10; f_equal; lia|]. split; [rewrite A11; exact P18|]. split; [exact A12|].
  split; [exact A1r|]. split; [exact A2|]. split; [exact A9|]. split; [exact A8|]. fr_weak Hfr.
Qed.

Lemma copy_blk : forall regs m2 A2 P2 (off : Z),
  BR6u F mem0 S p PBL m2 (upd4 ds A2 P2 0 0) ->
  0 <= P2 -> P2 + len <= PBL -> 0 < len ->
  buf = Some off -> bufp = W + off -> 0 <= off -> off + len <= WL ->
  cells s6u_segs mem W 1 1 WL (arr_get (ds_window ds)) ->
  (forall j, off <= j < off + len -> 0 <= arr_get (ds_window ds) j < 256) ->
  0 <= W -> W + WL <= 2 ^ 63 -> disj_franges F W WL ->
  getr regs 10 = zw (PB + P2) -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 1 = zw 0x1bc18 ->
  exists R m3,
    msteps s6u_segs (mkst regs (0x2a824 : word) m2 s6u_rom) (mkst R (0x1bc18 : word) m3 s6u_rom)
    /\ BR6u F mem0 S p PBL m3 (upd4 ds (arr_blit A2 P2 (ds_window ds) off len) P2 0 0)
    /\ (forall a w v, cell s6u_segs m2 a w v -> 0 <= a -> a + Z.of_nat w <= PB \/ PB + PBL <= a -> a + Z.of_nat w <= 2 ^ 64 ->
          cell s6u_segs m3 a w v)
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m2 A2 P2 off HB2 HP0 HP1 Hl0 Hbuf Hbufp Hoff0 Hoff1 HWc HWb HW0 HW1 HWF A10 A11 A12 A1r.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _ & _ & _ & HFPB). unfold dsl_SIZE in HS', HD.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB2) as (_ & _ & _ & _ & Hag2 & MS & MP & _).
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HBR0) as (_ & _ & _ & _ & Hag0 & _ & _ & _).
  assert (HWc2 : cells s6u_segs m2 W 1 1 WL (arr_get (ds_window ds))).
  { apply (cells_agree_out s6u_segs F mem m2); try lia; [| | exact HWc].
    - exact (agree_out_via F mem0 mem m2 Hag0 Hag2).
    - replace (1 * WL) with WL by lia. exact HWF. }
  set (n := Z.to_nat len).
  set (bs := fbytes (arr_get (ds_window ds)) off n).
  assert (Hrd : rdn s6u_segs m2 (zw (W + off)) n = Some bs).
  { subst bs. apply (cells_rdn s6u_segs m2 W WL); try lia. exact HWc2. }
  assert (Hapart : PB + PBL <= W \/ W + WL <= PB).
  { apply (franges_apart F); [exact HFPB | exact HWF | lia | lia]. }
  rewrite Hbufp in A11.
  destruct (MEMCPY m2 regs (PB + P2) (W + off) n bs (zw 0x1bc18) Hrd
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(eapply mapped_sub; [exact MP | lia | lia])
              ltac:(apply ret_ok_zw'; [lia | reflexivity])
              A1r A10 A11 ltac:(replace (Z.of_nat n) with len by lia; exact A12))
    as (R & Hms & B10 & Hfr).
  symex_pc_lit_in Hms.
  exists R, (wbytes m2 (zw (PB + P2)) bs). split; [exact Hms|].
  assert (Hbsl : length bs = n) by (subst bs; apply fbytes_length).
  split.
  { replace len with (Z.of_nat n) by lia.
    change (upd4 ds (arr_blit A2 P2 (ds_window ds) off (Z.of_nat n)) P2 0 0)
      with (set_pending_buf (upd4 ds A2 P2 0 0)
              (arr_blit (ds_pending_buf (upd4 ds A2 P2 0 0)) P2 (ds_window (upd4 ds A2 P2 0 0)) off (Z.of_nat n))).
    apply (BR_memcpy_pb _ _ _ _ F mem0 S p PBL HLb m2 _ P2 off n bs HB2); [reflexivity | | lia | lia].
    intros j Hj. apply HWb. lia. }
  split.
  { intros a w v Hc Ha Hd Hw. apply cell_write_other; rewrite ?Hbsl; try lia. exact Hc. }
  exact Hfr.
Qed.

Lemma t2_blk : forall regs (regs0 : bvmap 5 word) m3 A3 P2,
  BR6u F mem0 S p PBL m3 (upd4 ds A3 P2 0 0) ->
  0 <= P2 -> P2 + len <= PBL ->
  FRM regs0 m3 ->
  getr regs 2 = zw (sp - 48) -> getr regs 9 = zw S -> getr regs 8 = zw len ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bc18 : word) m3 s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (upd4 ds A3 (P2 + len) 0 0)
    /\ getr R 2 = zw sp /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9
    /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19 /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 18; 19]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m3 A3 P2 HB3 HP0 HP1 (C40f & C32f & C24f & C16f & C8f) P2r P9 P8.
  pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
  open_ubt HUB.
  destruct (BR_out _ _ _ _ _ _ _ _ _ _ _ HB3) as (_ & _ & _ & _ & _ & MS & MP & _). unfold mapped, dsl_SIZE in MS, MP.
  destruct (BR_cells _ _ _ _ _ _ _ _ _ _ _ HB3) as (C40 & C16 & _ & _ & Cpb). cbn [upd4 ds_pending set_bi_valid set_bi_buf set_pending set_pending_buf] in C40.
  pose proof Hfr48 as (Hsp & HFf & Hmf & HfS & HfP). unfold dsl_SIZE in HfS. clear Hroom.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19.
  pose proof Hret as Hret'. rewrite <- (zw_u ra) in Hret'. unfold ret_ok in Hret'.
  trun tC [RVal (EVar 34); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41)] tPINS2 NoDirs
       [S; 0; P2; len; sp - 48; bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9);
        bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19)].
  tfin Hms HB3.
  { st_eq; [reflexivity | lia | reflexivity | reflexivity]. }
  symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9.
  symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19. symex_reg HR (1%bv : reg) as A1r.
  split; [rewrite A2; f_equal; lia|]. split; [exact A8|]. split; [exact A9|]. split; [exact A18|]. split; [exact A19|].
  split; [exact A1r|]. exact Hfr.
Qed.

Lemma tail_run : forall regs (regs0 : bvmap 5 word) m1 A1 P1,
  BR6u F mem0 S p PBL m1 (upd4 ds A1 P1 0 0) ->
  0 <= P1 -> P1 + 1 + 1 + 1 + 1 + len <= PBL ->
  FRM regs0 m1 -> TREGS regs0 regs -> getr regs0 11 = zw bufp ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1bb1c : word) m1 s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (tsb_tail ds A1 P1 buf len)
    /\ getr R 2 = zw sp /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9
    /\ getr R 18 = getr regs0 18 /\ getr R 19 = getr regs0 19 /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r (1 :: 2 :: 8 :: 9 :: 18 :: 19 :: CLOB)%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 A1 P1 HB1 HP0 HP1 HF HT Q11.
  destruct (Z.eq_dec len 0) as [Hl0|Hl0].
  - exact (tail0_run regs regs0 m1 A1 P1 HB1 HP0 HP1 Hl0 HF HT).
  - pose proof HT as (P9 & P8 & P18 & P19 & P2).
    destruct (Hsrc Hl0) as (off & Hbuf & Hbufp & Hoff0 & Hoff1 & HWc & HWb & HW0 & HW1 & HWF).
    destruct (t1_blk regs regs0 m1 A1 P1 HB1 HP0 HP1 Hl0 HF HT)
      as (R1 & m2 & Hms1 & HB2 & HF2 & A10 & A11 & A12 & A1r & A2 & A9 & A8 & Hfr1).
    pose proof HLb as HL'. destruct HL' as (HS' & HPB & HD & _). unfold dsl_SIZE in HS', HD.
    pose proof Hfr48 as (Hsp & _ & _ & HfS & HfP). unfold dsl_SIZE in HfS.
    rewrite Q11 in A11.
    destruct (copy_blk R1 m2 (tsb_lenA A1 P1 len) (P1 + 1 + 1 + 1 + 1) off HB2 ltac:(lia) ltac:(lia) ltac:(lia)
                Hbuf Hbufp Hoff0 Hoff1 HWc HWb HW0 HW1 HWF A10 A11 A12 A1r)
      as (R2 & m3 & Hms2 & HB3 & Hcell & Hfr2).
    pose proof (u64_range ra) as U1.
    assert (B2 : getr R2 2 = zw (sp - 48)) by (rewrite (Hfr2 2%bv eq_refl); exact A2).
    assert (B9 : getr R2 9 = zw S) by (rewrite (Hfr2 9%bv eq_refl); exact A9).
    assert (B8 : getr R2 8 = zw len) by (rewrite (Hfr2 8%bv eq_refl); exact A8).
    destruct HF2 as (C40f & C32f & C24f & C16f & C8f).
    destruct (t2_blk R2 regs0 m3 _ (P1 + 1 + 1 + 1 + 1) HB3 ltac:(lia) ltac:(lia)
                (conj (ltac:(apply Hcell; [exact C40f | lia | lia | change (Z.of_nat 8) with 8; lia]))
                  (conj (ltac:(apply Hcell; [exact C32f | lia | lia | change (Z.of_nat 8) with 8; lia]))
                  (conj (ltac:(apply Hcell; [exact C24f | lia | lia | change (Z.of_nat 8) with 8; lia]))
                  (conj (ltac:(apply Hcell; [exact C16f | lia | lia | change (Z.of_nat 8) with 8; lia]))
                        (ltac:(apply Hcell; [exact C8f | lia | lia | change (Z.of_nat 8) with 8; lia]))))))
                B2 B9 B8)
      as (R3 & m4 & Hms3 & HB4 & E2 & E8 & E9 & E18 & E19 & E1 & Hfr3).
    exists R3, m4. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2 | exact Hms3]. }
    split.
    { unfold tsb_tail. replace (negb (len =? 0)) with true by (symmetry; apply Bool.negb_true_iff, Z.eqb_neq; exact Hl0).
      rewrite Hbuf. exact HB4. }
    split; [exact E2|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. split; [exact E1|].
    intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
    rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [| exact Hr]; reflexivity.
Qed.

Theorem tr_stored_block_run : forall regs,
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R m',
    msteps s6u_segs (mkst regs (0x1b9e4 : word) mem s6u_rom) (mkst R ra m' s6u_rom)
    /\ BR6u F mem0 S p PBL m' (tr_stored_block ds buf len last)
    /\ (forall r : reg, reg_in r CLOB = false -> getr R r = getr regs r).
Proof.
  intros regs P10 P11 P12 P13 P2 P1.
  pose proof Hbinv as (Hbv & Hbb & Hpend).
  destruct (head_run regs P10 P12 P13 P2 P1) as (R1 & m1 & Hms1 & HB1 & HF1 & HT & Q10 & Q1 & Hfr1).
  pose proof HR1 as HRm. pose proof (tsb_hP_range ds) as HPr.
  pose proof (sb_nb_range ds last) as Hnb.
  assert (HBI1 : BINV PBL (send_bits ds last 3)).
  { unfold BINV. destruct (Z.leb_spec bv 13) as [C|C].
    - rewrite send_bits_keep_eq by (unfold Buf_size; lia). rewrite upd4_bi_valid, upd4_bi_buf, upd4_pending. lia.
    - rewrite send_bits_flush_eq by (unfold Buf_size; lia). rewrite upd4_bi_valid, upd4_bi_buf, upd4_pending.
      pose proof (shiftr_wrap16_range last (Buf_size - bv) ltac:(unfold Buf_size; lia)). unfold Buf_size in *. lia. }
  assert (Hrw : ds_pending (bi_windup (send_bits ds last 3)) <= PBL).
  { rewrite tsb_head_eq by lia. rewrite upd4_pending. lia. }
  destruct (call_bw R1 regs m1 (send_bits ds last 3) HB1 HBI1 Hrw HF1 Q10 Q1) as (R2 & m2 & Hms2 & HB2 & HF2 & Hfr2).
  rewrite tsb_head_eq in HB2 by lia.
  assert (HT2 : TREGS regs R2).
  { destruct HT as (T9 & T8 & T18 & T19 & T2). unfold TREGS.
    rewrite (Hfr2 9%bv eq_refl), (Hfr2 8%bv eq_refl), (Hfr2 18%bv eq_refl), (Hfr2 19%bv eq_refl), (Hfr2 2%bv eq_refl). auto. }
  destruct (tail_run R2 regs m2 (tsb_hA ds last) (tsb_hP ds) HB2 ltac:(lia) HRm HF2 HT2 P11)
    as (R3 & m3 & Hms3 & HB3 & E2 & E8 & E9 & E18 & E19 & E1 & Hfr3).
  exists R3, m3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
  split; [rewrite tr_stored_block_eq by assumption; exact HB3|].
  apply (frame_fix R3 regs 2%bv); [rewrite E2; symmetry; exact P2|].
  apply (frame_fix R3 regs 8%bv); [exact E8|].
  apply (frame_fix R3 regs 9%bv); [exact E9|].
  apply (frame_fix R3 regs 18%bv); [exact E18|].
  apply (frame_fix R3 regs 19%bv); [exact E19|].
  apply (frame_fix R3 regs 1%bv); [rewrite E1; symmetry; exact P1|].
  intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
  apply Hfr1. eapply reg_in_sub; [| exact Hr]; reflexivity.
Qed.

End Walk.

Theorem tr_stored_block_run6u_ok : tr_stored_block_run6u.
Proof.
  unfold tr_stored_block_run6u, A6U_TR_STORED_BLOCK.
  intros F mem0 mem S p PBL ds ra regs sp buf bufp stored_len last MC HL Hbu Hret HB HI HR Hlast Hlen Hfr Hsrc HU P10 P11 P12 P13 P2 P1.
  replace (zw 0x1b9e4) with (0x1b9e4%bv : word) by (apply bv_eq; reflexivity).
  exact (tr_stored_block_run F mem0 mem S p PBL ds ra sp buf bufp stored_len last MC Hret HL Hbu HB HI HR Hlast Hlen Hfr Hsrc HU
           regs P10 P11 P12 P13 P2 P1).
Qed.
End FXG.
