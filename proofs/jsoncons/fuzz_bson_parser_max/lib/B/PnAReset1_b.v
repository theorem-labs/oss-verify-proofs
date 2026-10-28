(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx HeapIfaceANull. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMARS1.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Lemma srai_to fx R M (pc : Z) (W : bv 32) (rd rs : bv 5) (sh : bv 6) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false -> 0 <= pc -> pc + 4 < 2 ^ 64 ->
  msteps RSEGS (st fx R pc M) (st fx (regupd R rd (v_srai (getr R rs) (bv_unsigned sh))) (pc + 4) M).
Proof.
  intros HF HE HD HZ H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite (step_srai RSEGS R (Z_to_bv 64 pc) M (seg_rom RSEGS) W rd rs sh HF HE HD). rewrite HZ.
  f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_srai5_small d : 0 <= d < 2 ^ 63 -> v_srai (Z_to_bv 64 d) 5 = Z_to_bv 64 (d / 32).
Proof.
  intros Hd. unfold v_srai. f_equal.
  assert (S1 : bv_signed (Z_to_bv 64 d) = d).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_half_modulus 64) with (2 ^ 63). rewrite (Z.mod_small d) by lia. rewrite (Z.mod_small (d + 2 ^ 63)) by lia. lia. }
  rewrite S1. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma elem_of_In (x : Z) (l : list Z) : In x l -> x ∈ l.
Proof. induction l as [|a l IH]; intros H; [destruct H|]. destruct H as [<-|H]; [constructor| constructor; apply IH; exact H]. Qed.
Lemma fst_neq_app (l1 l2 : list (Z * Z)) B1 m1 B2 m2 :
  NoDup (map fst (l1 ++ l2)) -> In (B1, m1) l1 -> In (B2, m2) l2 -> B1 <> B2.
Proof.
  induction l1 as [|a l1 IH]; intros ND H1 H2; [destruct H1|]. cbn [app map] in ND. inversion ND as [|x l NI ND']. subst x l.
  destruct H1 as [->|H1].
  - cbn [fst] in NI. intros E. subst B2. apply NI. apply elem_of_In. rewrite map_app. apply in_or_app. right. apply (in_map fst l2 (B1, m2) H2).
  - apply IH; assumption.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LYa : L5A.as0_layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

(* [comment removed for export] *)
Lemma own_not_aclient LB1 LB2 FF LK cr Aw M V B m a sp scr :
  ri_inv HI (LB1 ++ LB2) FF LK cr Aw M V -> In (B, m) LB1 -> B <= a < B + m -> ~ aclient L ar LB2 FF sp scr a.
Proof.
  intros HH Hin Ha Hc.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & _ & ND & _).
  assert (INB : In (B, m) (LB1 ++ LB2)) by (apply in_or_app; left; exact Hin).
  pose proof (WB _ INB) as ((R0 & R1 & R2 & R3 & R4 & R5) & _ & _ & _ & AP & FA & _). cbn [fst snd] in *.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in R5.
  destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
  - destruct Hc as ((B2 & m2) & H2 & X). cbn [fst snd] in X.
    assert (NE : B <> B2) by exact (fst_neq_app LB1 LB2 B m B2 m2 ND Hin H2).
    pose proof (L5C.blocks_apart_in B m _ B2 m2 AP (L5C.in_lb_remove_neq B B2 m2 _ (in_or_app _ _ _ (or_intror H2)) (fun E => NE (eq_sym E)))). lia.
  - lia.
  - destruct R1 as [X|X]; lia.
  - destruct Hc as (f & Hf & X & _). destruct (FA f (in_or_app _ _ _ (or_introl Hf))); lia.
  - unfold in_shadow_of, S, SB in Hc. lia.
  - destruct Hc as (f & Hf & X). destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in FSAPP.
    unfold in_shadow_of, S, SB in X. unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. lia.
  - destruct Hc as ((B2 & m2) & H2 & X). pose proof (WB _ (in_or_app _ _ _ (or_intror H2))) as ((Z0 & Z1 & Z2 & Z3 & Z4 & Z5) & _).
    cbn [fst snd] in *. unfold app_mem in Z5. unfold in_shadow_of, S, SB in X. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ri_swap12 x y l FF LK cr Aw M V : ri_inv HI (x :: y :: l) FF LK cr Aw M V -> ri_inv HI (y :: x :: l) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ (y :: x :: l) FF FF LK cr Aw M V HH).
  - intros b. cbn [In]. tauto.
  - cbn [map] in *. assert (P : y.1 :: x.1 :: map fst l ≡ₚ x.1 :: y.1 :: map fst l) by apply perm_swap. rewrite P. exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
End WithHeap.

(* [comment removed for export] *)
Lemma acc_of_shadow_zero (M : word -> option byte) lo g a n :
  shadow_zero M lo g -> lo mod 8 = 0 -> lo <= a -> a + n <= lo + 8 * g -> aacc M a n.
Proof.
  intros SZ Hlo H1 H2 x Hx. left.
  assert (E : S x = S lo + (x - lo) / 8).
  { unfold S. assert (L8 : lo = (lo / 8) * 8) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
    replace x with ((x - lo) + (lo / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
  rewrite E. apply SZ. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma agA_trans (M1 M2 M3 : word -> option byte) a n : PMFA.agA M1 M2 a n -> PMFA.agA M2 M3 a n -> PMFA.agA M1 M3 a n.
Proof.
  intros [G1 S1] [G2 S2]. split.
  - intros i Hi. rewrite (G2 i Hi). apply G1. exact Hi.
  - intros x Hx. rewrite (S2 x Hx). apply S1. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma agsh_blk (L : asan_layout) (ar : asan_run) LB FF sp scr W M M' q m :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W -> In (q, m) LB -> 0 <= q -> q + m <= 2 ^ 47 -> PMFA.agsh M M' q m.
Proof.
  intros E WAPP Hin Hq Hqm x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SH. unfold BIGSHADOW_LO, BIGSHADOW_HI in SH.
  apply E. split; [lia|]. split.
  - unfold aclient, aclient_g. do 6 right. exists (q, m). split; [exact Hin|]. cbn [fst snd]. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
  - apply (PMKA.wapp_outside_shadow W (S x) WAPP). unfold BIGSHADOW_LO, BIGSHADOW_HI. lia.
Qed.

(* [comment removed for export] *)
Lemma reset_postA (M M5 : word -> option byte) op ois (s : PM.pst) :
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M op ois s -> (1 <= length (PM.p_stk s))%nat ->
  0 <= op -> op + 384 <= 2 ^ 64 -> 0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 ->
  PMFA.agA M M5 op 8 -> PMFA.agA M M5 (op + 16) 320 -> PMFA.agsh M M5 op 384 -> PMFA.agA M M5 (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  L5.defined M5 op 384 ->
  L5.u8_at RSEGS M5 (op + 8) 1 -> L5.u8_at RSEGS M5 (op + 9) 0 -> L5.u32_at RSEGS M5 (op + 12) 0 ->
  PM.vstr_at RSEGS PMSPA.accA M5 (op + 336) (PM.p_tb (PMSPA.pst_reset s)) ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA M5 (op + 360) (PM.p_b s) (PM.p_k s) [PM.ps_root] ->
  PM.parser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA M5 op ois (PMSPA.pst_reset s).
Proof.
  intros (H0 & D & C0 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) LEN Ho Ho' Hq Hq'
         AG0 AG16 SH AGQ D5 C8 C9 C12 TB5 VEC5.
  destruct AG0 as [G0 _]. destruct AG16 as [G16 S16].
  unfold PM.parser_at. cbn [PMSPA.pst_reset PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  split; [apply (L5C.u64_at_agree RSEGS M M5); [exact G0|lia|lia|exact H0]|].
  split; [exact D5|].
  split; [apply (PMFA.accA_agree M M5); [apply (PMFA.agsh_sub M M5 op 384 op 24 SH); lia| exact C0]|].
  split; [exact C8|]. split; [exact C9|]. split; [exact C12|].
  split; [apply (L5C.u8_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 16) 1 G16); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 20) 4 G16); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M M5 (op + 32)); [lia|lia| apply (PMFA.agA_sub M M5 (op + 16) 320); [split; assumption|lia|lia]| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS M M5 (op + 24) ois (ois + 16) (PM.p_src s)); [lia|lia|exact Hq|exact Hq'
            | apply (PMFA.agA_sub M M5 (op + 16) 320); [split; assumption|lia|lia]| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 320) 4 G16); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS M M5); [apply (L5C.agree_on_sub M M5 (op + 16) 320 (op + 328) 8 G16); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M5); [apply (PMFA.agsh_sub M M5 op 384 (op + 320) 64 SH); lia| exact C320]|].
  split; [exact TB5|]. split; [exact VEC5|].
  split; [right; reflexivity|]. split; [left; reflexivity|]. unfold PM.MAX_DEPTH; lia.
Qed.
End PMARS1.
