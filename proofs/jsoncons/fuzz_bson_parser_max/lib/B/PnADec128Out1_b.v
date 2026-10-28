(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDecFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAXD_b PnADec128Defs_b PnADec128K_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128OP1_b PnADec128OP2_b PnADec128OP3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADO1.
Import L5A. Import L5CA. Import L5SAR. Import PNADK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Section View.
Variables (R0 : bvmap 5 word) (S first vp F fl r : Z).
Hypothesis G : PNADD.geom S first vp F fl.

(* [comment removed for export] *)
Definition Wout (a : Z) : Prop := (first <= a < first + 42) \/ (F + 240 <= a < F + 264) \/ (PNADD.SH F + 30 <= a < PNADD.SH F + 33).
Definition vout (MV M : mem) : Prop := mem_grows MV M /\ PNADD.agree_but Wout MV M.
Lemma vout_refl M : vout M M.
Proof. split; [intros x Hx; exact Hx| intros a _ _; reflexivity]. Qed.
Lemma vout_trans M1 M2 M3 : vout M1 M2 -> vout M2 M3 -> vout M1 M3.
Proof.
  intros (G1 & A1) (G2 & A2). split; [intros x Hx; apply G2; apply G1; exact Hx|].
  intros a Ha Hn. rewrite (A2 a Ha Hn). exact (A1 a Ha Hn).
Qed.
Lemma vout_step M1 M2 M3 (P : Z -> Prop) : vout M1 M2 -> mem_grows M2 M3 ->
  (forall i : Z, 0 <= i < 2 ^ 64 -> ~ P i -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)) -> (forall a, P a -> Wout a) -> vout M1 M3.
Proof.
  intros V MG FZ PW. apply (vout_trans M1 M2 M3 V). split; [exact MG|]. intros a Ha Hn. apply FZ; [exact Ha|]. intros Pa. exact (Hn (PW a Pa)).
Qed.

Lemma geomF : 0 <= F / 8 <= 17592186044352 /\ 2147450880 <= PNADD.SH F /\ PNADD.SH F + 64 <= 17594333495296.
Proof.
  unfold PNADD.geom in G. destruct G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GFF1 & _).
  assert (E0 : 0 <= F / 8 <= 17592186044352) by (clear - GFF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  unfold PNADD.SH, PNADD.SBv. clear - E0. lia.
Qed.
Lemma geomfirst : 0 <= first / 8 <= 17592186044410 /\ 2147450880 <= PNADD.SH first /\ PNADD.SH first + 6 <= 17594333495296.
Proof.
  unfold PNADD.geom in G. destruct G as (_ & _ & GF1 & _).
  assert (E0 : 0 <= first / 8 <= 17592186044410) by (clear - GF1; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  unfold PNADD.SH, PNADD.SBv. clear - E0. lia.
Qed.

Lemma geomZ : F = 8 * (F / 8) /\ first = 8 * (first / 8).
Proof.
  unfold PNADD.geom in G. destruct G as (_ & _ & _ & GF8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & GFF32 & _).
  pose proof (Z.div_mod F 8 ltac:(clear; lia)) as D1. pose proof (Z.div_mod F 32 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound F 8 ltac:(clear; lia)) as D3.
  pose proof (Z.div_mod first 8 ltac:(clear; lia)) as D4. rewrite GFF32 in D2. rewrite GF8 in D4.
  split; [clear - D1 D2 D3; Lia.lia| clear - D4; Lia.lia].
Qed.
Lemma al4 i : (F + 32 + 4 * i) mod 4 = 0.
Proof.
  pose proof geomZ as (ZF & _). replace (F + 32 + 4 * i) with ((2 * (F / 8) + 8 + i) * 4) by (clear - ZF; Lia.lia). apply Z_mod_mult.
Qed.
(* [comment removed for export] *)
Lemma nW_img a : 65536 <= a < 6905856 -> ~ Wout a.
Proof.
  intros Ha. pose proof geomF as (E0 & SHlo & SHhi). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout. clear - Ha SHlo GFI GFFI. Lia.lia.
Qed.
Lemma nW_stk a : S - 256 <= a < S -> ~ Wout a.
Proof.
  intros Ha. pose proof geomF as (E0 & SHlo & SHhi). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout. clear - Ha SHhi GS1 GFS GFFS. Lia.lia.
Qed.
Lemma nW_F a : (F <= a < F + 240 \/ F + 264 <= a < F + 512) -> ~ Wout a.
Proof.
  intros Ha. pose proof geomF as (E0 & SHlo & SHhi). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout. clear - Ha SHlo SHhi GFFSH GFFf. Lia.lia.
Qed.
Lemma nW_shfirst a : PNADD.SH first <= a < PNADD.SH first + 6 -> ~ Wout a.
Proof.
  intros Ha. pose proof geomF as (E0 & SHlo & SHhi). pose proof geomfirst as (E1 & SFlo & SFhi). pose proof geomZ as (ZF & Zf). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout, PNADD.SH, PNADD.SBv in *. clear - Ha ZF Zf E0 E1 GFSH GFFSH GFFf. Lia.lia.
Qed.
Lemma nW_shF a : (PNADD.SH F <= a < PNADD.SH F + 30 \/ PNADD.SH F + 33 <= a < PNADD.SH F + 64) -> ~ Wout a.
Proof.
  intros Ha. pose proof geomF as (E0 & SHlo & SHhi). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout, PNADD.SH, PNADD.SBv in *. clear - Ha E0 GFSH GFFSH. Lia.lia.
Qed.
Lemma nW_fl : ~ Wout fl.
Proof.
  pose proof geomF as (E0 & SHlo & SHhi). unfold PNADD.geom in G.
  destruct G as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold Wout, PNADD.SH, PNADD.SBv in *. clear - E0 GFLSH GFLF GFLf. Lia.lia.
Qed.

Lemma MIA_out MV M : PNADD.MIA R0 S first r F fl MV -> vout MV M -> PNADD.MIA R0 S first r F fl M.
Proof.
  intros (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG) (MG & AG).
  pose proof geomF as (E0 & SHlo & SHhi). pose proof geomfirst as (E1 & SFlo & SFhi).
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  assert (AI : forall i, 65536 <= i < 6905856 -> M (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Hi; apply AG; [clear - Hi; lia| exact (nW_img i Hi)]).
  assert (AS : forall i, S - 256 <= i < S -> M (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Hi; apply AG; [clear - Hi GS1; lia| exact (nW_stk i Hi)]).
  split; [exact (L5.writable_grows RSEGS MV M _ _ MG W1)|]. split; [exact (L5.writable_grows RSEGS MV M _ _ MG W2)|].
  split; [exact (L5.writable_grows RSEGS MV M _ _ MG W3)|]. split; [exact (L5.writable_grows RSEGS MV M _ _ MG W4)|].
  split; [exact (L5.writable_grows RSEGS MV M _ _ MG W5)|].
  split. { intros i Hi. rewrite AI by (clear - Hi; lia). apply IC. exact Hi. }
  split. { eapply L5C.u64_at_agree; [intros i Hi; apply AI; clear - Hi; lia| clear; lia| clear; lia| exact CSB]. }
  split. { apply (PMF.u32_at_agree RSEGS MV M); [intros i Hi; apply AI; clear - Hi; lia| clear; lia| clear; lia| exact CUAR]. }
  split. { unfold PNADD.saves in *. destruct SV as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13).
           repeat split; (eapply L5C.u64_at_agree; [intros i Hi; apply AS; clear - Hi; lia| clear - GS1; lia| clear - GS1; lia| eassumption]). }
  split. { eapply L5C.u64_at_agree; [intros i Hi; apply AS; clear - Hi; lia| clear - GS1; lia| clear - GS1; lia| exact C128]. }
  split. { eapply L5C.u64_at_agree; [intros i Hi; apply AG; [clear - Hi GFF1; lia| apply nW_F; clear - Hi; lia]| clear - GFF1; lia| clear - GFF1; lia| exact FLC]. }
  split. { apply (PNADK.zeros_agree MV M _ _); [| exact ZF6]. intros i Hi. apply AG; [clear - Hi SFlo SFhi; lia| apply nW_shfirst; exact Hi]. }
  apply (PNADK.zeros_agree MV M _ _); [| exact ZSIG]. intros i Hi. apply AG; [clear - Hi SHlo SHhi; lia| apply nW_shF; clear - Hi; lia].
Qed.
Lemma sdigs_out MV M z sd : 0 <= z -> z + sd <= 36 -> PNADD.sdigs F MV z sd -> vout MV M -> PNADD.sdigs F M z sd.
Proof.
  intros Hz Hzs SD (MG & AG) i Hi. destruct (SD i Hi) as (v & CV & Hv). exists v. split; [| exact Hv].
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  unfold PNADD.cell in *. apply (PMF.u32_at_agree RSEGS MV M); [| clear - Hi Hz Hzs GFF1; lia| clear - Hi Hz Hzs GFF1; lia| exact CV].
  intros j Hj. apply AG; [clear - Hj Hi Hz Hzs GFF1; lia| apply nW_F; clear - Hj Hi Hz Hzs; lia].
Qed.

(* [comment removed for export] *)
Lemma dig_facts MV M z sd i : PNADD.MIA R0 S first r F fl MV -> PNADD.sdigs F MV z sd -> vout MV M -> 0 <= z -> z + sd <= 36 -> z <= i < z + sd ->
  exists d, 0 <= d <= 9 /\ 4096 <= F + 32 + 4 * i <= 140737488355320 /\ (F + 32 + 4 * i) mod 4 = 0
    /\ L5KA.zeros_at M ((F + 32 + 4 * i) / 8 + 2147450880) 1 /\ L5.u8_at RSEGS M (F + 32 + 4 * i) d
    /\ (2147446784 + 17592186048512 <= F + 32 + 4 * i \/ F + 32 + 4 * i + 4 <= 2147446784).
Proof.
  intros MI SD VO Hz Hzs Hi. pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (sdigs_out MV M z sd Hz Hzs SD VO i Hi) as (v & CV & Hv). exists v.
  pose proof geomF as (E0 & SHlo & SHhi). pose proof geomZ as (ZF & Zf).
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  split; [exact Hv|]. split; [clear - Hi Hz Hzs GFF1; lia|].
  split. { replace (F + 32 + 4 * i) with (F + (8 + i) * 4) by (clear; lia). rewrite Z_mod_plus_full. pose proof (Z.div_mod F 4 ltac:(clear; lia)) as D. pose proof (Z.mod_pos_bound F 4 ltac:(clear; lia)) as D3. clear - D D3 ZF. Lia.lia. }
  assert (H48 : (4 * i) / 8 = i / 2) by (change 8 with (4 * 2); apply Z.div_mul_cancel_l; clear; Lia.lia).
  assert (QI : (F + 32 + 4 * i) / 8 = F / 8 + 4 + i / 2).
  { rewrite ZF at 1. replace (8 * (F / 8) + 32 + 4 * i) with ((F / 8 + 4) * 8 + 4 * i) by (clear; Lia.lia). rewrite Z.div_add_l by (clear; Lia.lia). rewrite H48. reflexivity. }
  split. { rewrite QI. intros j Hj. assert (Hi2 : 0 <= i / 2 < 18) by (clear - Hi Hz Hzs; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
           replace (F / 8 + 4 + i / 2 + 2147450880 + j) with (PNADD.SH F + 4 + (i / 2 + j)) by (unfold PNADD.SH, PNADD.SBv; clear; lia). apply ZSIG. clear - Hj Hi2. lia. }
  split. { unfold PNADD.cell in CV. rewrite <- (Z.mod_small v 256) by (clear - Hv; lia). apply PMTK2.u8_of_u32; [clear - Hv; lia| exact CV]. }
  clear - Hi Hz Hzs GFFSH. lia.
Qed.
(* [comment removed for export] *)
Lemma dst_facts MV M k : PNADD.MIA R0 S first r F fl MV -> vout MV M -> 0 <= k < 42 ->
  4096 <= first + k <= 140737488355321 /\ L5KA.zeros_at M ((first + k) / 8 + 2147450880) 1 /\ L5.writable RSEGS M (first + k) 1
  /\ (2147446784 + 17592186048512 <= first + k \/ first + k + 1 <= 2147446784)
  /\ (S - 256 + 256 <= first + k \/ first + k + 1 <= S - 256) /\ (65536 + 6840320 <= first + k \/ first + k + 1 <= 65536)
  /\ (forall i, 0 <= i < 36 -> first + k + 1 <= F + 32 + 4 * i \/ F + 32 + 4 * i + 4 <= first + k).
Proof.
  intros MI VO Hk. pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  pose proof geomfirst as (E1 & SFlo & SFhi). pose proof geomZ as (ZF & Zf).
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  split; [clear - Hk GF1; lia|].
  assert (QK : (first + k) / 8 = first / 8 + k / 8).
  { rewrite Zf at 1. replace (8 * (first / 8) + k) with ((first / 8) * 8 + k) by (clear; Lia.lia). rewrite Z.div_add_l by (clear; Lia.lia). reflexivity. }
  split. { rewrite QK. intros j Hj. assert (Hk2 : 0 <= k / 8 < 6) by (clear - Hk; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
           replace (first / 8 + k / 8 + 2147450880 + j) with (PNADD.SH first + (k / 8 + j)) by (unfold PNADD.SH, PNADD.SBv; clear; lia). apply ZF6. clear - Hj Hk2. lia. }
  split. { apply (L5.writable_sub RSEGS M first 42 (first + k) 1 W2); clear - Hk; lia. }
  split; [clear - Hk GFSH; lia|]. split; [clear - Hk GFS; lia|]. split; [clear - Hk GFI; lia|].
  intros i Hi. clear - Hi Hk GFFf. lia.
Qed.

Section Arms.
Variables (MV : mem) (sigma z sd : Z).
Hypothesis MI : PNADD.MIA R0 S first r F fl MV.
Hypothesis SD : PNADD.sdigs F MV z sd.
Hypothesis Hsig : 0 <= sigma <= 1.
Hypothesis Hz : 0 <= z.
Hypothesis Hsd : 1 <= sd.
Hypothesis Hzs : z + sd <= 36.


Hypothesis SR : 140735332487296 <= S <= 140737488355328.
Hypothesis FHI : first + 48 <= S - 256.      (* [comment removed for export] *)
Hypothesis C176 : L5.u64_at RSEGS MV (S - 176) (first + 42).

Abbreviation st fx R pc M := (L5SAR.st fx R pc M).
Definition RL (R : bvmap 5 word) : Prop :=
  PNADD.RBA R0 S F R /\ getr R (reg 19) = Z_to_bv 64 PNADD.SBv /\ getr R (reg 20) = Z_to_bv 64 first.
Lemma to_bv_add a b : (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zplus_mod. reflexivity. Qed.
Lemma to_bv_mul a b : (Z_to_bv 64 a * Z_to_bv 64 b)%bv = Z_to_bv 64 (a * b).
Proof. apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite <- Zmult_mod. reflexivity. Qed.
Lemma C176_out M : vout MV M -> L5.u64_at RSEGS M (S - 176) (first + 42).
Proof.
  intros (MG & AG). pose proof G as G'. unfold PNADD.geom in G'. destruct G' as (GS1 & _).
  eapply L5C.u64_at_agree; [intros i Hi; apply AG; [clear - Hi GS1; lia| apply nW_stk; clear - Hi; lia]| clear - GS1; lia| clear - GS1; lia| exact C176].
Qed.
Ltac req H := first [exact H | (rewrite H; f_equal; clear; Lia.lia)].
Ltac kr KS := first [ assumption | (rewrite (KS _) by inl; assumption) | (match goal with H : getr ?R1 ?r = getr _ ?r |- getr ?R1 ?r = _ => rewrite H; assumption end) ].
Lemma k17_eq (f : nat -> word) g a b : f 77%nat = Z_to_bv 64 a -> f 76%nat = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  AX2.edenot (AX2.Env f g) (AX2.EAlu Instr.ALU_SRL (AX2.EAlu Instr.ALU_ADD (AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit (-1)) (AX2.EVar 77)) (AX2.EMd Instr.M_MUL (AX2.ELit 4) (AX2.EVar 76))) (AX2.ELit (-1))) (AX2.ELit 2))
  = Z_to_bv 64 (((- a + 4 * b - 1) mod 2 ^ 64) / 4).
Proof.
  intros H1 H2 Ha Hb.
  apply (L5KA.zpolyA_word _ (fun n => match n with 77%nat => a | _ => b end) _ ((((-1) * a + 4 * b) + (-1)) mod 2 ^ 64 / 2 ^ 2)).
  - cbn [L5K.zagree AX2.ev]. rewrite H1, H2, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite !Z.mod_small by lia. repeat split.
  - reflexivity.
  - unfold BL.MM. rewrite (Z.mod_small ((((-1) * a + 4 * b) + (-1)) mod 2 ^ 64 / 2 ^ 2) (2 ^ 64)).
    + replace (((-1) * a + 4 * b) + (-1)) with (- a + 4 * b - 1) by lia. reflexivity.
    + pose proof (Z.mod_pos_bound (((-1) * a + 4 * b) + (-1)) (2 ^ 64) ltac:(lia)). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.
Lemma k17g_eq (f : nat -> word) g a b : f 50%nat = Z_to_bv 64 a -> f 74%nat = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  AX2.edenot (AX2.Env f g) (AX2.EAlu Instr.ALU_SRL (AX2.EAlu Instr.ALU_ADD (AX2.EAlu Instr.ALU_ADD (AX2.EMd Instr.M_MUL (AX2.ELit (-1)) (AX2.EVar 50)) (AX2.EMd Instr.M_MUL (AX2.ELit (-4)) (AX2.EVar 74))) (AX2.ELit (-33))) (AX2.ELit 2))
  = Z_to_bv 64 (((- a - 4 * b - 33) mod 2 ^ 64) / 4).
Proof.
  intros H1 H2 Ha Hb.
  apply (L5KA.zpolyA_word _ (fun n => match n with 50%nat => a | _ => b end) _ ((((-1) * a + (-4) * b) + (-33)) mod 2 ^ 64 / 2 ^ 2)).
  - cbn [L5K.zagree AX2.ev]. rewrite H1, H2, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite !Z.mod_small by lia. repeat split.
  - reflexivity.
  - unfold BL.MM. rewrite (Z.mod_small ((((-1) * a + (-4) * b) + (-33)) mod 2 ^ 64 / 2 ^ 2) (2 ^ 64)).
    + replace (((-1) * a + (-4) * b) + (-33)) with (- a - 4 * b - 33) by lia. reflexivity.
    + pose proof (Z.mod_pos_bound (((-1) * a + (-4) * b) + (-33)) (2 ^ 64) ltac:(lia)). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gloop (n : nat) : forall fx R M i,
  sd - i = Z.of_nat n -> 0 <= i < sd -> RL R -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * (z + i)) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * (z + i)) ->
  getr R (reg 12) = Z_to_bv 64 i -> getr R (reg 13) = Z_to_bv 64 0 -> getr R (reg 16) = Z_to_bv 64 sd -> getr R (reg 5) = Z_to_bv 64 36 ->
  getr R (reg 15) = Z_to_bv 64 2 -> getr R (reg 17) = Z_to_bv 64 (((- F - 4 * z - 33) mod 2 ^ 64) / 4) ->
  vout MV M ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0xb430c M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F (first + sigma + cnt) 0 R' /\ i < cnt <= sd.
Proof.
  induction n as [|n IH]; intros fx R M i Hn Hi RLR G30 G10 G18 G12 G13 G16 G5 G15 G17 VO; [exfalso; clear - Hn Hi; lia|].
  destruct RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dig_facts MV M z sd (z + i) MI SD VO Hz Hzs ltac:(clear - Hi; lia)) as (d & Hd & DR & DA & DZ & DU & DSH).
  destruct (dst_facts MV M (sigma + i) MI VO ltac:(clear - Hi Hsig Hzs Hz; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (TD (z + i) ltac:(clear - Hi Hz Hzs; lia)) as TDi. clear TD. rewrite !Z.add_assoc in TR, TZ, TW, TSH, TS, TI, TDi.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X4 : 0 <= first + sigma < 2 ^ 64) by (clear - GF1 Hsig; lia). assert (X5 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X6 : 0 <= i < 2 ^ 64) by (clear - Hi Hzs Hz; lia). assert (X7 : 0 <= F + 32 + 4 * (z + i) < 2 ^ 64) by (clear - DR; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia). assert (X9 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Y1 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia). assert (Y2 : 0 <= i <= 35) by (clear - Hi Hzs Hz; lia).
  assert (Y3 : 4096 <= first + sigma <= 140737488355280) by (clear - GF1 Hsig FHI SR; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  LeanFeed.pfeed P (PNADOP1.adoG2_conc fx R M (fun j => match j with 2%nat => S | 33%nat => first | 38%nat => first + sigma | 50%nat => F | 75%nat => sd | 76%nat => i
      | 77%nat => F + 32 + 4 * (z + i) | 79%nat => sigma | 80%nat => d | _ => 0 end)) ltac:(first [PNADK.dsc | (rewrite G17; symmetry; erewrite k17_eq; [| reflexivity| reflexivity| lia| lia]; do 3 f_equal; lia)]).

  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A6 & A7 & A10 & A11 & A12 & A16 & A17 & A18 & A23 & A24 & HX) | [ (MS1 & KS1 & A6 & A7 & A11 & A16 & A17 & A21 & A24 & A25 & HX) | (MS1 & KS1 & A6 & A7 & A10 & A11 & A12 & A16 & A17 & A18 & A21 & A23 & A24 & A25 & HX) ]]).
  - (* [comment removed for export] *)
    assert (Hlt : i + 1 < sd).
    { destruct HX as (_ & Hlt & _). rewrite Z.mod_small in Hlt by (clear - Hi Hzs Hz; lia). exact Hlt. }
    assert (VO1 : vout MV M1).
    { apply (vout_step MV M M1 (fun a => first + sigma + i + 0 <= a < first + sigma + i + 0 + 1) VO MG1 FZ1). intros a Ha. left. clear - Ha Hi Hsig Hzs Hz. lia. }
    destruct (IH fx1 R1 M1 (i + 1) ltac:(clear - Hn; lia) ltac:(clear - Hi Hlt; lia)) as (fx2 & R2 & M2 & cnt & MS2 & VO2 & SE2 & Hcnt).
    + unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
    + rewrite (KS1 _) by inl. exact G30.
    + req A10.
    + req A18.
    + req A12.
    + rewrite (KS1 _) by inl. exact G13.
    + req A16.
    + rewrite (KS1 _) by inl. exact G5.
    + rewrite (KS1 _) by inl. exact G15.
    + rewrite A17. erewrite k17_eq; [| reflexivity| reflexivity| lia| lia]. do 3 f_equal. lia.
    + exact VO1.
    + exists fx2, R2, M2, cnt. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2| clear - Hcnt; lia].
  - (* [comment removed for export] *)
    assert (Hge : sd <= i + 1).
    { destruct HX as (Hge & _). rewrite Z.mod_small in Hge by (clear - Hi Hzs Hz; lia). exact Hge. }
    exists fx1, R1, M1, (i + 1). split; [exact MS1|].
    split. { apply (vout_step MV M M1 (fun a => first + sigma + i + 0 <= a < first + sigma + i + 0 + 1) VO MG1 FZ1). intros a Ha. left. clear - Ha Hi Hsig Hzs Hz. lia. }
    split. { unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [ kr KS1 | req A24 ]. }
    clear - Hi Hge. lia.
  - (* [comment removed for export] *)
    assert (Hlt : i + 1 < sd).
    { destruct HX as (_ & Hlt & _). rewrite Z.mod_small in Hlt by (clear - Hi Hzs Hz; lia). exact Hlt. }
    exists fx1, R1, M1, (i + 1). split; [exact MS1|].
    split. { apply (vout_step MV M M1 (fun a => first + sigma + i + 0 <= a < first + sigma + i + 0 + 1) VO MG1 FZ1). intros a Ha. left. clear - Ha Hi Hsig Hzs Hz. lia. }
    split. { unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [ kr KS1 | req A24 ]. }
    clear - Hi Hlt. lia.
Qed.

Lemma regular fx R M :
  RL R -> getr R (reg 30) = Z_to_bv 64 (first + sigma) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) ->
  getr R (reg 13) = Z_to_bv 64 sd -> vout MV M ->
  exists fx' R' M' cnt, msteps RSEGS (st fx R 0xb42cc M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F (first + sigma + cnt) 0 R' /\ 1 <= cnt <= sd.
Proof.
  intros RLR G30 G18 G13 VO.
  destruct RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia). assert (X6 : 0 <= z < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia).
  assert (Y1 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia). assert (Y2 : 0 <= z <= 35) by (clear - Hsd Hzs Hz; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32. assert (Y5 : 4096 <= F <= 140737488354816) by exact GFF1. assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  LeanFeed.pfeed P (PNADOP1.adoG1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => first | 50%nat => F | 74%nat => z | 75%nat => sd | 79%nat => sigma | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  destruct (gloop (Z.to_nat sd) fx1 R1 M 0 ltac:(clear - Hsd; lia) ltac:(clear - Hsd; lia)) as (fx2 & R2 & M2 & cnt & MS2 & VO2 & SE2 & Hcnt).
  - unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
  - rewrite (KS1 _) by inl. exact G30.
  - req A10.
  - rewrite (KS1 _) by inl. rewrite G18. f_equal. clear; lia.
  - req A12.
  - req A13.
  - req A16.
  - req A5.
  - req A15.
  - rewrite A17. erewrite k17g_eq; [reflexivity| reflexivity| reflexivity| lia| lia].
  - exact VO.
  - exists fx2, R2, M2, cnt. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2| clear - Hcnt; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma slt_lit a b : - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
  bv_unsigned (if bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) then Z_to_bv 64 1 else Z_to_bv 64 0) = (if a <? b then 1 else 0).
Proof.
  intros Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (HM : bv_half_modulus 64 = 2 ^ 63) by (vm_compute; reflexivity).
  rewrite !bv_swrap_small by (rewrite HM; clear -Ha Hb; Lia.lia). destruct (a <? b); reflexivity.
Qed.
Lemma to_bv_eqm a b : a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact E. Qed.
Lemma to_bv_of_unsigned (b : bv 64) v : bv_unsigned b = v -> b = Z_to_bv 64 v.
Proof. intros <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma alu_slt01 w : 0 < w < 2 ^ 63 -> alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 w) = Z_to_bv 64 1.
Proof.
  intros Hw. apply to_bv_of_unsigned. cbn [alu64 alu32 alu]. rewrite slt_lit by lia. destruct (Z.ltb_spec 0 w); [reflexivity| lia].
Qed.
Lemma mul_lit a b : mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. cbn [mul_div]. apply to_bv_mul. Qed.
Lemma add_lit a b : alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. cbn [alu64 alu32 alu]. apply to_bv_add. Qed.
Lemma and_m1 (x : word) : alu64 ALU_AND (Z_to_bv 64 (-1 * 1)) x = x.
Proof.
  apply bv_eq. cbn [alu64 alu32 alu]. rewrite bv_and_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change ((-1 * 1) mod 2 ^ 64) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small.
  pose proof (bv_unsigned_in_range 64 x) as U. change (bv_modulus 64) with (2 ^ 64) in U. exact U.
Qed.
Lemma srl_lit a s : 0 <= s < 64 -> alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 ((a mod 2 ^ 64) / 2 ^ s).
Proof.
  intros Hs. apply to_bv_of_unsigned. apply BL.zalu_sound. cbn [BL.zalu]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small s (2 ^ 64)) by lia. rewrite (Z.mod_small s 64) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma frac_loop (n : nat) : forall fx R M j q off cnt,
  cnt - j = Z.of_nat n -> 0 <= j < cnt -> z <= q -> q + cnt <= z + sd -> 2 <= off -> off + j <= 41 ->
  RL R -> getr R (reg 11) = Z_to_bv 64 (first + (j + off)) -> getr R (reg 12) = Z_to_bv 64 (first + (j + off)) ->
  getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * (q + j)) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * (q + j)) ->
  getr R (reg 13) = Z_to_bv 64 (j + 1) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 cnt ->
  getr R (reg 16) = Z_to_bv 64 18446744073709551611 -> getr R (reg 25) = Z_to_bv 64 0 ->
  vout MV M ->
  exists fx' R' M' m, msteps RSEGS (st fx R 0xb4910 M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F (first + off + m) 0 R' /\ j < m <= cnt /\ off + m <= 42.
Proof.
  induction n as [|n IH]; intros fx R M j q off cnt Hn Hj Hq Hqc Hoff Hoj RLR G11 G12 G10 G18 G13 G14 G15 G16 G25 VO; [exfalso; clear - Hn Hj; lia|].
  destruct RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dig_facts MV M z sd (q + j) MI SD VO Hz Hzs ltac:(clear - Hj Hq Hqc; lia)) as (d & Hd & DR & DA & DZ & DU & DSH).
  destruct (dst_facts MV M (j + off) MI VO ltac:(clear - Hj Hoff Hoj; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (TD (q + j) ltac:(clear - Hj Hq Hqc Hz Hzs; lia)) as TDi. clear TD.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= cnt < 2 ^ 64) by (clear - Hj Hq Hqc Hz Hzs; lia).
  assert (X6 : 0 <= j < 2 ^ 64) by (clear - Hj Hq Hqc Hz Hzs; lia). assert (X7 : 0 <= F + 32 + 4 * (q + j) < 2 ^ 64) by (clear - DR; lia).
  assert (X8 : 0 <= off < 2 ^ 64) by (clear - Hoff Hoj Hj; lia). assert (X9 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Y1 : 1 <= cnt <= 36) by (clear - Hj Hq Hqc Hz Hzs; lia). assert (Y2 : 0 <= j <= 35) by (clear - Hj Hq Hqc Hz Hzs; lia).
  assert (Y3 : 2 <= off <= 41) by (clear - Hoff Hoj Hj; lia). assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y5 : 2 <= j + off <= 41) by (clear - Hoff Hoj Hj; lia). assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  pose proof (C176_out M VO) as C176M.
  LeanFeed.pfeed P (PNADOP3.adoXL2_conc fx R M (fun k => match k with 2%nat => S | 33%nat => first | 50%nat => F | 76%nat => j
      | 77%nat => F + 32 + 4 * (q + j) | 78%nat => cnt | 79%nat => off | 80%nat => d | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + (j + off) + 0 <= a < first + (j + off) + 0 + 1 -> Wout a) by (intros a Ha; left; clear - Ha Hj Hoff Hoj; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A18 & A23 & A24 & HX) | [ (MS1 & KS1 & A5 & A11 & A13 & A14 & A15 & A17 & A21 & A24 & HX) | (MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A17 & A18 & A21 & A23 & A24 & HX) ]]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1.
  - (* [comment removed for export] *)
    destruct HX as (Hroom & Hlt & _).
    rewrite (Z.mod_small (j + 1)) in Hlt by (clear - Hj Y1; lia).
    rewrite (Z.mod_small (j + off)), (Z.mod_small (first + (j + off))), (Z.mod_small (first + (j + off) + 1)), (Z.mod_small (first + 42)) in Hroom by (clear - Y5 Y6; lia).
    destruct (IH fx1 R1 M1 (j + 1) q off cnt ltac:(clear - Hn; lia) ltac:(clear - Hj Hlt; lia) Hq Hqc Hoff ltac:(clear - Hroom; lia)) as (fx2 & R2 & M2 & m & MS2 & VO2 & SE2 & Hm & Hom).
    + unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
    + req A11.
    + req A12.
    + req A10.
    + req A18.
    + req A13.
    + req A14.
    + req A15.
    + rewrite (KS1 _) by inl. exact G16.
    + rewrite (KS1 _) by inl. exact G25.
    + exact VO1.
    + exists fx2, R2, M2, m. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2|]. split; [clear - Hm; lia| exact Hom].
  - (* [comment removed for export] *)
    destruct HX as (Hge & _). rewrite (Z.mod_small (j + 1)) in Hge by (clear - Hj Y1; lia).
    exists fx1, R1, M1, (j + 1). split; [exact MS1|]. split; [exact VO1|].
    split. { unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [ kr KS1 | req A24 ]. }
    split; [clear - Hj Hge; lia| clear - Hoj; lia].
  - (* [comment removed for export] *)
    destruct HX as (_ & Hlt & _). rewrite (Z.mod_small (j + 1)) in Hlt by (clear - Hj Y1; lia).
    exists fx1, R1, M1, (j + 1). split; [exact MS1|]. split; [exact VO1|].
    split. { unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [ kr KS1 | req A24 ]. }
    split; [clear - Hj Hlt; lia| clear - Hoj; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma int_loop (n : nat) : forall fx R M k rd,
  rd - k = Z.of_nat n -> 0 <= k < rd -> rd <= 35 -> rd <= sd ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 14) = Z_to_bv 64 rd ->
  getr R (reg 12) = Z_to_bv 64 (first + (sigma + k)) -> getr R (reg 30) = Z_to_bv 64 (first + (sigma + k)) ->
  getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * (z + k)) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * (z + k)) ->
  getr R (reg 16) = Z_to_bv 64 (k + 1) -> getr R (reg 5) = Z_to_bv 64 2 -> getr R (reg 15) = Z_to_bv 64 0 -> getr R (reg 17) = Z_to_bv 64 18446744073709551611 ->
  vout MV M ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb44d4 M) (st fx' R' 0xb484c M') /\ vout MV M'
    /\ RL R' /\ getr R' (reg 13) = Z_to_bv 64 sd /\ getr R' (reg 14) = Z_to_bv 64 rd
    /\ getr R' (reg 6) = Z_to_bv 64 (first + (sigma + rd)) /\ getr R' (reg 11) = Z_to_bv 64 (first + (sigma + rd))
    /\ getr R' (reg 10) = Z_to_bv 64 (F + 32 + 4 * (z + rd)) /\ getr R' (reg 18) = Z_to_bv 64 (F + 32 + 4 * (z + rd)).
Proof.
  induction n as [|n IH]; intros fx R M k rd Hn Hk Hrd Hrs RLR G13 G14 G12 G30 G10 G18 G16 G5 G15 G17 VO; [exfalso; clear - Hn Hk; lia|].
  destruct RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dig_facts MV M z sd (z + k) MI SD VO Hz Hzs ltac:(clear - Hk Hrs; lia)) as (d & Hd & DR & DA & DZ & DU & DSH).
  destruct (dst_facts MV M (sigma + k) MI VO ltac:(clear - Hk Hrd Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (TD (z + k) ltac:(clear - Hk Hrs Hz Hzs; lia)) as TDi. clear TD.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= rd < 2 ^ 64) by (clear - Hk Hrd; lia).
  assert (X6 : 0 <= k + 1 < 2 ^ 64) by (clear - Hk Hrd; lia). assert (X7 : 0 <= F + 32 + 4 * (z + k) < 2 ^ 64) by (clear - DR; lia).
  assert (X8 : 0 <= sigma + k < 2 ^ 64) by (clear - Hsig Hk Hrd; lia). assert (X9 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Y1 : 1 <= rd <= 35) by (clear - Hk Hrd; lia). assert (Y2 : 1 <= k + 1 <= 35) by (clear - Hk Hrd; lia).
  assert (Y3 : 0 <= sigma + k <= 35) by (clear - Hsig Hk Hrd; lia). assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  pose proof (C176_out M VO) as C176M.
  LeanFeed.pfeed P (PNADOP3.adoXL1_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 76%nat => k + 1
      | 77%nat => F + 32 + 4 * (z + k) | 79%nat => sigma + k | 80%nat => d | 86%nat => rd | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + (sigma + k) + 0 <= a < first + (sigma + k) + 0 + 1 -> Wout a) by (intros a Ha; left; clear - Ha Hk Hrd Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A6 & A7 & A10 & A11 & A12 & A14 & A15 & A16 & A18 & A21 & A22 & A23 & A30 & HX & _) | (MS1 & KS1 & A6 & A7 & A10 & A11 & A12 & A15 & A16 & A18 & A22 & A23 & HX & _) ]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1;
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in HX; rewrite slt_lit in HX by (clear - Hk Hrd; lia);
    destruct (Z.ltb_spec (k + 1) rd) as [Hl|Hl]; try (exfalso; clear - HX; lia).
  - (* [comment removed for export] *)
    destruct (IH fx1 R1 M1 (k + 1) rd ltac:(clear - Hn; lia) ltac:(clear - Hk Hl; lia) Hrd Hrs) as (fx2 & R2 & M2 & MS2 & VO2 & RL2 & B13 & B14 & B6 & B11 & B10 & B18).
    + unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
    + rewrite (KS1 _) by inl. exact G13.
    + req A14.
    + req A12.
    + req A30.
    + req A10.
    + req A18.
    + req A16.
    + rewrite (KS1 _) by inl. exact G5.
    + req A15.
    + rewrite (KS1 _) by inl. exact G17.
    + exact VO1.
    + exists fx2, R2, M2. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact RL2|]. split; [exact B13|]. split; [exact B14|]. split; [exact B6|]. split; [exact B11|]. split; [exact B10| exact B18].
  - (* [comment removed for export] *)
    assert (Ek : k + 1 = rd) by (clear - Hk Hl; lia).
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact VO1|].
    split. { unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1. }
    split; [rewrite (KS1 _) by inl; exact G13|]. split; [rewrite (KS1 _) by inl; exact G14|].
    split; [rewrite A6; f_equal; clear - Ek; lia|]. split; [rewrite A11; f_equal; clear - Ek; lia|].
    split; [rewrite A10; f_equal; clear - Ek; lia| rewrite A18; f_equal; clear - Ek; lia].
Qed.

(* [comment removed for export] *)
Lemma subw_val a b : 0 <= b <= a -> a <= 36 ->
  ((((4294967296 * a) mod 2 ^ 64) + ((18446744069414584320 * b) mod 2 ^ 64)) mod 2 ^ 64) / 4294967296 = a - b.
Proof.
  intros H1 H2. rewrite <- Zplus_mod. replace (4294967296 * a + 18446744069414584320 * b) with (4294967296 * (a - b) + b * 2 ^ 64) by (clear; Lia.lia).
  rewrite Z.mod_add by (clear; Lia.lia). rewrite Z.mod_small by (clear -H1 H2; Lia.lia). rewrite Z.mul_comm, Z.div_mul by (clear; Lia.lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dot_frac fx R M rd :
  1 <= rd -> rd <= 35 -> rd < sd ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 14) = Z_to_bv 64 rd ->
  getr R (reg 6) = Z_to_bv 64 (first + (sigma + rd)) -> getr R (reg 11) = Z_to_bv 64 (first + (sigma + rd)) ->
  getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * (z + rd)) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * (z + rd)) ->
  vout MV M ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0xb484c M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F ptr 0 R' /\ first <= ptr <= first + 42.
Proof.
  intros Hrd1 Hrd Hrs RLR G13 G14 G6 G11 G10 G18 VO.
  destruct RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dst_facts MV M (sigma + rd) MI VO ltac:(clear - Hrd1 Hrd Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD). clear TD.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= rd < 2 ^ 64) by (clear - Hrd1 Hrd; lia). assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X7 : 0 <= F + 32 + 4 * (z + rd) < 2 ^ 64) by (clear - GFF1 Hz Hzs Hrd1 Hrs; lia).
  assert (X8 : 0 <= sigma + rd < 2 ^ 64) by (clear - Hsig Hrd1 Hrd; lia).
  assert (Y1 : 0 <= rd <= 35) by (clear - Hrd1 Hrd; lia). assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia).
  assert (Y3 : 1 <= sigma + rd <= 36) by (clear - Hsig Hrd1 Hrd; lia). assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1. assert (Y7 : 4096 <= F + 32 + 4 * (z + rd) <= 140737488355320) by (clear - GFF1 Hz Hzs Hrd1 Hrs; lia).
  pose proof (C176_out M VO) as C176M. pose proof (al4 (z + rd)) as AL.
  LeanFeed.pfeed P (PNADOP3.adoXD_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 75%nat => sd
      | 77%nat => F + 32 + 4 * (z + rd) | 79%nat => sigma + rd | 86%nat => rd | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + (sigma + rd) + 0 <= a < first + (sigma + rd) + 0 + 1 -> Wout a) by (intros a Ha; left; clear - Ha Hrd1 Hrd Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A5 & A10 & A11 & A12 & A15 & A16 & A17 & A21 & A24 & A25 & HX & _) | (MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A21 & A24 & A25 & HX & _) ]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1.
  { exists fx1, R1, M1, (first + (sigma + rd) + 1). split; [exact MS1|]. split; [exact VO1|].
    split. { unfold PNADD.stE, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [ kr KS1 | req A24 ]. }
    clear - Hsig Hrd1 Hrd. lia. }
  rewrite (Z.mod_small (first + (sigma + rd))) in A12 by (clear - Y3 Y6; lia). rewrite Z.mod_small in A12 by (clear - Y3 Y6; lia). apply to_bv_of_unsigned in A12.
  assert (B15 : getr R1 (reg 15) = Z_to_bv 64 (sd - rd)).
  { rewrite A15. cbn [AX2.edenot AX2.ev]. rewrite alu_slt01 by lia. rewrite !mul_lit, and_m1, !mul_lit, add_lit, srl_lit by lia. f_equal.
    rewrite Z.mod_small by lia. symmetry. apply (Z.div_unique _ _ _ 0); [left; lia| lia]. }
  destruct (frac_loop (Z.to_nat (sd - rd)) fx1 R1 M1 0 (z + rd) (sigma + rd + 1) (sd - rd)
              ltac:(clear - Hrs; lia) ltac:(clear - Hrs; lia) ltac:(clear - Hrd1; lia) ltac:(clear; lia) ltac:(clear - Hsig Hrd1; lia) ltac:(clear - Hsig Hrd; lia))
    as (fx2 & R2 & M2 & m & MS2 & VO2 & SE2 & Hm & Hom).
  - unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
  - req A11.
  - req A12.
  - req A10.
  - rewrite (KS1 _) by inl. rewrite G18. f_equal. clear; lia.
  - req A13.
  - req A14.
  - exact B15.
  - req A16.
  - req A25.
  - exact VO1.
  - exists fx2, R2, M2, (first + (sigma + rd + 1) + m). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2|].
    clear - Hm Hom Hsig Hrd1. lia.
Qed.

(* [comment removed for export] *)
Lemma radix_pos fx R M rd :
  1 <= rd -> rd <= 35 -> rd < sd ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 14) = Z_to_bv 64 rd ->
  getr R (reg 30) = Z_to_bv 64 (first + sigma) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) ->
  vout MV M ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F ptr 0 R' /\ first <= ptr <= first + 42.
Proof.
  intros Hrd1 Hrd Hrs RLR G13 G14 G30 G18 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= rd < 2 ^ 64) by (clear - Hrd1 Hrd; lia).
  assert (X7 : 0 <= F + 32 + 4 * z < 2 ^ 64) by (clear - GFF1 Hz Hzs Hsd; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia).
  assert (Y1 : 1 <= rd <= 35) by (clear - Hrd1 Hrd; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1. assert (Y7 : 4096 <= F + 32 + 4 * z <= 140737488355320) by (clear - GFF1 Hz Hzs Hsd; lia).
  pose proof (C176_out M VO) as C176M. pose proof (al4 z) as AL.
  LeanFeed.pfeed P (PNADOP3.adoXP_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F
      | 77%nat => F + 32 + 4 * z | 79%nat => sigma | 86%nat => rd | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A5 & A10 & A11 & A12 & A14 & A15 & A16 & A17).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  destruct (int_loop (Z.to_nat rd) fx1 R1 M 0 rd ltac:(clear - Hrd1; lia) ltac:(clear - Hrd1; lia) Hrd ltac:(clear - Hrs; lia))
    as (fx2 & R2 & M2 & MS2 & VO2 & RL2 & B13 & B14 & B6 & B11 & B10 & B18).
  - unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
  - rewrite (KS1 _) by inl. exact G13.
  - req A14.
  - req A12.
  - rewrite (KS1 _) by inl. rewrite G30. f_equal. clear; lia.
  - req A10.
  - rewrite (KS1 _) by inl. rewrite G18. f_equal. clear; lia.
  - req A16.
  - req A5.
  - req A15.
  - req A17.
  - exact VO.
  - destruct (dot_frac fx2 R2 M2 rd Hrd1 Hrd Hrs RL2 B13 B14 B6 B11 B10 B18 VO2) as (fx3 & R3 & M3 & ptr & MS3 & VO3 & SE3 & Hp).
    exists fx3, R3, M3, ptr. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2| exact MS3]|]. split; [exact VO3|]. split; [exact SE3| exact Hp].
Qed.

(* [comment removed for export] *)
Lemma radix_zero fx R M :
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 14) = Z_to_bv 64 0 ->
  getr R (reg 30) = Z_to_bv 64 (first + sigma) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) ->
  vout MV M ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F ptr 0 R' /\ first <= ptr <= first + 42.
Proof.
  intros RLR G13 G14 G30 G18 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dst_facts MV M sigma MI VO ltac:(clear - Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD). clear TD.
  destruct (dst_facts MV M (sigma + 1) MI VO ltac:(clear - Hsig; lia)) as (UR & UZ & UW & USH & US & UI & UD). clear UD.
  rewrite !Z.add_assoc in UR, UZ, UW, USH, US, UI.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X7 : 0 <= F + 32 + 4 * z < 2 ^ 64) by (clear - GFF1 Hz Hzs Hsd; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1. assert (Y7 : 4096 <= F + 32 + 4 * z <= 140737488355320) by (clear - GFF1 Hz Hzs Hsd; lia).
  pose proof (C176_out M VO) as C176M. pose proof (al4 z) as AL.
  LeanFeed.pfeed P (PNADOP3.adoXN0_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 75%nat => sd
      | 77%nat => F + 32 + 4 * z | 79%nat => sigma | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + sigma + 0 <= a < first + sigma + 0 + 2 -> Wout a) by (intros a Ha; left; clear - Ha Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A5 & A10 & A11 & A12 & A13 & A15 & A16 & A17 & A21 & A22 & A24 & A25 & _).
  pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1.
  destruct (frac_loop (Z.to_nat sd) fx1 R1 M1 0 z (sigma + 2) sd
              ltac:(clear - Hsd; lia) ltac:(clear - Hsd; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hsig; lia) ltac:(clear - Hsig; lia))
    as (fx2 & R2 & M2 & m & MS2 & VO2 & SE2 & Hm & Hom).
  - unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
  - req A11.
  - req A12.
  - req A10.
  - rewrite (KS1 _) by inl. rewrite G18. f_equal. clear; lia.
  - req A13.
  - rewrite (KS1 _) by inl. exact G14.
  - req A15.
  - req A16.
  - req A25.
  - exact VO1.
  - exists fx2, R2, M2, (first + (sigma + 2) + m). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2|].
    clear - Hm Hom Hsig. lia.
Qed.

(* [comment removed for export] *)
Lemma radix_neg_pre fx R M nr :
  0 <= nr <= 4 ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 14) = Z_to_bv 64 (18446744073709551615 - nr) ->
  getr R (reg 30) = Z_to_bv 64 (first + sigma) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) ->
  vout MV M ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb44b0 M) (st fx' R' 0xb4884 M') /\ vout MV M'
    /\ RL R' /\ getr R' (reg 13) = Z_to_bv 64 sd /\ getr R' (reg 30) = Z_to_bv 64 (first + sigma)
    /\ getr R' (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) /\ getr R' (reg 10) = Z_to_bv 64 (F + 32 + 4 * z)
    /\ getr R' (reg 5) = Z_to_bv 64 (4 - nr - 4) /\ getr R' (reg 14) = Z_to_bv 64 (4 - nr - 5)
    /\ getr R' (reg 11) = Z_to_bv 64 (first + (sigma + 0) + 2) /\ getr R' (reg 12) = Z_to_bv 64 (first + (sigma + 0) + 2)
    /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551615 /\ getr R' (reg 16) = Z_to_bv 64 48
    /\ L5.u8_at RSEGS M' (first + sigma + 1) 46 /\ L5.u8_at RSEGS M' (first + sigma) 48.
Proof.
  intros Hnr RLR G13 G14 G30 G18 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dst_facts MV M sigma MI VO ltac:(clear - Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD). clear TD.
  destruct (dst_facts MV M (sigma + 1) MI VO ltac:(clear - Hsig; lia)) as (UR & UZ & UW & USH & US & UI & UD). clear UD.
  rewrite !Z.add_assoc in UR, UZ, UW, USH, US, UI.
  destruct (dst_facts MV M (sigma + 2) MI VO ltac:(clear - Hsig; lia)) as (VR & VZ & VW & VSH & VS & VI & VD). clear VD.
  rewrite !Z.add_assoc in VR, VZ, VW, VSH, VS, VI.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia). assert (X9 : 0 <= nr < 2 ^ 64) by (clear - Hnr; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  assert (Y8 : 18446744073709551611 <= 18446744073709551615 - nr <= 18446744073709551615) by (clear - Hnr; lia).
  pose proof (C176_out M VO) as C176M.
  LeanFeed.pfeed P (PNADOP3.adoXN_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 75%nat => sd
      | 79%nat => sigma | 87%nat => nr | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + sigma + 0 <= a < first + sigma + 0 + 2 -> Wout a) by (intros a Ha; left; clear - Ha Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & MS1 & KS1 & A1 & A5 & A10 & A11 & A12 & A13 & A15 & A16 & A21 & A22 & A24 & U1 & U0).
  pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1.
  exists fx1, R1, M1. split; [exact MS1|]. split; [exact VO1|].
  split. { unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1. }
  split; [exact A13|]. split; [rewrite (KS1 _) by inl; exact G30|]. split; [rewrite (KS1 _) by inl; exact G18|].
  split; [rewrite A10; exact G18|]. split; [rewrite A5; f_equal; clear; lia|].
  split; [rewrite (KS1 _) by inl; rewrite G14; apply to_bv_eqm; rewrite <- (Z.mod_add (4 - nr - 5) 1 (2 ^ 64)) by (clear; lia); f_equal; clear; lia|].
  split; [rewrite A11; f_equal; clear; lia|]. split; [rewrite A12; f_equal; clear; lia|].
  split; [exact A15|]. split; [exact A16|]. split; [exact U1| exact U0].
Qed.

Lemma nloop (n : nat) : forall fx R M nr j c,
  6 - c = Z.of_nat n -> 0 <= nr <= 4 -> 0 <= j -> 0 <= c <= 5 -> c - j + nr = 4 ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) -> getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * z) ->
  getr R (reg 5) = Z_to_bv 64 (c - 4) -> getr R (reg 14) = Z_to_bv 64 (c - 5) ->
  getr R (reg 11) = Z_to_bv 64 (first + (sigma + j) + 2) -> getr R (reg 12) = Z_to_bv 64 (first + (sigma + j) + 2) ->
  getr R (reg 15) = Z_to_bv 64 18446744073709551615 -> getr R (reg 16) = Z_to_bv 64 48 ->
  L5.u8_at RSEGS M (first + sigma + 1) 46 -> L5.u8_at RSEGS M (first + sigma) 48 ->
  vout MV M ->
  exists fx' R' M', msteps RSEGS (st fx R 0xb4884 M) (st fx' R' 0xb48cc M') /\ vout MV M'
    /\ RL R' /\ getr R' (reg 13) = Z_to_bv 64 sd /\ getr R' (reg 30) = Z_to_bv 64 (first + sigma)
    /\ getr R' (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) /\ getr R' (reg 10) = Z_to_bv 64 (F + 32 + 4 * z)
    /\ getr R' (reg 5) = Z_to_bv 64 1 /\ getr R' (reg 14) = Z_to_bv 64 0 /\ getr R' (reg 17) = Z_to_bv 64 1
    /\ getr R' (reg 11) = Z_to_bv 64 (first + (sigma + 1 + nr) + 2) /\ getr R' (reg 12) = Z_to_bv 64 (first + (sigma + 1 + nr) + 2).
Proof.
  induction n as [|n IH]; intros fx R M nr j c Hn Hnr Hj Hc Hcj RLR G13 G30 G18 G10 G5 G14 G11 G12 G15 G16 U1 U0 VO; [exfalso; clear - Hn Hc; lia|].
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  pose proof (C176_out M VO) as C176M.
  destruct (dst_facts MV M sigma MI VO ltac:(clear - Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD). clear TD.
  destruct (dst_facts MV M (sigma + 1) MI VO ltac:(clear - Hsig; lia)) as (UR & UZ & UW & USH & US & UI & UD). clear UD.
  rewrite !Z.add_assoc in UR, UZ, UW, USH, US, UI.
  destruct (dst_facts MV M (sigma + j + 2) MI VO ltac:(clear - Hsig Hj Hc Hcj Hnr; lia)) as (VR & VZ & VW & VSH & VS & VI & VD). clear VD.
  replace (first + (sigma + j + 2)) with (first + (sigma + j) + 2) in VR, VZ, VW, VSH, VS, VI by (clear; lia).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia). assert (X9 : 0 <= nr < 2 ^ 64) by (clear - Hnr; lia).
  assert (X10 : 0 <= j < 2 ^ 64) by (clear - Hj Hc Hcj Hnr; lia). assert (X11 : 0 <= c < 2 ^ 64) by (clear - Hc; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  assert (Y8 : 18446744073709551611 <= 18446744073709551615 - nr <= 18446744073709551615) by (clear - Hnr; lia).
  assert (Y9 : 0 <= j <= 5) by (clear - Hj Hc Hcj Hnr; lia).
  assert (Y10 : 0 <= (((-1) * (j)) + ((nr) + 1)) <= 134217728) by (clear - Hj Hc Hcj Hnr; lia).
  assert (Y11 : 4 <= (((c) - (j)) + (nr)) <= 4) by (clear - Hcj; lia).
  assert (G10' : getr R (reg 10) = Z_to_bv 64 (bv_unsigned (getr R (reg 18)))) by (rewrite Z_to_bv_bv_unsigned, G10, G18; reflexivity).
  LeanFeed.pfeed P (PNADOP3.adoXNL_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 75%nat => sd
      | 79%nat => sigma | 87%nat => nr | 88%nat => j | 89%nat => c | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + sigma + 0 <= a < first + sigma + 0 + 8 -> Wout a) by (intros a Ha; left; clear - Ha Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A5 & A11 & A12 & A14 & A17 & _ & HX & V1 & V0) | (MS1 & KS1 & A17 & HX & V1 & V0) ]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1;
    cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in HX; rewrite to_bv_add, slt_lit in HX by (clear - Hc; lia);
    destruct (Z.ltb_spec (c + -5) 0) as [Hl|Hl]; try (exfalso; clear - HX; lia).
  - destruct (IH fx1 R1 M1 nr (j + 1) (c + 1) ltac:(clear - Hn; lia) Hnr ltac:(clear - Hj; lia) ltac:(clear - Hc Hl; lia) ltac:(clear - Hcj; lia))
      as (fx2 & R2 & M2 & MS2 & VO2 & RL2 & B13 & B30 & B18 & B10 & B5 & B14 & B17 & B11 & B12).
    + unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
    + rewrite (KS1 _) by inl. exact G13.
    + rewrite (KS1 _) by inl. exact G30.
    + rewrite (KS1 _) by inl. exact G18.
    + rewrite (KS1 _) by inl. exact G10.
    + req A5.
    + req A14.
    + req A11.
    + req A12.
    + rewrite (KS1 _) by inl. exact G15.
    + rewrite (KS1 _) by inl. exact G16.
    + exact V1.
    + exact V0.
    + exact VO1.
    + exists fx2, R2, M2. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|].
      split; [exact RL2|]. split; [exact B13|]. split; [exact B30|]. split; [exact B18|]. split; [exact B10|].
      split; [exact B5|]. split; [exact B14|]. split; [exact B17|]. split; [exact B11| exact B12].
  - assert (Ec : c = 5) by (clear - Hc Hl; lia).
    exists fx1, R1, M1. split; [exact MS1|]. split; [exact VO1|].
    split. { unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1. }
    split; [rewrite (KS1 _) by inl; exact G13|]. split; [rewrite (KS1 _) by inl; exact G30|].
    split; [rewrite (KS1 _) by inl; exact G18|]. split; [rewrite (KS1 _) by inl; exact G10|].
    split; [rewrite (KS1 _) by inl; rewrite G5; f_equal; clear - Ec; lia|]. split; [rewrite (KS1 _) by inl; rewrite G14; f_equal; clear - Ec; lia|].
    split; [rewrite A17; f_equal; clear - Ec; lia|].
    split; [rewrite (KS1 _) by inl; rewrite G11; f_equal; clear - Ec Hcj; lia| rewrite (KS1 _) by inl; rewrite G12; f_equal; clear - Ec Hcj; lia].
Qed.
(* [comment removed for export] *)
Lemma radix_neg_post fx R M nr :
  0 <= nr <= 4 ->
  RL R -> getr R (reg 13) = Z_to_bv 64 sd -> getr R (reg 30) = Z_to_bv 64 (first + sigma) ->
  getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) -> getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * z) ->
  getr R (reg 5) = Z_to_bv 64 1 -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 17) = Z_to_bv 64 1 ->
  getr R (reg 11) = Z_to_bv 64 (first + (sigma + 1 + nr) + 2) -> getr R (reg 12) = Z_to_bv 64 (first + (sigma + 1 + nr) + 2) ->
  vout MV M ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0xb48cc M) (st fx' R' 0xb46b0 M') /\ vout MV M'
    /\ PNADD.stE R0 S F ptr 0 R' /\ first <= ptr <= first + 42.
Proof.
  intros Hnr RLR G13 G30 G18 G10 G5 G14 G17 G11 G12 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (X7 : 0 <= F + 32 + 4 * z < 2 ^ 64) by (clear - GFF1 Hz Hzs Hsd; lia).
  assert (X8 : 0 <= sigma + 1 < 2 ^ 64) by (clear - Hsig; lia). assert (X9 : 0 <= nr < 2 ^ 64) by (clear - Hnr; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia). assert (Y3 : 1 <= sigma + 1 <= 2) by (clear - Hsig; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32.
  assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1. assert (Y7 : 4096 <= F + 32 + 4 * z <= 140737488355320) by (clear - GFF1 Hz Hzs Hsd; lia).
  pose proof (C176_out M VO) as C176M. pose proof (al4 z) as AL.
  assert (G30' : getr R (reg 30) = Z_to_bv 64 (first + (sigma + 1) - 1)) by (rewrite G30; f_equal; clear; lia).
  LeanFeed.pfeed P (PNADOP3.adoXM_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 75%nat => sd
      | 77%nat => F + 32 + 4 * z | 79%nat => sigma + 1 | 87%nat => nr | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A10 & A12 & A13 & A15 & A16 & A21 & A24 & A25).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  destruct (frac_loop (Z.to_nat sd) fx1 R1 M 0 z (sigma + nr + 3) sd
              ltac:(clear - Hsd; lia) ltac:(clear - Hsd; lia) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - Hsig Hnr; lia) ltac:(clear - Hsig Hnr; lia))
    as (fx2 & R2 & M2 & m & MS2 & VO2 & SE2 & Hm & Hom).
  - unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; kr KS1.
  - rewrite (KS1 _) by inl. rewrite G11. f_equal. clear; lia.
  - req A12.
  - req A10.
  - rewrite (KS1 _) by inl. rewrite G18. f_equal. clear; lia.
  - req A13.
  - rewrite (KS1 _) by inl. exact G14.
  - req A15.
  - req A16.
  - req A25.
  - exact VO.
  - exists fx2, R2, M2, (first + (sigma + nr + 3) + m). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2|].
    clear - Hm Hom Hsig Hnr. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma to_bv_and a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof.
  intros Ha Hb. apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (PNADOP1.land_le_l a b ltac:(clear - Ha; Lia.lia) ltac:(clear - Hb; Lia.lia)) as L1.
  pose proof (Z.land_nonneg a b) as L2.
  rewrite (Z.mod_small a), (Z.mod_small b), (Z.mod_small (Z.land a b)); [reflexivity| | exact Hb| exact Ha].
  split; [apply L2; left; clear - Ha; Lia.lia| clear - L1 Ha; Lia.lia].
Qed.
Lemma wrap_sub1 x c : 0 <= x < 2 ^ 63 -> Z_to_bv 64 ((x + (18446744073709551616 - c)) mod 2 ^ 64) = Z_to_bv 64 (x - c).
Proof.
  intros Hx. apply to_bv_eqm. rewrite Z.mod_mod by (clear; Lia.lia). replace (x + (18446744073709551616 - c)) with (x - c + 1 * 2 ^ 64) by (clear; Lia.lia).
  rewrite Z.mod_add by (clear; Lia.lia). reflexivity.
Qed.
Lemma wrap_sub2 x c : 0 <= x < 2 ^ 63 -> Z_to_bv 64 ((x mod 2 ^ 64 + (18446744073709551616 - c)) mod 2 ^ 64) = Z_to_bv 64 (x - c).
Proof. intros Hx. rewrite (Z.mod_small x) by (clear - Hx; Lia.lia). apply wrap_sub1. exact Hx. Qed.
(* [comment removed for export] *)
Definition RLO (R : bvmap 5 word) : Prop :=
  RL R /\ getr R (reg 30) = Z_to_bv 64 (first + sigma) /\ getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z)
  /\ getr R (reg 13) = Z_to_bv 64 sd.
Lemma fork fx R M e :
  PNADD.stP R0 S F first sigma e z sd R -> 0 <= e <= 16383 -> vout MV M ->
  exists fx' R',
    (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb4388 M) /\ RLO R' /\ getr R' (reg 10) = Z_to_bv 64 (sd - 1)
       /\ getr R' (reg 24) = Z_to_bv 64 (sd + e - 6177) /\ (sd + e - 6177 < -6 \/ 6177 <= e))
    \/ (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb44ac M) /\ RLO R' /\ getr R' (reg 14) = Z_to_bv 64 (e - 6176)
       /\ e <= 6175 /\ -6 <= sd + e - 6177)
    \/ (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb42cc M) /\ RLO R' /\ e = 6176).
Proof.
  intros (((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20 & Q30) & Q18 & Q13 & QE & Q5) He VO.
  unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  set (E1 := bv_unsigned (getr R (reg 17))) in *.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 17))) as U11. change (bv_modulus 64) with (2 ^ 64) in U11. fold E1 in U11.
  assert (Q11 : getr R (reg 17) = Z_to_bv 64 E1) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia). assert (Y4 : S mod 32 = 0) by exact GS32.
  LeanFeed.pfeed P (PNADOP1.adoF_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 59%nat => E1 | 75%nat => sd | _ => 0 end)) ltac:(PNADK.dsc).
  assert (RK : forall R', (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 23; 26; 27; 30]%nat -> getr R' (reg x) = getr R (reg x)) -> getr R' (reg 13) = Z_to_bv 64 sd -> RLO R').
  { intros R' KS K13. unfold RLO, RL, PNADD.RBA, PNADD.SH, PNADD.SBv. repeat apply conj; first [exact K13 | (rewrite (KS _) by inl; assumption)]. }
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & [ (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & A24 & HX) | [ (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & A15 & A24 & Hbig & HX) | [ (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & A15 & A24 & Hne & Hsm & HX) | (MS1 & KS1 & A10 & A11 & A12 & A13 & A14 & A15 & A24 & A25 & Heq & Hsm & HX) ]]]);
    (assert (EM : M1 = M) by (apply functional_extensionality; exact FW1)); subst M1; exists fx1, R1;
    rewrite QE in *;
    try (cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in HX;
         rewrite (to_bv_and E1 16383) in HX by (first [exact U11 | clear; lia]); rewrite QE in HX;
         rewrite !to_bv_add, (to_bv_eqm 18446744073709551610 (-6)), slt_lit in HX by (first [reflexivity | clear - He Y2; lia]));
    assert (RK1 : RLO R1) by (apply RK; [intros x Hx; apply KS1; revert x Hx; apply L5K.incl_b; vm_compute; reflexivity| apply to_bv_of_unsigned; exact A13]).
  - left. destruct (Z.ltb_spec (sd + e + -6177) (-6)) as [Hl|Hl]; [| exfalso; clear - HX; lia].
    split; [exact MS1|]. split; [exact RK1|]. split; [apply to_bv_of_unsigned in A10; rewrite A10; apply to_bv_eqm; rewrite Z.mod_mod by (clear; lia); rewrite <- (Z.mod_add (sd - 1) 1 (2 ^ 64)) by (clear; lia); f_equal; clear; lia|].
    split; [apply to_bv_of_unsigned in A24; rewrite A24; apply (wrap_sub2 (sd + e) 6177); clear - He Y2; lia|]. left. clear - Hl. lia.
  - left. split; [exact MS1|]. split; [exact RK1|]. split; [apply to_bv_of_unsigned in A10; rewrite A10; apply to_bv_eqm; rewrite Z.mod_mod by (clear; lia); rewrite <- (Z.mod_add (sd - 1) 1 (2 ^ 64)) by (clear; lia); f_equal; clear; lia|].
    split; [apply to_bv_of_unsigned in A24; rewrite A24; apply (wrap_sub2 (sd + e) 6177); clear - He Y2; lia|]. right. exact Hbig.
  - right. left. destruct (Z.ltb_spec (sd + e + -6177) (-6)) as [Hl|Hl]; [exfalso; clear - HX; lia|].
    split; [exact MS1|]. split; [exact RK1|].
    split; [rewrite A14; cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div]; rewrite to_bv_and by (first [exact U11 | clear; lia]); rewrite QE, to_bv_add; f_equal; clear; lia|].
    split; [| clear - Hl; lia].
    destruct (Z_lt_le_dec e 6176) as [Y|Y]; [clear - Y; lia|]. exfalso. assert (E6 : e = 6176) by (clear - Y Hsm; lia). rewrite E6 in Hne. clear - Hne. change (6176 - 6176) with 0 in Hne. rewrite Z.mod_0_l in Hne by (clear; Lia.lia). Lia.lia.
  - right. right. split; [exact MS1|]. split; [exact RK1|].
    destruct (Z_lt_le_dec e 6176) as [Y|Y]; [| clear - Y Hsm; lia]. exfalso. rewrite <- (Z.mod_add (e - 6176) 1 (2 ^ 64)) in Heq by (clear; lia).
    rewrite Z.mod_small in Heq by (clear - Y He; lia). clear - Heq Y He. lia.
Qed.

(* [comment removed for export] *)
Lemma radix fx R M e :
  0 <= e <= 6175 -> -6 <= sd + e - 6177 ->
  RLO R -> getr R (reg 14) = Z_to_bv 64 (e - 6176) -> vout MV M ->
  exists fx' R' M' ptr, msteps RSEGS (st fx R 0xb44ac M) (st fx' R' 0xb46b0 M') /\ vout MV M'
      /\ PNADD.stE R0 S F ptr 0 R' /\ first <= ptr <= first + 42.
Proof.
  intros He Hlo (RLR & G30 & G18 & G13) G14 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X6 : 0 <= sd < 2 ^ 64) by (clear - Hsd Hzs Hz; lia). assert (X7 : 0 <= e < 2 ^ 64) by (clear - He; lia).
  assert (Y2 : 1 <= sd <= 36) by (clear - Hsd Hzs Hz; lia). assert (Y3 : 0 <= e <= 16383) by (clear - He; lia). assert (Y4 : S mod 32 = 0) by exact GS32.
  LeanFeed.pfeed P (PNADOP3.adoXA_conc fx R M (fun i => match i with 2%nat => S | 33%nat => first | 50%nat => F | 73%nat => e | 75%nat => sd | _ => 0 end)) ltac:(PNADK.dsc).
  destruct P as (fx1 & R1 & M1 & MG1 & FW1 & FZ1 & MS1 & KS1 & A12 & A14).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FW1). subst M1.
  assert (RL1 : RL R1) by (unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv; repeat apply conj; kr KS1).
  assert (B30 : getr R1 (reg 30) = Z_to_bv 64 (first + sigma)) by (rewrite (KS1 _) by inl; exact G30).
  assert (B18 : getr R1 (reg 18) = Z_to_bv 64 (F + 32 + 4 * z)) by (rewrite (KS1 _) by inl; exact G18).
  assert (B13 : getr R1 (reg 13) = Z_to_bv 64 sd) by (rewrite (KS1 _) by inl; exact G13).
  set (rd := sd + e - 6176).
  destruct (Z_lt_le_dec 0 rd) as [POS|NPOS]; [| destruct (Z.eq_dec rd 0) as [ZERO|NEG]].
  - destruct (radix_pos fx1 R1 M rd ltac:(clear - POS; lia) ltac:(subst rd; clear - He Y2; lia) ltac:(subst rd; clear - He; lia) RL1 B13
              ltac:(rewrite A14; f_equal; subst rd; clear; lia) B30 B18 VO) as (fx2 & R2 & M2 & ptr & MS2 & VO2 & SE2 & Hp).
    exists fx2, R2, M2, ptr. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2| exact Hp].
  - destruct (radix_zero fx1 R1 M RL1 B13 ltac:(rewrite A14; f_equal; subst rd; clear - ZERO; lia) B30 B18 VO) as (fx2 & R2 & M2 & ptr & MS2 & VO2 & SE2 & Hp).
    exists fx2, R2, M2, ptr. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact SE2| exact Hp].
  - set (nr := - rd - 1). assert (Hnr : 0 <= nr <= 4) by (subst nr rd; clear - NPOS NEG Hlo; lia).
    destruct (radix_neg_pre fx1 R1 M nr Hnr RL1 B13
                ltac:(rewrite A14; apply to_bv_eqm; replace (18446744073709551615 - nr) with (e + sd - 6176 + 1 * 2 ^ 64) by (subst nr rd; clear; lia); rewrite Z.mod_add by (clear; lia); reflexivity)
                B30 B18 VO)
      as (fx2 & R2 & M2 & MS2 & VO2 & RL2 & C13 & C30 & C18 & C10 & C5 & C14 & C11 & C12 & C15 & C16 & U1 & U0).
    destruct (nloop (Z.to_nat (nr + 2)) fx2 R2 M2 nr 0 (4 - nr) ltac:(clear - Hnr; lia) Hnr ltac:(clear; lia) ltac:(clear - Hnr; lia) ltac:(clear; lia)
                RL2 C13 C30 C18 C10 C5 C14 C11 C12 C15 C16 U1 U0 VO2)
      as (fx3 & R3 & M3 & MS3 & VO3 & RL3 & D13 & D30 & D18 & D10 & D5 & D14 & D17 & D11 & D12).
    destruct (radix_neg_post fx3 R3 M3 nr Hnr RL3 D13 D30 D18 D10 D5 D14 D17 D11 D12 VO3) as (fx4 & R4 & M4 & ptr & MS4 & VO4 & SE4 & Hp).
    exists fx4, R4, M4, ptr. split; [eapply msteps_trans; [exact MS1|]; eapply msteps_trans; [exact MS2|]; eapply msteps_trans; [exact MS3| exact MS4]|].
    split; [exact VO4|]. split; [exact SE4| exact Hp].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma iloop (scw : Z) (n : nat) : forall fx R M i cnt,
  cnt - i = Z.of_nat n -> 0 <= i < cnt -> cnt < sd -> sigma + 2 + i <= 35 ->
  RL R -> getr R (reg 30) = Z_to_bv 64 (first + sigma) -> getr R (reg 18) = Z_to_bv 64 (F + 32 + 4 * z) ->
  getr R (reg 24) = Z_to_bv 64 scw -> getr R (reg 14) = Z_to_bv 64 sigma ->
  getr R (reg 12) = Z_to_bv 64 (first + sigma + 2) -> getr R (reg 25) = Z_to_bv 64 (first + sigma + 1) ->
  getr R (reg 10) = Z_to_bv 64 (F + 32 + 4 * (z + (i + 1))) -> getr R (reg 21) = Z_to_bv 64 (F + 32 + 4 * (z + (i + 1))) ->
  getr R (reg 5) = Z_to_bv 64 (i + 1) -> getr R (reg 6) = Z_to_bv 64 36 -> getr R (reg 13) = Z_to_bv 64 0 ->
  getr R (reg 15) = Z_to_bv 64 18446744073709551611 -> getr R (reg 16) = Z_to_bv 64 18446744073709551615 -> getr R (reg 17) = Z_to_bv 64 cnt ->
  vout MV M ->
  exists fx' R' M' k, msteps RSEGS (st fx R 0xb4424 M) (st fx' R' 0xb45b8 M') /\ vout MV M'
    /\ RL R' /\ getr R' (reg 24) = Z_to_bv 64 scw /\ getr R' (reg 25) = Z_to_bv 64 (first + k) /\ sigma + 2 + i < k <= sigma + 2 + cnt /\ k <= 36.
Proof.
  induction n as [|n IH]; intros fx R M i cnt Hn Hi Hcs Hw RLR G30 G18 G24 G14 G12 G25 G10 G21 G5 G6 G13 G15 G16 G17 VO; [exfalso; clear - Hn Hi; lia|].
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dig_facts MV M z sd (z + (i + 1)) MI SD VO Hz Hzs ltac:(clear - Hi Hcs; lia)) as (d & Hd & DR & DA & DZ & DU & DSH).
  destruct (dst_facts MV M (sigma + 2 + i) MI VO ltac:(clear - Hi Hcs Hsig Hz Hzs; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (TD (z + (i + 1)) ltac:(clear - Hi Hcs Hz Hzs; lia)) as TDi. clear TD.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= cnt < 2 ^ 64) by (clear - Hi Hcs Hz Hzs; lia).
  assert (X6 : 0 <= i < 2 ^ 64) by (clear - Hi Hcs Hz Hzs; lia). assert (X7 : 0 <= F + 32 + 4 * (z + (i + 1)) < 2 ^ 64) by (clear - DR; lia).
  assert (X8 : 0 <= first + (sigma + 2 + i) < 2 ^ 64) by (clear - TR; lia). assert (X9 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Y1 : 1 <= cnt <= 35) by (clear - Hi Hcs Hz Hzs; lia). assert (Y2 : 0 <= i <= 34) by (clear - Hi Hcs Hz Hzs; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32. assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  assert (G12' : getr R (reg 12) = Z_to_bv 64 ((first + (sigma + 2 + i)) - (i))) by (rewrite G12; f_equal; clear; lia).
  assert (G25' : getr R (reg 25) = Z_to_bv 64 (((first + (sigma + 2 + i)) - (i)) - 1)) by (rewrite G25; f_equal; clear; lia).
  assert (G30' : getr R (reg 30) = Z_to_bv 64 (((first + (sigma + 2 + i)) - (i)) - 2)) by (rewrite G30; f_equal; clear; lia).
  assert (G18' : getr R (reg 18) = Z_to_bv 64 (((F + 32 + 4 * (z + (i + 1))) + ((-4) * (i))) - 4)) by (rewrite G18; f_equal; clear; lia).
  LeanFeed.pfeed P (PNADOP2.adoI2_conc fx R M (fun j => match j with 2%nat => S | 33%nat => first | 50%nat => F | 76%nat => i
      | 77%nat => F + 32 + 4 * (z + (i + 1)) | 78%nat => cnt | 80%nat => d | 82%nat => first + (sigma + 2 + i) | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + (sigma + 2 + i) + 0 <= a < first + (sigma + 2 + i) + 0 + 1 -> Wout a) by (intros a Ha; left; clear - Ha Hi Hcs Hsig Hz Hzs; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A5 & A7 & A10 & A11 & A12 & A14 & A15 & A21 & A23 & A25 & A28 & HX) | [ (MS1 & KS1 & A7 & A10 & A11 & A12 & A14 & A15 & A23 & A25 & A28 & HX) | (MS1 & KS1 & A5 & A7 & A10 & A11 & A12 & A14 & A15 & A21 & A23 & A25 & A28 & HX) ]]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1;
    assert (RL1 : RL R1) by (unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv; repeat apply conj; kr KS1);
    assert (B24 : getr R1 (reg 24) = Z_to_bv 64 scw) by (rewrite (KS1 _) by inl; exact G24).
  - (* [comment removed for export] *)
    assert (Hlt : i + 1 < cnt).
    { destruct HX as (_ & Hlt & _). rewrite Z.mod_small in Hlt by (clear - Hi Y1; lia). exact Hlt. }
    assert (Hw1 : sigma + 2 + (i + 1) <= 35).
    { destruct HX as (HS & _). cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in HS. rewrite G14 in HS.
      rewrite !to_bv_add, slt_lit in HS by (clear - Hi Hcs Hsig Hz Hzs; lia).
      destruct (Z.ltb_spec (sigma + i + 3) 36) as [Hl|Hl]; [clear - Hl; lia| exfalso; clear - HS; lia]. }
    destruct (IH fx1 R1 M1 (i + 1) cnt ltac:(clear - Hn; lia) ltac:(clear - Hi Hlt; lia) Hcs Hw1 RL1 ltac:(rewrite (KS1 _) by inl; exact G30)
                ltac:(rewrite (KS1 _) by inl; exact G18) B24 ltac:(rewrite A14; exact G14))
      as (fx2 & R2 & M2 & k & MS2 & VO2 & RL2 & C24 & C25 & Hk & Hk36).
    + req A12.
    + req A25.
    + req A10.
    + req A21.
    + req A5.
    + rewrite (KS1 _) by inl. exact G6.
    + rewrite (KS1 _) by inl. exact G13.
    + req A15.
    + rewrite (KS1 _) by inl. exact G16.
    + rewrite (KS1 _) by inl. exact G17.
    + exact VO1.
    + exists fx2, R2, M2, k. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact RL2|]. split; [exact C24|]. split; [exact C25|]. split; [clear - Hk; lia| exact Hk36].
  - (* [comment removed for export] *)
    exists fx1, R1, M1, (sigma + 2 + i + 1). split; [exact MS1|]. split; [exact VO1|]. split; [exact RL1|]. split; [exact B24|].
    split; [rewrite A25; f_equal; clear; lia|]. split; [clear - Hi; lia| clear - Hw; lia].
  - (* [comment removed for export] *)
    exists fx1, R1, M1, (sigma + 2 + i + 1). split; [exact MS1|]. split; [exact VO1|]. split; [exact RL1|]. split; [exact B24|].
    split; [rewrite A25; f_equal; clear; lia|]. split; [clear - Hi; lia| clear - Hw; lia].
Qed.

(* [comment removed for export] *)
Lemma sci_head (scw : Z) fx R M :
  RLO R -> getr R (reg 10) = Z_to_bv 64 (sd - 1) -> getr R (reg 24) = Z_to_bv 64 scw -> vout MV M ->
  exists fx' R' M' k, msteps RSEGS (st fx R 0xb4388 M) (st fx' R' 0xb45b8 M') /\ vout MV M'
    /\ RL R' /\ getr R' (reg 24) = Z_to_bv 64 scw /\ getr R' (reg 25) = Z_to_bv 64 (first + k) /\ sigma + 1 <= k <= sigma + 1 + sd /\ k <= 36.
Proof.
  intros (RLR & G30 & G18 & G13) G10 G24 VO.
  pose proof RLR as ((Q2 & Q3 & Q4 & Q8 & Q9 & Q23 & Q26 & Q27) & Q19 & Q20). unfold PNADD.SH, PNADD.SBv in Q23, Q19.
  pose proof G as G'. unfold PNADD.geom in G'.
  destruct G' as (GS1 & GS32 & GF1 & GF8 & GFSH & GFS & GFI & GV1 & GV8 & GVSH & GVS & GVF & GFF1 & GFF32 & GFFSH & GFFS & GFFI & GFFf & GFFv & GFL1 & GFLSH & GFLF & GFLS & GFLf & GFLv).
  pose proof (MIA_out MV M MI VO) as (W1 & W2 & W3 & W4 & W5 & IC & CSB & CUAR & SV & C128 & FLC & ZF6 & ZSIG).
  destruct (dig_facts MV M z sd z MI SD VO Hz Hzs ltac:(clear - Hsd; lia)) as (d & Hd & DR & DA & DZ & DU & DSH).
  destruct (dst_facts MV M sigma MI VO ltac:(clear - Hsig; lia)) as (TR & TZ & TW & TSH & TS & TI & TD).
  pose proof (TD z ltac:(clear - Hsd Hz Hzs; lia)) as TDi. clear TD.
  destruct (dst_facts MV M (sigma + 1) MI VO ltac:(clear - Hsig; lia)) as (UR & UZ & UW & USH & US & UI & UD).
  pose proof (UD z ltac:(clear - Hsd Hz Hzs; lia)) as UDi. clear UD.
  rewrite !Z.add_assoc in UR, UZ, UW, USH, US, UI, UDi.
  assert (X1 : 0 <= S < 2 ^ 64) by (clear - SR; lia). assert (X2 : 0 <= first < 2 ^ 64) by (clear - GF1; lia). assert (X3 : 0 <= F < 2 ^ 64) by (clear - GFF1; lia).
  assert (X5 : 0 <= sd - 1 < 2 ^ 64) by (clear - Hsd Hz Hzs; lia).
  assert (X7 : 0 <= F + 32 + 4 * z < 2 ^ 64) by (clear - DR; lia).
  assert (X8 : 0 <= sigma < 2 ^ 64) by (clear - Hsig; lia). assert (X9 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Y1 : 0 <= sd - 1 <= 35) by (clear - Hsd Hz Hzs; lia).
  assert (Y4 : S mod 32 = 0) by exact GS32. assert (Y6 : 4096 <= first <= 140737488355280) by exact GF1.
  LeanFeed.pfeed P (PNADOP2.adoI1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => first | 50%nat => F
      | 77%nat => F + 32 + 4 * z | 78%nat => sd - 1 | 79%nat => sigma | 80%nat => d | _ => 0 end)) ltac:(PNADK.dsc).
  assert (WS : forall a, first + sigma + 0 <= a < first + sigma + 0 + 2 -> Wout a) by (intros a Ha; left; clear - Ha Hsig; lia).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & [ (MS1 & KS1 & A10 & A11 & A12 & A25 & HX & _) | (MS1 & KS1 & A5 & A6 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A21 & A25 & _ & HX & _) ]);
    pose proof (vout_step MV M M1 _ VO MG1 FZ1 WS) as VO1;
    assert (RL1 : RL R1) by (unfold RL, PNADD.RBA, PNADD.SH, PNADD.SBv; repeat apply conj; kr KS1);
    assert (B24 : getr R1 (reg 24) = Z_to_bv 64 scw) by (rewrite (KS1 _) by inl; exact G24).
  - (* [comment removed for export] *)
    exists fx1, R1, M1, (sigma + 1). split; [exact MS1|]. split; [exact VO1|]. split; [exact RL1|]. split; [exact B24|].
    split; [rewrite A25; f_equal; clear; lia|]. split; [clear - Hsd; lia| clear - Hsig; lia].
  - rewrite Z.sub_0_r, Z.mod_small in HX by (clear - Y1; lia).
    destruct (iloop scw (Z.to_nat (sd - 1)) fx1 R1 M1 0 (sd - 1) ltac:(clear - HX; lia) ltac:(clear - HX; lia) ltac:(clear; lia) ltac:(clear - Hsig; lia) RL1
                ltac:(rewrite (KS1 _) by inl; exact G30) ltac:(rewrite (KS1 _) by inl; exact G18) B24 A14)
      as (fx2 & R2 & M2 & k & MS2 & VO2 & RL2 & C24 & C25 & Hk & Hk36).
    + exact A12.
    + exact A25.
    + req A10.
    + req A21.
    + req A5.
    + exact A6.
    + exact A13.
    + exact A15.
    + exact A16.
    + exact A17.
    + exact VO1.
    + exists fx2, R2, M2, k. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact VO2|]. split; [exact RL2|]. split; [exact C24|]. split; [exact C25|]. split; [clear - Hk; lia| exact Hk36].
Qed.

End Arms.
End View.
End PNADO1.
