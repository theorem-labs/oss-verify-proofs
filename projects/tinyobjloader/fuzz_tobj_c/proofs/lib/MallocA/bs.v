(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_066.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq cd.

(* [comment removed for export] *)
Module SpineMallocQ12.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "mul"; "of_nat"; "lt"; "div"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "true"; "length"; "list"; "nil"; "Some"; "option"; "false"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SAlu"; "SLit"; "eval"; "ss_next"; "sv"; "sprop"; "valuation"; "ss_facts"; "ss_lenient"; "SMd"; "SPNot"; "SVar"; "holds"; "swf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "cs_free_array"; "cs_mapped_free_array"; "cs_allocated_user"; "cs_mapped_user"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "gh_new"; "JR"; "ghosts"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "ALU_SLL"; "ALU_SUB"; "M_DIVU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "vNEW"; "GR"; "F_new"; "cD"; "vAU"; "vMFA"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQ12"; "F_geu"; "need_e"; "new_e"; "facap_okb"; "rup_e"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "V_SIZE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "Size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit"; "CLS30"; "FACAP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2"; "rigids"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA EntailA CFGA GlueA SummaryA LedgerA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws PrimCredit PrimCreditLaws GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel RefillBits.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aj.SpineMallocS2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillBits OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.RefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition new_e : sv := ltac2:(tb__ "0|0|
S25S36S1cS35S1cS32S3eS1dZ40000A1A3S3cA3S27S4dA1A3").
Definition need_e : sv := ltac2:(tb__ "0|0|
S1cS34S1cS32S3fS38A3S1dZ2A1A3").
Definition F_geu : sprop := SPBranch BC_GEU vMFA need_e.
Definition rup_e : sv := ltac2:(tb__ "0|0|
S1cS33S1cS32S41S1dZ3ffffA1A3S1dZfffffffffffc0000A1A3").

Definition facap_okb (c : Z) : bool := FACAP c <=? 536608768.
Lemma facap_okb_all : ltac2:(tb__ "0|0|
S2S11S48S0S43S4fA3S13A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma facap_room : ltac2:(tb__ "0|0|
S0S1S5Z1R1A2S5R1Z1eA2A2S5S50R2A1Z1ffc0000A2F_;Fc;").
Proof. intros c Hc. pose proof (proj1 (forallb_forall _ _) facap_okb_all c (proj2 (In_CLS30 c) Hc)) as H. apply Z.leb_le in H. exact H. Qed.

Section VALS.
Variables (A : AA) (rb r : valuation).
Hypothesis CF : cfacts A rb.
Hypothesis PF : popfacts A rb.
Hypothesis RG : ltac2:(tb__ "0|0|
S53VA;Vrb;Vr;A3").
Hypothesis GH : ltac2:(tb__ "0|0|
S31VA;Vrb;Vr;A3").
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let cs : class_state := cst_of A nv.

Lemma new_nums : ltac2:(tb__ "0|5|
S4eVc;A1S0S8S14S0S2bVcs;A1A2A1S0S2dVcs;A1S0S2eVcs;A1S0S2cVcs;A1S0S2fVA;Vrb;A2S0S1S1S5Z20R6A2S5R6Z10000A2A2S1S1S5Z0M0R4A2S5R4R3A2A2S1S5R3Zdffc0000A2S1S1S5Z4M1R1A2S5R1Z2001A2A2S1S5S51Vc;A1R1A2S1S5S6R4S7R1R6A2A2M2S6R3Z40000M3A2M4A2S1S9G4S6G2R6A2A2S1S5G0R5A2S1S5S7G1R5A2R2A2S1S5R2Z1ffc0000A2S1S2S0SbR2G3A2G0A3S2S0R1SaScG4R4A2R6A2A3A2A2A2A2A2A2A2A2A2A2A2Tnew;Tmfa;Tmu;Tau;Tnf;TS;").
Proof.
  intros S nf au mu mfa new.
  destruct (pop_nums A rb CF PF) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8). cbn zeta in N1, N2, N3, N4, N5, N6, N7, N8. fold nv c cs in N1, N2, N3, N4, N5, N6, N7, N8. fold S nf au mu in N1, N2, N3, N4, N5, N6, N7, N8.
  unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as ((_ & C1 & _) & (_ & _ & K3) & _ & (MF0 & MF1) & (_ & FC0 & _) & _). fold S in K3. fold nf mfa in MF0, MF1, FC0.
  pose proof (facap_room c C1) as FR.
  assert (EN : new = (mu + 262144 - au) / S) by (unfold new, gh_new, kUserMapSize; fold nv c cs; reflexivity).
  pose proof (Z.div_mod (mu + 262144 - au) S ltac:(clear -N1; lia)) as DM. pose proof (Z.mod_pos_bound (mu + 262144 - au) S ltac:(clear -N1; lia)) as MB.
  rewrite <- EN in DM. clearbody new.
  assert (Q1 : 262144 - S < new * S <= 262144 + S) by (clear -DM MB N4 N6 N1; nia).
  assert (Q2 : 4 <= new <= 8193) by (clear -Q1 N1; nia).
  assert (Q3 : kchunks c <= new) by (clear -Q1 N1 N2 K3; nia).
  split; [exact N1|]. split; [exact N4|]. split; [exact N5|]. split; [exact Q2|]. split; [exact Q3|].
  split; [clear -DM MB; nia|]. split; [clear -DM MB; nia|]. split; [clear -N3; lia|]. split; [clear -MF1; lia|]. split; [clear -FC0 FR; lia|]. split; [exact MF0 | exact EN].
Qed.

Lemma new_val : ltac2:(tb__ "0|0|
S2S45Q40A1S1eVr;S42A2S1eVr;S38A2A3").
Proof.
  destruct new_nums as (N1 & N2 & N3 & N4 & _ & _ & _ & _ & _ & _ & _ & EN). cbn zeta in N1, N2, N3, N4, EN. fold nv c cs in N1, N2, N3, N4, EN.
  destruct RG as (_ & E148 & _). fold nv c in E148.
  destruct GH as (_ & _ & _ & Q223 & Q224 & _ & _ & _ & Q228 & _). fold nv c cs in Q223, Q224.
  unfold new_e, vMU, vAU, vNEW, V_SIZE. cbn [eval]. apply bv_eq. rewrite divu_val by (rewrite E148, u64_lit; clear -N1; lia).
  rewrite sub_val, add_val, E148, Q223, Q224, Q228, !u64_lit by (clear -N1 N2 N3 N4; lia).
  rewrite (Z.mod_small (cs_mapped_user cs + 262144)) by (clear -N2 N3; lia). rewrite Z.mod_small by (clear -N2 N3; lia). symmetry. exact EN.
Qed.

Lemma F_new_hold : Forall (holds r) F_new.
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _ & _ & _ & _ & _ & Q228 & _). fold nv c cs in Q222.
  unfold F_new. repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; unfold vNEW, vMFA; cbn [eval]; rewrite ?Q222, ?Q228, ?u64_lit by (clear -N4 N8 N9 N10; lia).
  - clear -N4; lia.
  - clear -N4; lia.
  - exact N10.
  - split; [clear; lia | change (2 ^ 18) with 262144; exact N11].
Qed.

Lemma need_val : ltac2:(tb__ "0|0|
S2S0S46Q40S1eVr;S41A2A2S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A3").
Proof.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N4, N8, N9, N10. fold nv c cs in N4, N8, N9, N10.
  destruct GH as (_ & Q221 & _ & _ & _ & _ & _ & _ & Q228 & _). unfold gh_nf in Q221. fold nv c cs in Q221.
  unfold need_e, vNF, vNEW. cbn [eval]. rewrite sll_val, add_val, Q221, Q228, !u64_lit by (clear -N4 N8 N9 N10; lia).
  change (2 mod 64) with 2. rewrite Z.shiftl_mul_pow2 by (clear; lia). rewrite (Z.mod_small (_ + _)) by (clear -N4 N8 N9 N10; lia).
  rewrite Z.mod_small by (clear -N4 N8 N9 N10; lia). clear; lia.
Qed.

Lemma geu_iff : ltac2:(tb__ "0|0|
S4S28Vr;S40A2S3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2A1A2").
Proof.
  destruct new_nums as (_ & _ & _ & _ & _ & _ & _ & N8 & N9 & N10 & _). cbn zeta in N8, N9, N10. fold nv c cs in N8, N9, N10.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  unfold F_geu. cbn [holds]. unfold branch_taken, bv_ltu. rewrite need_val. unfold vMFA. cbn [eval]. rewrite Q222, u64_lit by (clear -N8 N9 N10; lia).
  rewrite negb_true_iff, Z.ltb_ge. clear; lia.
Qed.

Lemma rup_val : ltac2:(tb__ "0|0|
S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2S2S45Q40A1S1eVr;S44A2S1eVr;S1cS32S3dS1dZ40000A1A3A2A3F_;").
Proof.
  intros HLT. pose proof need_val as NV.
  destruct new_nums as (_ & _ & _ & N4 & _ & _ & _ & N8 & N9 & N10 & N11 & _). cbn zeta in N4, N8, N9, N10, N11. fold nv c cs in N4, N8, N9, N10, N11.
  destruct GH as (_ & _ & Q222 & _). fold nv c cs in Q222.
  set (need := 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)) in *. set (mfa := cs_mapped_free_array cs) in *.
  unfold rup_e. cbn [eval]. apply bv_eq. rewrite and_val, !add_val, NV. unfold vMFA. cbn [eval]. rewrite Q222.
  replace (bv_unsigned (Z_to_bv 64 18446744073709289472)) with 18446744073709289472 by reflexivity. rewrite !u64_lit by (clear -N9 N10; lia).
  rewrite (Z.mod_small (need + 262143)) by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite land_m18_up by (unfold need; clear -N4 N8 N9 N10; lia).
  rewrite (Z.mod_small (mfa + 262144)) by (clear -N9 N10 N8; lia).
  destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) N11) as [q Hq].
  assert (E : (need + 262143) / 262144 = q + 1).
  { symmetry. apply Z.div_unique with (need + 262143 - (q + 1) * 262144); [left; unfold need in *; clear -HLT Hq N4 N9; lia | clear; lia]. }
  rewrite E, Hq. clear; lia.
Qed.
End VALS.

Section POPMID.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list ulink) (st : ustop) (rho : valuation).
Hypothesis HE : ltac2:(tb__ "0|0|
S52VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis PF : popfacts A rb.
Notation JRp := (JR A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let cs : class_state := cst_of A nv.
Variable ph : phase.

Variable F : nat.
Variables (E3 RU : axst) (LD LF0 LFm : leafA).
Let FR : list sprop := factsQ E3.
Let CD : axst := ltac2:(tb__ "0|0|
S3bVFR;SeVLD;A1A2").
Hypothesis R_d : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z416f0S16S0A1A3VRU;S13A5S17G0S12SfVLD;S16SfA1A3A2A3").
Hypothesis LN_u : ltac2:(tb__ "0|0|
S2S11S24SdVRU;A1A1S19A3").
Hypothesis NX_u : ltac2:(tb__ "0|0|
S2S11S49S39S1fSdVRU;A1A1A2S13A3").
Hypothesis W_d : ltac2:(tb__ "0|0|
S2S11S29SdVCD;A1A1S13A3").
Hypothesis D_d : ltac2:(tb__ "0|4|
S2S18S1bS15S1bS20S20A2M0A1M1S15S21A1M2A2M3A1S4cSdSeVLD;A1A1SdVCD;A1A2S17G3S1aG1G2S12G0S1aS20S20S42S38A4S16G0A1A3S3aA4A2A3").
Hypothesis NX_d : ltac2:(tb__ "0|0|
S2S11S4aS1fSdVCD;A1A1S1fSdSeVLD;A1A1A1A2S13A3").
Hypothesis R_f : ltac2:(tb__ "0|1|
S2S18S15SfA1M0A1S10S2aVF;S12S0Z3f270S12S0Z4172cS16S0A1A3A3VCD;S13A5S17G0S12SfVLF0;S12SfVLFm;S16SfA1A3A3A2A3").
Hypothesis LN_d : ltac2:(tb__ "0|0|
S2S11S24SdVCD;A1A1S19A3").
Hypothesis NXr_d : ltac2:(tb__ "0|0|
S2S11S49S39S1fSdVCD;A1A1A2S13A3").
Hypothesis F0_in : ltac2:(tb__ "0|0|
S47S21S40S23SdSeVLF0;A1A1A1A3").
Hypothesis Fm_in : ltac2:(tb__ "0|0|
S47S21S26S40A1S23SdSeVLFm;A1A1A1A3").

Theorem populate_mid : ltac2:(tb__ "0|2|
S22S15S45Q40A1A1S4bS3S9S2cVcs;A1S7Z4S6S8S14S0S2bVcs;A1A2A1S2fVA;Vrb;A2A2A2A2M0A1S22VTR;S37S2aS30VA;VKc;Vrb;Vtp0;Vmd0;Vph;A6M1SeVLF0;A1R1R4A5R3A2Fr';F_;G0S22VTR;S37S2aG1SeVLFm;A1R1R5A5R4A2Fr';F_;VTR;S37S2aG1VRU;R5R4A5R3A2F_;F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q H0 Hm.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x416f0] RU [LD] ph r tp Q R_d LN_u NX_u).
  intros L r1 [<-|[]] _.
  apply (jr_restate A Kc rb tp0 md0 TR KIT (la_state LD) (ax_S CD) _ _ ph r1 tp Q W_d D_d NX_d).
  { intros tr md (HFz & HGh & _) _. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG. split.
    - unfold diffs_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. exact (new_val A rb r1 CF PF RG HGh).
    - exact (F_new_hold A rb r1 CF PF HGh). }
  change (ax_setS (la_state LD) (ax_S CD)) with CD.
  apply (jr_run A Kc rb tp0 md0 TR KIT HKc F [0x3f270; 0x4172c] CD [LF0; LFm] ph r1 tp Q R_f LN_d NXr_d).
  intros L r2 [<-|[<-|[]]] _.
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ F0_in) as BF.
    apply (tr_pure Kc TR KIT (~ (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb)))).
    { intros w [_ (HFz & HGh & _)]. exact (proj1 (geu_iff A rb r2 CF PF HGh) BF). }
    intros X. exact (H0 X r2).
  - apply (tr_facts Kc TR KIT). intros HF. pose proof (proj1 (Forall_forall _ _) HF _ Fm_in) as BF. cbn [holds] in BF.
    apply (tr_pure Kc TR KIT (cs_mapped_free_array cs < 4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))).
    { intros w [_ (HFz & HGh & _)].
      destruct (Z_lt_dec (cs_mapped_free_array cs) (4 * (Z.of_nat (length (cs_free_array cs)) + gh_new A rb))) as [X|X]; [exact X|].
      exfalso. apply BF. exact (proj2 (geu_iff A rb r2 CF PF HGh) X). }
    intros X. exact (Hm X r2).
Qed.
End POPMID.
End SpineMallocQ12.

(* [comment removed for export] *)
Module SpineCallocU2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "ss_objs"; "ss_next"; "sprop"; "ss_facts"; "ss_lenient"; "swf"; "rw"; "rm"; "agree_below"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "sym_runA"; "ax_X"; "axst"; "la_state"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "cons"; "true"; "prod"; "app"; "false"; "Some"; "option"; "nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3"; "skel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1"; "cU1"; "cU0"; "kU1"; "kU2"; "JU"; "cU2"; "perm_okb"; "O_arrF"; "O_pcmZ"; "eU"; "idx1"; "idx2"; "sU1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR"; "nobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP"; "O_st"; "O_pcc0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2"; "BASEF"; "BASEO"; "@Stdlib.Lists.List"; "incl"; "In"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "Kc_ok"; "mem_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI"; "initA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "entryR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase"; "stopJ_w"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR"; "TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5"; "posts_conv"; "rho_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cnt_of"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertCallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertCallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.GlueMC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bi.SpineCallocS9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.CRebuildRN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocU1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section UCHAIN.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variables (A : AA) (Kc : KcA) (rb : valuation) (tp0 : list word) (md0 : Model).
Variable TR : assn -> assn -> Prop.
Hypothesis KIT : TRok Kc TR.
Hypothesis HKc : Kc_ok Kc.
Variables (W : list Iface.ulink) (st : ustop) (rho : valuation).
Hypothesis HW : stopJ_w W st.
Hypothesis HE : ltac2:(tb__ "0|0|
S49VA;Vrb;Vtp0;Vmd0;VW;Vst;Vrho;A7").
Hypothesis Hini : aa_cache_inited A = false.
Notation JUp := (JU A Kc rb tp0 md0).
Let nv : Z := bv_unsigned (rw rb 12%positive).
Let c : Z := cls_of nv.
Let T : Z := ag_thread (aa_geom A).

Lemma ju_run : ltac2:(tb__ "0|1|
S1dS13S21A1S11S13SeA1M0S14S2S13S3cQ40A1A1S33ScS1cG0A1SfS1eR8R7R6S17A5S1bG0R5A2A3ScS14S7SdR7A1A1S1aA3ScS14S3bPdcS4SdR8A1A1A2S17A3SeS2S3aSeR2RaA3SbS4SdRcA1A1R9R2A3VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;RbA6S12R4A1R3R9A5R8A2F_;F_;Fr';FL;VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;R8A6RaR7R6A5R5A2F_;F_;F_;F_;FQ;Ftp;Fr;Fs;Fleaves;FE;Fcuts;Ffuel;").
Proof.
  intros fuel cuts E leaves s r tp Q Hrun Hl Hn HL.
  apply (tr_run Kc TR KIT fuel cuts E leaves (JUp s) r tp Q (JU_K A Kc rb tp0 md0 s)); [|exact Hrun | exact Hl | exact HL].
  apply JU_stable; [exact HKc | apply Pos.leb_le; exact Hn].
Qed.

Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis R_u1 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z411c4S15S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S15SeA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
ScS14S7SdS26VE3;A1A1A1S1aA3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
ScS14S3bPdcS4SdS26VE3;A1A1A1A2S17A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
ScS14S2bS32VL1;A1S2fVL1;A1A2S17A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdS31VL1;A1A1A1M0S19S0S20S0S3eS32VL1;A1U2A2G0A3S16S0S36S16S0S2dS15S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS27VL1;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S15S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS27VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S27VL1;A1A1S15G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
ScS14S8SdS25VL1;A1A1A1S17A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41260S15S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S15SeA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
ScS14S7SdS25VL1;A1A1A1S1aA3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
ScS14S3bPdcS4SdS25VL1;A1A1A1A2S17A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdVL2;A1A1M0S19S0S20S0S3eS32VL2;A1U1A2G0A3S16S0S2cVcellsF;A1S15S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS28VL2;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S15S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS28VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S28VL2;A1A1S15G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
ScS14S8SdS2aVL2;A1A1A1S17A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
ScS14S2bS32S2aVL2;A1M0A1S30G0A1A2S17A3").

Lemma u_carve_arr : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S34S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S1aA6M0S27VL1;A1R3R2R1A6S23S1eG0S25VL1;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR.
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET.
  pose proof HE as (_ & HA & _). destruct (uninit_frame A rb tp0 md0 HA Hini) as (FZ & PRS). fold T in FZ, PRS.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU1 L1)) [O_st] r _ HW HE HFz Hsm SK_k1 XF_k1) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }

  assert (PR : forall z, T + 288 <= z < T + 2768 -> exists b, view segs (rm r) z = Some b).
  { intros z Hz. rewrite (HR z). destruct (Z_lt_dec z (T + 2688)) as [LT|GE]; [|apply PRS; clear -Hz GE; lia].
    exists (Z_to_bv 8 0). apply (FZ ((z - T - 208) / 80) z).
    - pose proof (Z.div_le_mono 80 (z - T - 208) 80 ltac:(clear; lia) ltac:(clear -Hz; lia)) as D1. change (80 / 80) with 1 in D1.
      pose proof (Z.div_lt_upper_bound (z - T - 208) 80 31 ltac:(clear; lia) ltac:(clear -LT; lia)) as D2. clear -D1 D2. lia.
    - pose proof (Z.div_mod (z - T - 208) 80 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound (z - T - 208) 80 ltac:(clear; lia)) as MB. clear -DM MB. lia. }
  assert (ZB : forall c' j, 1 <= c' <= 30 -> (j < 4)%nat -> rd_of segs (rm r) (Z_to_bv 64 (T + (208 + 80 * c') + Z.of_nat j)) = Some (Z_to_bv 8 0)).
  { intros c' j Hc' Hj. pose proof (FZ c' (T + (208 + 80 * c') + Z.of_nat j) Hc' ltac:(clear -Hj; lia)) as Hb. rewrite <- (HR _) in Hb.
    rewrite view_in in Hb by (clear -Hc' Hj T1 T2 TG; lia). exact Hb. }
  apply (SPA_carve_list segs _ r (kU1 L1) tp w NU1 (nxt L1) Hsp W_c1).
  - apply Pos.le_refl.
  - unfold NU1. apply Forall_cons; [|apply Forall_nil].
    rewrite ET. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -T1; lia|]. split; [clear -T1 T2 TG; lia|].
    split.
    { unfold cells_inside, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'. clear -Hc'. lia. }
    split.
    { intros off Hoff. destruct (PR (T + off) ltac:(clear -Hoff; lia)) as [b Hb]. rewrite view_in in Hb by (clear -Hoff T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Hb]; [clear -Hoff T1 T2 TG; lia | clear -Hoff TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k1; intros rr y j []].
    unfold cells_in_view, cnt_spec. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc'). apply In_CLS30 in Hc'.
    intros j Hj. cbn [eval]. rewrite (enc_bytes_zero_nth 4 (Z_to_bv 64 0) j ltac:(apply u64_lit; clear; lia) Hj). exact (ZB c' j Hc' Hj).
  - cbn [map carve_obj NU1]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite ET.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear. lia.
  - cbn [map carve_obj NU1 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma u_carve_cnt : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S34S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S17A6M0S28VL2;A1R3R2R1A6S23S1eG0S2aVL2;A1R4R3R2A6F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w Hsp. pose proof Hsp as [HsmA HJ]. destruct HJ as (HFz & _ & _ & HR & _). cbn [umem] in HR. fold T in HR. destruct HR as (_ & L2' & L3).
  destruct (u_nums A rb tp0 md0 W st rho HE) as (C1 & T1 & T2 & TG & TI & PCr). fold T in T1, T2, TI, PCr. fold nv in C1, PCr. fold c in C1, PCr.
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. pose proof (entry_rigids _ _ _ _ _ _ _ _ HE HFz) as RG.
  pose proof (vT_val A rb r CF RG) as ET. fold T in ET. pose proof (pc_base_val A rb r CF RG) as EB. rewrite PCr in EB.
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  destruct (arm_base_disj A rb tp0 md0 W st rho (ax_S (kU2 L2)) [O_st] r _ HW HE HFz Hsm SK_k2 XF_k2) as (ob & ox & EO & SKx & BZ).
  destruct ox as [|os [|? ?]]; cbn [map] in SKx; try (exfalso; clear -SKx; discriminate SKx).
  assert (SKs : skel os = skel O_st) by (clear -SKx; congruence).
  assert (RNs : obj_range r os = (T + 2768, T + 3168)).
  { rewrite (obj_range_skel r os O_st SKs). unfold O_st. rewrite obj_range_mk by (clear; lia). rewrite ET. reflexivity. }
  destruct (L3 c C1) as (K1 & _ & _).
  apply (SPA_carve_list segs _ r (kU2 L2) tp w NU2 (nxt L2) Hsp W_c2).
  - apply Pos.le_refl.
  - unfold NU2. apply Forall_cons; [|apply Forall_nil].
    rewrite EB. split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [clear -C1 T1; lia|]. split; [clear -C1 T1 T2 TG; lia|].
    split; [repeat apply Forall_cons; try apply Forall_nil; clear; lia|].
    split.
    { intros off Hoff. pose proof (L2' (T + 208 + 80 * c + off) ltac:(unfold ZI, T; clear -Hoff C1; lia)) as D.
      destruct (view segs (rm r) (T + 208 + 80 * c + off)) as [b|] eqn:Eb; [|contradiction]. rewrite view_in in Eb by (clear -Hoff C1 T1 T2 TG; lia).
      eapply wok_rd_off_image2; [| |exact Eb]; [clear -Hoff C1 T1 T2 TG; lia | clear -Hoff C1 TI; lia]. }
    split; [|unfold xwords_clear; rewrite XX_k2; intros rr y j []].
    apply Forall_cons; [|apply Forall_nil]. intros j Hj. cbn [eval]. specialize (K1 j Hj). cbn [c_addr c_w RtCells.c_val] in K1.
    rewrite view_in in K1 by (clear -Hj C1 T1 T2 TG; lia). replace (T + 208 + 80 * c + 0 + Z.of_nat j) with (T + 208 + 80 * c + Z.of_nat j) by (clear; lia). exact K1.
  - cbn [map carve_obj NU2]. unfold carved. apply Forall_cons; [|apply Forall_nil]. rewrite obj_range_mk by (clear; lia). rewrite EB.
    rewrite EO. apply Forall_app. split.
    + apply BZ. left. fold T. clear -C1. lia.
    + apply Forall_cons; [|apply Forall_nil]. rewrite RNs. unfold ranges_disjoint; cbn [fst snd]. clear -C1. lia.
  - cbn [map carve_obj NU2 pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Theorem uninit_chain : ltac2:(tb__ "0|1|
S2S13S3cQ40A1A1S33S2S45VCST;VXGL;VA;S48VA;A1M0SaVrb;A1SaR1A1A6VTR;S23S1eS3fVW;Vst;G0VKc;S4dVrho;R2A2A5S2eVL2;A1R2R4A5R3A2F_;Fr';VTR;S23S1eS29VA;VKc;Vrb;Vtp0;Vmd0;S1aA6S26VE3;A1R4R3A5R2A2F_;FQ;Ftp;Fr;").
Proof.
  intros r tp Q HC.
  apply (ju_run F [0x411c4] (cU0 E3) [LU1] false r tp Q R_u1 LN_u1 NX_u1). intros L r1 [<-|[]] _. fold L1.

  destruct (perm_okb_sound _ _ PERM1) as (ND1 & LT1 & CV1).
  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (sU1 L1) r1 tp)).
  { intros w Hw. exact (SPA_select segs (JUp false) r1 L1 (idx1 L1) tp w Hw ND1 LT1 CV1). }
  apply (tr_cut Kc TR KIT valuation _ (fun r2 => SPA segs (JUp false) (kU1 L1) r2 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r1 [O_pcc0; O_pcmZ] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp false) r1 (sU1 L1) _ [O_pcc0; O_pcmZ] tp tr ms md OB_s1 Hw).
    intros Hsm HJ. exact (u_release1 A Kc rb tp0 md0 W st rho HE Hini _ _ r1 tp tr (vms md tp ms) (vmd md) md OB_s1 Hsm HJ). }
  intros r2.

  apply (tr_pre Kc TR KIT (SPA segs (JUp false) (cU1 L1) r2 tp)); [intros w Hw; exact (u_carve_arr r2 tp w Hw)|].
  apply (ju_run F [0x41260] (cU1 L1) [LU2] false r2 tp Q R_u2 LN_u2 NX_u2). intros L r3 [<-|[]] _. fold L2.
  apply (tr_cut Kc TR KIT valuation _ (fun r4 => SPA segs (JUp true) (kU2 L2) r4 tp) Q).
  { intros [tr [ms md]] Hw. exists (rho_absorb r3 [O_arrF cellsF] (vms md tp ms)).
    apply (SPA_unobj_J (JUp false) (JUp true) r3 L2 _ [O_arrF cellsF] tp tr ms md OB_u2 Hw).
    intros Hsm HJ. exact (u_release2 A Kc rb tp0 md0 W st rho HE _ _ cellsF r3 tp tr (vms md tp ms) (vmd md) md OB_u2 ARR_ok Hsm HJ). }
  intros r4.

  apply (tr_pure Kc TR KIT (mem_keptA CST XGL A (initA A) (rm rb) (rm r4))).
  { intros w [_ HJ]. exact (proj2 (u_rebuild CST XGL HCST HXGL A Kc rb tp0 md0 W st rho HE Hini r4 tp _ _ HJ)). }
  intros HMK.
  apply (tr_pre Kc TR KIT (SPA segs (JG W st (initA A) Kc (rho_after rho r4)) (eU L2) r4 tp)); [|exact (HC r4 HMK)].
  intros w Hw. destruct (perm_okb_sound _ _ PERM2) as (ND2 & LT2 & CV2).
  apply (SPA_J (JUp true) (JG W st (initA A) Kc (rho_after rho r4)) (eU L2) r4 tp w).
  { intros HJ. exact (JG_init CST XGL HCST HXGL A Kc rb tp0 md0 W st rho HW HE Hini r4 tp _ _ HJ). }
  exact (SPA_select segs (JUp true) r4 (cU2 L2) (idx2 (cU2 L2)) tp w (u_carve_cnt r4 tp w Hw) ND2 LT2 CV2).
Qed.
End UCHAIN.

Section UTOP.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Variable PFam : ltac2:(tb__ "0|0|
S46S43S13S18S11S42A2A1F_;F_;").
Hypothesis HPF : ltac2:(tb__ "0|0|
S4cVCST;VXGL;VPFam;A3").
Variable nW : nat. Variable st : ustop.
Let W : list Iface.ulink := Wcan nW.
Variable F : nat.
Variable E3 : axst.
Variables LU1 LU2 : leafA.
Variable cellsF : list cell.
Let L1 : axst := la_state LU1.
Let L2 : axst := la_state LU2.
Hypothesis SK3 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdVE3;A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S36S16S0S35S15S0A1A3A3A3A4A3").
Hypothesis XX3 : ax_X E3 = [].
Hypothesis XF3 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdVE3;A1A1A3").
Hypothesis WU0 : ltac2:(tb__ "0|0|
ScS14S8SdS26VE3;A1A1A1S17A3").
Hypothesis R_u1 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z411c4S15S21A1A3S26VE3;A1S17A5S1bG0S16SeVLU1;S15SeA1A3A2A3").
Hypothesis LN_u1 : ltac2:(tb__ "0|0|
ScS14S7SdS26VE3;A1A1A1S1aA3").
Hypothesis NX_u1 : ltac2:(tb__ "0|0|
ScS14S3bPdcS4SdS26VE3;A1A1A1A2S17A3").
Hypothesis PERM1 : ltac2:(tb__ "0|0|
ScS14S2bS32VL1;A1S2fVL1;A1A2S17A3").
Hypothesis OB_s1 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdS31VL1;A1A1A1M0S19S0S20S0S3eS32VL1;A1U2A2G0A3S16S0S36S16S0S2dS15S0A1A3A3A3A3").
Hypothesis SK_k1 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS27VL1;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S15S0A1A3A3A4A3").
Hypothesis XF_k1 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS27VL1;A1A1A1A3").
Hypothesis XX_k1 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S27VL1;A1A1S15G0A1A3").
Hypothesis W_c1 : ltac2:(tb__ "0|0|
ScS14S8SdS25VL1;A1A1A1S17A3").
Hypothesis R_u2 : ltac2:(tb__ "0|1|
ScS1cS13SeA1M0A1SfS1eVF;S16S21Z41260S15S21A1A3S25VL1;A1S17A5S1bG0S16SeVLU2;S15SeA1A3A2A3").
Hypothesis LN_u2 : ltac2:(tb__ "0|0|
ScS14S7SdS25VL1;A1A1A1S1aA3").
Hypothesis NX_u2 : ltac2:(tb__ "0|0|
ScS14S3bPdcS4SdS25VL1;A1A1A1A2S17A3").
Hypothesis OB_u2 : ltac2:(tb__ "0|1|
ScS13S0A1S3SdVL2;A1A1M0S19S0S20S0S3eS32VL2;A1U1A2G0A3S16S0S2cVcellsF;A1S15S0A1A3A3A3").
Hypothesis ARR_ok : arr_okb cellsF = true.
Hypothesis SK_k2 : ltac2:(tb__ "0|1|
ScS13S18S18S1S1A2S1A2M0A1S1fS0G0S24S3SdS28VL2;A1A1A1A4S1fS0G0S24S19S0S38VW;A1S16S0S35S15S0A1A3A3A4A3").
Hypothesis XF_k2 : ltac2:(tb__ "0|0|
S39S5S37VW;Vst;A2S6SdS28VL2;A1A1A1A3").
Hypothesis XX_k2 : ltac2:(tb__ "0|1|
ScS13S18S1S1A2M0A1S10S28VL2;A1A1S15G0A1A3").
Hypothesis W_c2 : ltac2:(tb__ "0|0|
ScS14S8SdS2aVL2;A1A1A1S17A3").
Hypothesis PERM2 : ltac2:(tb__ "0|1|
ScS14S2bS32S2aVL2;A1M0A1S30G0A1A2S17A3").

Theorem refill_uninit : ltac2:(tb__ "0|3|
S46S43S2S13S3cQ40M0A1M1A1S33S33OF_;F_;S4bR4R1A2S44R5A1S4aVW;Vst;A2ScS14S47R8A1S1aA3ScS21S4eR9S3dG0S9R7PcA2A2A2Z0A3S41S1eS40R8R7VPFam;RaR9A2A5S33S2S2ScS22G1F_;S9R2A1S9RbA1A3RaS23S1eS3fVW;Vst;S48ReA1M2RdR3A5S2eVL2;A1R2RbA5S41S1eS40R3RbVPFam;G2RdA2A5A2F_;FrX;Frho1;S2R9S23S1eS3fVW;Vst;RdRcRbA5VE3;R1RaA5R3A2FrhoE;F_;TQ;F_;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp TR KIT HKc HW Hini Hcnt Q HCONT rhoE.
  apply (tr_cutP Kc TR KIT Model _ (fun md0 => entryR A rhoE tp md0 W st rho) (fun md0 => SPA segs (JU A Kc rhoE tp md0 false) (cU0 E3) rhoE tp) Q).
  { intros w Hw. exists (cfg_model (w_cfg w)). exact (uninit_entry nW st E3 SK3 XX3 XF3 WU0 A Kc rho rhoE tp w HW Hini Hcnt Hw). }
  intros md0 HE.
  refine (uninit_chain CST XGL HCST HXGL A Kc rhoE tp md0 TR KIT HKc W st rho HW HE Hini F E3 LU1 LU2 cellsF
            R_u1 LN_u1 NX_u1 PERM1 OB_s1 SK_k1 XF_k1 XX_k1 W_c1 R_u2 LN_u2 NX_u2 OB_u2 ARR_ok SK_k2 XF_k2 XX_k2 W_c2 PERM2 rhoE tp Q _).
  intros r' HMK.
  assert (Erm : rm rhoE = rm rho).
  { destruct HE as ((_ & _ & Hm) & _). apply functional_extensionality. intros a. rewrite <- (Hm a). unfold rhoM_of. rewrite rm_rho_sets. reflexivity. }
  rewrite Erm in HMK.
  apply (tr_post Kc TR KIT _ _ _ (fun w Hw => posts_init CST XGL A Kc rho PFam HPF r' tp w HMK Hw)).
  exact (HCONT (rho_after rho r') r' eq_refl).
Qed.
End UTOP.
End SpineCallocU2.

(* [comment removed for export] *)
Module SpineMallocQi.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "Some"; "option"; "pair"; "app"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_objs"; "SAlu"; "SLit"; "ss_facts"; "ss_lenient"; "SVar"; "rw"; "swf"; "SPBranch"; "valuation"; "SPNot"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocQi"; "e3r"; "icc"; "r_9N_0"; "ct0N"; "FUEL"; "r_1_0"; "r_2_1"; "W0"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "s_fN"; "y4N"; "y3N"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cE1"; "GR"; "cR1"; "PV4"; "cE2"; "cT1"; "nobj"; "PV6"; "vK"; "O_pccK"; "O_pcm"; "k_e"; "keepn"; "O_ri"; "PNX"; "cR0a"; "fa_e"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "factsQ"; "cQ0"; "entryRq"; "BASEFq"; "BASEOq"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "ulink"; "KcA"; "Kc_ok"; "UStopLeOrPc"; "pre_facts"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4"; "swM"; "O_rif"; "idx_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS"; "L_rf"; "JLRf"; "JRf"; "NXR"; "NXRC"; "Pre_rf"; "rf_depth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3"; "O_dstc"; "O_srcc"; "e_end"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "nodupN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "LIMIT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG"; "BASEG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR"; "TRokD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA";
"aa_cache_inited"; "budget_bound"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.Arith.PeanoNat.Nat"; "leb"; "@Stdlib.Lists.List"; "forallb"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ DrainTR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.DrainTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := [].
Definition FUEL : nat := 4000%nat.
Definition e3r := Eval vm_compute in (Pre_rf).
Lemma E3r_eq : Pre_rf = e3r.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S5S6S6SdSdA2SdA2M0A1S5fScG0S5bS10S1cS24A1A1A4S5fScG0S5bSaScS8cS1ScS77S1ScS78S4ScA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S24A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S3S5aS67S85A1S13S1cS24A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S3S5cSfS1cS24A1A1PdcA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S3S17S1cS48S24A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S3S96SeS1bS3aA1S52S24A1A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z412e8S4S23A1A3S53S24A1S2A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cQ0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsQ e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41570; 0x413cc] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z412e8S4S23A1A3S53S24A1S2A5S7G0S1S1eS29S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S3S14S1cS53S24A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS53S24A1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S3S17S1cS3bS52S24A1S1dS29A1A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0S8S6S5S6SdSdA2M0A1M1S5SeA1M2A2M3A1S73S1cS1dS29A1M4A1S1cS3bS52S24A1G4A2A1A2S7G3S9G1G2S1G0S9SdSdS4aS51A4S1G0S9SdSdS44S41A4S1G0S9SdSdS49S4dA4S4G0A1A3A3A3S4SeA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S3S5dSfS1cS3bS52S24A1S1dS29A1M0A2A1A1SfS1cG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z41570S1S23Z413ccS4S23A1A3A3S3bS52S24A1S1dS29A1A2S2A5S7G0S1S1eS33S1S1eS2aS4S1eA1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S3S14S1cS3bS52S24A1S1dS29A1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS3bS52S24A1S1dS29A1A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z413dcS1S23Z413f0S4S23A1A3A3S1dS2aA1S2A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z413dcS1S23Z413f0S4S23A1A3A3S3eS27A1S2A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S5S6S6SdSdA2SdA2M0A1S5fScG0S5bS10S1cS27A1A1A4S5fScG0S5bSaScS56S2bA1S1ScS77S1ScS78S1ScS43S1ScS46S4ScA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S27A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S3S5aS55S2bS62A2S13S1cS27A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S3S5dSfS1cS27A1A1S47A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S3S17S1cS3eS27A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z413dcS1S23Z413f0S4S23A1A3A3S3eS27A1S2A5S7G0S1S1eS2cS1S1eS31S4S1eA1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S3S14S1cS3eS27A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S5ScA1S10S1cS1dS2cA1A1A1M0SaScS5eScS30G0A3S1ScS87S1ScS86S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S5ScA1S10S1cS1dS31A1A1A1M0SaScS5eScS30G0A3S1ScS87S1ScS86S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S3S22S45S1dS2cA1S30A2S27S2dA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S3S61S2dS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SdS60S2dS3cA2S11S57S15S3cA1S12Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SdS60S2dS40A2S11S57S15S40A1S12Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS18S58S11S57S15S3cA1S12Z4A1A3S88A3S4SeA1A3S13S1cS1dS2cA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS1aS18S58S11S57S15S3cA1S12Z4A1A3S88A3A1S4SeA1A3S13S1cS1dS31A1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z413dcS1S23Z413f0S4S23A1A3A3S1dS2aA1S2A5S7G0S1S1eS34S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S3S14S1cS1dS2aA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS1dS2aA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S3S22S1dS34A1S27S2eA3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S3S61S2eS3aA2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SdS60S2eS3cA2S11S57S79S12Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SdS60S2eS40A2S93A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S1fS38S28S1S23Z411c0S4S23A1A3S2fS2A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition y3N := Eval vm_compute in (swM (cE2 (cE1 (la_state r_9N_0) icc))).
Definition y4N := Eval vm_compute in (keepn y3N (nobj y3N - 1)).
Definition s_fN := Eval vm_compute in (infer_sub NXRC (ax_S y4N) (ax_S L_rf)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0S8S5S1eA1M0A1S1fS38S28S1S23Z411c0S4S23A1A3S2fS2A5S7G0S1S1eS26S4S1eA1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S3S14S1cS2fA1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S3S5cS3aSfS1cS2fA1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_y1N : ltac2:(tb__ "0|0|
S0S3S17S1cS39S1dS26A1S25A2A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_y1N : ltac2:(tb__ "0|5|
S0S8S6S5S6SdSdA2M0A1M1S5SeA1M2A2M3A1S73S1cS1dS26A1M4A1S1cS39G4S25A2A1A2S7G3S9G1G2S1G0S9SdSdS44S41A4S4G0A1A3S4SeA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_y1N : ltac2:(tb__ "0|1|
S0S3S5dSfS1cS39S1dS26A1M0S25A2A1A1SfS1cG0A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_y1N : ltac2:(tb__ "0|1|
S0S5S6SdSdA2M0A1S21S39S1dS26A1S25A2A1S4G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_y1N : ltac2:(tb__ "0|0|
S0S8ScA1S97ScS10S1cS39S1dS26A1S25A2A1A1S25A3S7ScS42A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y1N : ltac2:(tb__ "0|2|
S0S5ScA1S10S1cS39S1dS26A1S25A2M0A1A1M1SaScS5eScS6cS3fG0A1U2A2G1A3S1ScS43S1ScS71S32A1S4ScA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_y1N : ltac2:(tb__ "0|0|
S0S3S4bS32S92S4eS4cS4fA5S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ND_y3N : ltac2:(tb__ "0|0|
S0S3S8aS72S3dS39S1dS26A1S25A2A1A1A1S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NO_y3N : ltac2:(tb__ "0|0|
S0S3S95U2S3fS3dS39S1dS26A1S25A2A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma Y3_eqN : ltac2:(tb__ "0|0|
S0S20S70S3dS39S1dS26A1S25A2A1A1S37A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma Y4_eqN : ltac2:(tb__ "0|1|
S0S20S45S70S3dS39S1dS26A1S25A2A1A1M0S6cS3fG0A1U1A2A2S36A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_y3N : ltac2:(tb__ "0|2|
S0S5ScA1S10S1cS70S3dS39S1dS26A1S25A2A1A1M0A1A1M1SaScS5eScS6cS3fG0A1U1A2G1A3S1ScS42S4ScA1A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_fN : ltac2:(tb__ "0|0|
S0S3S22S36S7fS35A3S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_fN : ltac2:(tb__ "0|0|
S0S3S61S35S83A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma HW0 : ltac2:(tb__ "0|0|
S0S68S62S66A3S0S5S63A1S2bS4S63A1A3F_;"). Proof. intros E; discriminate E. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv :=
  exit_stepsQ A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv FUEL xlN icc LN_9N NX_9N r_9N_0 cellsfN
    R_9N W_y1N D_y1N NX_y1N XX_y1N IC_y1N OB_y1N RI_y1N ND_y3N NO_y3N OB_y3N.
Definition fin_N A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq HREB HZD HPOST :=
  fin_leaf A Kc rb tp0 md0 W0 UStopLe rho HE HKc phF HREB HZD TR KIT y4N s_fN ENT_fN SID_fN rhoQ tpQ JLq HPOST.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S3S5aS1SeS1aS18S59S50S41A3A1S4SeA1A3S13S1cS1dS2aA1A1A1A2S2A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|4|
S8fS64S23S23S19S5S6bQ40M0A1A1M1S6fS6fOF_;F_;S8dR6R1A2S65R7A1S89S91R9A1S8bA2S0S3S90RaA1S2A3S76S38S82R7R6S1S6S20S75A2M2S9S20S75S7fS80RbRaR9A3A4S4G2A1A3A5S6fS6dS54RdR9R8R1S2bS62R9A7S89S7dS69S6aG0S16RaPcM3A2A2A1A1S7bReRaA2A2S19G1S5S6eA1S6dS7aR13R12RfReR7S94S7dS69S6aG0S16RfG3A2A2A1A1A1R4R3R2R1AaS8eS7eR14S69S6aG0S16R10G3A2A2A1A2R5R4R2A4F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;S6dS19S0S23RdS69S6aG0S16RbG3A2A2A1A3S54R10RcRbR3S2bS62RcA7RbS74S38S7aR11R10RdRcR4S7cA6S1dS33A1R3RcA5R6A2F_;F_;Fr';Fmd0;R8S74S38S81ReRdRcRbA4S84RaR9A5R3A2F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;Fnv0;Fc0;FKc;FA;").
Proof.
  rewrite E3r_eq.
  apply (refill_N W0 UStopLe e3r (la_state r_2_0) (la_state r_2_1) xlN y4N (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc c0 nv0 rhoE tp w HBUD Hini Hw. exact (entry_i A Kc c0 nv0 rhoE tp w HBUD Hini Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq. exact (fin_N A Kc rb tp0 md0 TR KIT HKc rho HE phF rhoQ tpQ JLq).
Qed.
End SpineMallocQi.

(* [comment removed for export] *)
Module CRebuildRQ.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "false"; "length"; "nat"; "@Corelib.Init.Logic"; "eq"; "and"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rm"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.CRebuildRQ"; "phQ"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ"; "gh_new"; "phase"; "JR"; "entryR"; "mkPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15"; "phFin"; "phU3"; "phUF3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "mem_keptA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "class_state"; "cs_free_array"; "cs_mapped_free_array"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7"; "popfacts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cst_of"; "@Stdlib.ZArith.BinInt.Z"; "add"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ai.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require am.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM RefillModel RefillModelP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ac.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR CRefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ai.SpineCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.am.SpineCallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModelP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ac.CertCallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CRefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.CRefillJP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SpineCallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineCallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SpineCallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineCallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SpineCallocR7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bk.SpineCallocR9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineCallocR12 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineCallocR13 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineCallocR14 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineCallocR15 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.CRebuildRM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.CallocBase.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Definition phQ (b : bool) (new k : Z) : phase := ltac2:(tb__ "0|1|
S14U3M0S1S6Lb;Vb;G0U0X1x2Vnew;Vk;S2S2A6").
Lemma phQ_P : ltac2:(tb__ "0|0|
S0S0S7S11S15S16R2R1A3SdS4R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.
Lemma phQ_M : ltac2:(tb__ "0|0|
S0S0S7S11S15S17R2R1A3SdS2R2R1A3A3Fk;Fnew;"). Proof. reflexivity. Qed.

Section RQ.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.

Theorem refill_rebuild_Q : ltac2:(tb__ "0|3|
S1eS19SaS3S2cQ40M0A1A1M1SeS3S1bA1S1cSaS13R8R6R5R4R3R2R1A7S25R9R7A2S1S7S1S1fRbA1S2A3S2dG0ScRaPcA2A2S0S26R1A1S0S27ReR2A2S20S9S7S1R5S2A3S29S22R1A1S2aZ4S28S2bS5S0S21R1A1A2A1S10RfRdA2A2A2A2A2SaG1S3SfA1SeS12R14R13R12R11R10SdRaS10R14R12A2S23R7A1A3R4R3R2R1AaS8S1dS18S24R15R8A2M2R5R4R2A5S1aVCST;VXGL;R15G2SbR13A1SbR5A1A6A2F_;Fmd;Ftr;Ftp;Fr;F_;Tcs;Tc;Tnv;F_;Fb;FPF;FHE;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE PF b Hini nv c cs HB r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  destruct (pop_geo A rb tp0 md0 W st rho HE PF) as (C1 & S1 & AU0 & MU1 & N4 & K1 & KN & NF0 & MF1 & MF2 & MF0 & G13 & G14 & FAr & T1 & PS1 & TB).
  fold nv c cs in C1, S1, AU0, MU1, N4, K1, KN, NF0, MF1, MF2, MF0, FAr.
  destruct (entry_pure A rb tp0 md0 W st rho HE PF) as (HP & Hc0 & NP & RM). fold nv c cs in HP, Hc0, NP, RM.
  pose proof (P_csR A rb tp0 md0 W st rho HE PF) as (X1 & X2 & X3 & X5 & X6 & X7 & LP' & HIDS). cbn zeta in X1, X2, X3, X5, X6, X7, LP', HIDS. fold nv c cs in X1, X2, X3, X5, X6, X7, LP', HIDS.
  pose proof (P_fields c cs _ C1 HP NP RM) as PFL. cbn zeta in PFL. destruct PFL as (_ & _ & _ & XFA & _). pose proof (P_newZ A rb) as ENZ. fold nv c cs in ENZ. pose proof (P_faP_len c cs _ C1 HP RM) as LPz. rewrite ENZ in LPz. rewrite LPz in XFA.
  destruct (refill_pure c cs _ C1 HP Hc0 ltac:(intros _; exact RM)) as (HPR & _). cbn zeta in HPR.
  pose proof (pop_credit_eq A rb tp0 md0 W st rho HE PF) as CEQ. fold nv c cs in CEQ.
  set (k := kchunks c) in *. set (new := gh_new A rb) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  set (mu := cs_mapped_user cs) in *. set (mfa := cs_mapped_free_array cs) in *. set (au := cs_allocated_user cs) in *. set (fP := faP c cs) in *.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Eb : (mfa <? 4 * (nf + new)) = b).
  { destruct b; [apply Z.ltb_lt; apply (proj1 HB); reflexivity | apply Z.ltb_ge; destruct (Z_lt_dec mfa (4 * (nf + new))) as [X|X]; [discriminate (proj2 HB X) | clear -X; lia]]. }
  rewrite Eb in X7, CEQ.
  pose proof HE as (_ & HA & _ & _ & _ & Hnv & _ & _ & HWF). fold nv in Hnv.
  pose proof HA as (HG & _ & _ & HRest0 & HMI0 & HI3 & HB0). destruct HRest0 as (_ & _ & (PL & _) & _).

  assert (EU0 : U0 A rb = SB + c * 4294967296 + mu) by (unfold U0, region_beg, kRegionSize; fold nv c cs; fold G SB mu; clear; lia).
  assert (EF0 : F0 A rb = SB + c * 4294967296 + 3758096384 + mfa) by (unfold F0, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; fold nv c cs; fold G SB mfa; clear; lia).
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  assert (G12 : SB mod 65536 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. destruct CF as (_ & _ & _ & _ & _ & (X & _) & _). exact X. }
  assert (MU18 : mu mod 262144 = 0).
  { pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c cs in CF. destruct CF as (_ & _ & (X & _) & _). exact X. }
  assert (UM : U0 A rb mod 65536 = 0).
  { rewrite EU0. destruct (proj1 (Z.mod_divide mu 262144 ltac:(clear; lia)) MU18) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + q * 262144) with ((q2 + c * 65536 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  assert (FM : F0 A rb mod 65536 = 0).
  { rewrite EF0. destruct (proj1 (Z.mod_divide mfa 262144 ltac:(clear; lia)) MF0) as [q Hq]. destruct (proj1 (Z.mod_divide SB 65536 ltac:(clear; lia)) G12) as [q2 Hq2].
    rewrite Hq, Hq2. replace (q2 * 65536 + c * 4294967296 + 3758096384 + q * 262144) with ((q2 + c * 65536 + 57344 + q * 4) * 65536) by (clear; lia). apply Z_mod_mult. }
  destruct (sh_run_nums SB (U0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EU0; clear -C1 AU0; lia) ltac:(rewrite EU0; clear -C1 MU1; lia) G14 UM) as (QU1 & QU2 & QU3 & QU4).
  destruct (sh_run_nums SB (F0 A rb) ltac:(clear -G13; lia) ltac:(rewrite EF0; clear -C1 NF0 MF1; lia) ltac:(rewrite EF0; clear -C1 MF2; lia) G14 FM) as (QF1 & QF2 & QF3 & QF4).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }

  set (ZQ := fun z : Z => (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768) \/ (U0 A rb <= z < U0 A rb + 262144)
                          \/ (b = true /\ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768) \/ (b = true /\ F0 A rb <= z < F0 A rb + 262144)
                          \/ (FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new))
                          \/ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k) \/ (PCE A rb <= z < PCE A rb + 4) \/ (ri <= z < ri + 128)).
  assert (ZI : forall z, zoneR A rb (phQ b new k) z <-> ZQ z).
  { intros z. unfold zoneR, phQ, ZQ, revealedp, releasedp, kUserMapSize, kFreeArrayMapSize. cbn [ph_u ph_f ph_fill ph_pop ph_cnt ph_ri Nat.leb].
    unfold gh_nf. fold nv c cs nf new. fold G SB ri. replace (nf + new - new) with nf by (clear; lia).
    destruct b; cbn [Nat.leb]; split.
    - intros [[_ H]|[[_ H]|[[_ H]|[[_ H]|[[H _]|[H|[[_ H]|[_ H]]]]]]]].
      + left; exact H.
      + right; left; exact H.
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[_ H]|[[_ H]|[H|[H|[H|H]]]]]]].
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; left; split; [reflexivity | exact H].
      + right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H].
    - intros [[_ H]|[[_ H]|[[X _]|[[X _]|[[H _]|[H|[[_ H]|[_ H]]]]]]]]; try discriminate X.
      + left; exact H.
      + right; left; exact H.
      + right; right; right; right; left; exact H.
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; right; exact H.
    - intros [H|[H|[[X _]|[[X _]|[H|[H|[H|H]]]]]]]; try discriminate X.
      + left; split; [reflexivity | exact H].
      + right; left; split; [reflexivity | exact H].
      + right; right; right; right; left; split; [exact H | clear -N4; lia].
      + right; right; right; right; right; left; exact H.
      + right; right; right; right; right; right; left; split; [reflexivity | exact H].
      + right; right; right; right; right; right; right; split; [reflexivity | exact H]. }
  assert (ZD : forall z, zoneR A rb (phQ b new k) z \/ ~ zoneR A rb (phQ b new k) z).
  { intros z. assert (D : ZQ z \/ ~ ZQ z).
    { unfold ZQ. destruct b.
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144 \/ Sh (F0 A rb) <= z < Sh (F0 A rb) + 32768 \/ F0 A rb <= z < F0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left | right]; [clear -D'; tauto | intros X; apply D'; clear -X; tauto].
      - assert (D' : (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                       \/ ~ (Sh (U0 A rb) <= z < Sh (U0 A rb) + 32768 \/ U0 A rb <= z < U0 A rb + 262144
                        \/ FAb A rb + 4 * nf <= z < FAb A rb + 4 * (nf + new) \/ PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
        destruct D' as [D'|D']; [left; clear -D'; tauto|]. right. intros X. apply D'. clear -X. destruct X as [X|[X|[[E _]|[[E _]|X]]]]; try discriminate E; tauto. }
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros X; apply D; apply ZI; exact X]. }
  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.

  unfold mlink in HM. cbn zeta in HM. unfold phQ in HM. cbn [ph_u ph_f] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & M9 & M10).
  assert (ECF : committed (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  assert (ERF : revealedp (if b then 3%nat else 0%nat) = b) by (destruct b; reflexivity).
  rewrite ECF in M5, M6, M10. rewrite ERF in M8, M9, M10. change (committed 3) with true in M5, M6, M10. change (revealedp 3) with true in M8, M9, M10.
  apply (refill_rebuild CST XGL HCST HXGL A rb r tp0 tp md0 md nv (zoneR A rb (phQ b new k)) HA Hnv Hini); fold c cs; fold G; fold SB T; fold nf mu.
  - exact HPR.
  - rewrite X5. fold au. clear -N4 S1. nia.
  - rewrite X6. clear; lia.
  - rewrite X7. fold mfa. destruct b; clear; lia.
  - rewrite X2. destruct (kchunks_facts c C1) as (_ & K2 & _). fold k in K2. clear -K1 K2. lia.
  - exact ZD.
  -
    intros z HZ. apply ZI in HZ. unfold envR. unfold ZQ in HZ. rewrite EU0, EF0, FAr, PCr in HZ. rewrite EU0 in QU3, QU4. rewrite EF0 in QF3, QF4.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu) (SB + c * 4294967296 + 3758096384 + mfa) ltac:(clear -MU1 NF0 MF1; lia)) as SM1.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + mu + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MU1; lia)) as SM2.
    pose proof (Geometry.Sh_mono (SB + c * 4294967296 + 3758096384 + mfa + 262144) (SB + c * 2 ^ 32 + 2 ^ 32) ltac:(clear -MF2; lia)) as SM3.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) by (clear; lia).
    destruct HZ as [X|[X|[[_ X]|[[_ X]|[X|[X|[X|X]]]]]]].
    + right; right; right; right; right. clear -X QU4 SM2. lia.
    + right; right; right; right; left. clear -X MU1. lia.
    + right; right; right; right; right. clear -X QF4 SM1 SM3. lia.
    + right; right; right; left. clear -X MF1 MF2. lia.
    + right; right; right; left. clear -X N4 MF1 MF2. lia.
    + right; right; left. clear -X K1. lia.
    + right; left. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b0, m z = Some b0). destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    rewrite XFA. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -LP' KN NF0 K1; lia).
    rewrite nth_error_firstn in Hi. replace (i <? Z.to_nat (nf + new - k))%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (P_HSRC A rb tp0 md0 W st rho HE PF (phQ b new k) m eq_refl ltac:(cbn [ph_pop phQ]; clear -K1; lia) (conj L1 (conj L2 (conj L3 (conj L4 (conj L5 L6))))) (Z.of_nat i)
                  ltac:(fold nv c cs fP; rewrite LP'; clear -Li KN NF0 K1; lia)) as CE.
    fold nv c cs fP in CE. rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity). exact CE.
  - rewrite X2. replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  - intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite <- (Nat2Z.id (length (cs_cache (refill_cs c cs)))) in Li. rewrite X2 in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phQ] in CE. specialize (CE ltac:(clear -Li K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - rewrite X6. intros z Hz. apply ZI. right; left. rewrite EU0. unfold region_beg, kRegionSize in Hz. clear -Hz. lia.
  - rewrite X6. intros z Hz. apply ZI. left. rewrite EU0 in QU4 |- *. unfold region_beg, kRegionSize in Hz.
    replace (SB + c * 2 ^ 32 + mu) with (SB + c * 4294967296 + mu) in Hz by (clear; lia).
    replace (SB + c * 2 ^ 32 + (mu + 262144)) with (SB + c * 4294967296 + mu + 262144) in Hz by (clear; lia). clear -Hz QU4. lia.
  - rewrite X7. fold mfa. intros z Hz. destruct b; [|exfalso; clear -Hz; lia]. apply ZI. right; right; right; left. split; [reflexivity|].
    rewrite EF0. unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize in Hz. clear -Hz. lia.
  -
    change (subF A rb b (subU A rb true (vm_noaccess (m_vmmaps md0))))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (vm_noaccess (m_vmmaps md0))) in M5.
    change (subF A rb b (subU A rb true (m_vm_lazy md0)))
      with (sub2 true (U0 A rb) (U0 A rb + kUserMapSize) b (F0 A rb) (F0 A rb + kFreeArrayMapSize) (m_vm_lazy md0)) in M6.
    rewrite M7.
    apply (model_inv_sub2 A (refillA A c) tp0 tp1 md0 md true b (U0 A rb) (U0 A rb + kUserMapSize) (F0 A rb) (F0 A rb + kFreeArrayMapSize)); try reflexivity; try assumption.
    + unfold kUserMapSize. clear; lia.
    + unfold kFreeArrayMapSize. clear; lia.
    + fold G SB. rewrite EU0. clear -C1 AU0. lia.
    + fold G SB. rewrite EU0, kSpaceSize_val. unfold kUserMapSize. clear -C1 MU1. lia.
    + fold G SB. rewrite EF0. clear -C1 NF0 MF1. lia.
    + fold G SB. rewrite EF0, kSpaceSize_val. unfold kFreeArrayMapSize. clear -C1 MF2. lia.
    + fold G SB. unfold HIGH_SHADOW_END. clear -G13. lia.
    + intros p Hp. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[_ (j & Hj & Ej)]]]; rewrite Ej; unfold band_page; right; unfold HIGH_SHADOW_BEG, HIGH_SHADOW_END, PG.
      * clear -Hj QU2 QU3. lia.
      * clear -Hj QF2 QF3. lia.
    +
      destruct HMI0 as (_ & PB0 & _). rewrite <- M7. unfold kUserMapSize, kFreeArrayMapSize in M10.
      destruct b; clear -PB0 M10 CEQ; lia.
  -
    rewrite M7. apply (bandtp_grow m tp0).
    + eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. destruct (ZD z) as [ZIz|ZOz]; [exact (L2 z ZIz) | rewrite (L1 z ZOz); exact Hd].
    + intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [|left; exact Hp]. right. intros _ z Hz.
      assert (ZIz : zoneR A rb (phQ b new k) z).
      { apply ZI. destruct (M8 p Hp) as [_ [[_ (j & Hj & Ej)]|[Eb' (j & Hj & Ej)]]]; rewrite Ej in Hz; unfold PG in Hz.
        - left. clear -Hz Hj. lia.
        - right; right; left. split; [exact Eb' | clear -Hz Hj; lia]. }
      pose proof (L2 z ZIz) as D. destruct (m z) as [b0|]; [exists b0; reflexivity | contradiction].
Qed.
End RQ.
End CRebuildRQ.

(* [comment removed for export] *)
Module RebuildQN.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC"; "AInvQC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "gh_nf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1"; "entryRq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt StepA SoundA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require PrimCredit PrimCreditLaws Inv SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require av.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bm.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildRZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.PrimCreditLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.InvQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.av.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b1.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.SpineMallocQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b6.SpineMallocQ2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.SpineMallocQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bm.SpineMallocQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bn.SpineMallocQ5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bq.SpineMallocQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildRZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.RebuildRP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b2.RebuildR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b4.RebuildG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildGC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b5.RebuildD.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bz.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require c3.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree.segsA.

Section RN.
Theorem refill_rebuild_N : ltac2:(tb__ "0|2|
SfSbS3S0S17Q40M0A1A1M1S6S0ScA1SdS3S14R8R6R5R4R3R2R1A7SaS1S10R9A1S2A3S18G0S4R8PcA2A2S5S13R1A1S5S16S8R1A1S12RcRaA2A2S3G1S0S7A1S6S11R11R10RfReRdS15S8R6A1A1R4R3R2R1AaSeS9R12R7A2R5R4R2A4F_;Fmd;Ftr;Ftp;Fr;F_;Tc;Tnv;F_;F_;Frho;Fst;FW;Fmd0;Ftp0;Frb;FKc;FA;").
Proof.
  intros A Kc rb tp0 md0 W st rho HE Hini nv c HNP r tp tr md (HFz & HGh & HK & HM & HR & HRM).
  pose proof (entry_cfacts _ _ _ _ _ _ _ HE) as CF. unfold cfacts in CF. cbn zeta in CF. fold nv c in CF.
  destruct CF as ((Hnv & C1 & S1 & S16) & (K1 & K2 & K3) & (MU0 & AU0 & MU1 & AU1 & TI0) & (MF0 & MF1) & (MC0 & FC0 & Hcs0) & (G12 & G13 & G14 & TG) & (T1 & T2 & TI & PS1) & TB).
  pose proof HE as (_ & HA & _).
  set (cs := cst_of A nv) in *. set (k := kchunks c) in *. unfold gh_nf in HNP. fold nv c cs in HNP.
  set (G := aa_geom A) in *. set (SB := ag_spacebeg G) in *. set (T := ag_thread G) in *.
  assert (Hk : (Z.to_nat k <= length (cs_free_array cs))%nat) by (clear -HNP K1; lia).

  pose proof (N_refill_cs A rb HNP) as ECS. fold nv c cs k in ECS.
  pose proof HA as (HG & _ & _ & HRest & HM0 & _ & HB0). destruct HRest as (_ & _ & Hprim & _ & Hq & _). destruct Hprim as (_ & _ & _ & PC).
  pose proof (entry_cls_pureQ _ A c C1 (PC c C1) (proj1 Hq)) as HP0. change (nthZ (aa_cls A) c cs_empty) with cs in HP0.
  destruct (take_pure c cs _ (Z.to_nat k) HP0 Hcs0 Hk) as (HP1 & EFC & LC & LF & EMU & EAU & EMF). cbn zeta in HP1, EFC, LC, LF, EMU, EAU, EMF.

  unfold mlink in HM. cbn zeta in HM. unfold phFN, ph_setri, ph_setcnt, phK, ph0, committed, revealedp, subU, subF in HM. cbn [ph_u ph_f Nat.leb] in HM.
  destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & tp1 & M7 & M8 & _ & M10).
  assert (Etp1 : tp1 = []).
  { destruct tp1 as [|p tp1']; [reflexivity|]. exfalso. destruct (M8 p (or_introl eq_refl)) as [_ [[X _]|[X _]]]; discriminate X. }
  subst tp1. cbn [app length Z.of_nat] in M7, M10. subst tp.

  unfold rlink in HR. destruct HR as (L1 & L2 & L3 & L4 & L5 & L6).
  assert (ZI := zone_FN A rb k). fold nv c in ZI. fold G in ZI. fold SB in ZI.
  assert (PCr : PCE A rb = T + 208 + 80 * c) by (unfold PCE; fold nv c; fold G T; clear; lia).
  set (ri := region_info SB c) in *.
  assert (RIr : SB + 137438953472 + 128 <= ri /\ ri + 128 <= SB + 137438953472 + 4096).
  { unfold ri, region_info, kRegionInfoStride. rewrite kSpaceSize_val. clear -C1. lia. }
  assert (FAr : FAb A rb = SB + c * 4294967296 + 3758096384).
  { unfold FAb, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize. fold nv c. fold G SB. clear; lia. }
  set (m0 := view segs (rm rb)) in *. set (m := view segs (rm r)) in *.
  rewrite refillA_setcls. change (nth (Z.to_nat c) (aa_cls A) cs_empty) with cs.
  eapply proj1. apply (class_rebuildC [] [] OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.cst_ok_nil OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.c3.DrainF.xgl_ok_nil A rb r tp0 tp0 md0 md c (refill_cs c cs) (zoneR A rb (phFN k)) HA C1 Hini); change (nthZ (aa_cls A) c cs_empty) with cs.
  -   fold c cs. rewrite ECS. exact HP1.
  - fold c cs. rewrite ECS. rewrite EAU. clear; lia.
  - fold c cs. rewrite ECS. rewrite EMU. clear; lia.
  - fold c cs. rewrite ECS. rewrite EMF. clear; lia.
  - fold c cs. rewrite ECS. rewrite LC. clear -K1 K2. fold k in K1, K2. lia.
  - intros z.
    assert (D : (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                \/ ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
    destruct D as [D|D]; [left; apply ZI; exact D | right; intros HZ; apply D; apply ZI; exact HZ].
  -
    intros z HZ. apply ZI in HZ. fold c cs. fold G. fold T SB. unfold envR.
    destruct HZ as [X|[X|X]].
    + right; right; left. rewrite PCr in X. clear -X K1. fold k in K1. lia.
    + right; left. rewrite PCr in X. clear -X. lia.
    + left. unfold ri, region_info, kRegionInfoStride in X. rewrite kSpaceSize_val in X. clear -X. lia.
  - intros z Hz. exact (L1 z Hz).
  - intros z Hz. pose proof (L2 z Hz) as D. change (exists b, m z = Some b). destruct (m z) as [b|]; [exists b; reflexivity | contradiction].
  - exact HRM.
  - exact (proj1 (L6 eq_refl)).
  - exact (proj1 (proj2 (L6 eq_refl))).
  - exact (proj1 (proj2 (proj2 (L6 eq_refl)))).
  - exact (proj1 (proj2 (proj2 (proj2 (L6 eq_refl))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl))))))).
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (L6 eq_refl)))))))).
  -
    fold c cs G. fold SB. rewrite ECS. unfold take_cs. cbn [cs_free_array].
    intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite firstn_length_le in Li by (clear -Hk; lia).
    rewrite nth_error_firstn in Hi. replace (i <? length (cs_free_array cs) - Z.to_nat k)%nat with true in Hi by (symmetry; apply Nat.ltb_lt; exact Li).
    pose proof (proj1 (entry_fa _ _ _ _ _ _ _ HE) (Z.of_nat i)) as CE. cbn zeta in CE. fold nv c cs in CE. fold m0 in CE.
    specialize (CE ltac:(clear -Li; lia)). rewrite Nat2Z.id in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (free_array SB c) with (FAb A rb) by (unfold FAb; fold nv c; reflexivity).
    eapply cell_ok_agree_range; [|exact CE]. cbn [c_addr c_w]. intros z Hz. apply L1. intros HZ. apply ZI in HZ.
    change (Z.of_nat 4) with 4 in Hz. rewrite FAr in Hz. rewrite PCr in HZ.
    assert (Li' : Z.of_nat i < 2 ^ 27) by (clear -Li MF1; lia).
    clear -Hz HZ Li' C1 K1 G13 G14 T1 PS1 RIr. fold k in K1. lia.
  -
    fold c cs. rewrite ECS. rewrite LC. rewrite Z2Nat.id by (clear -K1; fold k in K1; lia).
    replace (T + 208 + 80 * c) with (PCE A rb) by (rewrite PCr; reflexivity). exact (L5 eq_refl).
  -
    fold c cs. intros i x Hi. pose proof (nth_error_Some_lt _ _ _ Hi) as Li. rewrite ECS in Li. rewrite LC in Li.
    pose proof (L4 (Z.of_nat i)) as CE. cbn [ph_pop phFN ph_setri ph_setcnt phK] in CE. specialize (CE ltac:(clear -Li K1; fold k in K1; lia)).
    rewrite Nat2Z.id in CE. fold nv c cs in CE. rewrite (nth_error_nth _ _ 0 Hi) in CE.
    replace (T + 208 + 80 * c + 16 + 4 * Z.of_nat i) with (PCE A rb + 16 + 4 * Z.of_nat i) by (rewrite PCr; reflexivity). exact CE.
  - fold c cs. rewrite ECS, EMU. intros z Hz. exfalso. clear -Hz. lia.
  - fold c cs. rewrite ECS, EMU. intros z Hz. exfalso. clear -Hz. lia.
  - fold c cs. rewrite ECS, EMF. intros z Hz. exfalso. clear -Hz. lia.
  -
    apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bz.RebuildRN.model_inv_fields A (setclsA A c (refill_cs c cs)) tp0 md0 md); try reflexivity; try assumption.
    + apply prim_credit_maps. intros c' Hc'. unfold setclsA. cbn [aa_cls].
      destruct (Z.eq_dec c' c) as [->|Hne].
      * rewrite nth_list_upd_same by (destruct HA as (_ & _ & _ & HRest' & _); destruct HRest' as (_ & _ & (PL & _) & _); rewrite PL; clear -C1; lia).
        change (nth (Z.to_nat c) (aa_cls A) cs_empty) with cs. rewrite ECS. split; [exact EMU | exact EMF].
      * rewrite nth_list_upd_other by (clear -Hne Hc' C1; lia). split; reflexivity.
    + clear -M10. lia.
  -
    eapply bandtp_mono; [|exact HB0]. intros z _ Hd. fold m0 in Hd. fold m.
    assert (D : (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)
                \/ ~ (PCE A rb + 16 <= z < PCE A rb + 16 + 4 * k \/ PCE A rb <= z < PCE A rb + 4 \/ ri <= z < ri + 128)) by (clear; lia).
    destruct D as [D|D]; [apply L2; apply ZI; exact D | rewrite L1 by (intros HZ; apply D; apply ZI; exact HZ); exact Hd].
Qed.
End RN.
End RebuildQN.

(* [comment removed for export] *)
Module SpineMallocRi0u.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "true"; "bool"; "nil"; "list"; "prod"; "app"; "Some"; "option"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "sprop"; "ss_next"; "ss_facts"; "valuation"; "ss_objs"; "ss_lenient"; "swf"; "SAlu"; "SLit"; "SVar"; "rw"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "la_state"; "leafA"; "sym_runA"; "axst"; "ax_X"; "entailsA"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bs.SpineMallocRi0u"; "e3r"; "icc"; "r_9N_0"; "W0"; "FUEL"; "ct0N"; "r_1_0"; "r_2_1"; "r_t1N_0"; "s_bkN"; "s_inN"; "xlN"; "e3p"; "nob"; "r_t1N_1"; "cellsfN"; "r_2_0"; "r_t0N_0"; "r_zN_0"; "s_xN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR"; "cE1"; "cE2"; "GR"; "cR1"; "factsR"; "PV4"; "cR0"; "cT1"; "PV6"; "cE3"; "vK"; "O_pcm"; "cE3b"; "k_e"; "F_r0"; "F_r1"; "F_x"; "O_pccK"; "O_ri"; "PNX"; "cE3a"; "cR0a"; "fa_e"; "keepn"; "nobj"; "ri_e"; "ri_has"; "vAU"; "vFA"; "vMFA"; "vMU"; "vNF"; "vRI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "UStopLe"; "KcA"; "ulink"; "A_globals"; "Kc_ok"; "UStopLeOrPc"; "malloc_depth"; "mem_keptA"; "pre_facts"; "unwind_factsS"; "unwind_objs"; "ustop"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3"; "inclb"; "skel"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_NE"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP"; "O_pcc0"; "O_st"; "E3p"; "F_gen"; "pc_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_cache_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI"; "cls_of"; "cnt_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "LQPA"; "jpostA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ"; "JR"; "entryR"; "gh_nf"; "ph0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel"; "kchunks"; "refillA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2"; "BASEF"; "BASEO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3"; "O_dstc"; "O_srcc"; "e_end"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1"; "JG"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1"; "RT_m1"; "sw_s1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR";
"TRok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4"; "O_rif"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5"; "posts_conv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6"; "e16N"; "e_srcN"; "phFN"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require an.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ao.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RefillTR RefillJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bp.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bw.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cd.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SpineMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.an.SpineMallocS3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ao.SpineMallocS3i OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillTR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RefillJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SpineMallocR1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SpineMallocR2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SpineMallocR3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bp.SpineMallocR4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bw.SpineMallocR5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SpineMallocR6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cd.SpineMallocRu0.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition W0 : list ulink := Wcan 0.
Definition FUEL : nat := 4000%nat.
Definition e3r : axst := e3u.
Lemma SK3 : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS26A1A1A4S68SdG0S6bS8SdS8SdS2SdS96S8SdS66S29A1S5fA3A3S95A3S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX3 : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S26A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF3b : ltac2:(tb__ "0|0|
S0S4S6aS8SfS8SfS65S29S5cA2S64S62A1A3S7cA3S11S1eS26A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX3 : ltac2:(tb__ "0|0|
S0S4S6cS10S1eS26A1A1PdcA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma WR0a : ltac2:(tb__ "0|0|
S0S4S15S1eS50S26A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB0 : ltac2:(tb__ "0|0|
S0S4S92SfS1dS3dA1S8SfS11S1eS26A1A1S8SfS49S4aA3A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition R_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z412e8S5S25A1A3S41S26A1S3A5").
Local Strategy expand [R_1__R].
Definition r_1 := Eval vm_compute in ((fun ro1__ : option (list leafA) => (match ro1__ with Some l => l | None => [] end)) R_1__R).
Definition r_1_0 := Eval vm_compute in (nth 0 r_1 (mkLeafA (cR0 e3r) RsCut)).
Definition cr1 := Eval vm_compute in (cR1 (factsR e3r) (la_state r_1_0)).
Definition r_2 := Eval vm_compute in (match sym_runA segsA FUEL [0x41570; 0x413cc] cr1 true with Some l => l | None => [] end).
Definition r_2_0 := Eval vm_compute in (nth 0 r_2 (mkLeafA cr1 RsCut)).
Definition r_2_1 := Eval vm_compute in (nth 1 r_2 (mkLeafA cr1 RsCut)).
Lemma R_1 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z412e8S5S25A1A3S41S26A1S3A5S9G0S2S20S2cS5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_1__R <: R_1__R = Some [r_1_0]). Qed.
Lemma LN_0 : ltac2:(tb__ "0|0|
S0S4S14S1eS41S26A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_0 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS41S26A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_r1 : ltac2:(tb__ "0|0|
S0S4S15S1eS3eS3fS26A1S1fS2cA1A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_r1 : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S83S1eS1fS2cA1M4A1S1eS3eS3fS26A1G4A2A1A2S9G3ScG1G2S2G0ScSeSeS54S5bA4S2G0ScSeSeS48S45A4S2G0ScSeSeS51S57A4S5G0A1A3A3A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_r1 : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3eS3fS26A1S1fS2cA1M0A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_2 : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z41570S2S25Z413ccS5S25A1A3A3S3eS3fS26A1S1fS2cA1A2S3A5S9G0S2S20S36S2S20S2dS5S20A1A3A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_1 : ltac2:(tb__ "0|0|
S0S4S14S1eS3eS3fS26A1S1fS2cA1A2A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_1 : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS3eS3fS26A1S1fS2cA1A2A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition nob := Eval vm_compute in ((length (ss_objs (ax_S e3r)) + 2)%nat).
Definition icc := Eval vm_compute in ((length (ss_objs (ax_S e3r)) - 2)%nat).
Definition R_t0N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z413dcS2S25Z413f0S5S25A1A3A3S1fS2dA1S3A5").
Local Strategy expand [R_t0N__R].
Definition r_t0N := Eval vm_compute in ((fun ro3__ : option (list leafA) => (match ro3__ with Some l => l | None => [] end)) R_t0N__R).
Definition r_t0N_0 := Eval vm_compute in (nth 0 r_t0N (mkLeafA (la_state r_2_1) RsCut)).
Definition ct0N := Eval vm_compute in (cT0 (la_state r_t0N_0)).
Definition R_t1N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z413dcS2S25Z413f0S5S25A1A3A3S42S2bA1S3A5").
Local Strategy expand [R_t1N__R].
Definition r_t1N := Eval vm_compute in ((fun ro2__ : option (list leafA) => (match ro2__ with Some l => l | None => [] end)) R_t1N__R).
Definition r_t1N_0 := Eval vm_compute in (nth 0 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition r_t1N_1 := Eval vm_compute in (nth 1 r_t1N (mkLeafA (cT1 ct0N) RsCut)).
Definition s_inN := Eval vm_compute in (infer_sub GR (ax_S (la_state r_t0N_0)) (ax_S ct0N)).
Definition s_bkN := Eval vm_compute in (infer_sub GR (ax_S (keepn (la_state r_t1N_0) nob)) (ax_S ct0N)).
Lemma SK_tN : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS2bA1A1A4S68SdG0S6bS8SdS8dS29A1S2SdS79S2SdS7aS2SdS46S2SdS4dS5SdA1A3A3A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_tN : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S2bA1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_tNb : ltac2:(tb__ "0|0|
S0S4S6aS8cS29S5cA2S11S1eS2bA1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma NX_tN : ltac2:(tb__ "0|0|
S0S4S6dS10S1eS2bA1A1S4eA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_t1N : ltac2:(tb__ "0|0|
S0S4S15S1eS42S2bA1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t1N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z413dcS2S25Z413f0S5S25A1A3A3S42S2bA1S3A5S9G0S2S20S2eS2S20S34S5S20A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t1N__R <: R_t1N__R = Some [r_t1N_0; r_t1N_1]). Qed.
Lemma LN_t1N : ltac2:(tb__ "0|0|
S0S4S14S1eS42S2bA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma OB_bN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS2eA1A1A1M0S8SdS69SdS33G0A3S2SdS8fS2SdS8eS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_xN : ltac2:(tb__ "0|1|
S0S6SdA1S13S1eS1fS34A1A1A1M0S8SdS69SdS33G0A3S2SdS8fS2SdS8eS5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma ENT_bkN : ltac2:(tb__ "0|0|
S0S4S24S52S1fS2eA1S33A2S2bS2fA3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_bkN : ltac2:(tb__ "0|0|
S0S4S72S2fS3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_bk4N : ltac2:(tb__ "0|0|
S0SeS71S2fS40A2S16S6eS18S40A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_bk6N : ltac2:(tb__ "0|0|
S0SeS71S2fS43A2S16S6eS18S43A1S17Z4A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma FB_bNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1aS6fS16S6eS18S40A1S17Z4A1A3S90A3S5SfA1A3S11S1eS1fS2eA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_xNb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS6fS16S6eS18S40A1S17Z4A1A3S90A3A1S5SfA1A3S11S1eS1fS34A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_t0N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z413dcS2S25Z413f0S5S25A1A3A3S1fS2dA1S3A5S9G0S2S20S37S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_t0N__R <: R_t0N__R = Some [r_t0N_0]). Qed.
Lemma LN_t0N : ltac2:(tb__ "0|0|
S0S4S14S1eS1fS2dA1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_t0N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ENT_inN : ltac2:(tb__ "0|0|
S0S4S24S1fS37A1S2bS30A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SID_inN : ltac2:(tb__ "0|0|
S0S4S72S30S3dA2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S_in4N : ltac2:(tb__ "0|0|
S0SeS71S30S40A2S16S6eS7dS17Z10A1A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S_in6N : ltac2:(tb__ "0|0|
S0SeS71S30S43A2S9cA3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition xlN := Eval vm_compute in (keepn (la_state r_t1N_1) nob).
Definition R_9N__R : option (list leafA) := ltac2:(tb__ "0|0|
S21S3aS2aS2S25Z40cc8S5S25A1A3S31S3A5").
Local Strategy expand [R_9N__R].
Definition r_9N := Eval vm_compute in ((fun ro4__ : option (list leafA) => (match ro4__ with Some l => l | None => [] end)) R_9N__R).
Definition r_9N_0 := Eval vm_compute in (nth 0 r_9N (mkLeafA xlN RsCut)).
Definition cellsfN := Eval vm_compute in (ob_cells (last (ss_objs (ax_S (cE1 (la_state r_9N_0) icc))) O_ri)).
Definition x3N := Eval vm_compute in (cE3 (cE2 (cE1 (la_state r_9N_0) icc))).
Definition r_zN := Eval vm_compute in (match sym_runA segsA FUEL [0x3c480] x3N true with Some l => l | None => [] end).
Definition r_zN_0 := Eval vm_compute in (nth 0 r_zN (mkLeafA x3N RsCut)).
Lemma R_9N : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z40cc8S5S25A1A3S31S3A5S9G0S2S20S28S5S20A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) R_9N__R <: R_9N__R = Some [r_9N_0]). Qed.
Lemma LN_9N : ltac2:(tb__ "0|0|
S0S4S14S1eS31A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_9N : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS31A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_x1N : ltac2:(tb__ "0|0|
S0S4S15S1eS3bS1fS28A1S27A2A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma D_x1N : ltac2:(tb__ "0|5|
S0SaS7S6S7SeSeA2M0A1M1S6SfA1M2A2M3A1S83S1eS1fS28A1M4A1S1eS3bG4S27A2A1A2S9G3ScG1G2S2G0ScSeSeS48S45A4S5G0A1A3S5SfA1A4A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma NX_x1N : ltac2:(tb__ "0|1|
S0S4S6dS10S1eS3bS1fS28A1M0S27A2A1A1S10S1eG0A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma XX_1N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3bS1fS28A1S27A2A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma IC_1N : ltac2:(tb__ "0|0|
S0SaSdA1S93SdS13S1eS3bS1fS28A1S27A2A1A1S27A3S9SdS4cA2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma OB_1N : ltac2:(tb__ "0|2|
S0S6SdA1S13S1eS3bS1fS28A1S27A2M0A1A1M1S8SdS69SdS94S53G0A1U2A2G1A3S2SdS46S2SdS99S35A1S5SdA1A3A3A3A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma RI_1N : ltac2:(tb__ "0|0|
S0S4S55S35S9bS58S56S59A5S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SK_2N : ltac2:(tb__ "0|1|
S0S6S7S7SeSeA2SeA2M0A1S68SdG0S6bS13S1eS3cS3bS1fS28A1S27A2A1A1A1A4S68SdG0S6bS8SdS8dS29A1S2SdS79S2SdS7aS5SdA1A3A3A3A4A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XX_2N : ltac2:(tb__ "0|1|
S0S6S7SeSeA2M0A1S23S3cS3bS1fS28A1S27A2A1A1S5G0A1A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma XF_2Nb : ltac2:(tb__ "0|0|
S0S4S6aS8cS29S5cA2S11S1eS3cS3bS1fS28A1S27A2A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3aN : ltac2:(tb__ "0|0|
S0S4S15S1eS4fS3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma W_3bN : ltac2:(tb__ "0|0|
S0S4S15S1eS47S3cS3bS1fS28A1S27A2A1A1A1A1S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma FB_3N : ltac2:(tb__ "0|1|
S0S4S92SfS1dS10S1eS47S3cS3bS1fS28A1S27A2A1A1A1M0A1A1S8SfS4bS11G0A1A3A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma R_zN : ltac2:(tb__ "0|1|
S0SaS6S20A1M0A1S21S3aS2aS2S25Z3c480S5S25A1A3S44S3cS3bS1fS28A1S27A2A1A1S3A5S9G0S2S20S38S5S20A1A3A2A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma LN_zN : ltac2:(tb__ "0|0|
S0S4S14S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1SbA3").
Proof. vm_cast_no_check (eq_refl false). Qed.
Lemma NX_zN : ltac2:(tb__ "0|0|
S0S4S6cS3dS10S1eS44S3cS3bS1fS28A1S27A2A1A1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Definition e3p := Eval vm_compute in (E3p W0 UStopLe 2).
Lemma E3p_eq : ltac2:(tb__ "0|0|
S0S22S7bS29S5cZ2A3S32A3").
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Definition s_xN := Eval vm_compute in (s_exit (la_state r_zN_0) e3p).
Lemma ENT_xN : ltac2:(tb__ "0|0|
S0S4S24S1fS38A1S32S39A3S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma SX_xN : sx_okb s_xN = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma S149_xN : wsub_get s_xN 149%positive = vK.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.
Lemma S159_xN : wsub_get s_xN 159%positive = vCHX.
Proof. match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end. Qed.

Lemma HW0 : ltac2:(tb__ "0|0|
S0S67S5cS61A3S0S6S5eA1S29S5S5eA1A3F_;"). Proof. intros E; discriminate E. Qed.
Definition pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE :=
  pop_all A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE ph PH0 faP HSRC HKF HNFP HFILLR HIDS HCACHE FUEL ct0N r_t1N_0 r_t1N_1 nob s_bkN
    SK_tN XX_tN (inclb_incl _ _ XF_tNb) NX_tN W_t1N R_t1N LN_t1N OB_bN OB_xN ENT_bkN SID_bkN S_bk4N S_bk6N (In_of_inclb _ _ FB_bNb) (In_of_inclb _ _ FB_xNb)
    (la_state r_2_1) r_t0N_0 s_inN e_srcN R_t0N LN_t0N NX_t0N ENT_inN SID_inN S_in4N S_in6N.
Definition entry_i := refill_entry 0 UStopLe e3r SK3 XX3 (inclb_incl _ _ XF3b) NX3 WR0a FB0.
Definition prefix_i A Kc rb tp0 md0 TR KIT HKc := refill_prefix A Kc rb tp0 md0 TR KIT HKc FUEL e3r r_1_0 r_2_0 r_2_1 R_1 LN_0 NX_0 W_r1 D_r1 NX_r1 R_2 LN_1 NX_1.
Definition exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX PHX HFILLX Hini HRIv HLEN HIDC :=
  exit_steps A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho HW0 HE phX PHX HFILLX Hini e16N vMFA vAU vMU HRIv HLEN HIDC FUEL xlN r_9N_0 r_zN_0 icc cellsfN
    R_9N LN_9N NX_9N W_x1N D_x1N NX_x1N XX_1N IC_1N OB_1N RI_1N SK_2N XX_2N (inclb_incl _ _ XF_2Nb) W_3aN W_3bN FB_3N R_zN LN_zN NX_zN.
Definition back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW HE phF HREB HMK HLEN HPOP :=
  refill_back CST XGL PFam HPF A Kc rb tp0 md0 TR KIT W0 UStopLe rho HW HE phF HREB HMK HLEN e3p (la_state r_zN_0) s_xN ENT_xN SX_xN S149_xN S159_xN HPOP.
Lemma FJ_Nb : ltac2:(tb__ "0|0|
S0S4S6aS2SfS1bS1aS70S5aS45A3A1S5SfA1A3S11S1eS1fS2dA1A1A1A2S3A3").
Proof. vm_cast_no_check (eq_refl true). Qed.

Theorem refill_N_i : ltac2:(tb__ "0|5|
S6S7S25S25A2A1M0G0S7eS5dS6S7S22S85A2A1F_;F_;S9aR3R2R1A3S22S22S0S22R2S26A3S0S22R2S32A3S7eS5dS12S6S74Q40M1A1A1M2S77S77OF_;F_;S98R4R1A2S60R5A1S0S4S7fR7A1S3A3S0S25S81R8S73G1S19R6PcM3A2A2A2Z0A3S84S3aS82R7R6RfR9R8A2A5S77S12S75S87RcR2R9R1S29S5cRaA7S9eS8aS80S73G1S19R3G3A2A2A1A1S88RdR3A2A2S12G2S6S76A1S75S86R12R11R8RfR7S9dS8aS80S73G1S19R8G3A2A2A1A1A1R4R3R2R1AaS1S97S3aS8bR13S80S73G1S19R9G3A2A2A1A2M4R5R4R2A5S63R1bR1aR13G4S1cR9A1S1cR5A1A6A2F_;Fmd;Ftr;Ftp';Fr;F_;FHE;Fmd0;Frb;S7eS12G2S12RbS78S3aS91S29S5cR4ReR3A5R12R1R2A5S84S3aS82R3R2R15R4ReA2A5A2FrX;Ftp';Frho';FA';S12S75S12S87RfR3RcR2S29S5cRdA7RcS78S3aS86R10RfR4RdR3S89A6S1fS36A1R2RdA5R7A2F_;Fr';Fmd0;Frb;S12RaS78S3aS91S29S5cReRdRcA5R12R1RbA5R5A2FrhoE;F_;F_;F_;TQ;F_;F_;FHKc;FKIT;FTR;Ftp;Frho;FKc;FA;F_;F_;FE3P;FE3;FHPF;FPFam;FXGL;FCST;").
Proof.
  intros CST XGL PFam HPF E3 E3P -> ->.
  apply (refill_N CST XGL PFam W0 UStopLe e3r e3p (la_state r_2_0) (la_state r_2_1) xlN (la_state r_zN_0) (In_of_inclb _ _ FJ_Nb)).
  - intros A Kc rho rhoE tp w Hini Hcnt Hw. exact (entry_i A Kc rho rhoE tp w HW0 Hini Hcnt Hw).
  - intros A Kc rb tp0 md0 TR KIT HKc rho r tp Q HE. exact (prefix_i A Kc rb tp0 md0 TR KIT HKc W0 UStopLe rho r tp Q HE).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP. exact (pop_N A Kc rb tp0 md0 TR KIT HKc rho HE ph PH0 faP).
  - intros A Kc rb tp0 md0 TR KIT HKc rho HE phX. exact (exit_N A Kc rb tp0 md0 TR KIT HKc rho HE phX).
  - intros A Kc rb tp0 md0 TR KIT rho HE phF. exact (back_N CST XGL PFam HPF A Kc rb tp0 md0 TR KIT rho HW0 HE phF).
Qed.
End SpineMallocRi0u.

