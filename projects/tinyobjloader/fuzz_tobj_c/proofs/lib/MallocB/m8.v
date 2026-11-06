(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EvalMemo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.

(* [comment removed for export] *)
Module SpineMallocS2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "valuation"; "ss_next"; "eval"; "ss_facts"; "rw"; "swf"; "SLit"; "SPBranch"; "sobj"; "SPNot"; "mkVal"; "@Corelib.Init.Datatypes"; "bool"; "true"; "nil"; "list"; "nat"; "pair"; "prod"; "cons"; "Some"; "option"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "Wcan"; "KcA"; "J_alloc_preT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP"; "E2a"; "E2b"; "creg_a"; "V_CLS"; "creg_b"; "F_gen"; "V_ND"; "upd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2"; "only_var"; "tab_ok"; "E2a'"; "rho_one"; "zseq8"; "tab_ok_ref"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@Corelib.Init.Decimal"; "D8"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "ClassID"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineMallocS2.S2"; "E2a'"; "E2b'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@Stdlib.Lists.List"; "In"; "forallb"; "incl"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "mul"; "of_nat"; "sub"; "eqb"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EvalMemo"; "eval_f"; "@Stdlib.PArith.BinPos.Pos"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SpineMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EvalMemo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Fixpoint only_var (i : positive) (e : sv) : bool :=
  match e with
  | SLit _ => true
  | SVar j => Pos.eqb j i
  | SAlu _ a b | SAluW _ a b | SMd _ a b | SMdW _ a b => only_var i a && only_var i b
  | SExt _ _ a => only_var i a
  | SLBytes _ _ _ => false
  end.
Definition rho_one (i : positive) (v : word) : valuation := ltac2:(tb__ "0|3|
S13S3S14S33Q40M0A1M1L_;S50R1Vi;A2Vv;S32G0Z0A2X14x2Lj;S3S16S33Q8A1M2A1L_;G1S1fG2A1L_;A3").
Lemma eval_only_var : ltac2:(tb__ "0|0|
S3S6S9S0S14S2cR3R2A2S15A3S0S33Q40A1SbR2R3A2SbS2fR4SdR2R4A2A2R3A2A3F_;Frho;Fe;Fi;").
Proof.
  intros i e rho. induction e; cbn [only_var eval]; intros H; try reflexivity.
  - apply Pos.eqb_eq in H. subst. cbn. rewrite Pos.eqb_refl. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - apply andb_prop in H as [H1 H2]. rewrite IHe1, IHe2 by assumption. reflexivity.
  - rewrite IHe by assumption. reflexivity.
  - discriminate H.
Qed.

Fixpoint zseq8 (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq8 (lo + 8) n' end.
Lemma in_zseq8 : ltac2:(tb__ "0|1|
S2S18S2S1S43R3R1A2S44R1S42R3S46Z8M0S47R2A1A2A2A2A2S0S2S45S48R2R4A2G0A2Z0A3S3fS2R3S30R5R4A2A3F_;F_;Fz;Fn;Flo;").
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z Hz Hm; [lia|]. cbn [zseq8].
  destruct (Z.eq_dec z lo) as [->|Hne]; [left; reflexivity | right]. rewrite Nat2Z.inj_succ in Hz.
  apply IH; [|replace (z - (lo + 8)) with (z - lo - 8) by lia; rewrite Zminus_mod, Hm, Z.mod_same by lia; reflexivity].
  assert ((z - lo) = 8 * ((z - lo) / 8)) by (pose proof (Z_div_mod_eq_full (z - lo) 8); lia).
  assert (1 <= (z - lo) / 8) by lia. lia.
Qed.
Definition tab_ok_ref (i : positive) (e : sv) (g : Z -> Z) (lo : Z) (n : nat) : bool := ltac2:(tb__ "0|1|
S40S2S2S49S34Q40M0SbS2fVi;S32G0R1A2A2Ve;A2A2Vg;R1A1A2Lz;S30Vlo;Vn;A2A3").
Lemma tab_ok_ref_sound : ltac2:(tb__ "0|3|
S3S6S2S2F_;S2S18S9S2S0S14S31R7R6R5R4R3A5S15A3S0S14S2cR8R7A2S15A3S0S33Q40M0A1M1SdR4R9A2S32G0R3A2A3S1S43R7R4A2S44R4S42R7S46Z8M2S47R6A1A2A2A2A2S0S2S45S48R5R8A2G2A2Z0A3S0G1SbR7RbA2S32G0RaR6A1A2A3F_;F_;F_;F_;F_;Fz;Frho;Fn;Flo;Fg;Fe;Fi;").
Proof.
  intros i e g lo n rho z Ht Ho Hi Hz Hm.
  pose proof (proj1 (forallb_forall _ _) Ht z (in_zseq8 lo n z Hz Hm)) as T. cbn beta in T. apply Z.eqb_eq in T.
  rewrite (eval_only_var i e rho Ho), Hi. rewrite <- T. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Definition tab_ok (i : positive) (e : sv) (g : Z -> Z) (lo : Z) (n : nat) : bool := ltac2:(tb__ "0|1|
S40S2S2S49S34Q40M0S4fS2fVi;S32G0R1A2A2Ve;A2A2Vg;R1A1A2Lz;S30Vlo;Vn;A2A3").
Lemma tab_ok_ref_eq : ltac2:(tb__ "0|0|
S3S6S2S2F_;S2S18S0S14S2dR5R4R3R2R1A5S31R5R4R3R2R1A5A3Fn;Flo;Fg;Fe;Fi;").
Proof.
  intros i e g lo n. unfold tab_ok, tab_ok_ref. generalize (zseq8 lo n). intros l.
  induction l as [|z t IH]; cbn [forallb]; [reflexivity|]. rewrite IH, EvalMemo.eval_f_eq. reflexivity.
Qed.
Lemma tab_ok_sound : ltac2:(tb__ "0|3|
S3S6S2S2F_;S2S18S9S2S0S14S2dR7R6R5R4R3A5S15A3S0S14S2cR8R7A2S15A3S0S33Q40M0A1M1SdR4R9A2S32G0R3A2A3S1S43R7R4A2S44R4S42R7S46Z8M2S47R6A1A2A2A2A2S0S2S45S48R5R8A2G2A2Z0A3S0G1SbR7RbA2S32G0RaR6A1A2A3F_;F_;F_;F_;F_;Fz;Frho;Fn;Flo;Fg;Fe;Fi;").
Proof.
  intros i e g lo n rho z Ht. rewrite tab_ok_ref_eq in Ht. exact (tab_ok_ref_sound i e g lo n rho z Ht).
Qed.

Section S2.
Variable nW : nat. Variable st : ustop. Variable tmax : Z.
Let W : list ulink := Wcan nW.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (W : list ulink) (st : ustop) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S23VAInv;VW;Vst;VA;VKc;S8PcA1A6").

Hypothesis OVa : ltac2:(tb__ "0|0|
S0S14S2cP9dS26VW;Vst;Vtmax;A3A2S15A3").
Hypothesis OVb : ltac2:(tb__ "0|0|
S0S14S2cP9dS28VW;Vst;Vtmax;A3A2S15A3").
Hypothesis TABa : ltac2:(tb__ "0|0|
S0S14S2dP9dS26VW;Vst;Vtmax;A3S3aZ208S4aS4bS35S36S37S35S38A1A1A1A1A1A1A5S15A3").
Hypothesis TABb : ltac2:(tb__ "0|0|
S0S14S2dP9dS28VW;Vst;Vtmax;A3S3aZ18U3eA5S15A3").

Definition E2a' : axst := ltac2:(tb__ "0|1|
S2bVW;Vst;Vtmax;S24VW;Vst;Vtmax;A3Z40d40S1bS1aS18S6A2M0S19S18S6U8S8S27A1A4S16G0A1A3S16S11A1S1eS16S7A1A9").
Definition E2b' : axst := ltac2:(tb__ "0|1|
S2bVW;Vst;Vtmax;S25VW;Vst;Vtmax;A3Z40d40S1bS1aS18S6A2M0S19S18S6U8S8S27A1A4S16G0A1A3S16S11A1S1eS16S7A1A9").
Hypothesis Wa' : ltac2:(tb__ "0|0|
S0S14SeS4S3cA1A1S15A3").
Hypothesis Wb' : ltac2:(tb__ "0|0|
S0S14SeS4S3dA1A1S15A3").
Hypothesis Da' : ltac2:(tb__ "0|4|
S0S1dS1aS17S1aS6S6A2M0A1M1S17S7A1M2A2M3A1S3eS4S24VW;Vst;Vtmax;A3A1S4S3cA1A2S1cG3S19G1G2S1bG0S19S6S6S26VW;Vst;Vtmax;A3S8S27A1A4S16G0A1A3S16S7A1A4A2A3").

Hypothesis NXa : ltac2:(tb__ "0|0|
S0S3SaS4S3cA1A1SaS4S24VW;Vst;Vtmax;A3A1A1A3").
Hypothesis NXb : ltac2:(tb__ "0|0|
S0S3SaS4S3dA1A1SaS4S25VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Db' : ltac2:(tb__ "0|4|
S0S1dS1aS17S1aS6S6A2M0A1M1S17S7A1M2A2M3A1S3eS4S25VW;Vst;Vtmax;A3A1S4S3dA1A2S1cG3S19G1G2S1bG0S19S6S6S28VW;Vst;Vtmax;A3S8S27A1A4S16G0A1A3S16S7A1A4A2A3").

Hypothesis Fa : ltac2:(tb__ "0|0|
S3fS7S10S4cSfZ200A1S8S2aA1A3ScS4S24VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Fb : ltac2:(tb__ "0|0|
S3fS7S12S10S4cSfZ200A1S8S2aA1A3A1ScS4S25VW;Vst;Vtmax;A3A1A1A3").

Hypothesis Ga : ltac2:(tb__ "0|0|
S41S7S29ScS4S24VW;Vst;Vtmax;A3A1A1A3").
Hypothesis Gb : ltac2:(tb__ "0|0|
S41S7S29ScS4S25VW;Vst;Vtmax;A3A1A1A3").

Lemma class_restate_a : ltac2:(tb__ "0|1|
S4eS22S9S17S33Q40A1A1S4dS9S39Vsegs;S3bVW;Vst;R6R5R4A5S24VW;Vst;Vtmax;A3M0R1R3R2A6S39Vsegs;S3bVW;Vst;R7R6R5A5S5G0S4S3cA1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fa) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Ga; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  rewrite bt_ltu_lit in F1 by lia. apply Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wa' | exact Da' | exact NXa | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 520 8128%nat rhoE (needed8 nv) TABa OVa E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 520) with (needed8 nv + (- 65) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.

Lemma class_restate_b : ltac2:(tb__ "0|1|
S4eS22S9S17S33Q40A1A1S4dS9S39Vsegs;S3bVW;Vst;R6R5R4A5S25VW;Vst;Vtmax;A3M0R1R3R2A6S39Vsegs;S3bVW;Vst;R7R6R5A5S5G0S4S3dA1A2R2R4R3A6F_;FrhoE;Fw;Ftp;Frho;FKc;FA;").
Proof.
  intros A Kc rho tp w rhoE H. pose proof H as [HsmA [Hag HJ]]. destruct Hag as (Hagw & Hagl & Hagm).
  destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop). cbn [eval] in HN.
  assert (E12 : rw rhoE 12%positive = rw rho 12%positive). { rewrite <- (Hagw 12%positive) by (unfold GW; lia). reflexivity. }
  rewrite E12 in HN. set (nv := bv_unsigned (rw rho 12%positive)) in *.
  assert (NB0 : 0 <= needed8 nv < 2 ^ 62).
  { unfold needed8, round_up. pose proof (rz_bound nv). pose proof (Z.mul_div_le (Z.max nv 8 + 8 - 1) 8 ltac:(lia)).
    pose proof (Z.div_pos (Z.max nv 8 + 8 - 1) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (E157 : rw rhoE 157%positive = Z_to_bv 64 (needed8 nv)). { rewrite <- (Hagw 157%positive) by (unfold GW; lia). reflexivity. }
  assert (E158 : rw rhoE 158%positive = Z_to_bv 64 (cls_of nv)). { rewrite <- (Hagw 158%positive) by (unfold GW; lia). reflexivity. }
  pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ Fb) as F1. cbn [holds eval V_ND] in F1. unfold V_ND in F1. rewrite E157 in F1.
  assert (G1 : holds rhoE (SPUle (SLit 24) (SVar V_ND))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G2 : holds rhoE (SPUle (SVar V_ND) (SLit 65536))) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto).
  assert (G3 : holds rhoE (SPAlign V_ND 3)) by (apply (proj1 (Forall_forall _ _) HFa); apply Gb; unfold F_gen; cbn; tauto). cbn [holds eval] in G1, G2, G3. unfold V_ND in G1, G2, G3. rewrite E157 in G1, G2, G3.
  unfold not in F1. rewrite bt_ltu_lit in F1 by lia. rewrite Z.ltb_lt in F1. rewrite !u64_lit in G1, G2 by lia.
  destruct G3 as [_ G3]. rewrite u64_lit in G3 by lia.
  eapply SPA_restate; [exact Wb' | exact Db' | exact NXb | | constructor | exact H].
  constructor; [|constructor]. cbn [fst snd]. cbn [eval]. unfold V_CLS. rewrite E158.
  rewrite (tab_ok_sound 157 _ ClassID 24 62%nat rhoE (needed8 nv) TABb OVb E157); [unfold cls_of; reflexivity | cbn; lia |].
  replace (needed8 nv - 24) with (needed8 nv + (- 3) * 8) by lia. rewrite Z.mod_add by lia. exact G3.
Qed.
End S2.

Lemma OVa_0 : ltac2:(tb__ "0|0|
S0S14S2cP9dS26S21U0A1S20Z2A3A2S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma OVb_0 : ltac2:(tb__ "0|0|
S0S14S2cP9dS28S21U0A1S20Z2A3A2S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABa_0 : ltac2:(tb__ "0|0|
S0S14S2dP9dS26S21U0A1S20Z2A3S3aZ208S4aS4bS35S36S37S35S38A1A1A1A1A1A1A5S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma TABb_0 : ltac2:(tb__ "0|0|
S0S14S2dP9dS28S21U0A1S20Z2A3S3aZ18U3eA5S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma NXa_0 : ltac2:(tb__ "0|2|
S0S3SaS4S2eU0M0S20Z2M1A3A1A1SaS4S24S21G0A1S20G1A3A1A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Da'_0 : ltac2:(tb__ "0|7|
S0S1dS1aS17S1aS6S6A2M0A1M1S17S7A1M2A2M3A1S3eS4S24S21U0M4A1M5S20Z2M6A3A1S4S2eG4S20G6A3A1A2S1cG3S19G1G2S1bG0S19S6S6S26G5S20G6A3S8S27A1A4S16G0A1A3S16S7A1A4A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Wa'_0 : ltac2:(tb__ "0|0|
S0S14SeS4S2eU0S20Z2A3A1A1S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

End SpineMallocS2.

(* [comment removed for export] *)
Module SpineCallocI2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "SVar"; "rl"; "rm"; "sv"; "agree_below"; "eval"; "sprop"; "@Corelib.Init.Logic"; "eq"; "not"; "or"; "@Corelib.Numbers.BinNums"; "positive"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "rhoM_of"; "stopJ_stable"; "@Corelib.Init.Datatypes"; "list"; "cons"; "pair"; "option"; "prod"; "bool"; "nil"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocI2"; "rho_c"; "stopJ_sw"; "s_sw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "rho_ce"; "Jc"; "P0e"; "nwc"; "PRODe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "ulink"; "J_alloc_preT"; "KcA"; "ustop"; "UStopLe"; "unwind_stopJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1"; "P0c"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.
Local Notation U := bv_unsigned.

Definition s_sw : wsub := ltac2:(tb__ "0|2|
S12S15ScS5A2M0S13ScS5P8fS2PcM1A1A4S12G0S13ScS5P90S2PdA1A4S12G0S13ScS5G1S20A4S17G0A1A3A3A3").

Definition rho_c (rho : valuation) : valuation := ltac2:(tb__ "0|1|
S24S24S24Vrho;PcM0S1fVrho;A1A3P8fS0Vrho;G0A2A3P90S0Vrho;PdA2A3").

Definition stopJ_sw (W : list ulink) (st : ustop) : Prop := ltac2:(tb__ "0|1|
S1S1ScS35R1S32A2SaS9ScR2PcA3A1S9SdQ40A1S0R4R3A2S0R5R3A2A3F_;F_;Fi;S2aVW;Vst;R3A3M0G0F_;F_;Frho';Frho;").

Lemma rw_rho_sets_ext : ltac2:(tb__ "0|1|
S11S15ScSdQ40A1M0A2A1S1S1ScS9G0S0R3R1A2S0R2R1A2A3S9G0S0S2cR4R5A2R2A2S0S2cR3R5A2R2A2A3F_;Fi;Fr';Fr;Fl;").
Proof.
  induction l as [|[j v] l IH]; intros r r' i H; cbn [rho_sets]; [exact H|].
  apply IH. rewrite !rw_set. destruct (Pos.eqb i j); [reflexivity | exact H].
Qed.
Lemma rhoM_of_ext : ltac2:(tb__ "0|2|
SeS1S1ScS9SdQ40A1M0S0R3PcM1A2S0R2G1A2A3S9G0S0R4R2A2S0R3R2A2A3S9G0S0SfR6R5A2R3A2S0SfR6R4A2R3A2A3F_;F_;Fi;Fr';Fr;FA;").
Proof. intros A r r' i H12 Hi. unfold rhoM_of. cbv zeta. rewrite H12. apply rw_rho_sets_ext. exact Hi. Qed.
Lemma rhoM_of_rl : ltac2:(tb__ "0|0|
SeS1ScS9S11SdQ8A1A1S3SfR3R2A2R1A2S3R2R1A2A3Fl;Fr;FA;").
Proof. intros. unfold rhoM_of. cbv zeta. apply (f_equal (fun f => f l)). apply rl_rho_sets. Qed.
Lemma rhoM_of_rm : ltac2:(tb__ "0|0|
SeS1S9SdQ40A1S14SdQ8A1A1F_;S4SfR2R1A2A1S4R1A1A3Fr;FA;").
Proof. intros. unfold rhoM_of. cbv zeta. apply rm_rho_sets. Qed.

Lemma rhoM_of_keep : ltac2:(tb__ "0|0|
SeS1ScSbS9ScR1PcA3SbS9ScR1PdA3SbS9ScR1P8fA3S9ScR1P90A3A2A2A2S9SdQ40A1S0SfR4R3A2R2A2S0R3R2A2A3F_;Fi;Fr;FA;").
Proof.
  intros A r i Hi. unfold rhoM_of. cbv zeta. apply rw_rho_sets_other.
  - intros v Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as E _; destruct Hi as [->|[->|[->| ->]]]; discriminate E|]). exact Hin.
  - intros j v Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- _; destruct Hi as [->|[->|[->| ->]]]; discriminate|]). destruct Hin.
Qed.

Lemma rce_12 : ltac2:(tb__ "0|1|
SeS1S9SdQ40A1S0S1cR2R1A2PcM0A2S0R1G0A2A3Frho;FA;").
Proof. intros. unfold rho_ce. rewrite rw_set. reflexivity. Qed.
Lemma rce_13 : ltac2:(tb__ "0|1|
SeS1S9SdQ40A1S0S1cR2R1A2PdM0A2S0R1G0A2A3Frho;FA;").
Proof.
  intros. unfold rho_ce. rewrite rw_set. change (Pos.eqb 13 12) with false. cbv iota.
  rewrite (rhoM_of_keep A _ 13%positive) by tauto. rewrite rw_set. reflexivity.
Qed.
Lemma rc_12 : ltac2:(tb__ "0|0|
SeS1S9SdQ40A1S0SfR2S19R1A1A2PcA2S1fR1A1A3Frho;FA;").
Proof. intros. rewrite (rhoM_of_keep A _ 12%positive) by tauto. unfold rho_c. rewrite !rw_set. reflexivity. Qed.
Lemma rc_143 : ltac2:(tb__ "0|0|
SeS1S9SdQ40A1S0SfR2S19R1A1A2P8fA2S0R1PcA2A3Frho;FA;").
Proof. intros. rewrite (rhoM_of_keep A _ 143%positive) by tauto. unfold rho_c. rewrite !rw_set. reflexivity. Qed.
Lemma rc_144 : ltac2:(tb__ "0|0|
SeS1S9SdQ40A1S0SfR2S19R1A1A2P90A2S0R1PdA2A3Frho;FA;").
Proof. intros. rewrite (rhoM_of_keep A _ 144%positive) by tauto. unfold rho_c. rewrite !rw_set. reflexivity. Qed.
Lemma rc_other : ltac2:(tb__ "0|0|
SeS1ScSaS9ScR1PcA3A1SaS9ScR2P8fA3A1SaS9ScR3P90A3A1S9SdQ40A1S0S1cR6R5A2R4A2S0SfR6S19R5A1A2R4A2A3F_;F_;F_;Fi;Frho;FA;").
Proof.
  intros A rho i H1 H2 H3. unfold rho_ce. rewrite rw_set. rewrite (proj2 (Pos.eqb_neq _ _) H1).
  apply rhoM_of_ext.
  - unfold rho_c. rewrite !rw_set. reflexivity.
  - unfold rho_c. rewrite !rw_set. rewrite (proj2 (Pos.eqb_neq _ _) H1), (proj2 (Pos.eqb_neq _ _) H2), (proj2 (Pos.eqb_neq _ _) H3). reflexivity.
Qed.

Lemma rw_rho_sub : ltac2:(tb__ "0|0|
S1S22ScS9SdQ40A1S0S21R3R2A2R1A2S7R3S23R2R1A2A2A3Fi;Fs;Fr;"). Proof. reflexivity. Qed.
Lemma rl_rho_sub : ltac2:(tb__ "0|0|
S1S22ScS9S11SdQ8A1A1S3S21R3R2A2R1A2S3R3R1A2A3Fl;Fs;Fr;"). Proof. reflexivity. Qed.
Lemma rm_rho_sub : ltac2:(tb__ "0|0|
S1S22SdQ40A1S9S14SdQ8A1A1S4S21R3R2A2R1A2S4R3R1A2A3Fa;Fs;Fr;"). Proof. reflexivity. Qed.
Lemma sw_agree : ltac2:(tb__ "0|0|
SeS1S6S34S21S1cR2R1A2S1bA2SfR2S19R1A1A2A3Frho;FA;").
Proof.
  intros A rho. split; [|split].
  - intros i _. rewrite rw_rho_sub. unfold s_sw. cbn [wsub_get].
    destruct (Pos.eqb i 143) eqn:E1; [apply Pos.eqb_eq in E1; subst i; rewrite rc_143; cbn [eval]; apply rce_12|].
    destruct (Pos.eqb i 144) eqn:E2; [apply Pos.eqb_eq in E2; subst i; rewrite rc_144; cbn [eval]; apply rce_13|].
    destruct (Pos.eqb i 12) eqn:E3; [apply Pos.eqb_eq in E3; subst i|].
    { rewrite rc_12. unfold PRODe. cbn [eval]. rewrite rce_12, rce_13. unfold nwc. rewrite calloc_size_val. apply mul_word_comm. }
    cbn [eval]. apply rc_other; apply Pos.eqb_neq; assumption.
  - intros l. rewrite rl_rho_sub. unfold rho_ce. rewrite rl_set, !rhoM_of_rl.
    unfold rho_c. rewrite !rl_set. reflexivity.
  - intros a. rewrite rm_rho_sub. unfold rho_ce. rewrite rm_set, !rhoM_of_rm.
    unfold rho_c. rewrite !rm_set. reflexivity.
Qed.

Section SW.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.

Lemma Jc_switch : ltac2:(tb__ "0|0|
S11S25A1S28SeS27S1S11SdQ40A1A1S11S30A1S2fS1aR8R7A2S10R9R8A2S1dRaR9R8R7S1cR8R6A2R5R4R3A8S26VAInv;RbRaR9R8S2PcA1SfR9S19R7A1A2R6R5R4AaF_;F_;F_;Fmd;Ftr;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp tr md HSW HUS HJ.

  assert (HJ0 : Jc W st A Kc rho tp tr md).
  { apply (JMc_agree W st A Kc (rho_ce A rho) rho tp tr md HUS); [|exact HJ].
    destruct (rho_ce_agree A rho) as (Hw & Hl & Hm). repeat split; intros; symmetry; auto. }
  destruct HJ0 as (HA & HK & Htp & HU & HB & HN & Htop).
  set (rc := rhoM_of A (rho_c rho)).
  assert (Eo : forall i, i <> 12%positive -> i <> 143%positive -> i <> 144%positive -> (i < NF)%positive -> rw rc i = rw rho i).
  { intros i H1 H2 H3 Hi. unfold rc. rewrite <- (proj1 (rhoM_agree A (rho_c rho)) i Hi). unfold rho_c. rewrite !rw_set.
    rewrite (proj2 (Pos.eqb_neq _ _) H1), (proj2 (Pos.eqb_neq _ _) H2), (proj2 (Pos.eqb_neq _ _) H3). reflexivity. }
  assert (Erm : rm rc = rm rho) by (unfold rc; rewrite rhoM_of_rm; reflexivity).
  assert (E12 : rw rc 12%positive = nwc rho) by (unfold rc; rewrite (rhoM_of_keep A (rho_c rho) 12%positive) by tauto; reflexivity).
  split; [unfold AInv, AInvA in *; rewrite Erm; exact HA|]. split; [exact HK|].
  split; [unfold tp_ok in *; rewrite (Eo 24%positive) by (unfold NF; lia || discriminate); exact Htp|].
  split.
  { apply (HSW rho rc); [|exact HU]. intros i Hi H1. apply (Eo i H1); [| |exact Hi]; intros ->; unfold NF in Hi; lia. }
  cbn [eval]. rewrite E12. unfold nwc in *. split; [exact HB|]. split; [exact HN|].
  unfold top_high in *. rewrite (Eo 10%positive) by (unfold NF; lia || discriminate). rewrite (Eo V_DEPTH) by (unfold NF, V_DEPTH; lia || discriminate). exact Htop.
Qed.

Theorem c_switch : ltac2:(tb__ "0|1|
S11S25A1S28SeS27S1S11SdQ40A1A1S31S11S8A1M0G0S1aR9R8A2S10RaR9A2S9S16S33S1eRbRaR4A3S2dRbRaR3A3S1bA3S18A3S2bS2eS1dRcRbRaR9A4S1eRcRbR5A3S1cRaR8A2R7R6A6S2bS2eS26VAInv;RdRcRbRaS2PcA1A6S2dRdRcR5A3SfRbS19R9A1A2R8R7A6F_;F_;F_;F_;Ffx;Ffxe;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w fxe fx HSW HUS HENT [Hsm HJ]. split.
  - apply (smatchA_agree segs (rho_sub (rho_ce A rho) s_sw) (rhoM_of A (rho_c rho)) tp (P0c W st fx) w); [exact (sw_agree A rho)|].
    exact (smatchA_entails segs _ _ s_sw (rho_ce A rho) tp w HENT Hsm).
  - exact (Jc_switch W st A Kc rho tp _ _ HSW HUS HJ).
Qed.

Lemma stopJ_sw_le : ltac2:(tb__ "0|0|
S11S25A1S1aR1S29A2FW;").
Proof. intros W rho rho' _ H. unfold unwind_stopJ in *. destruct W; exact I. Qed.
Lemma stopJ_sw_1pc : stopJ_sw (Wcan 1) UStopLeOrPc.
Proof.
  intros rho rho' He H. unfold unwind_stopJ, Wcan, Wcan_from, last_link, link_var in *. cbn [nth eval] in *.
  rewrite !He by (unfold NF; first [lia | discriminate]). exact H.
Qed.
End SW.
End SpineCallocI2.

(* [comment removed for export] *)
Module SpineCallocIo.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "sobj"; "SLit"; "SVar"; "FcsrFrm0"; "SPUle"; "mkSS"; "rw"; "swf"; "valuation"; "SPBranch"; "SPNot"; "rm"; "sprop_below"; "@Corelib.Init.Datatypes"; "pair"; "app"; "cons"; "prod"; "nil"; "list"; "nat"; "bool"; "true"; "None"; "false"; "Some"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "AE_A"; "A_globals"; "Pre_callocI"; "ae_calloc"; "malloc_depth"; "pre_facts"; "stack_win"; "unwind_factsS"; "unwind_objs"; "KcA"; "mkA"; "ulink"; "ustop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "F_geom_fn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "ERRNO_A"; "cell_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI"; "Jc"; "sa_c"; "F_s1e"; "MHe"; "rho_ce"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m8.SpineCallocIo.CSPINEO"; "FACTSo"; "N_ovx"; "F_argo"; "P0o"; "sb_o"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "N_m1"; "stopJ_stable"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "mul"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RebuildSM SMGlue InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNullInit SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineCallocI.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RebuildSM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SMGlue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.CertMallocM0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CallocArith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.CertCallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineCallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation segs := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.segsA.
Local Notation U := bv_unsigned.

Section CSPINEO.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Definition F_argo : list sprop := ltac2:(tb__ "0|1|
S11S1S6S3Z1A1M0S4PcA1A2S11S1S6G0S4PdA1A2S11S1ScSbS4aS3eS3Z0A1A3A1S13S1A1A3A3A3").
Definition FACTSo (W : list ulink) (st : ustop) : list sprop := ltac2:(tb__ "0|0|
S10S1S10S1S10S1S10S1S27VW;Vst;A2S25S24A1A3S2eA3S3dA3S42A3").

Definition N_ovx : list carve_spec := ltac2:(tb__ "0|8|
S11S12S12S12S0S1cA2M0S1cA2M1S14S12S12S1cS15A2M2S0A2M3A1M4A2M5SfG1G4SfG0S1cSfS0S1cS3Z0A1M6Z170320A4Z170322A4S11G3SfG2S0SfS1cS15Z170321U1A4S3Z1A1A4S13G3A1M7A3A4S11G5SfG1G4SfG0S1cSfS0S1cG6S37A4S4fS37Z4A2A4G7A4S13G5A1A3A3").
Definition sb_o (W : list ulink) (st : ustop) : sstate := ltac2:(tb__ "0|1|
S7S23S20A1S34S33S11S12S15S0A2M0SfS15S0U4S3S30A1A4S13G0A1A3A2S32S5S18S0A1S10S2S11S2S26S10S2S28VW;A1S21A3A3S31S1eS2S1fS10S1eS45S41A3A4A3S10S1S27VW;Vst;A2S25S24A1A3S2dS19A9").
Definition P0o (W : list ulink) (st : ustop) : axst := ltac2:(tb__ "0|1|
S2aS7S23S20A1S34S33S11S12S15S0A2M0SfS15S0U4S3S30A1A4S13G0A1A3A2S32S5S18S0A1S10S2S11S2S26S10S2S28VW;A1S21A3A3S31S1eS2S1fS10S1eS45S41A3A4A3S40VW;Vst;A2S2dS19A9S13S12S0S0A2A1A2").
Hypothesis law_die : ltac2:(tb__ "0|0|
S36SaS14S47Q40A1A1S49VAInv;R4R3R2R1A4S38S3aS2fSdR4A1A2S39Z17fbdcU4Z0A3A2F_;Fmd;Ftp;Frho;FA;").

Local Ltac civ_try2F HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Local Ltac civ_any2F HR := first [ civ_try2F HR 43%nat | civ_try2F HR 44%nat | civ_try2F HR 45%nat | civ_try2F HR 46%nat | civ_try2F HR 47%nat | civ_try2F HR 48%nat | civ_try2F HR 49%nat | civ_try2F HR 50%nat | civ_try2F HR 51%nat | civ_try2F HR 52%nat | civ_try2F HR 53%nat | civ_try2F HR 54%nat | civ_try2F HR 0%nat | civ_try2F HR 1%nat | civ_try2F HR 2%nat | civ_try2F HR 3%nat | civ_try2F HR 4%nat | civ_try2F HR 5%nat | civ_try2F HR 6%nat | civ_try2F HR 7%nat | civ_try2F HR 8%nat | civ_try2F HR 9%nat | civ_try2F HR 10%nat | civ_try2F HR 11%nat | civ_try2F HR 12%nat | civ_try2F HR 13%nat | civ_try2F HR 14%nat | civ_try2F HR 15%nat | civ_try2F HR 16%nat | civ_try2F HR 17%nat | civ_try2F HR 18%nat | civ_try2F HR 19%nat | civ_try2F HR 20%nat | civ_try2F HR 21%nat | civ_try2F HR 22%nat | civ_try2F HR 23%nat | civ_try2F HR 24%nat | civ_try2F HR 25%nat | civ_try2F HR 26%nat | civ_try2F HR 27%nat | civ_try2F HR 28%nat | civ_try2F HR 29%nat | civ_try2F HR 30%nat | civ_try2F HR 31%nat | civ_try2F HR 32%nat | civ_try2F HR 33%nat | civ_try2F HR 34%nat | civ_try2F HR 35%nat | civ_try2F HR 36%nat | civ_try2F HR 37%nat | civ_try2F HR 38%nat | civ_try2F HR 39%nat | civ_try2F HR 40%nat | civ_try2F HR 41%nat | civ_try2F HR 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma c_instantiate_ov : ltac2:(tb__ "0|5|
S14S2bA1S2cS36S29SaS14S47Q40M0A1A1S4bS46R7R6A2S1dS16S9S3cR8R7A2A1S17A3S1dS1bS12S14S12S0S0A2M1A1M2S14S1A1M3A2M4A1S4cS4dS22S20R9R8A3A1S3cR9R8A2A2S1aG4SfG2G3S11G1SfS0S0S4P18A1S3S30A1A4S13G1A1A3S13S1A1A4A2A3S1dS16S9S44RaR9A2A1S17A3S1dS16S4eS1SeS2dA1S40RbRaA2A3S17A3S50S52Z2Z40A2S51S48G0S8R8PcA2A2S48G0S8R8PdA2A2A2A2S35S2fS3bRdRcRbRaA4S22S20RdRcA3R9R8R7A6S35S2fS3bReRdRcRbA4S43ReRdA2S3fRcRaA2R9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fst;FW;").
Proof.
  intros W st A Kc rho tp w HUS Wa Da Wb Fbo HOV H.
  set (rho1 := rho_ce A rho).
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HK & Htp & HU & HB & HN & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _). unfold IMG_LO, IMG_HI in TI, CI.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by reflexivity.
  assert (E10 : rw rho1 10%positive = rw rho 10%positive) by reflexivity.
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A))) by reflexivity.
  assert (E156 : rw rho1 156%positive = Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize)) by reflexivity.
  pose proof (urange (rw rho 12%positive)) as U12. pose proof (urange (rw rho 13%positive)) as U13.
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).

  assert (H1 : SPA segs (Jc W st A Kc) (Pre_callocI AE_A W st) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rho_ce_agree]; cbv; discriminate | apply JMc_agree; [exact HUS | apply rho_ce_agree]]. }
  clear H HsmA.

  assert (H2 : SPA segs (Jc W st A Kc) (mkAX (sa_c W st) [] base_sv) rho1 tp w).
  { change (mkAX (sa_c W st) [] base_sv) with (ax_setS (Pre_callocI AE_A W st) (sa_c W st)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HRest as (Hsep & _ & _ & _ & _ & _ & _ & HTH & HMI). unfold thread_inv in HTH. destruct HTH as [HTH HTS].
  rewrite maskv_out in HTH by (apply fs_footb_thread; [exact HG0 | lia]).

  destruct HMI as [HMIc _]. pose proof (Forall_inv (Forall_inv_tail HMIc)) as HPP.
  assert (HPP' : cell_ok (view segs (rm rho)) (mkACell (0 + 0xeb90d) 1 1)).
  { intros j Hj. specialize (HPP j Hj). cbn [c_addr c_w c_val] in HPP, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HPP; [exact HPP | apply fs_footb_img; [exact HG0 | lia]]. }

  pose proof (law_die A rho tp _ HA) as HDIE.
  assert (HDIE' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fbdc) 4 0)) by (rewrite Z.add_0_l; exact HDIE).

  pose proof (Forall_inv HMIc) as HMRN.
  assert (HMRN' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x170321) 1 1)).
  { intros j Hj. specialize (HMRN j Hj). cbn [c_addr c_w c_val] in HMRN, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HMRN; [exact HMRN | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HMIc))) as HCSD.
  assert (HCSD' : cell_ok (view segs (rm rho)) (mkACell (0 + 0x17fcd8) 4 0)).
  { intros j Hj. specialize (HCSD j Hj). cbn [c_addr c_w c_val] in HCSD, Hj |- *. rewrite Z.add_0_l.
    rewrite maskv_out in HCSD; [exact HCSD | apply fs_footb_img; [exact HG0 | lia]]. }
  pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
  pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
  assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn [ss_facts sa_c]; apply in_or_app; right; cbn; tauto).
  destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).

  assert (LNK : Forall (fun o => topG (aa_geom A) + 16 <= bv_unsigned (eval rho1 (ob_base o)) <= 2 ^ 47 /\ ob_lo o = SLit (-16) /\ ob_hi o = SLit 0)
                  (unwind_objs W)).
  { unfold unwind_objs. destruct W as [|l W']; [constructor|].
    assert (HC : Forall (holds rho1) (chain_pre (l :: W'))).
    { apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) HFa). cbn [ss_facts sa_c]. apply in_or_app. left.
      destruct st; [apply chain_pre_in; exact Hp | exact Hp]. }
    unfold chain_pre in HC. cbn [app] in HC.
    pose proof (Forall_inv HC) as C0. pose proof (Forall_inv (Forall_inv_tail HC)) as C1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HC))) as C2. do 3 apply Forall_inv_tail in HC.
    cbn [holds eval] in C0, C1, C2. rewrite u64_lit in C0 by lia. rewrite add_val, !u64_lit in C1 by lia. rewrite u64_lit in C2 by lia.
    pose proof (urange (rw rho1 10%positive)). rewrite Z.mod_small in C1 by lia.
    eapply Forall_impl; [|apply (chain_facts_bases rho1 (SVar 28) (l :: W') HC); cbn [eval]; lia].
    intros o (B & L & Hh). cbn [eval] in B. repeat split; try assumption; clear TI CI G15 G16 G17 G18 G19 G20 G21; lia. }

  assert (H3 : SPA segs (Jc W st A Kc) (mkAX (sb_o W st) [] base_sv) rho1 tp w).
  { change (mkAX (sb_o W st) [] base_sv) with
      (ax_setS (mkAX (sa_c W st) [] base_sv) (let S := ax_S (mkAX (sa_c W st) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (N_m1 ++ N_ovx)) (ss_facts S) NW2 (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      clear G15 G16 G17 G18 G19 G20 G21 TI CI.
      unfold N_ovx, N_m1, N_rest, N_fn, N_m5. unfold ERRNO_A. cbn [tl app]. unfold vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      all: match goal with
           | |- cells_in_view _ _ 0 [(0xeb90d, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0xeb90d 1 1 (SLit 1) HPP' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x170321, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x170321 1 1 (SLit 1) HMRN' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x17fbdc, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x17fbdc 4 0 (SLit 0) HDIE' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ 0 [(0x17fcd8, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               exact (civ_cell rho1 (rm rho) 0 0x17fcd8 4 0 (SLit 0) HCSD' eq_refl ltac:(lia) ltac:(lia))
           | |- cells_in_view _ _ (ag_thread _) [(3168, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil]; intros j Hj; replace j with 0%nat by lia;
               rewrite nth0_enc1_zero; cbn [Z.of_nat]; rewrite Z.add_0_r; rewrite <- view_in by lia; exact HTH
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156; civ_any2F HR
           | _ => idtac end.
      all: try match goal with
           | |- forall off, 3168 <= off < 3169 -> _ =>
               intros off Hoff; replace off with 3168 by lia; eapply wok_rd_off_image2;
               [lia | (pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia) |]; rewrite <- view_in by lia; exact HTH
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           | |- forall off, _ -> wok_of _ _ _ = true /\ _ =>
               intros off Hoff;
               first [ wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16)]; wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & _); unfold IMG_LO, IMG_HI in *; lia) ]
           end.
      all: fail "m_instantiate: carve obligation left".
    -
      unfold N_ovx, N_m1, N_rest, N_fn, N_m5. unfold ERRNO_A. cbn [tl app map carve_obj ss_objs ax_S sa_c]. unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      repeat (apply Forall_cons;
        [ apply Forall_cons;
          [ unfold ranges_disjoint; rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]);
            destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
          | apply Forall_app; split;
            [ eapply Forall_impl; [|exact LNK]; intros [ob olo ohi ocs od] (B & L & Hh); cbn [ob_base ob_lo ob_hi] in B, L, Hh; subst olo ohi;
              unfold ranges_disjoint; rewrite !obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; cbn [eval] in B; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 B G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ])
            | repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
              rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]) ] ]
        | ]).
      apply Forall_nil.
    -
      unfold N_ovx, N_m1, N_rest, N_fn, N_m5. unfold ERRNO_A. cbn [tl app map carve_obj pairwise_disjoint]. unfold carved, vT, vCTX, vTOP, vBOT, vSB, vRIS.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); cbn [fst snd eval]; rewrite ?E151, ?E152, ?u64_lit by (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]); (first [ clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 TI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 CI; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G15; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G16; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G17; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G18; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G19; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G20; lia | clear - G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo SW1 SW2 SW3 G21; lia | clear TI CI G15 G16 G17 G18 G19 G20 G21; lia | clear G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI; lia | lia ]). }
  clear H2.

  set (nv := U (nwc rho)) in *.
  assert (ENW : nwc rho = mul_div M_MUL (rw rho 12%positive) (rw rho 13%positive)) by reflexivity.
  assert (HNv : 1 <= nv < 2 ^ 39) by (unfold nv, nwc; exact HN).
  assert (E13 : rw rho1 13%positive = rw rho 13%positive) by reflexivity.
  assert (EP : eval rho1 PRODe = nwc rho).
  { unfold PRODe. cbn [eval]. rewrite E12, E13, ENW. apply mul_word_comm. }
  assert (EMH : U (eval rho1 MHe) <> 0).
  { unfold MHe. cbn [eval]. rewrite E12, E13. intros E0. apply mulhu_zero_iff in E0. lia. }
  assert (CS1 : 1 <= U (rw rho 12%positive) /\ 1 <= U (rw rho 13%positive)).
  { pose proof (urange (rw rho 12%positive)) as UU12. pose proof (urange (rw rho 13%positive)) as UU13. clear -HOV UU12 UU13. nia. }
  destruct CS1 as [C1 S1].
  change (P0o W st) with (ax_with_facts (mkAX (sb_o W st) [] base_sv) (FACTSo W st)).
  eapply SPA_refacts; [exact H3 | exact Fbo |].
  intros Hold. unfold FACTSo. apply Forall_app. split; [apply Forall_app; split; [apply Forall_app; split; [exact Hold|]|]|].
  - unfold F_geom_fn, vT, vCTX, vTOP, vBOT. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
  - unfold F_s1e, vSB, vRIS. unfold HIGH_SHADOW_END. rewrite kSpaceSize_val. clear TI CI G15 G16 G17 G18 G19 G20 G21.
    cbn [fst snd] in SW1, SW2. pose proof (urange (rw rho 10%positive)) as U10.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?EP; fold nv; cbn [eval]; rewrite ?E155, ?E156, ?E10; rewrite ?kSpaceSize_val; rewrite ?u64_lit by lia; try lia.
    +
      cbn [branch_taken]. unfold bv_eqb. rewrite add_val, !u64_lit by lia. rewrite Z.mod_small by lia. apply Z.eqb_refl.
    +
      intros E. cbn [branch_taken] in E. unfold bv_eqb in E. rewrite add_val in E. rewrite (u64_lit 0) in E by lia.
      replace (bv_unsigned (Z_to_bv 64 (-2136))) with (2 ^ 64 - 2136) in E by reflexivity.
      rewrite E10 in SW2. set (sp := bv_unsigned (rw rho 10%positive)) in *.
      replace (sp + (2 ^ 64 - 2136)) with ((sp - 2136) + 1 * 2 ^ 64) in E by lia.
      rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. apply Z.eqb_eq in E. lia.
  - unfold F_argo. repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
    + cbn [eval]. rewrite E12, u64_lit by lia. lia.
    + cbn [eval]. rewrite E13, u64_lit by lia. lia.
    + cbn [branch_taken]. unfold bv_eqb. cbn [eval] in EMH |- *. rewrite (u64_lit 0) by lia. intros E0. apply Z.eqb_eq in E0. exact (EMH E0).
Qed.
End CSPINEO.
End SpineCallocIo.

