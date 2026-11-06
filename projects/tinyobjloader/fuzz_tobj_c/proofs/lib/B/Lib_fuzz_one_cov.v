(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "SLit"; "SPUle"; "eval"; "SAlu"; "sv"; "valuation"; "sobj"; "sv_eqb"; "SVar"; "rw"; "SPBranch"; "soff"; "ss_facts"; "SPEq"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "sprop_eqb"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Init.Datatypes"; "cons"; "andb"; "bool"; "true"; "list"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_glue"; "vH"; "vG10"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_cov"; "has_objb"; "cov_chkb"; "cov_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "in_ranges"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CursorGlue"; "Zsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_one_ad"; "E_fa"; "E_fd"; "R_fa"; "R_fd"; "s_fa"; "s_fd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "V_TOP"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary SymObj SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SummaryA2 MemoFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_fuzz_iface2 Lib_fuzz_one_glue Lib_fuzz_one Lib_fuzz_one_ad.
Import ListNotations. Close Scope bv_scope. Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation U := bv_unsigned.

Definition has_objb (b lo hi : sv) (objs : list sobj) : bool := ltac2:(tb__ "0|0|
S33SdSdS21S21SeS16R1A1Vb;A2SeS18R1A1Vlo;A2A2SeS17R1A1Vhi;A2A2Lo;Vobjs;A3").
Lemma has_objb_sound : ltac2:(tb__ "0|3|
SbSbSbS24SdA1ScS1fQ40M0A1S1bS22S2aR6R5R4R3A4S23A3S1aS0S1S1dG0S9R3R7A2A2M1S12R3R6A2A2S1dG0R2A2M2A2S3G2S1G1S12R3R5A2A2A2A2S2eR4R5R3A3F_;F_;Fa;Frho;Fobjs;Fhi;Flo;Fb;").
Proof.
  intros b lo hi objs rho a H Hr. apply existsb_exists in H as (o & Ho & E). apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  exists o. split; [exact Ho|]. unfold obj_range, obj_lo_of, obj_hi_of. cbn [fst snd]. rewrite E1, E2, E3. exact Hr.
Qed.

Definition cov_facts : list sprop := ltac2:(tb__ "0|2|
S20S6S14SaS28SfPaA1M0S27A3SaS28S26S7Ze0A1A3A2S20S6S11S29S7N40A1S27A3S20S6S11S29S27S7N50A1A3S20S6S8SaS28S26S7Z120A1A3G0A2S20S6S8S7Z7fff7f807ff0A1S26A2S20S6S8S26S7Z7ffffffffe00A1A2S20S6S8SfP1eA1M1SaS28G0S7N8120A1A3A2S20S6S8G1S7Z7fffff800000A1A2S20S6S8S7Z7fff7f808120A1G0A2S20S6S8G0S7Z800000000000A1A2S25S6A1A3A3A3A3A3A3A3A3A3A3").
Definition cov_chkb (E : axst) (s : wsub) (R : list sobj) : bool := ltac2:(tb__ "0|3|
S21S21S21S21S34S6S6S33S6S19R1A1S13S31VE;A1A1A3Lf;S2cA3SeS2dVs;PaM0A2SaS28S26S7N80A1M1A3A2A2S2aS26G1S7Z0A1M2VR;A4A2S2aS26G2S7Ze0A1VR;A4A2S2aSfG0A1S27G2VR;A4A2").

Lemma U_add : ltac2:(tb__ "0|1|
ScSbSbS1bS1cS1dQ40M0S9R3SaS28R2R1A3A2A2S2S1S1dG0S9R3R2A2A2S1dG0S9R3R1A2A2A2S4Z2Z40A2A2A3Fb;Fa;Frho;").
Proof. intros rho a b. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned. unfold bv_wrap. reflexivity. Qed.
Lemma U_lit : ltac2:(tb__ "0|0|
ScS1cS1bS1cS1dQ40S9R2S7R1A1A2A2S2R1S4Z2Z40A2A2A3Fc;Frho;").
Proof. intros rho c. cbn [eval]. rewrite Z_to_bv_unsigned. unfold bv_wrap. reflexivity. Qed.

Lemma p64 : 2 ^ 64 = 18446744073709551616. Proof. reflexivity. Qed.
Lemma p47 : 2 ^ 47 = 140737488355328. Proof. reflexivity. Qed.
Lemma m_224 : 224 mod 18446744073709551616 = 224. Proof. reflexivity. Qed.
Lemma m_288 : 288 mod 18446744073709551616 = 288. Proof. reflexivity. Qed.
Lemma m_n64 : (-64) mod 18446744073709551616 = 18446744073709551552. Proof. reflexivity. Qed.
Lemma m_n80 : (-80) mod 18446744073709551616 = 18446744073709551536. Proof. reflexivity. Qed.
Lemma m_n128 : (-128) mod 18446744073709551616 = 18446744073709551488. Proof. reflexivity. Qed.
Lemma m_n33056 : (-33056) mod 18446744073709551616 = 18446744073709518560. Proof. reflexivity. Qed.
Lemma m_c1 : 140735332515824 mod 18446744073709551616 = 140735332515824. Proof. reflexivity. Qed.
Lemma m_c2 : 140737488354816 mod 18446744073709551616 = 140737488354816. Proof. reflexivity. Qed.
Lemma m_c3 : 140737479966720 mod 18446744073709551616 = 140737479966720. Proof. reflexivity. Qed.
Lemma m_c4 : 140735332516128 mod 18446744073709551616 = 140735332516128. Proof. reflexivity. Qed.
Lemma m_c5 : 140737488355328 mod 18446744073709551616 = 140737488355328. Proof. reflexivity. Qed.
Lemma zs_n64 : Zsigned 18446744073709551552 = -64. Proof. reflexivity. Qed.
Lemma zs_n80 : Zsigned 18446744073709551536 = -80. Proof. reflexivity. Qed.

Lemma cov_arith : ltac2:(tb__ "0|6|
S1cS1cS1cS1cS1aS0Z0R4A2S3R4Z10000000000000000M0A2A2M1G1G1G1S1bS1cS2S1R7R6A2G0A2S2S1R8Ze0M2A2G0A2A3S0S30R7A1N40A2S0N50S30R8A1A2S0S2S1RbZ120A2G0A2RaA2S0Z7fff7f807ff0RcA2S0RdZ7ffffffffe00A2S0RbS2S1RdZffffffffffff7ee0A2G0A2A2S0RcZ7fffff800000A2S0Z7fff7f808120RfA2S0R10Z800000000000M3A2S1aS0RfR11A2S1aS0S1RfZ800000A2G3A2S1aS1bS1cS2S1R12Zffffffffffffff80A2G0A2S5R12Z80A2M4A3S1aS1aS0Z643000G4A2S0G4R11A2A2S1aS1bS1cS1R11S30R10A1A2S1R12G2A2M5A3S0G5R11A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftop;Fug;Fsp;Fh;").
Proof.
  intros h sp ug top Hh Hsp Hug Htop E1 G1 G2 F4 F6 F7 F8 F9 F10 F11.
  destruct (Zsigned_spec ug) as [[A B]|[A B]]; rewrite B in *; [exfalso; clear - A G1 Hug; lia|].
  rewrite (Z.mod_small (h + 224)) in E1 by (clear - Hh F7; lia). rewrite (Z.mod_small (h + 288)) in F4 by (clear - Hh F7; lia).
  assert (X : sp + ug - 18446744073709551616 = (sp + ug) mod 18446744073709551616) by (apply Z.mod_unique_pos with (q := 1); clear - Hsp Hug G2 F10 F11; lia).
  assert (F8' : sp - 33056 = (sp + 18446744073709518560) mod 18446744073709551616) by (apply Z.mod_unique_pos with (q := 1); clear - Hsp F10 F11; lia).
  assert (E128 : h - 128 = (h + 18446744073709551488) mod 18446744073709551616) by (apply Z.mod_unique_pos with (q := 1); clear - Hh F6 F7; lia).
  rewrite <- F8' in F8. rewrite <- E128. rewrite <- X in E1. clear X F8' E128 B. lia.
Qed.

Theorem cov_sound : ltac2:(tb__ "0|4|
S32S2fS24SdA1ScScS1bS22S2bR5R4R3A3S23A3S35S6S15R2A1S13S31R6A1A1A3S3cS3dR4R3A3S1aS0S3eR5A1S1dQ40M0S10R5PaM1A2A2M2A2S1aS0S1S1dG0S10R5S40A2A2Z800000A2S4Z2Z2fA2A2S1aS1aS0S3fS1dG0S9R4S2dR7G1A2A2A2M3A2S0G3G2A2A2S1cS1aS0S1dG0S9R5S2dR8G1A2A2A2R1A2S3R1S1dG0S10R6G1A2A2A2A2S2eR6R8S1eG0R2A2A3F_;Fz;A2A2A2F_;F_;F_;Frho;Frho0;FR;Fs;FE;").
Proof.
  intros E s R rho0 rho Hc HF Hag.
  unfold cov_chkb in Hc. apply andb_prop in Hc as [Hc O3]. apply andb_prop in Hc as [Hc O2]. apply andb_prop in Hc as [Hc O1]. apply andb_prop in Hc as [Hfs Hs].
  apply sv_eqb_sound in Hs. rewrite Hs.
  assert (HX : forall f, In f cov_facts -> holds rho f).
  { intros f Hin. apply (holds_mem rho (ss_facts (ax_S E)) f HF). exact (proj1 (forallb_forall _ _) Hfs f Hin). }
  pose proof (HX _ (or_introl eq_refl)) as E1.
  pose proof (HX _ (or_intror (or_introl eq_refl))) as G1.
  pose proof (HX _ (or_intror (or_intror (or_introl eq_refl)))) as G2.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_introl eq_refl))))) as F4.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) as F6.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) as F7.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as F8.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as F9.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as F10.
  pose proof (HX _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as F11.
  clear HX Hfs HF.
  apply (proj1 (holds_bge _ _ _)) in G1. apply (proj1 (holds_bge _ _ _)) in G2.
  cbn [holds] in E1, F4, F6, F7, F8, F9, F10, F11. apply (f_equal U) in E1.
  unfold vH, vG10 in *. rewrite ?U_add, ?U_lit in *. cbn [eval] in *. rewrite p64 in *.
  rewrite ?m_224, ?m_288, ?m_n64, ?m_n80, ?m_n33056, ?m_c1, ?m_c2, ?m_c3, ?m_c4, ?m_c5, ?zs_n64, ?zs_n80 in *. rewrite m_n128.
  assert (E10 : rw rho0 10%positive = rw rho 10%positive) by (apply (proj1 Hag); unfold NF; lia).
  assert (E30 : rw rho0 30%positive = rw rho 30%positive) by (apply (proj1 Hag); unfold NF; lia).
  unfold T0. change Contract.V_TOP with 30%positive. change V_TOP with 30%positive. rewrite E10, E30. rewrite p47.
  pose proof (bv_unsigned_in_range _ (rw rho 100%positive)) as Rh. pose proof (bv_unsigned_in_range _ (rw rho 10%positive)) as Rsp.
  pose proof (bv_unsigned_in_range _ (rw rho 102%positive)) as Rg. pose proof (bv_unsigned_in_range _ (rw rho 30%positive)) as Rt.
  change (bv_modulus 64) with 18446744073709551616 in Rh, Rsp, Rg, Rt.
  destruct (cov_arith _ _ _ _ Rh Rsp Rg Rt E1 G1 G2 F4 F6 F7 F8 F9 F10 F11) as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite C3. unfold IMG_HI.
  split; [exact C1|]. split; [exact C2|]. split; [exact C4|].
  intros z Hz.
  assert (Uz : U (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. apply Z.mod_small. clear - Hz Rsp C4. lia. }
  destruct (Z_lt_ge_dec z (U (rw rho 100%positive))) as [Z1|Z1]; [|destruct (Z_lt_ge_dec z (U (rw rho 100%positive) + 224)) as [Z2|Z2]].
  - apply (has_objb_sound _ _ _ R rho _ O1). cbn [eval]. rewrite Uz, !soff_lit_small by (change (2 ^ 63) with 9223372036854775808; lia). clear - Hz Z1. lia.
  - apply (has_objb_sound _ _ _ R rho _ O2). cbn [eval]. rewrite Uz, !soff_lit_small by (change (2 ^ 63) with 9223372036854775808; lia). clear - Z1 Z2. lia.
  - apply (has_objb_sound _ _ _ R rho _ O3). cbn [eval]. rewrite Uz, soff_lit_small by (change (2 ^ 63) with 9223372036854775808; lia).
    unfold soff. cbn [eval]. rewrite bv_signed_U. clear - Hz Z2 C5. lia.
Qed.

Lemma cov_fd : ltac2:(tb__ "0|0|
S1bS22S2bS37S3bS39A3S23A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma cov_fa : ltac2:(tb__ "0|0|
S1bS22S2bS36S3aS38A3S23A3"). Proof. vm_cast_no_check (eq_refl true). Qed.
