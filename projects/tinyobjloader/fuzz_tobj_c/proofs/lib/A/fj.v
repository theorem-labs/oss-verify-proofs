(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require DrvPristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err e9.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.

(* [comment removed for export] *)
Module Icpt_region_full.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "bool"; "list"; "true"; "app"; "None"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "SPUle"; "SLit"; "sobj"; "valuation"; "SVar"; "holds"; "FcsrFrm0"; "mkSS"; "sprop_below"; "ss_facts"; "ss_next"; "SPEq"; "eval"; "SAlu"; "agree_below"; "cell"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "A_globals"; "SHB"; "mkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "pre_regs"; "setregs"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "leafA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_C0"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "add"; "beg"; "endd"; "base_facts"; "vB"; "O_rtc2"; "O_stk"; "X_rip"; "g_facts"; "g8"; "shp"; "stk_cells"; "vN"; "C0"; "HSE"; "KHME"; "M8"; "regs_C0"; "vL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "E_A"; "rdn"; "rup"; "Pre_rip"; "Pre_rip_lo"; "s_A"; "C0_0"; "FUELA"; "Pre_rip'"; "Pre_rip_lo'"; "hd"; "hu"; "F_A"; "d_facts"; "d_facts_lo"; "andm8"; "regs_EA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "ax_add_facts"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "baseZ"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "sub"; "mul"; "lt"; "pow"; "modulo"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub_id_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2 CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hi_facts : list sprop := ltac2:(tb__ "0|0|
S0SbSdSeS45A1S3bA2S2SbA1A3").
Definition lo_facts : list sprop := ltac2:(tb__ "0|0|
S0SbSdS37S3bS49A2SeS6aS1fZ8A2A1A2S2SbA1A3").
Definition Pre_of (cls : list sprop) : axst := ltac2:(tb__ "0|1|
S20S14S36S24S23S0SaS1ScA2M0S3S1ScUaS38A4S0G0S3S1ScUbS43A4S2G0A1A3A3A2S22S13S8ScA1S7SfS0SfS3dS2S1cA1A1S0SfS3cS2SfA1A3A3S1eA3S7SbVcls;S3aA3S21S9A9S3eA2").
Definition Pre_rip : axst := Pre_of hi_facts.
Definition Pre_rip_lo : axst := Pre_of lo_facts.

Definition d_facts : list sprop := ltac2:(tb__ "0|1|
S0SbSdS38SeS46A1M0A2S0SbSdS39G0A2S0SbSdS37S38SeZ7A1A2G0A2S2SbA1A3A3A3").
Definition d_facts_lo : list sprop := ltac2:(tb__ "0|1|
S0SbSdS38SeS6aS1fZ1A2A1M0A2S0SbSdS39G0A2S0SbSdS37S38SeZ7A1A2G0A2S2SbA1A3A3A3").
Definition Pre_rip' : axst := ax_add_facts d_facts Pre_rip.
Definition Pre_rip_lo' : axst := ax_add_facts d_facts_lo Pre_rip_lo.

Definition hu : sv := SVar 100.
Definition hd : sv := SVar 101.
Definition andm8 (e : sv) : sv := ltac2:(tb__ "0|0|
S1aS73Ve;SeS47A1A3").
Definition rup : sv := andm8 (add beg (SLit 7)).
Definition rdn : sv := andm8 endd.

Definition regs_EA : list sv := ltac2:(tb__ "0|1|
S24S23S0SaS1ScA2M0S3S1ScU1SeS35A1A4S0G0S3S1ScU2S37S11PaA1SeN40A1A2A4S0G0S3S1ScU5S11P67A1A4S0G0S3S1ScU8S38A4S0G0S3S1ScU9S43A4S0G0S3S1ScUaS41S54A1A4S0G0S3S1ScUbSeS1fA1A4S0G0S3S1ScUcS11P68A1A4S0G0S3S1ScUdS11P69A1A4S0G0S3S1ScUeS11P6aA1A4S0G0S3S1ScUfS11P6bA1A4S0G0S3S1ScU10S11P6cA1A4S0G0S3S1ScU11S11P6dA1A4S0G0S3S1ScU12S39A4S0G0S3S1ScU13S41S55A1A4S0G0S3S1ScU14S4bA4S0G0S3S1ScU15SeZf13f8A1A4S2G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A2").

Definition F_A : list sprop := ltac2:(tb__ "0|5|
S0SbS18S40S54A1M0S4bA2S0SbSdS54SeS6aS6dZ2Z3dA2Z1A2A1M1A2S0SbSdG0S4bA2S0SbSdS4bG0A2S0SbS18S40S55A1M2S4cA2S0SbSdS55G1A2S0SbSdG2S4cA2S0SbSdS4cG2A2S0SbSdS4bS39A2S0SbSdS39S37S4bSeZ7A1M3A2A2S0SbSdS3bS4bA2S0SbSdS4cS37S38G3A2M4A2S0SbSdG4S37S4cG3A2A2S0SbSdS3bS4cA2S2SbA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition E_A : axst := ltac2:(tb__ "0|0|
S20S14S35S5aS22S13S8ScA1S7SfS0SfS3dS42A1S0SfS3cS2SfA1A3A3S1eA3S7SbS56S3aA3P6eS9A9S3eA2").

Definition FUELA : nat := 400%nat.

Lemma echeck_ripA : ltac2:(tb__ "0|3|
S25S4S60S1dS51S0S28S35S2S28A1A3S21S0S5dS5eS52Z1SeZ0M0A1M1A3S2S5dA1M2A3S0S5dS5eS4aG0G1A3G2A3A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_ripA : ltac2:(tb__ "0|1|
S25S4S5fS1dS51S0S28S35S2S28A1A3S21S0S30S52S2S30A1M0A3S0S30S4aG0A3A6S6A3").
Proof. exact (check_cfgA_of_ecfgA segs FUELA [rip_C0] NF _ _ _ _ eq_refl eq_refl echeck_ripA). Qed.
Lemma echeck_ripA_lo : ltac2:(tb__ "0|3|
S25S4S60S1dS51S0S28S35S2S28A1A3S21S0S5dS5eS53Z1SeZ0M0A1M1A3S2S5dA1M2A3S0S5dS5eS4aG0G1A3G2A3A6S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma check_ripA_lo : ltac2:(tb__ "0|1|
S25S4S5fS1dS51S0S28S35S2S28A1A3S21S0S30S53S2S30A1M0A3S0S30S4aG0A3A6S6A3").
Proof. exact (check_cfgA_of_ecfgA segs FUELA [rip_C0] NF _ _ _ _ eq_refl eq_refl echeck_ripA_lo). Qed.

Definition C0_0 : axst := ltac2:(tb__ "0|0|
S20S14S35S48S22S13S8ScA1S7SfS0SfS3dS42A1S0SfS3cS2SfA1A3A3S1eA3S3aP89S9A9S3eA2").

Lemma C0_split : ltac2:(tb__ "0|0|
S25S30S61S3fS50A2S44A3").
Proof. reflexivity. Qed.

Definition s_A : wsub := ltac2:(tb__ "0|0|
S74S21S2fS4aA1S2fS50A1A3").
Lemma ent_A : ltac2:(tb__ "0|0|
S25S4S31S4aS50S4fA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma id_A : ltac2:(tb__ "0|0|
S25S4S72S4fS21A2S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma gf_below : ltac2:(tb__ "0|0|
S25S4S6fSbS15S17S2fS50A1A1A1S3fA3S6A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_A_vals : ltac2:(tb__ "0|0|
S25S5ScA1S34S29ScS70S4fA1S0S29P78S0S29P79S2S29A1A3A3A4S0ScS11P64A1S0ScS11P65A1S2ScA1A3A3A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma s_A_glob : ltac2:(tb__ "0|0|
S29S75R1S21A2S25ScS70S4fR2A2S11R2A1A3F_;Fv;").
Proof. intros v Hv. apply wsub_get_id with (g := NF); [exact id_A | exact Hv]. Qed.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma U_andm8 : ltac2:(tb__ "0|1|
S10ScS28S25S28S5cQ40M0S19R3R2A2A2R1A3S25S28S5cG0S19R4S59R3A1A2A2S6aR2S6eR2Z8A2A2A3F_;Fx;Fe;Frho;").
Proof.
  intros rho e x Hx. unfold andm8. rewrite (U_and_hmask rho e M8 8 eq_refl). rewrite Hx. reflexivity.
Qed.

Section GlueA.
Variable rho : valuation.
Let B := bv_unsigned (rw rho 15). Let L := bv_unsigned (rw rho 16). Let O := bv_unsigned (rw rho 17). Let N := bv_unsigned (rw rho 18).
Let u := bv_unsigned (rw rho 100). Let d := bv_unsigned (rw rho 101).

Lemma F_A_Z : ltac2:(tb__ "0|7|
S33SbS12Vrho;A1S7SbS56S3aA3A3S26S67Vrho;A1S26S6cVu;S6dZ2Z3dA2M0A2S26S6cVd;G0A2S26S26S69S68VB;VO;A2M1S6bZ8M2Vu;A2M3A2S69G3S68G1Z7M4A2A2A2S26S26S69S6bG2Vd;A2M5S68G1VN;A2M6A2S69G6S68G5G4A2A2A2S27S28S28S25S28VB;S6bG2R1A2A3Lk;A2A2A2A2A2A2F_;").
Proof.
  intros HF. apply Forall_app in HF as [HA HB].
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 18)) as R18. pose proof (urange (rw rho 100)) as R100. pose proof (urange (rw rho 101)) as R101.

  have_fact A1 HB (SPUle (add vO vN) vL). have_fact A2 HB (SPUle vL (SLit (2 ^ 40))). have_fact A3 HB (SPUle (SLit 1) vN).
  have_fact A4 HB (SPUle (SLit 4096) vB). have_fact A5 HB (SPUle (add vB vL) (SLit (2 ^ 47 - 8))).
  have_fact A6 HB (SPUle vO vL). have_fact A7 HB (SPUle vN vL). have_fact A8 HB (SPUle vB (SLit (2 ^ 47 - 8))).
  have_fact A9 HB (SPAlign 15 3).
  unfold vB, vL, vO, vN, add in A1, A2, A3, A4, A5, A6, A7, A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho 1) in A3 by lia.
  rewrite (U_lit64 rho 4096) in A4 by lia.
  pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as TA. rewrite TA in A5. rewrite TA in A8.
  cbn [eval] in A2, A3, A4, A6, A7, A8. unfold HSE, ACEIL in A4, A5, A8.
  assert (B1718 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 18) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1718) in A1.
  assert (B1516 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B1516) in A5.

  assert (Ebeg : UU rho beg = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17)).
  { unfold beg, add, vB, vO. apply U_add2; [reflexivity | reflexivity | lia]. }
  assert (Ebeg7 : UU rho (add beg (SLit 7)) = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7).
  { unfold add at 1. apply (U_addc rho beg 7 _ Ebeg); lia. }
  assert (Eend : UU rho endd = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  { unfold endd, add at 1. apply U_add2; [reflexivity | exact Ebeg | lia]. }
  pose proof (U_andm8 rho _ _ Ebeg7) as Erup. pose proof (U_andm8 rho _ _ Eend) as Erdn.
  fold (andm8 (add beg (SLit 7))) in Erup. fold rup in Erup. fold (andm8 endd) in Erdn. fold rdn in Erdn.

  have_fact G1 HA (SPUle hd (SLit (2 ^ 61 - 1))). have_fact G2 HA (SPUle (g8 hd) rdn). have_fact G3 HA (SPUle rdn (g8 hd)).
  have_fact G4 HA (SPUle hu (SLit (2 ^ 61 - 1))). have_fact G5 HA (SPUle (g8 hu) rup). have_fact G6 HA (SPUle rup (g8 hu)).
  unfold hd in G1, G2, G3. unfold hu in G4, G5, G6.
  pose proof (U_lit64 rho (2 ^ 61 - 1) ltac:(lia)) as TL. rewrite TL in G1. rewrite TL in G4. cbn [eval] in G1, G4.
  assert (Hu : bv_unsigned (rw rho 100) < 2 ^ 61) by lia. assert (Hd : bv_unsigned (rw rho 101) < 2 ^ 61) by lia.
  rewrite (U_g8 rho 101 Hd) in G2, G3. rewrite (U_g8 rho 100 Hu) in G5, G6.
  rewrite Erdn in G2, G3. rewrite Erup in G5, G6.
  pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7) 8 ltac:(lia)) as M1.
  pose proof (Z.mod_pos_bound (bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))) 8 ltac:(lia)) as M2.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7) 8 ltac:(lia)) as D1.
  pose proof (Z.div_mod (bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))) 8 ltac:(lia)) as D2.
  destruct A9 as [_ A9]. change (2 ^ 3) with 8 in A9.
  unfold baseZ. subst B L O N u d. unfold HSE, ACEIL. cbv zeta. cbn [eval] in A1.
  split; [repeat split; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  exists (bv_unsigned (rw rho 15) / 8). pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)). lia.
Qed.

Lemma glue_A : ltac2:(tb__ "0|0|
S33SbS12Vrho;A1S16S2fS4aA1A1A3S33SbS12S71Vrho;S4fA2A1S3fA3F_;").
Proof.
  intros HF. cbn [ax_S ss_facts E_A mkA] in HF.
  destruct (F_A_Z HF) as ((Z1 & Z2 & Z3 & Z4 & Z5) & Hu & Hd & [U1 U2] & [D1 D2] & [k Hk]).
  unfold HSE, ACEIL in Z1, Z2, Z3, Z4, Z5.
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 18)) as R18. pose proof (urange (rw rho 100)) as R100. pose proof (urange (rw rho 101)) as R101.
  assert (W120 : wsub_get s_A 120 = SVar 100) by (pose proof s_A_vals as V; cbn [map] in V; congruence).
  assert (W121 : wsub_get s_A 121 = SVar 101) by (pose proof s_A_vals as V; cbn [map] in V; congruence).
  set (rho' := rho_sub rho s_A).
  assert (E15 : rw rho' 15 = rw rho 15) by (subst rho'; rewrite rw_sub, (s_A_glob 15 ltac:(reflexivity)); reflexivity).
  assert (E16 : rw rho' 16 = rw rho 16) by (subst rho'; rewrite rw_sub, (s_A_glob 16 ltac:(reflexivity)); reflexivity).
  assert (E17 : rw rho' 17 = rw rho 17) by (subst rho'; rewrite rw_sub, (s_A_glob 17 ltac:(reflexivity)); reflexivity).
  assert (E18 : rw rho' 18 = rw rho 18) by (subst rho'; rewrite rw_sub, (s_A_glob 18 ltac:(reflexivity)); reflexivity).
  assert (E120 : rw rho' 120 = rw rho 100) by (subst rho'; rewrite rw_sub, W120; reflexivity).
  assert (E121 : rw rho' 121 = rw rho 101) by (subst rho'; rewrite rw_sub, W121; reflexivity).

  assert (Ebeg : UU rho' beg = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17)).
  { unfold beg, add, vB, vO. apply U_add2; [cbn [eval]; rewrite E15; reflexivity | cbn [eval]; rewrite E17; reflexivity | lia]. }
  assert (Ebeg7 : UU rho' (add beg (SLit 7)) = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7).
  { unfold add at 1. apply (U_addc rho' beg 7 _ Ebeg); lia. }
  assert (Eend : UU rho' endd = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  { unfold endd. unfold add at 1. apply U_add2; [unfold vN; cbn [eval]; rewrite E18; reflexivity | exact Ebeg | lia]. }
  assert (Eend7 : UU rho' (add endd (SLit (-7))) = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17)) + (-7)).
  { unfold add at 1. apply (U_addc rho' endd (-7) _ Eend); lia. }
  assert (Egu : UU rho' (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gu) = 8 * bv_unsigned (rw rho 100)).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gu. rewrite U_g8; rewrite E120; [reflexivity | lia]. }
  assert (Egd : UU rho' (g8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gd) = 8 * bv_unsigned (rw rho 101)).
  { unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gd. rewrite U_g8; rewrite E121; [reflexivity | lia]. }
  assert (EBL : UU rho' (add vB vL) = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16)).
  { unfold add, vB, vL. apply U_add2; [cbn [eval]; rewrite E15; reflexivity | cbn [eval]; rewrite E16; reflexivity | lia]. }
  assert (Egu37 : UU rho' (add OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gu (SLit (2 ^ 37))) = bv_unsigned (rw rho 100) + 2 ^ 37).
  { unfold add, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gu. apply (U_addc rho' (SVar 120) (2 ^ 37) (bv_unsigned (rw rho 100))); [cbn [eval]; rewrite E120; reflexivity | lia | lia]. }
  unfold g_facts.
  constructor. { cbn [holds]. rewrite Ebeg, Egu. lia. }
  constructor. { cbn [holds]. rewrite Egu, Ebeg7. lia. }
  constructor. { cbn [holds]. rewrite Egd, Eend. lia. }
  constructor. { cbn [holds]. rewrite Eend7, Egd. lia. }
  constructor. { cbn [holds]. rewrite Egu. change (eval rho' vB) with (rw rho' 15). rewrite E15. lia. }
  constructor. { cbn [holds]. rewrite Egd. change (eval rho' vB) with (rw rho' 15). rewrite E15. nia. }
  constructor. { cbn [holds]. rewrite Egd, EBL. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' (2 ^ 61 - 1)) by lia. change (eval rho' OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gu) with (rw rho' 120). rewrite E120. lia. }
  constructor. { cbn [holds]. rewrite (U_lit64 rho' (2 ^ 61 - 1)) by lia. change (eval rho' OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gd) with (rw rho' 121). rewrite E121. lia. }
  constructor. { cbn [holds]. rewrite Egu37. change (eval rho' OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.gd) with (rw rho' 121). rewrite E121. lia. }
  constructor.
Qed.
End GlueA.

Lemma d_facts_below : ltac2:(tb__ "0|0|
S25S4S6fSbS15S17S2fS4dA1A1A1S57A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma d_facts_Z : ltac2:(tb__ "0|0|
S10S33SbS12R1A1S16S2fS4dA1A1A3S33SbS12R2A1S57A3F_;Frho;").
Proof.
  intros rho HB. cbn [ax_S ss_facts Pre_rip Pre_of mkA] in HB. apply Forall_app in HB as [_ HB].
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 18)) as R18.
  have_fact A1 HB (SPUle (add vO vN) vL). have_fact A3 HB (SPUle (SLit 1) vN).
  have_fact A5 HB (SPUle (add vB vL) (SLit (2 ^ 47 - 8))). have_fact A6 HB (SPUle vO vL).
  have_fact A2 HB (SPUle vL (SLit (2 ^ 40))). have_fact A7 HB (SPUle vN vL). have_fact A8 HB (SPUle vB (SLit (2 ^ 47 - 8))).
  unfold vB, vL, vO, vN, add in A1, A3, A5, A6, A2, A7, A8.
  rewrite (U_lit64 rho 1) in A3 by lia. pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as TA. rewrite TA in A5. rewrite TA in A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia.
  cbn [eval] in A3, A6, A2, A7, A8.
  assert (B1718 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 18) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1718) in A1.
  cbn [eval] in A1.
  assert (B1516 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B1516) in A5.
  assert (Ebeg : UU rho beg = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17)).
  { unfold beg, add, vB, vO. apply U_add2; [reflexivity | reflexivity | lia]. }
  assert (Ebeg7 : UU rho (add beg (SLit 7)) = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7).
  { unfold add at 1. apply (U_addc rho beg 7 _ Ebeg); lia. }
  assert (Eend : UU rho endd = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  { unfold endd. unfold add at 1. apply U_add2; [reflexivity | exact Ebeg | lia]. }
  pose proof (U_lit64 rho KHME ltac:(unfold KHME; lia)) as TK.
  unfold d_facts. unfold KHME in *.
  constructor. { cbn [holds]. rewrite Ebeg, TK. lia. }
  constructor. { cbn [holds]. rewrite Eend, TK. lia. }
  constructor. { cbn [holds]. rewrite Ebeg7, TK. lia. }
  constructor.
Qed.

Lemma SPA_Pre' : ltac2:(tb__ "0|0|
S2bS10S5S5bQ40A1A1S63S2aS1dR4S4dR3R2R1A6S2aS1dR5S52R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w [Hsm Hk]. split; [|exact Hk].
  apply smatchA_add_facts; [exact Hsm | | exact d_facts_below].
  apply d_facts_Z. eapply smatchA_facts. exact Hsm.
Qed.

Lemma d_facts_lo_below : ltac2:(tb__ "0|0|
S25S4S6fSbS15S17S2fS4eA1A1A1S58A3S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma d_facts_lo_Z : ltac2:(tb__ "0|0|
S10S33SbS12R1A1S16S2fS4eA1A1A3S33SbS12R2A1S58A3F_;Frho;").
Proof.
  intros rho HB. cbn [ax_S ss_facts Pre_rip_lo Pre_of mkA] in HB. apply Forall_app in HB as [HL HB].
  pose proof (urange (rw rho 15)) as R15. pose proof (urange (rw rho 16)) as R16. pose proof (urange (rw rho 17)) as R17.
  pose proof (urange (rw rho 18)) as R18.
  have_fact A1 HB (SPUle (add vO vN) vL). have_fact A3 HB (SPUle (SLit 1) vN).
  have_fact A6 HB (SPUle vO vL). have_fact A2 HB (SPUle vL (SLit (2 ^ 40))). have_fact A7 HB (SPUle vN vL).
  have_fact A8 HB (SPUle vB (SLit (2 ^ 47 - 8))).
  have_fact AL HL (SPUle (add vB vL) (SLit (SHB - 8))).
  unfold vB, vL, vO, vN, add in A1, A3, A6, A2, A7, A8, AL.
  rewrite (U_lit64 rho 1) in A3 by lia. pose proof (U_lit64 rho (2 ^ 47 - 8) ltac:(lia)) as TA. rewrite TA in A8.
  rewrite (U_lit64 rho (2 ^ 40)) in A2 by lia. rewrite (U_lit64 rho (SHB - 8)) in AL by (unfold SHB; lia).
  cbn [eval] in A3, A6, A2, A7, A8.
  assert (B1718 : 0 <= bv_unsigned (rw rho 17) + bv_unsigned (rw rho 18) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 17) (SVar 18) (bv_unsigned (rw rho 17)) (bv_unsigned (rw rho 18)) eq_refl eq_refl B1718) in A1.
  cbn [eval] in A1.
  assert (B1516 : 0 <= bv_unsigned (rw rho 15) + bv_unsigned (rw rho 16) < 2 ^ 64) by lia.
  rewrite (U_add2 rho (SVar 15) (SVar 16) (bv_unsigned (rw rho 15)) (bv_unsigned (rw rho 16)) eq_refl eq_refl B1516) in AL.
  assert (Ebeg : UU rho beg = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17)).
  { unfold beg, add, vB, vO. apply U_add2; [reflexivity | reflexivity | lia]. }
  assert (Ebeg7 : UU rho (add beg (SLit 7)) = bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17) + 7).
  { unfold add at 1. apply (U_addc rho beg 7 _ Ebeg); lia. }
  assert (Eend : UU rho endd = bv_unsigned (rw rho 18) + (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  { unfold endd. unfold add at 1. apply U_add2; [reflexivity | exact Ebeg | lia]. }
  pose proof (U_lit64 rho (SHB - 1) ltac:(unfold SHB; lia)) as TK.
  unfold d_facts_lo. unfold SHB in *.
  constructor. { cbn [holds]. rewrite Ebeg, TK. lia. }
  constructor. { cbn [holds]. rewrite Eend, TK. lia. }
  constructor. { cbn [holds]. rewrite Ebeg7, TK. lia. }
  constructor.
Qed.

Lemma SPA_Pre_lo' : ltac2:(tb__ "0|0|
S2bS10S5S5bQ40A1A1S63S2aS1dR4S4eR3R2R1A6S2aS1dR5S53R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w [Hsm Hk]. split; [|exact Hk].
  apply smatchA_add_facts; [exact Hsm | | exact d_facts_lo_below].
  apply d_facts_lo_Z. eapply smatchA_facts. exact Hsm.
Qed.

Lemma LQA_unG : ltac2:(tb__ "0|0|
S2bS29S10S10S5S5bQ40A1A1S5S32A1S63S2cS1dS62S10S1bR7R6R1A3Lr;R7A2R6R4R3R2R1A7S2cS1dR8R7R6R4R3R2A7F_;Fw;Fposts;Ftp;FrhoX;Frho;Fn;FJ;").
Proof.
  intros J n rho rhoX tp posts w (L & rho'' & Hin & _ & Hsm & [Hag Hk]). exists L, rho''. auto.
Qed.

Theorem region_sum : ltac2:(tb__ "0|0|
S63OF_;S2bS10S5S5bQ40A1A1S2eS1dR4R3A3S2dS1dS21R4A3S65S1dR6S2aS1dR5S4dR4R3A5S2cS1dR5S21R4R3S66A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  set (J' := withGA (fun r => agree_below NF rho r) J).
  assert (HokG : ok_frameA segs ok J') by (intros r t tr ms md msv' [_ HJ]; eapply Hok; eauto).
  assert (HstG : stableA segs NF J').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_rip' rho tp w (SPA_Pre' J rho tp w Hw)) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELA [rip_C0] NF [Pre_rip'] [E_A] J' ok (LQA segs J NF rho tp Posts_rip) tp HokG HstG check_ripA);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  eapply triple_conseq; [ | intros w Hw; right; exact Hw | ].
  { intros w Hw. exact (SPA_entails_sem segs J' NF E_A C0_0 g_facts s_A rhoE tp w ent_A id_A HstG gf_below
                         (fun r _ _ _ _ HF => glue_A r HF) Hw). }
  rewrite C0_split.
  eapply triple_conseq; [intros w Hw; exact Hw | | exact (region_B_sum ok J' (rho_sub rhoE s_A) tp HokG HstG)].
  intros w Hw. exact (LQA_unG J NF rho _ tp Posts_rip w Hw).
Qed.

Theorem region_sum_ex : ltac2:(tb__ "0|0|
S2bS10S5S5bQ40A1A1S2dS1dS21R3A3S64S1dS2aS1dR4S4dR3R2A5S2cS1dR4S21R3R2S66A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  set (J' := withGA (fun r => agree_below NF rho r) J).
  assert (HstG : stableA segs NF J').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_rip' rho tp w (SPA_Pre' J rho tp w Hw)) | intros w Hw; exact Hw |].
  change Pre_rip' with (vna_state (mkVNA Pre_rip' 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELA [rip_C0] NF [mkVNA Pre_rip' 1 (SLit 0)] [mkVNA E_A 0 (SLit 0)] J'
           (LQA segs J NF rho tp Posts_rip) tp HstG);
    [intros n [<-|[]]; cbv; congruence | exact echeck_ripA | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  eapply etriple_conseq; [ | intros w Hw; right; exact Hw | ].
  { intros w Hw. exact (SPA_entails_sem segs J' NF E_A C0_0 g_facts s_A rhoE tp w ent_A id_A HstG gf_below
                         (fun r _ _ _ _ HF => glue_A r HF) Hw). }
  rewrite C0_split.
  eapply etriple_conseq; [intros w Hw; exact Hw | | exact (region_B_sum_ex J' (rho_sub rhoE s_A) tp HstG)].
  intros w Hw. exact (LQA_unG J NF rho _ tp Posts_rip w Hw).
Qed.

Theorem region_sum_lo : ltac2:(tb__ "0|0|
S63OF_;S2bS10S5S5bQ40A1A1S2eS1dR4R3A3S2dS1dS21R4A3S65S1dR6S2aS1dR5S4eR4R3A5S2cS1dR5S21R4R3S66A6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  set (J' := withGA (fun r => agree_below NF rho r) J).
  assert (HokG : ok_frameA segs ok J') by (intros r t tr ms md msv' [_ HJ]; eapply Hok; eauto).
  assert (HstG : stableA segs NF J').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_rip_lo' rho tp w (SPA_Pre_lo' J rho tp w Hw)) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUELA [rip_C0] NF [Pre_rip_lo'] [E_A] J' ok (LQA segs J NF rho tp Posts_rip) tp HokG HstG check_ripA_lo);
    [| left; reflexivity].
  intros E rhoE [<-|[]].
  eapply triple_conseq; [ | intros w Hw; right; exact Hw | ].
  { intros w Hw. exact (SPA_entails_sem segs J' NF E_A C0_0 g_facts s_A rhoE tp w ent_A id_A HstG gf_below
                         (fun r _ _ _ _ HF => glue_A r HF) Hw). }
  rewrite C0_split.
  eapply triple_conseq; [intros w Hw; exact Hw | | exact (region_B_sum ok J' (rho_sub rhoE s_A) tp HokG HstG)].
  intros w Hw. exact (LQA_unG J NF rho _ tp Posts_rip w Hw).
Qed.

Theorem region_sum_lo_ex : ltac2:(tb__ "0|0|
S2bS10S5S5bQ40A1A1S2dS1dS21R3A3S64S1dS2aS1dR4S4eR3R2A5S2cS1dR4S21R3R2S66A6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  set (J' := withGA (fun r => agree_below NF rho r) J).
  assert (HstG : stableA segs NF J').
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_rip_lo' rho tp w (SPA_Pre_lo' J rho tp w Hw)) | intros w Hw; exact Hw |].
  change Pre_rip_lo' with (vna_state (mkVNA Pre_rip_lo' 1 (SLit 0))).
  apply (cfg_complete_autoA segs FUELA [rip_C0] NF [mkVNA Pre_rip_lo' 1 (SLit 0)] [mkVNA E_A 0 (SLit 0)] J'
           (LQA segs J NF rho tp Posts_rip) tp HstG);
    [intros n [<-|[]]; cbv; congruence | exact echeck_ripA_lo | | left; reflexivity].
  intros E rhoE [<-|[]]. cbn [vna_state].
  eapply etriple_conseq; [ | intros w Hw; right; exact Hw | ].
  { intros w Hw. exact (SPA_entails_sem segs J' NF E_A C0_0 g_facts s_A rhoE tp w ent_A id_A HstG gf_below
                         (fun r _ _ _ _ HF => glue_A r HF) Hw). }
  rewrite C0_split.
  eapply etriple_conseq; [intros w Hw; exact Hw | | exact (region_B_sum_ex J' (rho_sub rhoE s_A) tp HstG)].
  intros w Hw. exact (LQA_unG J NF rho _ tp Posts_rip w Hw).
Qed.
End Icpt_region_full.

(* [comment removed for export] *)
Module StartWit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement"; "gw_sizes"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Datatypes"; "prod"; "list"; "length"; "app"; "cons"; "nat"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "lt"; "modulo"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "Model"; "vm_maps"; "vm_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "init_sp_ok"; "mmap_place_ok_none"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA GlueA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Init Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Start8M.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Start8M.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma gw_sizes_app : ltac2:(tb__ "0|3|
S6S5S12Q40A1M0G0A2M1A1M2G2S0S4S3S8G1R2R1A3A1SdS3R2A1S3R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. induction l1 as [|[b s] l1 IH]; cbn [gw_sizes List.app]; [lia|]. cbn [snd]. rewrite IH. lia. Qed.

Lemma gw_sizes_cons : ltac2:(tb__ "0|3|
S12Q40M0A1M1G1S6S5G1G1A2M2A1S0S4S3S9G2SbG1G1R3R2A4R1A3A1SdS14G0R2A2S3R1A1A2A3Fl;Fs;Fb;").
Proof. intros. reflexivity. Qed.

Lemma gw_sizes_segsA : ltac2:(tb__ "0|2|
S1S0S4S3S19S1aA1M0A1Z636000A3S0SaS7S5S12Q40A1M1G1A2G0A2U4A3A2").
Proof. rewrite segments_reserved_A. cbn [gw_sizes length snd]. rewrite !u64_of_lit by lia. split; reflexivity. Qed.

Theorem place_witness : ltac2:(tb__ "0|6|
S16S6S5S12Q40M0A1M1G1A2M2A1M3S4S4S0G3S18S15R4A1A1S19S1aA1A3S0G3S17S15R5A1A1R4A3S1bS15R6A1A1SfZ0M4R5A2S0S4S10R6Z1000A2G4A3ScR7SeZ2M5Z26A2A2ScS3R9A1R7A2ScR8SeG5Z2dA2A2ScS11S7G2RbA2A1Z40A2S2G1G1S1cS13G0G4A2ReS13G0RcA2R1A4La;A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftot;Flen;FL;Fmd;").
Proof.
  intros md L len tot HR HM HT Hpos Hal Hlen Htot Htot2 Hcnt.
  pose proof gw_sizes_segsA as [GS GL].
  destruct (free_gap_below_top (m_vmmaps md) len 0x10007fff8000 (0x636000 + tot) HT ltac:(lia) ltac:(reflexivity) ltac:(lia)) as (g & Gal & Gfl & Gc & Gtop & Gfree).
  { rewrite HR, HM, gw_sizes_app, GS. lia. }
  { rewrite HR, HM, length_app, GL, Nat2Z.inj_add. change (Z.of_nat 4) with 4. unfold alloc_ceiling_lo. nia. }
  exists (Z_to_bv 64 g). unfold alloc_ceiling_lo in Gc. unfold page_size in Gal.
  destruct (mmap_nZ_of_pages len Hpos Hal ltac:(lia)) as [NZ Nn].
  unfold mmap_place_ok_none. rewrite NZ, Nn, u64_of_lit by lia. unfold page_size.
  split; [exact Gal|]. split; [lia|]. split; [exact Gtop|]. exact Gfree.
Qed.
End StartWit.

(* [comment removed for export] *)
Module DrvFwStates.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nat"; "true"; "bool"; "nil"; "list"; "option"; "Some"; "app"; "prod"; "pair"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "SLit"; "sstate"; "ss_next"; "ss_objs"; "ss_facts"; "ss_pc"; "sprop"; "swf"; "ss_lenient"; "cell"; "mkObj"; "ss_regs"; "DList"; "DRom"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_resv"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "ax_S"; "axst"; "sym_runA"; "ax_base"; "mkLeafA"; "ax_X"; "entailsA"; "la_state"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.DrvFwStates"; "CUTS_FW"; "FUEL_FW"; "O_b1z"; "app_obj"; "S4_1"; "S4_2"; "S4_3"; "s_1"; "s_2"; "s_3"; "O_b2r"; "W_1"; "W_2"; "W_3"; "F_1"; "F_2"; "F_3"; "G3_1"; "G3_2"; "G3_3"; "Tf_1"; "Tf_2"; "Tf_3"; "C_1"; "C_2"; "C_3"; "Cs_1"; "Cs_2"; "Cs_3"; "G1_1"; "G1_2"; "G1_3"; "R_1"; "R_2"; "R_3"; "T_1"; "T_2"; "T_3"; "XS1"; "XS2"; "axc"; "obindW"; "splits_fw"; "sp_1"; "sp_2"; "sp_3"; "G2_1"; "G2_2"; "G2_3"; "junk_fw"; "leaf1W"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "facts_fw"; "Pre_fw"; "EBUF"; "fw_ret"; "MSGB"; "P_fw"; "objs_farW"; "xblk"; "FERR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err.WLerrS"; "Pre_wl1"; "D"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "XMerge"; "XSelect"; "XRebase"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "SHB"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ReprGlue"; "state_nolist"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.DrvPristine"; "rom_bytes_ok"; "@Stdlib.PArith.BinPos.Pos"; "add"; "of_nat"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform DrvPristine.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Musl_wl_err.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Musl_wl_err OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition leaf1W (A : axst) (o : option (list leafA)) : axst := ltac2:(tb__ "0|1|
S8S7S24A1M0A1S26Lo;Vo;G0G0S26Ll0;R1VA;S24G0G0S26Ll1;R1S2cR2A1S24G0VA;Ll3;Ll2;X7x2Ll1;Ll;X7x2Ll0;VA;X8x2").
Definition run_toW (fuel : nat) (cuts : list Z) (A : axst) : axst := ltac2:(tb__ "0|0|
S61VA;S27S2eVfuel;Vcuts;VA;S4A5A2").
Definition CUTS_FW : list Z := ltac2:(tb__ "0|0|
S2S23Zd9ad4S2S23S68S6S23A1A3A3").
Definition FUEL_FW : nat := 1200%nat.

Definition obindW {A B} (o : option A) (f : A -> option B) : option B :=
  match o with Some x => f x | None => None end.
Definition app_obj (S : sstate) (o : sobj) : sstate := ltac2:(tb__ "0|0|
S1eS15VS;A1S1bVS;A1S20VS;A1S1fVS;A1S21VS;A1SaSeS13VS;A1S2SeVo;S6SeA1A3A3S14VS;A1S12VS;A1S18VS;A1A9").

Definition O_b1z : sobj := ltac2:(tb__ "0|1|
S1aS10S67A1S10Z0A1M0G0S6S19A1S1cP5A1A5").
Definition O_b2r (msg len : Z) : sobj := ltac2:(tb__ "0|0|
S1aS10Vmsg;A1S10Z0A1S10Vlen;A1S6S19A1S1dP6A1A5").

Definition splits_fw (S : sstate) : option sstate := ltac2:(tb__ "0|0|
S58S11S11S7eVS;U0S10N8f8A1A3S11S58S11S11S7eR1U1S10N8d8A1A3S11S58S11S11S7eR1U3S10S7aS6dZ78A2A1A3S11S7eR1U4S10S7aS6dZ7cA2A1A3LS3;A4LS2;A4LS1;A4").
Definition wl1_sub_head (msg len : Z) : wsub := ltac2:(tb__ "0|1|
S2SbS22SfA2M0ScS22SfPcS10S67A1A4S2G0ScS22SfPdS10Z0A1A4S2G0ScS22SfPeS10Vmsg;A1A4S2G0ScS22SfPfS10Vlen;A1A4S6G0A1A3A3A3A3").

Definition XS1 : list xform := ltac2:(tb__ "0|0|
S2S70S73S2S3U0S2S3U3S2S3U4S2S3U5S2S3U6S2S3U7S2S3U8S2S3U9S2S3UaS2S3UbS2S3UcS2S3U1S2S3U2S6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A1S6S70A1A3").
Definition XS2 : list xform := ltac2:(tb__ "0|4|
S2S70S74U0M0A1S2S70S73S2S3U2S2S3G0S2S3U3S2S3U4S2S3U1M1S2S3U5S2S3U6S2S3U7S2S3U8S2S3U9S2S3UaS6S3A1A3A3A3A3A3A3A3A3A3A3A3A1S2S70S72G0A1M2S2S70G2S2S70S72G1A1M3S2S70G3S6S70A1A3A3A3A3A3A3").
Definition drop2 (S : sstate) : sstate := ltac2:(tb__ "0|0|
S78VS;S7bSeUbS13VS;A1A3A2").
Definition axc (S : sstate) : axst := ltac2:(tb__ "0|0|
S2dVS;S6SbSfSfA2A1S10S75A1A3").
Definition junk_fw : list nat := ltac2:(tb__ "0|0|
S2S3U5S2S3U6S2S3U7S2S3UbS2S3UcS2S3UdS2S3UeS2S3UfS2S3U10S2S3U11S2S3U1cS2S3U1dS2S3U1eS2S3U1fS6S3A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition post_sub_fw (S : sstate) : wsub := ltac2:(tb__ "0|0|
S7cS3SbS22SfA2S3ScS22SfS84P64S85R1A1A2S7dSfR1S1bVS;A1S10Z0A1A4A4Lr;S60A4").

Definition runW_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS66Z21441Z1fA2S4A5").
Local Strategy expand [runW_1__R].
Definition W_1 : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => ((leaf1W (Pre_fw 136257 31) (ro1__)))) runW_1__R).
Lemma runW_1 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS66Z21441Z1fA2S4A5S9G0S2S24S29S3aS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runW_1__R <: runW_1__R = Some [mkLeafA W_1 RsCut]). Qed.
Definition S4_1 : sstate := Eval vm_compute in (match splits_fw (ax_S W_1) with Some s => s | None => ax_S W_1 end).
Lemma splits_1 : ltac2:(tb__ "0|0|
S0S8S11A1S59S25S3aA1A1S9S11S33A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Cs_1 : sstate := Eval vm_compute in (app_obj (app_obj S4_1 O_b1z) (O_b2r 136257 31)).
Lemma finish_1 : ltac2:(tb__ "0|0|
S0S11S32S32S33S31A2S39Z21441Z1fA2A2S49A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_1 : axst := ax_setS W_1 Cs_1.
Definition s_1 : wsub := Eval vm_compute in (wl1_sub_head 136257 31 ++ infer_sub 10 Cs_1 (ax_S WLerrS.Pre_wl1)).
Definition R_1 : list sobj := Eval vm_compute in (match entails_frA C_1 WLerrS.Pre_wl1 s_1 with Some R => R | None => [] end).
Lemma efr_1 : ltac2:(tb__ "0|1|
S0S8S7SeA1M0A1S81S46S6eS36A3S9G0S4fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_1 : ltac2:(tb__ "0|0|
S0S5S80S46S6eS36S4fS2S26S6fS6S26A1A3A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_1 : axst := Eval vm_compute in (import_postA s_1 WLerrS.Pre_wl1 WLerrS.D C_1 R_1).
Lemma T_1_eq : ltac2:(tb__ "0|0|
S0S26S82S36S6eS6fS46S4fA5S52A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_1 : axst := Eval vm_compute in (ax_add_facts facts_fw T_1).
Lemma Tf_1_eq : ltac2:(tb__ "0|0|
S0S26S7fS65S52A2S43A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition runF_1__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS43S4A5").
Local Strategy expand [runF_1__R].
Definition F_1 : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => ((leaf1W Tf_1 (ro2__)))) runF_1__R).
Lemma runF_1 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS43S4A5S9G0S2S24S29S3dS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runF_1__R <: runF_1__R = Some [mkLeafA F_1 RsCut]). Qed.
Definition G1_1 : sstate := Eval vm_compute in (match apply_xforms (ax_S F_1) XS1 with Some s => s | None => ax_S F_1 end).
Lemma xs1_1 : ltac2:(tb__ "0|0|
S0S8S11A1S71S25S3dA1S55A2S9S11S4cA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G2_1 : sstate := Eval vm_compute in (drop2 G1_1).
Lemma drop2_1 : drop2 G1_1 = G2_1. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G3_1 : sstate := Eval vm_compute in (match apply_xforms G2_1 XS2 with Some s => s | None => G2_1 end).
Lemma xs2_1 : ltac2:(tb__ "0|0|
S0S8S11A1S71S5dS56A2S9S11S40A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sp_1 : wsub := Eval vm_compute in (post_sub_fw G3_1).
Lemma ent_1 : ltac2:(tb__ "0|0|
S0S5S2bS57S40A1S6aS5aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma shapeW_1 : ltac2:(tb__ "0|2|
S1S0S22S12S25S3aA1M0A1S64A3S1S0S7SbSfSfA2M1A1S2aS3aA1S2G1S6cZ21441Z1fA2S6G1A1A3A3S1S0SfS28S3aA1S10S75A1A3S1S0S7S16A1S14G0A1S65A3S0S23S15G0A1Zd9ad4A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeC_1 : ltac2:(tb__ "0|4|
S1S0S5S17S32S33S31A2M0A1S4A3S1S0S5S17S49A1S4A3S1S0S22S12S49A1S64A3S1S0S7S16A1S14S33A1S65A3S1S0S5S6bZ21441M1S7aG1Z1fM2A2S13S33A1M3A3S4A3S1S0S5S83S76G1S69G1G2A2A3S4A3S1S0S5S79S33A1S4A3S1S0S22S12S33A1S64A3S0S7SeA1S13G0A1SaSeG3S2SeS31S6SeA1A3A3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeS_1 : ltac2:(tb__ "0|0|
S1S0SfS62S36PcA2S10S67A1A3S1S0SfS62S36PdA2S10Z0A1A3S1S0SfS62S36PeA2S10Z21441A1A3S0SfS62S36PfA2S10Z1fA1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeT_1 : ltac2:(tb__ "0|2|
S1S0S22S12S25S52A1A1P7dM0A3S1S0S5S18S25S43A1M1A1SdA3S0S22S12G1A1G0A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeF_1 : ltac2:(tb__ "0|3|
S1S0S23S15S25S3dA1M0A1S68A3S1S0S22S12G0A1P7dM1A3S1S0SfS28S3dA1S10S75A1A3S1S0S7SeA1S13S4cA1M2SaSeS7bSeUbG2A3S2SeS31S2SeS39Z21441Z1fA2S6SeA1A3A3A3A3S1S0S22S12S4cA1G1A3S1S0S22S12S40A1G1A3S1S0S5S79S40A1S4A3S0S5S63S5aS64A2S4A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition runW_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS66Z1609eZ1fA2S4A5").
Local Strategy expand [runW_2__R].
Definition W_2 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => ((leaf1W (Pre_fw 90270 31) (ro3__)))) runW_2__R).
Lemma runW_2 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS66Z1609eZ1fA2S4A5S9G0S2S24S29S3bS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runW_2__R <: runW_2__R = Some [mkLeafA W_2 RsCut]). Qed.
Definition S4_2 : sstate := Eval vm_compute in (match splits_fw (ax_S W_2) with Some s => s | None => ax_S W_2 end).
Lemma splits_2 : ltac2:(tb__ "0|0|
S0S8S11A1S59S25S3bA1A1S9S11S34A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Cs_2 : sstate := Eval vm_compute in (app_obj (app_obj S4_2 O_b1z) (O_b2r 90270 31)).
Lemma finish_2 : ltac2:(tb__ "0|0|
S0S11S32S32S34S31A2S39Z1609eZ1fA2A2S4aA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_2 : axst := ax_setS W_2 Cs_2.
Definition s_2 : wsub := Eval vm_compute in (wl1_sub_head 90270 31 ++ infer_sub 10 Cs_2 (ax_S WLerrS.Pre_wl1)).
Definition R_2 : list sobj := Eval vm_compute in (match entails_frA C_2 WLerrS.Pre_wl1 s_2 with Some R => R | None => [] end).
Lemma efr_2 : ltac2:(tb__ "0|1|
S0S8S7SeA1M0A1S81S47S6eS37A3S9G0S50A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_2 : ltac2:(tb__ "0|0|
S0S5S80S47S6eS37S50S2S26S6fS6S26A1A3A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_2 : axst := Eval vm_compute in (import_postA s_2 WLerrS.Pre_wl1 WLerrS.D C_2 R_2).
Lemma T_2_eq : ltac2:(tb__ "0|0|
S0S26S82S37S6eS6fS47S50A5S53A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_2 : axst := Eval vm_compute in (ax_add_facts facts_fw T_2).
Lemma Tf_2_eq : ltac2:(tb__ "0|0|
S0S26S7fS65S53A2S44A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition runF_2__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS44S4A5").
Local Strategy expand [runF_2__R].
Definition F_2 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => ((leaf1W Tf_2 (ro4__)))) runF_2__R).
Lemma runF_2 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS44S4A5S9G0S2S24S29S3eS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runF_2__R <: runF_2__R = Some [mkLeafA F_2 RsCut]). Qed.
Definition G1_2 : sstate := Eval vm_compute in (match apply_xforms (ax_S F_2) XS1 with Some s => s | None => ax_S F_2 end).
Lemma xs1_2 : ltac2:(tb__ "0|0|
S0S8S11A1S71S25S3eA1S55A2S9S11S4dA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G2_2 : sstate := Eval vm_compute in (drop2 G1_2).
Lemma drop2_2 : drop2 G1_2 = G2_2. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G3_2 : sstate := Eval vm_compute in (match apply_xforms G2_2 XS2 with Some s => s | None => G2_2 end).
Lemma xs2_2 : ltac2:(tb__ "0|0|
S0S8S11A1S71S5eS56A2S9S11S41A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sp_2 : wsub := Eval vm_compute in (post_sub_fw G3_2).
Lemma ent_2 : ltac2:(tb__ "0|0|
S0S5S2bS57S41A1S6aS5bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma shapeW_2 : ltac2:(tb__ "0|2|
S1S0S22S12S25S3bA1M0A1S64A3S1S0S7SbSfSfA2M1A1S2aS3bA1S2G1S6cZ1609eZ1fA2S6G1A1A3A3S1S0SfS28S3bA1S10S75A1A3S1S0S7S16A1S14G0A1S65A3S0S23S15G0A1Zd9ad4A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeC_2 : ltac2:(tb__ "0|4|
S1S0S5S17S32S34S31A2M0A1S4A3S1S0S5S17S4aA1S4A3S1S0S22S12S4aA1S64A3S1S0S7S16A1S14S34A1S65A3S1S0S5S6bZ1609eM1S7aG1Z1fM2A2S13S34A1M3A3S4A3S1S0S5S83S76G1S69G1G2A2A3S4A3S1S0S5S79S34A1S4A3S1S0S22S12S34A1S64A3S0S7SeA1S13G0A1SaSeG3S2SeS31S6SeA1A3A3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeS_2 : ltac2:(tb__ "0|0|
S1S0SfS62S37PcA2S10S67A1A3S1S0SfS62S37PdA2S10Z0A1A3S1S0SfS62S37PeA2S10Z1609eA1A3S0SfS62S37PfA2S10Z1fA1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeT_2 : ltac2:(tb__ "0|2|
S1S0S22S12S25S53A1A1P7dM0A3S1S0S5S18S25S44A1M1A1SdA3S0S22S12G1A1G0A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeF_2 : ltac2:(tb__ "0|3|
S1S0S23S15S25S3eA1M0A1S68A3S1S0S22S12G0A1P7dM1A3S1S0SfS28S3eA1S10S75A1A3S1S0S7SeA1S13S4dA1M2SaSeS7bSeUbG2A3S2SeS31S2SeS39Z1609eZ1fA2S6SeA1A3A3A3A3S1S0S22S12S4dA1G1A3S1S0S22S12S41A1G1A3S1S0S5S79S41A1S4A3S0S5S63S5bS64A2S4A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition runW_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS66Z14d77Z13A2S4A5").
Local Strategy expand [runW_3__R].
Definition W_3 : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => ((leaf1W (Pre_fw 85367 19) (ro5__)))) runW_3__R).
Lemma runW_3 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS66Z14d77Z13A2S4A5S9G0S2S24S29S3cS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runW_3__R <: runW_3__R = Some [mkLeafA W_3 RsCut]). Qed.
Definition S4_3 : sstate := Eval vm_compute in (match splits_fw (ax_S W_3) with Some s => s | None => ax_S W_3 end).
Lemma splits_3 : ltac2:(tb__ "0|0|
S0S8S11A1S59S25S3cA1A1S9S11S35A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Cs_3 : sstate := Eval vm_compute in (app_obj (app_obj S4_3 O_b1z) (O_b2r 85367 19)).
Lemma finish_3 : ltac2:(tb__ "0|0|
S0S11S32S32S35S31A2S39Z14d77Z13A2A2S4bA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C_3 : axst := ax_setS W_3 Cs_3.
Definition s_3 : wsub := Eval vm_compute in (wl1_sub_head 85367 19 ++ infer_sub 10 Cs_3 (ax_S WLerrS.Pre_wl1)).
Definition R_3 : list sobj := Eval vm_compute in (match entails_frA C_3 WLerrS.Pre_wl1 s_3 with Some R => R | None => [] end).
Lemma efr_3 : ltac2:(tb__ "0|1|
S0S8S7SeA1M0A1S81S48S6eS38A3S9G0S51A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chk_3 : ltac2:(tb__ "0|0|
S0S5S80S48S6eS38S51S2S26S6fS6S26A1A3A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition T_3 : axst := Eval vm_compute in (import_postA s_3 WLerrS.Pre_wl1 WLerrS.D C_3 R_3).
Lemma T_3_eq : ltac2:(tb__ "0|0|
S0S26S82S38S6eS6fS48S51A5S54A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Tf_3 : axst := Eval vm_compute in (ax_add_facts facts_fw T_3).
Lemma Tf_3_eq : ltac2:(tb__ "0|0|
S0S26S7fS65S54A2S45A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition runF_3__R : option (list leafA) := ltac2:(tb__ "0|0|
S27S2eS30S2fS45S4A5").
Local Strategy expand [runF_3__R].
Definition F_3 : axst := Eval vm_compute in ((fun ro6__ : option (list leafA) => ((leaf1W Tf_3 (ro6__)))) runF_3__R).
Lemma runF_3 : ltac2:(tb__ "0|1|
S0S8S7S24A1M0A1S27S2eS30S2fS45S4A5S9G0S2S24S29S3fS77A2S6S24A1A3A2A3"). Proof. exact (@eq_refl (option (list leafA)) runF_3__R <: runF_3__R = Some [mkLeafA F_3 RsCut]). Qed.
Definition G1_3 : sstate := Eval vm_compute in (match apply_xforms (ax_S F_3) XS1 with Some s => s | None => ax_S F_3 end).
Lemma xs1_3 : ltac2:(tb__ "0|0|
S0S8S11A1S71S25S3fA1S55A2S9S11S4eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G2_3 : sstate := Eval vm_compute in (drop2 G1_3).
Lemma drop2_3 : drop2 G1_3 = G2_3. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition G3_3 : sstate := Eval vm_compute in (match apply_xforms G2_3 XS2 with Some s => s | None => G2_3 end).
Lemma xs2_3 : ltac2:(tb__ "0|0|
S0S8S11A1S71S5fS56A2S9S11S42A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition sp_3 : wsub := Eval vm_compute in (post_sub_fw G3_3).
Lemma ent_3 : ltac2:(tb__ "0|0|
S0S5S2bS57S42A1S6aS5cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma shapeW_3 : ltac2:(tb__ "0|2|
S1S0S22S12S25S3cA1M0A1S64A3S1S0S7SbSfSfA2M1A1S2aS3cA1S2G1S6cZ14d77Z13A2S6G1A1A3A3S1S0SfS28S3cA1S10S75A1A3S1S0S7S16A1S14G0A1S65A3S0S23S15G0A1Zd9ad4A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeC_3 : ltac2:(tb__ "0|4|
S1S0S5S17S32S35S31A2M0A1S4A3S1S0S5S17S4bA1S4A3S1S0S22S12S4bA1S64A3S1S0S7S16A1S14S35A1S65A3S1S0S5S6bZ14d77M1S7aG1Z13M2A2S13S35A1M3A3S4A3S1S0S5S83S76G1S69G1G2A2A3S4A3S1S0S5S79S35A1S4A3S1S0S22S12S35A1S64A3S0S7SeA1S13G0A1SaSeG3S2SeS31S6SeA1A3A3A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeS_3 : ltac2:(tb__ "0|0|
S1S0SfS62S38PcA2S10S67A1A3S1S0SfS62S38PdA2S10Z0A1A3S1S0SfS62S38PeA2S10Z14d77A1A3S0SfS62S38PfA2S10Z13A1A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeT_3 : ltac2:(tb__ "0|2|
S1S0S22S12S25S54A1A1P7dM0A3S1S0S5S18S25S45A1M1A1SdA3S0S22S12G1A1G0A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma shapeF_3 : ltac2:(tb__ "0|3|
S1S0S23S15S25S3fA1M0A1S68A3S1S0S22S12G0A1P7dM1A3S1S0SfS28S3fA1S10S75A1A3S1S0S7SeA1S13S4eA1M2SaSeS7bSeUbG2A3S2SeS31S2SeS39Z14d77Z13A2S6SeA1A3A3A3A3S1S0S22S12S4eA1G1A3S1S0S22S12S42A1G1A3S1S0S5S79S42A1S4A3S0S5S63S5cS64A2S4A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End DrvFwStates.

(* [comment removed for export] *)
Module Drv_printf0_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "reg_sv"; "cell"; "mkCell"; "ss_next"; "SVar"; "ss_lenient"; "SPUle"; "ss_facts"; "ob_cells"; "sobj"; "ss_pc"; "SAlu"; "ob_base"; "ss_objs"; "DUnknown"; "SPBranch"; "SPNot"; "image_byte"; "mkObj"; "obj_wf"; "ro_addr"; "@Corelib.Init.Datatypes"; "nil"; "true"; "bool"; "cons"; "option"; "Some"; "false"; "list"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "sym_runA"; "mkLeafA"; "axst"; "entailsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "ACEIL"; "@Stdlib.Lists.List"; "In"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0_states"; "E_w"; "L_w2"; "FUEL_f"; "L_fin1"; "P_io"; "W1"; "W2"; "E_io"; "L_fin2"; "FUEL_io"; "FUEL_w"; "s_fin1"; "s_fin2"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "ALU_ADD"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.PFAddr"; "SBUF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA"; "obA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "Pre_pf0"; "P_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymBytes"; "bexp"; "BLit"; "cells_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsEcall"; "instr_at"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Peano"; "le"; "@Corelib.Lists.ListDef"; "firstn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_write"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "A_after"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymBytes Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition run0 (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S1eS21S24A1M0A1G0Lx;S25S29Vfuel;S1aS2cA1VA;S1bA5G0R1Ll;S1aS24A1X1ex2").
Definition leaf0 (A : axst) (l : list leafA) : axst := match l with L :: _ => la_state L | _ => A end.
Definition FUEL_io : nat := 8000%nat.
Definition FUEL_w : nat := 3000%nat.
Definition FUEL_f : nat := 5000%nat.

Definition run_io__R : option (list leafA) := ltac2:(tb__ "0|0|
S25S29S37S1aS2cA1S44S1bA5").
Local Strategy expand [run_io__R].
Definition E_io : axst := Eval vm_compute in ((fun ro1__ : option (list leafA) => leaf0 Pre_pf0 ((match ro1__ with Some l => l | None => [] end))) run_io__R).
Lemma run_io : ltac2:(tb__ "0|1|
S0S1eS21S24A1M0A1S25S29S37S1aS2cA1S44S1bA5S1fG0S1dS24S26S35S49A2S1aS24A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_io__R <: run_io__R = Some [mkLeafA E_io RsEcall]). Qed.
Lemma E_io_at : ltac2:(tb__ "0|2|
S1S0S1eS3bA1S4aS29SfS23S35A1M0A1A2S1fS3bS3cA2A3S1S0S3S5G0Z11A2S2Z1dA1A3S1S0S3S5G0ZaA2S2Z1A1A3S1S0S3S5G0ZbA2S2Z5413A1A3S1S0S2dS8G0A1P69A3S1S0S1cSaG0A1S20A3S1S0S2dS8S23S44A1M1A1S4cA3S0S1cSaG1A1S20A3A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition P_io : axst := Eval vm_compute in A_after E_io (SLit (2 ^ 64 - 25)).
Lemma P_io_eq : ltac2:(tb__ "0|0|
S0S27S53S35S2S43S42Z2Z40A2Z19A2A1A2S32A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run_w__R : option (list leafA) := ltac2:(tb__ "0|0|
S25S29S38S1aS2cA1S32S1bA5").
Local Strategy expand [run_w__R].
Definition E_w : axst := Eval vm_compute in ((fun ro2__ : option (list leafA) => leaf0 P_io ((match ro2__ with Some l => l | None => [] end))) run_w__R).
Lemma run_w : ltac2:(tb__ "0|1|
S0S1eS21S24A1M0A1S25S29S38S1aS2cA1S32S1bA5S1fG0S1dS24S26S2eS49A2S1aS24A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_w__R <: run_w__R = Some [mkLeafA E_w RsEcall]). Qed.
Lemma E_w_at : ltac2:(tb__ "0|3|
S1S0S1eS3bA1S4aS29SfS23S2eA1M0A1A2S1fS3bS3cA2A3S1S0S3S5G0Z11A2S2Z42A1A3S1S0S3S5G0ZaA2S2Z1A1A3S1S0S3S5G0ZcA2S2Z2A1A3S1S0S3S5G0ZbA2S10S3dS9PaA1S2N508A1A3A3S1S0S2dS8G0A1P69M1A3S1S0S1cSaG0A1S20A3S1S0S2dS8S23S32A1M2A1G1A3S0S1cSaG2A1S20A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma E_w_iov : ltac2:(tb__ "0|6|
S1S2bS6S7S2N508A1Z8M0S2S3fA1M1A3SdS40S2eU0A2M2A1M3A3S1S2bS6S7S2N500A1G0S2Z1M4A1M5A3G3A3S1S2bS6S7S2N4f8A1G0S2Z14d8dA1A3G3A3S1S2bS6S7S2N4f0A1G0G5A3G3A3S1S0S3S11G2A1S9PaA1A3S1S0SeS40S2eU2A2S17S2Z0A1G1S2S41S3fZ400A2A1S1dS6S7G1G4S2Z30A1A3S1aS6A1A3S13A5A3S4dUcS22SeS12S23S2eA1A1A2A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity; try lia; repeat (try (left; reflexivity); right). Qed.
Lemma E_w_buf : ltac2:(tb__ "0|2|
S1S0S1cS18Pc8S40S2eU2A2M0A2S1bA3S0S1eS21S46A1M1A1S48SdG0A1S2S3fA1Z0U1A4S1fG1S1dS46S47Z30A1S1aS46A1A3A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma sp_facts_E_w : ltac2:(tb__ "0|2|
S1S2bS4SbS2S41S2aZ10000A2A1S9PaA1M0A2ScS23S2eA1A1M1A3S2bS4SbG0S2S43S42Z2Z2fA2Z10A2A1A2G1A3A2").
Proof. vm_compute. split; repeat (try (left; reflexivity); right). Qed.

Lemma nl_rom : ltac2:(tb__ "0|3|
S1S0S1cS19S29S51Q40Z14d8dA2M0A2S1bA3S0S1eS52Q8M1A1M2A1S16S29G0A2S1fG2S51G1ZaA2A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition W1 : axst := Eval vm_compute in A_after_write E_w (SLit 2).
Lemma W1_eq : ltac2:(tb__ "0|0|
S0S27S50S2eS2Z2A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition run_w1__R : option (list leafA) := ltac2:(tb__ "0|0|
S25S29S30S1aS2cA1S33S1bA5").
Local Strategy expand [run_w1__R].
Definition L_w2 : axst := Eval vm_compute in ((fun ro3__ : option (list leafA) => leaf0 W1 ((match ro3__ with Some l => l | None => [] end))) run_w1__R).
Definition L_fin1 : axst := Eval vm_compute in ((fun ro4__ : option (list leafA) => leaf0 W1 (tl ((match ro4__ with Some l => l | None => [] end)))) run_w1__R).
Lemma run_w1 : ltac2:(tb__ "0|1|
S0S1eS21S24A1M0A1S25S29S30S1aS2cA1S33S1bA5S1fG0S1dS24S26S2fS49A2S1dS24S26S31S4bA2S1aS24A1A3A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_w1__R <: run_w1__R = Some [mkLeafA L_w2 RsEcall; mkLeafA L_fin1 RsSymJump]). Qed.
Lemma L_w2_at : ltac2:(tb__ "0|3|
S1S0S1eS3bA1S4aS29SfS23S2fA1M0A1A2S1fS3bS3cA2A3S1S0S3S5G0Z11A2S2Z42A1A3S1S0S3S5G0ZaA2S2Z1A1A3S1S0S3S5G0ZcA2S2Z2A1A3S1S0S3S5G0ZbA2S10S3dS9PaA1S2N508A1A3A3S1S0S2dS8G0A1P6aM1A3S1S0S1cSaG0A1S20A3S1S0S2dS8S23S33A1M2A1G1A3S1S0S1cSaG2A1S20A3S0S2dS8S23S31A1A1G1A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma L_w2_iov : ltac2:(tb__ "0|4|
S1S2bS6S7S2N508A1Z8M0S2S41S3fZ1M1A2A1A3SdS40S2fU0A2M2A1M3A3S1S2bS6S7S2N500A1G0S2Z0A1A3G3A3S1S2bS6S7S2N4f8A1G0S2Z14d8dA1A3G3A3S1S2bS6S7S2N4f0A1G0S2G1A1A3G3A3S1S0S3S11G2A1S9PaA1A3S4dUcS22SeS12S23S2fA1A1A2A2A2A2A2A2A2").
Proof. vm_compute. repeat split; try reflexivity; try lia; repeat (try (left; reflexivity); right). Qed.
Lemma sp_facts_L_w2 : ltac2:(tb__ "0|2|
S1S2bS4SbS2S41S2aZ10000A2A1S9PaA1M0A2ScS23S2fA1A1M1A3S2bS4SbG0S2S43S42Z2Z2fA2Z10A2A1A2G1A3A2").
Proof. vm_compute. split; repeat (try (left; reflexivity); right). Qed.

Lemma L_facts : ltac2:(tb__ "0|5|
S1S0S21S4A1M0S4eS4U3ScS23S2fA1A1A3S1dS4S14S3eS9P69A1M1S2Z2A1M2A3M3S1dS4SbG1G2A2S1dS4SbS2Z1A1G1A2S1aS4A1M4A3A3A3A3S0G0S4eS4U1ScS23S31A1A1A3S1dS4S15G3A1G4A3A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition W2 : axst := Eval vm_compute in A_after_write L_w2 (SLit 1).
Lemma W2_eq : ltac2:(tb__ "0|0|
S0S27S50S2fS2Z1A1A2S34A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition run_w2__R : option (list leafA) := ltac2:(tb__ "0|0|
S25S29S30S1aS2cA1S34S1bA5").
Local Strategy expand [run_w2__R].
Definition L_fin2 : axst := Eval vm_compute in ((fun ro5__ : option (list leafA) => leaf0 W2 ((match ro5__ with Some l => l | None => [] end))) run_w2__R).
Lemma run_w2 : ltac2:(tb__ "0|1|
S0S1eS21S24A1M0A1S25S29S30S1aS2cA1S34S1bA5S1fG0S1dS24S26S36S4bA2S1aS24A1A3A2A3").
Proof. exact (@eq_refl (option (list leafA)) run_w2__R <: run_w2__R = Some [mkLeafA L_fin2 RsSymJump]). Qed.
Lemma W2_at : ltac2:(tb__ "0|2|
S1S0S2dS8S23S34A1M0A1P6bM1A3S1S0S1cSaG0A1S20A3S0S2dS8S23S36A1A1G1A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition s_fin1 : wsub := Eval vm_compute in infer_sub NF (ax_S L_fin1) (ax_S (P_pf 0)).
Definition s_fin2 : wsub := Eval vm_compute in infer_sub NF (ax_S L_fin2) (ax_S (P_pf 0)).
Lemma ent_fin1 : ltac2:(tb__ "0|0|
S0S1cS28S31S45Z0A1S39A3S1bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_fin2 : ltac2:(tb__ "0|0|
S0S1cS28S36S45Z0A1S3aA3S1bA3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_fin : ltac2:(tb__ "0|0|
S1S0S1cS4fS39S4cA2S1bA3S0S1cS4fS3aS4cA2S1bA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Drv_printf0_states.

(* [comment removed for export] *)
Module Drv_printf0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "option"; "Some"; "cons"; "nat"; "nil"; "pair"; "app"; "bool"; "length"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "ACEIL"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "SLit"; "sprop"; "SPUle"; "SVar"; "rw"; "cell"; "holds"; "image_byte"; "mkCell"; "ob_base"; "ob_cells"; "ro_addr"; "sobj"; "ss_objs"; "sv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "read_bytes_map"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "read_u64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0.Printf0"; "Kw"; "ch1"; "EVS"; "MSG0"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "Posts_pf"; "Pre_pf0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA"; "obA"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysStepA SysA MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Drv_printf0_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma rom_read1 : ltac2:(tb__ "0|5|
S13S0SdQ40M0A1M1A1S43S0S23A1M2S39S24G1SdQ8A1M3S45SbR8R7R6S6G2S3bR5S3cR4R3A2A4A5S10S8S1fSbR3A2SaA3S10S1G3A1S1bSbR4A2S2G3R3A2A3S10S1S0G3A1M4A1S26S3aS47R6RaR7A3A1R5SeG0Z1A2A3S2G4S3G3R4S5G3A1A3A2A3F_;F_;F_;Fb;Fa;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof.
  intros rho tp A tr ms md a b Hsp Hro Hib.
  pose proof (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) as Hsp'.
  pose proof (smatch_pending_rom segs _ _ _ _ _ Hsp') as Hrom.
  pose proof (smatch_pending_ro_clear segs _ _ _ _ _ Hsp') as Hroc.
  rewrite read_bytes_map_eq. unfold word_to_nat. change (Z.to_nat (bv_unsigned (Z_to_bv 64 1))) with 1%nat.
  cbn [read_bytes_aux]. unfold ms_read_byte. rewrite (Hroc a Hro), (Hrom a), Hib. reflexivity.
Qed.

Lemma read0 : ltac2:(tb__ "0|4|
SdQ40M0A1M1S1SdQ8A1M2A1F_;G1S10S1S0G2A1M3A1S26R2R1SeG0Z0A2A3S2G3S5G2A1A2A3Fa;Fmp;").
Proof. intros mp a. rewrite read_bytes_map_eq. reflexivity. Qed.

Lemma sp_range : ltac2:(tb__ "0|5|
S13S0S15A1S4aS15S1aR2A1R1A3S33S15S16S14S35ScZ10000A2M0A1S17PaM1A1M2A2R2A3S33S15S16G2S14S38S37Z2Z2fA2Z10A2M3A1A2R3A3S11S34G0SfQ40S18R5G1A2A2M4A2S34G4G3A2A2F_;F_;F_;FF;Frho;").
Proof.
  intros rho F HF H1 H2.
  pose proof (proj1 (Forall_forall _ _) HF _ H1) as A1. pose proof (proj1 (Forall_forall _ _) HF _ H2) as A2.
  cbn [holds] in A1, A2. rewrite (U_lit64 rho (ACEIL + 65536)) in A1 by (unfold ACEIL; lia).
  rewrite (U_lit64 rho (2 ^ 47 - 16)) in A2 by lia. cbn [eval] in A1, A2. unfold ACEIL in *. lia.
Qed.

Lemma iov_read : ltac2:(tb__ "0|5|
S13S0SdQ40M0A1M1A1S43S0S23A1M2S39S24S30S30G1S45SbR9R8R7S6G2S3bR6S3cR5R4A2A4A5S49U0M3S9S20S21S44R8A1A1A2A2S10S22S1dS48R9G3A2A1S17PaM4A1A3S33S19S1cS14R6A1Z8S14R5A1A3S1eS48RaG3A2A1A3S11S34N1000R7A2S36R7Z0A2A2S10S30SfG0R6A2S35SfG0S18ReG4A2A2R8A2A3S10S1G1A1S2bS3aS47RaReRbA3A1R7A2S2G1SeG0R8A2A2A3F_;F_;F_;F_;F_;F_;Fa;Fz;Foff;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof.
  intros rho tp A tr ms md off z a Hsp Hlen Hb Hin Hoff Ha.
  pose proof (objsA_hold segs rho tp A tr ms md 0 Hsp Hlen) as Ho.
  change (Z_to_bv 64 z) with (eval rho (SLit z)).
  apply (cell_read_u64 segs rho (vms md tp ms) (obA A 0) (SLit off) (SLit z) a Ho Hin).
  rewrite Hb. change (eval rho (SVar 10)) with (rw rho 10). rewrite soff_lit_small by lia. lia.
Qed.

Lemma u1 : bv_unsigned (Z_to_bv 64 1) = 1. Proof. reflexivity. Qed.
Lemma u0 : bv_unsigned (Z_to_bv 64 0) = 0. Proof. reflexivity. Qed.
Lemma u24 : bv_unsigned (16%bv + 8%bv : bv 64)%bv = 24. Proof. reflexivity. Qed.

Section Printf0.
Variable ok : assn.
Variable J0 : jpredA.
Definition ch1 : word := Z_to_bv 64 1.
Definition MSG0 : list byte := ltac2:(tb__ "0|2|
S3SdQ8M0A1M1SeG0Z30A2S3G1SeG0ZaA2S5G1A1A3A3").
Definition EVS (n : nat) : list event := ltac2:(tb__ "0|1|
S4cSdQ8A1M0S23S28S2dA1S4bG0Vn;S2fA3A4").

Definition Kw (n : nat) : jpredA := ltac2:(tb__ "0|1|
S13S0SdQ40A1A1S0S23A1M0S24S12G0G0S11VJ0;R5R4R1R2A4S10G0R3S7S23R1S2eVn;A1A3A3A2Ltr0;A2Lmd;Ltr;Lt;Lr;").
Hypothesis Hst0 : stableA segs NF J0.
Hypothesis Hfd : ltac2:(tb__ "0|0|
S13S0SdQ40A1A1S0S23A1S24VJ0;R4R3R2R1A4S10S1S25A1S29S2aR2A1S2dA2S2S25S27S2dA1A2A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HokK : ltac2:(tb__ "0|0|
S4S41SbVok;S2cR1A1A3Fn;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S4S46SbVok;S2cR1A1A3Fn;").

Lemma Kw_stable : ltac2:(tb__ "0|0|
S4S31S4fS32R1A2S42SbR2S2cR3A1A3F_;Fm;Fn;").
Proof.
  intros n m Hm rho rho' tp tr md md' Hag Hme (tr0 & HJ & ->). exists tr0. split; [|reflexivity].
  eapply (stableA_mono segs NF m J0 Hm Hst0); eauto.
Qed.

Theorem printf0_sum : ltac2:(tb__ "0|0|
S13S0SdQ40A1A1S4eSbVok;S40SbVJ0;S3eR2R1A5S3fSbS2cU2A1S32R2R1S3dZ0A1A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  set (G := fun r : valuation => agree_below NF rho r).
  set (K := fun n => withGA G (Kw n)).
  assert (HstK : forall n m, (NF <= m)%positive -> stableA segs m (K n)).
  { intros n m Hm. apply stableA_withG; [| apply Kw_stable; exact Hm].
    intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [exact Hm | exact H2]. }
  assert (HokK' : forall n, ok_frameA segs ok (K n)) by (intros n r t tr ms md msv' [_ HJ]; eapply HokK; eauto).
  assert (HokP' : forall n, ok_pframeA segs ok (K n)) by (intros n r t tr ms md x8 [_ HJ]; eapply HokP; eauto).
  assert (NF100 : NF = 100%positive) by reflexivity.

  eapply triple_conseq with (P := SPA segs (K 0%nat) Pre_pf0 rho tp); [ | intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. split; [apply agree_below_refl|]. exists (w_tr w). split; [exact HJ|].
    unfold EVS. cbn. rewrite app_nil_r. reflexivity. }
  destruct E_io_at as (Hi & H17 & H10 & H11 & Hnx & Hlen & HnxP & HlenP0).

  eapply (runA_tr segs ok FUEL_io [] Pre_pf0 _ (K 0%nat) rho tp); [exact run_io | exact HlenP0 | apply HokK' | rewrite HnxP; apply HstK; apply Pos.le_refl |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnxP in Hag1.

  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_ioctlA segs E_io rho1 tp 1 Hi H17 H10 H11 ltac:(lia) ok (K 0%nat) (K 0%nat));
      [apply HokK' | apply HokP' | rewrite Hnx; apply HstK; rewrite NF100; lia | | intros tr md HJ; exact HJ].
    intros tr md [_ (tr0 & HJ & _)]. eexists. exact (Hfd _ _ _ _ HJ). }
  unfold ioctlA'. rewrite P_io_eq.
  destruct E_w_at as (Hiw & H17w & H10w & H12w & H11w & Hnxw & Hlenw & HnxPio & HlenPio).

  eapply (runA_tr segs ok FUEL_w [] P_io _ (K 0%nat) rho1 tp); [exact run_w | exact HlenPio | apply HokK' | rewrite HnxPio; apply HstK; rewrite NF100; lia |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state]. rewrite HnxPio in Hag2.

  set (K1 := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               exists k, rw r 105%positive = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= 2)%nat /\ K k r t tr md).
  assert (HstK1 : stableA segs 106 K1).
  { intros r r' t tr md md' Hag Hme (k & Hk & Hkb & HK). exists k.
    split; [rewrite <- (proj1 Hag 105%positive ltac:(cbv; reflexivity)); exact Hk|]. split; [exact Hkb|].
    eapply (HstK k 106%positive); [rewrite NF100; lia | exact Hag | exact Hme | exact HK]. }
  destruct E_w_iov as (C1 & C2 & C3 & C4 & Hb0 & Ob2 & Hlen12).
  destruct E_w_buf as [Hwf2 Hcb2]. destruct nl_rom as [Hro Hib].
  eapply triple_seq.
  { apply triple1_triple.
    apply (triple1_writev2A segs ok (K 0%nat) K1 E_w rho2 tp 1 [Z_to_bv 8 48] [Z_to_bv 8 10] (SLit 2));
      [apply HokK' | apply HokP' | rewrite Hnxw; apply HstK; rewrite NF100; lia | rewrite Hnxw; exact HstK1
      | exact Hiw | exact H17w | exact H10w | exact H12w | lia | cbn; unfold MAX_RW_COUNT; cbn; lia | reflexivity | |].
    - intros rho' tr md k Hag Hrw [HG (tr0 & HJ & ->)] Hk. split; [exact (Hfd _ _ _ _ HJ)|].
      exists k. rewrite Hnxw in Hrw, Hag. split; [exact Hrw|]. split; [exact Hk|]. split.
      + eapply agree_below_trans; [exact HG|]. eapply agree_below_le; [|exact Hag]. rewrite NF100; lia.
      + exists tr0. split; [eapply Hst0; [eapply agree_below_le; [|exact Hag]; rewrite NF100; lia | apply mat_equiv_refl | exact HJ]|].
        unfold EVS. cbn [firstn MSG0 map app]. rewrite <- app_assoc. destruct k as [|[|[|k]]]; try lia; reflexivity.
    - intros tr ms md Hsp HJ. rewrite H11w.
      pose proof (sp_range rho2 _ (smatch_pendingA_facts segs _ _ _ _ Hsp) (proj1 sp_facts_E_w) (proj2 sp_facts_E_w)) as SP.
      assert (Ua : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) = bv_unsigned (rw rho2 10) - 1288).
      { rewrite (U_addc rho2 (SVar 10) (-1288) (bv_unsigned (rw rho2 10)) eq_refl); [lia | unfold ACEIL in SP; lia | lia]. }
      set (a := eval rho2 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) in *.
      exists (Z_to_bv 64 SBUF), (Z_to_bv 64 1), (Z_to_bv 64 85389), (Z_to_bv 64 1).
      assert (L0 : (0 < length (ss_objs (ax_S E_w)))%nat) by lia.
      split; [apply (iov_read rho2 tp E_w tr ms md (-1288) SBUF a Hsp L0 Hb0 C1); lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1280) 1 _ Hsp L0 Hb0 C2); [lia|]; rewrite (U_bvadd a _ _ 8 Ua u8); unfold ACEIL in SP; lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1272) 85389 _ Hsp L0 Hb0 C3); [lia|]; rewrite (U_bvadd a _ _ 16 Ua u16); unfold ACEIL in SP; lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1264) 1 _ Hsp L0 Hb0 C4); [lia|];
             rewrite (U_bvadd (a + 16)%bv _ _ 8 (U_bvadd a _ _ 16 Ua u16 ltac:(unfold ACEIL in SP; lia)) u8); unfold ACEIL in SP; lia|].
      split.
      + pose proof (objsA_hold segs rho2 tp E_w tr ms md 2 Hsp ltac:(lia)) as Ho2.
        change [Z_to_bv 8 48] with (map (beval rho2) [BLit 48]).
        apply (cells_read_bytes_map segs rho2 (vms md tp ms) (obA E_w 2) 200 (SLit SBUF) 0 1 [BLit 48] _ _ Ho2 Hwf2); [| exact Hcb2 | |].
        * rewrite Ob2. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by (unfold SBUF; lia). unfold SBUF. lia.
        * rewrite Ob2. cbn [ob_base]. rewrite (U_lit64 rho2 0) by lia. rewrite soff_lit_small by (unfold SBUF; lia). unfold SBUF. reflexivity.
        * reflexivity.
      + split; [exact (rom_read1 rho2 tp E_w tr ms md _ _ Hsp Hro Hib)|]. split; [reflexivity|].

        split; [unfold TASK_SIZE; unfold ACEIL in SP; lia|]. split; apply Z.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }

  apply triple_ex; intros rho3. apply triple_pure; intros Hag3. rewrite W1_eq. rewrite Hnxw in Hag3.
  destruct L_w2_at as (Hiw2 & H17w2 & H10w2 & H12w2 & H11w2 & Hnxw2 & Hlenw2 & HnxW1 & HlenW1 & HnxF1).
  eapply (runA_tr segs ok FUEL_f [] W1 _ K1 rho3 tp); [exact run_w1 | exact HlenW1 | | rewrite HnxW1; exact HstK1 |].
  { intros r t tr ms md msv' (k & _ & _ & [_ HJ]). eapply HokK; eauto. }
  intros L rho4 [<-|[<-|[]]] Hag4; cbn [la_state]; rewrite HnxW1 in Hag4.
  -
    destruct L_facts as [F3 _].
    eapply triple_conseq with (P := SPA segs (K 1%nat) L_w2 rho4 tp); [| intros w Hw; exact Hw |].
    { intros w [Hsm HX]. subst K1. destruct HX as (k & Hk & Hkb & HK). split; [exact Hsm|].
      pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
      assert (Hne : holds rho4 (SPBranch BC_NE (SVar 105) (SLit 2))).
      { apply (proj1 (Forall_forall _ _) HF). rewrite <- (firstn_skipn 3 (ss_facts (ax_S L_w2))), F3. left; reflexivity. }
      apply holds_bne in Hne. rewrite (U_lit64 rho4 2) in Hne by lia.
      change (eval rho4 (SVar 105)) with (rw rho4 105%positive) in Hne. rewrite Hk in Hne.
      rewrite Z_to_bv_small in Hne by (rewrite two64; lia).
      assert (k = 1%nat) as -> by lia. exact HK. }
    destruct L_w2_iov as (D1 & D2 & D3 & D4 & Hb0' & Hlen12').
    set (K2 := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
                 exists k, rw r 106%positive = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= 1)%nat /\ K (1 + k)%nat r t tr md).
    assert (HstK2 : stableA segs 107 K2).
    { intros r r' t tr md md' Hag Hme (k & Hk & Hkb & HK). exists k.
      split; [rewrite <- (proj1 Hag 106%positive ltac:(cbv; reflexivity)); exact Hk|]. split; [exact Hkb|].
      eapply (HstK (1 + k)%nat 107%positive); [rewrite NF100; lia | exact Hag | exact Hme | exact HK]. }
    eapply triple_seq.
    { apply triple1_triple.
      apply (triple1_writev2A segs ok (K 1%nat) K2 L_w2 rho4 tp 1 [] [Z_to_bv 8 10] (SLit 1));
        [apply HokK' | apply HokP' | rewrite Hnxw2; apply HstK; rewrite NF100; lia | rewrite Hnxw2; exact HstK2
        | exact Hiw2 | exact H17w2 | exact H10w2 | exact H12w2 | lia | cbn; unfold MAX_RW_COUNT; cbn; lia | reflexivity | |].
      - intros rho' tr md k Hag Hrw [HG (tr1 & HJ & ->)] Hk. split; [exact (Hfd _ _ _ _ HJ)|].
        exists k. rewrite Hnxw2 in Hrw, Hag. split; [exact Hrw|]. split; [exact Hk|]. split.
        + eapply agree_below_trans; [exact HG|]. eapply agree_below_le; [|exact Hag]. rewrite NF100; lia.
        + exists tr1. split; [eapply Hst0; [eapply agree_below_le; [|exact Hag]; rewrite NF100; lia | apply mat_equiv_refl | exact HJ]|].
          unfold EVS. cbn in Hk. replace k with 1%nat by lia. cbn [firstn MSG0 map app]. rewrite <- app_assoc. reflexivity.
      - intros tr ms md Hsp HJ. rewrite H11w2.
        pose proof (sp_range rho4 _ (smatch_pendingA_facts segs _ _ _ _ Hsp) (proj1 sp_facts_L_w2) (proj2 sp_facts_L_w2)) as SP.
        assert (Ua : bv_unsigned (eval rho4 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) = bv_unsigned (rw rho4 10) - 1288).
        { rewrite (U_addc rho4 (SVar 10) (-1288) (bv_unsigned (rw rho4 10)) eq_refl); [lia | unfold ACEIL in SP; lia | lia]. }
        set (a := eval rho4 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) in *.
        exists (Z_to_bv 64 (SBUF + 1)), (Z_to_bv 64 0), (Z_to_bv 64 85389), (Z_to_bv 64 1).
        assert (L0 : (0 < length (ss_objs (ax_S L_w2)))%nat) by lia.
        split; [apply (iov_read rho4 tp L_w2 tr ms md (-1288) (SBUF + 1) a Hsp L0 Hb0' D1); lia|].
        split; [apply (iov_read rho4 tp L_w2 tr ms md (-1280) 0 _ Hsp L0 Hb0' D2); [lia|]; rewrite (U_bvadd a _ _ 8 Ua u8); unfold ACEIL in SP; lia|].
        split; [apply (iov_read rho4 tp L_w2 tr ms md (-1272) 85389 _ Hsp L0 Hb0' D3); [lia|]; rewrite (U_bvadd a _ _ 16 Ua u16); unfold ACEIL in SP; lia|].
        split; [apply (iov_read rho4 tp L_w2 tr ms md (-1264) 1 _ Hsp L0 Hb0' D4); [lia|];
               rewrite (U_bvadd (a + 16)%bv _ _ 8 (U_bvadd a _ _ 16 Ua u16 ltac:(unfold ACEIL in SP; lia)) u8); unfold ACEIL in SP; lia|].
        split; [apply read0|]. split; [exact (rom_read1 rho4 tp L_w2 tr ms md _ _ Hsp Hro Hib)|]. split; [reflexivity|].

        split; [unfold TASK_SIZE; unfold ACEIL in SP; lia|]. split; apply Z.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }

    apply triple_ex; intros rho5. apply triple_pure; intros Hag5. rewrite W2_eq. rewrite Hnxw2 in Hag5.
    destruct W2_at as (HnxW2 & HlenW2 & HnxF2).
    eapply (runA_tr segs ok FUEL_f [] W2 _ K2 rho5 tp); [exact run_w2 | exact HlenW2 | | rewrite HnxW2; exact HstK2 |].
    { intros r t tr ms md msv' (k & _ & _ & [_ HJ]). eapply HokK; eauto. }
    intros L rho6 [<-|[]] Hag6. cbn [la_state]. rewrite HnxW2 in Hag6.

    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm HX]. subst K2 K. destruct HX as (k & Hk & Hkb & [HG HK]). assert (k = 1%nat) as -> by lia.
    apply (LQA_intro segs (Kw 2) NF rho tp (mkLeafA (P_pf 0) RsSymJump) (Posts_pf 0) (rho_sub rho6 s_fin2) w); [left; reflexivity | |].
    + eapply agree_below_trans; [exact HG|]. apply rho_sub_agree. exact (proj2 ids_fin).
    + split; [exact (smatchA_entails segs L_fin2 (P_pf 0) s_fin2 rho6 tp w ent_fin2 Hsm)|].
      eapply (Kw_stable 2 NF (Pos.le_refl _)); [apply rho_sub_agree; exact (proj2 ids_fin) | apply mat_equiv_refl | exact HK].
  -
    destruct L_facts as [_ F1].
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w [Hsm HX]. subst K1 K. destruct HX as (k & Hk & Hkb & [HG HK]).
    pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
    assert (Heq : holds rho4 (SPNot (SPBranch BC_NE (SVar 105) (SLit 2)))).
    { apply (proj1 (Forall_forall _ _) HF). rewrite <- (firstn_skipn 1 (ss_facts (ax_S L_fin1))), F1. left; reflexivity. }
    apply holds_nbne in Heq. rewrite (U_lit64 rho4 2) in Heq by lia.
    change (eval rho4 (SVar 105)) with (rw rho4 105%positive) in Heq. rewrite Hk in Heq.
    rewrite Z_to_bv_small in Heq by (rewrite two64; lia).
    assert (k = 2%nat) as -> by lia.
    apply (LQA_intro segs (Kw 2) NF rho tp (mkLeafA (P_pf 0) RsSymJump) (Posts_pf 0) (rho_sub rho4 s_fin1) w); [left; reflexivity | |].
    + eapply agree_below_trans; [exact HG|]. apply rho_sub_agree. exact (proj1 ids_fin).
    + split; [exact (smatchA_entails segs L_fin1 (P_pf 0) s_fin1 rho4 tp w ent_fin1 Hsm)|].
      eapply (Kw_stable 2 NF (Pos.le_refl _)); [apply rho_sub_agree; exact (proj1 ids_fin) | apply mat_equiv_refl | exact HK].
Qed.

Theorem printf0_sum_ex : ltac2:(tb__ "0|0|
S13S0SdQ40A1A1S4dSbS40SbVJ0;S3eR2R1A5S3fSbS2cU2A1S32R2R1S3dZ0A1A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  set (G := fun r : valuation => agree_below NF rho r).
  set (K := fun n => withGA G (Kw n)).
  assert (HstK : forall n m, (NF <= m)%positive -> stableA segs m (K n)).
  { intros n m Hm. apply stableA_withG; [| apply Kw_stable; exact Hm].
    intros r1 r2 H1 H2. eapply agree_below_trans; [exact H1|]. eapply agree_below_le; [exact Hm | exact H2]. }
  assert (NF100 : NF = 100%positive) by reflexivity.
  eapply etriple_conseq with (P := SPA segs (K 0%nat) Pre_pf0 rho tp); [ | intros w Hw; exact Hw |].
  { intros w [Hsm HJ]. split; [exact Hsm|]. split; [apply agree_below_refl|]. exists (w_tr w). split; [exact HJ|].
    unfold EVS. cbn. rewrite app_nil_r. reflexivity. }
  destruct E_io_at as (Hi & H17 & H10 & H11 & Hnx & Hlen & HnxP & HlenP0).
  eapply (erunA_tr segs FUEL_io [] Pre_pf0 _ (K 0%nat) rho tp); [exact run_io | exact HlenP0 | rewrite HnxP; apply HstK; apply Pos.le_refl |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnxP in Hag1.
  eapply etriple_seq.
  { apply (etriple_ioctlA segs E_io rho1 tp 1 Hi H17 H10 H11 ltac:(lia) (K 0%nat) (K 0%nat));
      [rewrite Hnx; apply HstK; rewrite NF100; lia | | intros tr md HJ; exact HJ].
    intros tr md [_ (tr0 & HJ & _)]. eexists. exact (Hfd _ _ _ _ HJ). }
  unfold ioctlA'. rewrite P_io_eq.
  destruct E_w_at as (Hiw & H17w & H10w & H12w & H11w & Hnxw & Hlenw & HnxPio & HlenPio).
  eapply (erunA_tr segs FUEL_w [] P_io _ (K 0%nat) rho1 tp); [exact run_w | exact HlenPio | rewrite HnxPio; apply HstK; rewrite NF100; lia |].
  intros L rho2 [<-|[]] Hag2. cbn [la_state]. rewrite HnxPio in Hag2.
  set (K1 := fun (r : valuation) (t : list word) (tr : list event) (md : Model) =>
               exists k, rw r 105%positive = Z_to_bv 64 (Z.of_nat k) /\ (1 <= k <= 2)%nat /\ K k r t tr md).
  assert (HstK1 : stableA segs 106 K1).
  { intros r r' t tr md md' Hag Hme (k & Hk & Hkb & HK). exists k.
    split; [rewrite <- (proj1 Hag 105%positive ltac:(cbv; reflexivity)); exact Hk|]. split; [exact Hkb|].
    eapply (HstK k 106%positive); [rewrite NF100; lia | exact Hag | exact Hme | exact HK]. }
  destruct E_w_iov as (C1 & C2 & C3 & C4 & Hb0 & Ob2 & Hlen12).
  destruct E_w_buf as [Hwf2 Hcb2]. destruct nl_rom as [Hro Hib].
  eapply etriple_seq.
  { apply (etriple_writev2A segs (K 0%nat) K1 E_w rho2 tp 1 [Z_to_bv 8 48] [Z_to_bv 8 10] (SLit 2));
      [rewrite Hnxw; apply HstK; rewrite NF100; lia | rewrite Hnxw; exact HstK1
      | exact Hiw | exact H17w | exact H10w | exact H12w | lia | cbn; unfold MAX_RW_COUNT; cbn; lia | reflexivity | |].
    - intros rho' tr md k Hag Hrw [HG (tr0 & HJ & ->)] Hk. split; [exact (Hfd _ _ _ _ HJ)|].
      exists k. rewrite Hnxw in Hrw, Hag. split; [exact Hrw|]. split; [exact Hk|]. split.
      + eapply agree_below_trans; [exact HG|]. eapply agree_below_le; [|exact Hag]. rewrite NF100; lia.
      + exists tr0. split; [eapply Hst0; [eapply agree_below_le; [|exact Hag]; rewrite NF100; lia | apply mat_equiv_refl | exact HJ]|].
        unfold EVS. cbn [firstn MSG0 map app]. rewrite <- app_assoc. destruct k as [|[|[|k]]]; try lia; reflexivity.
    - intros tr ms md Hsp HJ. rewrite H11w.
      pose proof (sp_range rho2 _ (smatch_pendingA_facts segs _ _ _ _ Hsp) (proj1 sp_facts_E_w) (proj2 sp_facts_E_w)) as SP.
      assert (Ua : bv_unsigned (eval rho2 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) = bv_unsigned (rw rho2 10) - 1288).
      { rewrite (U_addc rho2 (SVar 10) (-1288) (bv_unsigned (rw rho2 10)) eq_refl); [lia | unfold ACEIL in SP; lia | lia]. }
      set (a := eval rho2 (SAlu ALU_ADD (SVar 10) (SLit (-1288)))) in *.
      exists (Z_to_bv 64 SBUF), (Z_to_bv 64 1), (Z_to_bv 64 85389), (Z_to_bv 64 1).
      assert (L0 : (0 < length (ss_objs (ax_S E_w)))%nat) by lia.
      split; [apply (iov_read rho2 tp E_w tr ms md (-1288) SBUF a Hsp L0 Hb0 C1); lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1280) 1 _ Hsp L0 Hb0 C2); [lia|]; rewrite (U_bvadd a _ _ 8 Ua u8); unfold ACEIL in SP; lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1272) 85389 _ Hsp L0 Hb0 C3); [lia|]; rewrite (U_bvadd a _ _ 16 Ua u16); unfold ACEIL in SP; lia|].
      split; [apply (iov_read rho2 tp E_w tr ms md (-1264) 1 _ Hsp L0 Hb0 C4); [lia|];
             rewrite (U_bvadd (a + 16)%bv _ _ 8 (U_bvadd a _ _ 16 Ua u16 ltac:(unfold ACEIL in SP; lia)) u8); unfold ACEIL in SP; lia|].
      split.
      + pose proof (objsA_hold segs rho2 tp E_w tr ms md 2 Hsp ltac:(lia)) as Ho2.
        change [Z_to_bv 8 48] with (map (beval rho2) [BLit 48]).
        apply (cells_read_bytes_map segs rho2 (vms md tp ms) (obA E_w 2) 200 (SLit SBUF) 0 1 [BLit 48] _ _ Ho2 Hwf2); [| exact Hcb2 | |].
        * rewrite Ob2. unfold obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by (unfold SBUF; lia). unfold SBUF. lia.
        * rewrite Ob2. cbn [ob_base]. rewrite (U_lit64 rho2 0) by lia. rewrite soff_lit_small by (unfold SBUF; lia). unfold SBUF. reflexivity.
        * reflexivity.
      + split; [exact (rom_read1 rho2 tp E_w tr ms md _ _ Hsp Hro Hib)|]. split; [reflexivity|].

        split; [unfold TASK_SIZE; unfold ACEIL in SP; lia|]. split; apply Z.leb_le; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. }

  apply etriple_ex; intros rho3. apply etriple_pure; intros Hag3. apply etriple_pure; intros Hrw3. rewrite W1_eq. rewrite Hnxw in Hag3, Hrw3.
  destruct L_w2_at as (Hiw2 & H17w2 & H10w2 & H12w2 & H11w2 & Hnxw2 & Hlenw2 & HnxW1 & HlenW1 & HnxF1).
  set (K1e := withGA (fun r => rw r 105%positive = Z_to_bv 64 2) K1).
  eapply etriple_conseq with (P := SPA segs K1e W1 rho3 tp); [intros w [Hsm HJ]; split; [exact Hsm|]; split; [exact Hrw3 | exact HJ] | intros w Hw; exact Hw |].
  assert (HstK1e : stableA segs 106 K1e).
  { apply stableA_withG; [| exact HstK1]. intros r1 r2 H1 H2. rewrite <- (proj1 H2 105%positive ltac:(cbv; reflexivity)). exact H1. }
  eapply (erunA_tr segs FUEL_f [] W1 _ K1e rho3 tp); [exact run_w1 | exact HlenW1 | rewrite HnxW1; exact HstK1e |].
  intros L rho4 [<-|[<-|[]]] Hag4; cbn [la_state]; rewrite HnxW1 in Hag4.
  -
    destruct L_facts as [F3 _]. intros w [Hsm [Hrw4 _]]. exfalso.
    pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
    assert (Hne : holds rho4 (SPBranch BC_NE (SVar 105) (SLit 2))).
    { apply (proj1 (Forall_forall _ _) HF). rewrite <- (firstn_skipn 3 (ss_facts (ax_S L_w2))), F3. left; reflexivity. }
    apply holds_bne in Hne. apply Hne. change (eval rho4 (SVar 105)) with (rw rho4 105%positive). rewrite Hrw4. reflexivity.
  -
    intros w [Hsm [Hrw4 HX]]. subst K1 K. destruct HX as (k & Hk & Hkb & [HG HK]).
    rewrite Hrw4 in Hk. apply (f_equal bv_unsigned) in Hk. rewrite !Z_to_bv_small in Hk by (rewrite two64; lia).
    assert (k = 2%nat) as -> by lia.
    exists w. split; [apply wsteps_refl|].
    apply (LQA_intro segs (Kw 2) NF rho tp (mkLeafA (P_pf 0) RsSymJump) (Posts_pf 0) (rho_sub rho4 s_fin1) w); [left; reflexivity | |].
    + eapply agree_below_trans; [exact HG|]. apply rho_sub_agree. exact (proj1 ids_fin).
    + split; [exact (smatchA_entails segs L_fin1 (P_pf 0) s_fin1 rho4 tp w ent_fin1 Hsm)|].
      eapply (Kw_stable 2 NF (Pos.le_refl _)); [apply rho_sub_agree; exact (proj1 ids_fin) | apply mat_equiv_refl | exact HK].
Qed.
End Printf0.
End Drv_printf0.

