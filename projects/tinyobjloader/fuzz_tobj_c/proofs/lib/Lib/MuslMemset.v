(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "bool"; "prod"; "true"; "false"; "None"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SVar"; "SLit"; "sprop"; "sv"; "SAlu"; "SPUle"; "sobj"; "cell"; "sstate"; "SPBranch"; "SPNot"; "mkCell"; "ss_facts"; "FcsrFrm0"; "mkSS"; "holds"; "valuation"; "DUnknown"; "mkObj"; "SPAlign"; "sprop_below"; "ss_next"; "SAluW"; "SMd"; "ss_lenient"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_LTU"; "ALU_AND"; "ALU_SUB"; "ALU_SLL"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "M_MULHU"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "check_ecfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "pre_regs"; "two62"; "setregs"; "NPOST"; "post_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemset.MuslMemset"; "E_in"; "E_164"; "s_in"; "N14"; "O_dst"; "Pre_memset"; "k2x"; "P_ret_memset"; "kx"; "s164"; "C_164"; "C_164_0"; "C_loop"; "C_loop_0"; "F164_sem"; "FUEL_MS"; "Floop_sem"; "Posts_memset"; "cutpcs_memset"; "cuts_memset"; "F164_auto"; "Floop_auto"; "exits_memset"; "nx"; "vcuts_memset"; "vexits_memset"; "@Stdlib.ZArith.BinInt.Z"; "add"; "land"; "le"; "lt"; "modulo"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "itv"; "leaf"; "RsSymJump"; "list_set"; "mkLeaf"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_get"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section MuslMemset.
Variable segs : list Segment.
Variable base : Z.

Lemma two64_val : 2 ^ 64 = 18446744073709551616. Proof using . reflexivity. Qed.

Lemma land_m4 : ltac2:(tb__ "0|0|
S23S2eS56Z0R1A2S57R1S59Z2Z40A2A2A2S2dS23S55R2ZfffffffffffffffcA2S5aR2S58R2Z4A2A2A3F_;Fx;").
Proof using .
  intros x Hx. change 18446744073709551612 with (2 ^ 64 - 2 ^ 2).
  rewrite land_high_mask by lia. reflexivity.
Qed.

Definition FUEL_MS : nat := 2000%nat.
Definition N14 : sprop := SPUle (SVar 14) (SLit two62).
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S1cSaPcA1SbZ0A1SaPeA1S3S11A1S1bA5").

Definition Pre_memset : sstate := ltac2:(tb__ "0|0|
S18Vbase;S35S34S17S8SdA1S0S10S3eS3S10A1A3S0ScS3dS3ScA1A3S33S7A9").

Definition F164_sem : list sprop := ltac2:(tb__ "0|1|
S0ScS1dP79M0Z2A2S0ScSfSeS24SaP78A1SaG0A1A3SaPeA1A2S3ScA1A3A3").
Definition F164_auto : list sprop := ltac2:(tb__ "0|1|
S0ScSfSaP78A1SbZ3A1A2S0ScSfSbZ4A1SaP79A1M0A2S0ScSfG0SbS36A1A2S0ScS3dS3ScA1A3A3A3A3").
Definition C_164_0 : sstate := ltac2:(tb__ "0|1|
S18S54Vbase;Z68A2S37S35S0S5S2SdA2M0S1S2SdUbSeS24SaPcA1SaP78A1A3A4S0G0S1S2SdUcSaP70A1A4S0G0S1S2SdUdSaP71A1A4S0G0S1S2SdUeSaP79A1A4S0G0S1S2SdUfSbZ9A1A4S0G0S1S2SdU10SaP74A1A4S3G0A1A3A3A3A3A3A3A2S34S17S8SdA1S0S10S3eS3S10A1A3S4eP7aS7A9").
Definition C_164 : sstate := add_facts F164_sem C_164_0.

Definition Floop_sem : list sprop := ltac2:(tb__ "0|1|
S0ScSfSeS24SaP78A1M0SaP79A1A3SaPeA1A2S0ScSfG0SbS36A1A2S3ScA1A3A3").
Definition Floop_auto : list sprop := ltac2:(tb__ "0|1|
S0ScS13S25SbZ1fA1SaP79A1M0A3S0ScSfG0SbS36A1A2S0ScS3dS3ScA1A3A3A3").
Definition C_loop_0 : sstate := ltac2:(tb__ "0|1|
S18S54Vbase;Zd8A2S37S35S0S5S2SdA2M0S1S2SdUbSeS24SaPcA1SaP78A1A3A4S0G0S1S2SdUcSaP70A1A4S0G0S1S2SdUdSbZ1fA1A4S0G0S1S2SdUeSaP79A1A4S0G0S1S2SdUfSaP73A1A4S0G0S1S2SdU10SbZ20A1A4S3G0A1A3A3A3A3A3A3A2S34S17S8SdA1S0S10S3eS3S10A1A3S4fP7aS7A9").
Definition C_loop : sstate := add_facts Floop_sem C_loop_0.

Definition P_ret_memset : sstate := ltac2:(tb__ "0|0|
S18S54Vbase;Zf4A2S5eSdS39S33A1UaSaPcA1A4S34S17S8SdA1S0S10S3eS3S10A1A3S0ScS3dS3ScA1A3S38S7A9").
Definition Posts_memset : list leaf := ltac2:(tb__ "0|0|
S0S5cS5fS41S5dA2S3S5cA1A3").

Definition cutpcs_memset : list Z := ltac2:(tb__ "0|0|
S0S23S54Vbase;Z68A2S0S23S54Vbase;Zd8A2S3S23A1A3A3").

Definition kx : sv := ltac2:(tb__ "0|0|
SeS26S20S27SbZ0A1SaPcA1A3SbZ3A1A3").
Definition nx : sv := ltac2:(tb__ "0|0|
SeS26SeS27SaPeA1S42A3SbZfffffffffffffffcA1A3").
Definition E_164 : sstate := ltac2:(tb__ "0|9|
S18S54Vbase;Z68A2S37S35S0S5S2SdA2M0S1S2SdUbSeS24SaPcA1M1S42A3A4S0G0S1S2SdUcS21S2cSeS28SaPdA1M2SbZ38A1A3M3SbZ101010100A1M4A3A4S0G0S1S2SdUdG4A4S0G0S1S2SdUeS51A4S0G0S1S2SdUfSbZ9A1M5A4S0G0S1S2SdU10G3A4S3G0A1A3A3A3A3A3A3A2S34S17S8SdA1S0S10S1cG1SbZ0A1M6SaPeA1M7S0S11S15SeS24G7SbN4A1A3Z1M8G2A3S0S11S15SeS24G7SbN2A1A3G8G2A3S0S11S15SeS24G7SbN3A1A3G8G2A3S3S11A1A3A3A3S1bA5S3S10A1A3S0ScS14S13S25G7G5A3A1S0ScS14S13S25G7SbZ7A1A3A1S0ScS14S13S25G7SbZ3A1A3A1S0ScS14S13S2bG7G6A3A1S0ScSfG7SbZ4000000000000000A1A2S3ScA1A3A3A3A3A3P64S7A9").

Definition k2x : sv := ltac2:(tb__ "0|0|
SeS24SeS26SeS24SaPcA1SaP78A1A3SbZ4A1A3SbZ18A1A3").
Definition E_in : sstate := ltac2:(tb__ "0|d|
S18S54Vbase;Zd8A2S37S35S0S5S2SdA2M0S1S2SdUbSeS24SeS24SaPcA1M1SaP78A1M2A3S40A3A4S0G0S1S2SdUcSeS29SeS28SaP70A1M3SbZ20A1M4A3M5SeS2aG5G4A3A3A4S0G0S1S2SdUdSbZ1fA1A4S0G0S1S2SdUeSeS27SaP79M6A1M7S40A3M8A4S0G0S1S2SdUfS40A4S0G0S1S2SdU10G4A4S3G0A1A3A3A3A3A3A3A2S34S17S8SdA1S0S10S1cG1SbZ0A1SaPeA1M9S0S11S15SeS24SeS24G7G2A3MaSbN10A1A3Z4MbG3A3S0S11S15SeS24GaSbN14A1A3GbG3A3S0S11S15SeS24GaSbN18A1A3GbG3A3S0S11S15SeS24GaSbN1cA1A3GbG3A3S3S11A1A3A3A3A3S1bA5S3S10A1A3S0ScS14S13S25G8G4A3A1S0ScS14S13S25G7SbZ19A1A3A1S0ScS14S13S25G7SbZ9A1A3A1S0ScS1dG6Z2A2S0ScSfSeS24G2G7A3G9A2S0ScSfG2SbZ3A1A2S0ScSfSbGbA1G7A2S0ScSfG7SbZ4000000000000000A1McA2S0ScSfG9GcA2S3ScA1A3A3A3A3A3A3A3A3A3P7aS7A9").

Definition cuts_memset : list sstate := ltac2:(tb__ "0|0|
S0S12S3fS0S12S44S0S12S46S3S12A1A3A3A3").
Definition exits_memset : list sstate := ltac2:(tb__ "0|0|
S0S12S41S0S12S3bS0S12S3aS3S12A1A3A3A3").

Hypothesis check_memset : ltac2:(tb__ "0|0|
S2dS4S31Vsegs;S49S4cS33S4dS50A6S6A3").

Definition s164 : wsub := infer_sub NF E_164 C_164_0.
Definition s_in : wsub := infer_sub NF E_in C_loop_0.

Hypothesis ent_164 : ltac2:(tb__ "0|0|
S2dS4S63S3bS45S43A3S6A3").
Hypothesis ent_in : ltac2:(tb__ "0|0|
S2dS4S63S3aS47S3cA3S6A3").
Lemma s164_id : ltac2:(tb__ "0|0|
S2dS4S66S43S33A2S6A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma s_in_id : ltac2:(tb__ "0|0|
S2dS4S66S3cS33A2S6A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma s164_120 : wsub_get s164 120 = kx. Proof using . vm_compute. reflexivity. Qed.
Lemma s164_121 : wsub_get s164 121 = nx. Proof using . vm_compute. reflexivity. Qed.
Lemma s164_14 : wsub_get s164 14 = SVar 14. Proof using . vm_compute. reflexivity. Qed.
Lemma s_in_120 : ltac2:(tb__ "0|2|
S2dSdS65S3cP78M0A2SeS24SeS24SeS26SeS24SaPcA1SaG0A1M1A3SbZ4A1A3G1A3SbZ18A1A3A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma s_in_121 : ltac2:(tb__ "0|1|
S2dSdS65S3cP79M0A2SeS27SaG0A1S40A3A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma s_in_14 : wsub_get s_in 14 = SVar 14. Proof using . vm_compute. reflexivity. Qed.

Lemma itv_kx : ltac2:(tb__ "0|0|
S2dS5S23S23A2S5bS16S3bA1S42A2S1S23S23Z0Z3A4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma itv_14 : ltac2:(tb__ "0|0|
S2dS5S23S23A2S5bS16S3bA1SaPeA1A2S1S23S23Z9S36A4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma itv_in_k2 : ltac2:(tb__ "0|1|
S2dS5S23S23A2S5bS16S3aA1SeS26SeS24SaPcA1SaP78A1A3SbZ4M0A1A3A2S1S23S23Z0G0A4A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma itv_in_121 : ltac2:(tb__ "0|0|
S2dS5S23S23A2S5bS16S3aA1SaP79A1A2S1S23S23Z1cS36A4A3"). Proof using . vm_compute. reflexivity. Qed.
Lemma itv_in_120 : ltac2:(tb__ "0|0|
S2dS5S23S23A2S5bS16S3aA1SaP78A1A2S1S23S23Z0Z3A4A3"). Proof using . vm_compute. reflexivity. Qed.

Ltac itv_fact H lem rho e HF :=
  pose proof (itv_sound rho _ e HF) as H; rewrite lem in H; unfold in_itv in H; cbn [fst snd] in H.

Lemma glue_164 : ltac2:(tb__ "0|0|
S1aS60ScS19R1A1S16S3bA1A3S60ScS19S64R2S43A2A1S48A3F_;Frho;").
Proof using .
  intros rho HF.
  itv_fact Bk itv_kx rho kx HF. itv_fact Bn itv_14 rho (SVar 14) HF.
  pose proof (urange (eval rho kx)) as Rk. pose proof (urange (rw rho 14)) as Rn.
  cbn [eval] in Bn. unfold two62 in Bn.
  set (k := bv_unsigned (eval rho kx)) in *. set (n := bv_unsigned (rw rho 14)) in *.

  assert (Vnx : bv_unsigned (eval rho nx) = (n - k) - (n - k) mod 4).
  { unfold nx. cbn [eval]. fold kx. rewrite and_val, lit_unsigned, sub_val. fold k. fold n.
    change (18446744073709551612 mod 2 ^ 64) with 18446744073709551612.
    rewrite (Z.mod_small (n - k)) by lia. rewrite land_m4 by lia. reflexivity. }
  pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)) as M4.
  unfold F164_sem. constructor; [|constructor; [|constructor]].
  -   cbn [holds]. unfold rho_sub. cbn [rw]. rewrite s164_121. split; [lia|].
    rewrite Vnx. change (2 ^ 2) with 4.
    rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
  -   cbn [holds eval]. unfold rho_sub. cbn [rw]. rewrite s164_120, s164_121, s164_14.
    rewrite add_val, Vnx. cbn [eval]. fold k. fold n. rewrite Z.mod_small by lia. lia.
Qed.

Lemma glue_in : ltac2:(tb__ "0|0|
S1aS60ScS19R1A1S16S3aA1A3S60ScS19S64R2S3cA2A1S4aA3F_;Frho;").
Proof using .
  intros rho HF.
  itv_fact Bk2 itv_in_k2 rho (SAlu ALU_AND (SAlu ALU_ADD (SVar 12) (SVar 120)) (SLit 4)) HF. itv_fact B121 itv_in_121 rho (SVar 121) HF. itv_fact B120 itv_in_120 rho (SVar 120) HF.

  assert (J : bv_unsigned (eval rho (SAlu ALU_ADD (SVar 120) (SVar 121))) <= bv_unsigned (eval rho (SVar 14))).
  { exact (proj1 (Forall_forall _ _) HF (SPUle (SAlu ALU_ADD (SVar 120) (SVar 121)) (SVar 14)) ltac:(cbn; tauto)). }
  assert (N : bv_unsigned (eval rho (SVar 14)) <= 4611686018427387904).
  { pose proof (proj1 (Forall_forall _ _) HF (SPUle (SVar 14) (SLit 4611686018427387904)) ltac:(cbn; tauto)) as X.
    cbn [holds eval] in X. rewrite lit_unsigned in X. exact X. }
  cbn [eval] in J. rewrite add_val in J.
  set (a := bv_unsigned (eval rho (SAlu ALU_AND (SAlu ALU_ADD (SVar 12) (SVar 120)) (SLit 4)))) in *.
  set (v120 := bv_unsigned (rw rho 120)) in *. set (v121 := bv_unsigned (rw rho 121)) in *.
  set (n := bv_unsigned (rw rho 14)) in *. cbn [eval] in B121, B120, N. fold v120 in B120. fold v121 in B121. fold n in N.
  unfold two62 in *. rewrite Z.mod_small in J by lia.
  assert (Vk2 : bv_unsigned (eval rho k2x) = a + 24).
  { unfold k2x. cbn [eval]. rewrite add_lit_val. fold a. change (snorm 24) with 24. apply Z.mod_small. lia. }
  assert (V120 : bv_unsigned (eval rho (wsub_get s_in 120)) = a + v120 + 24).
  { rewrite s_in_120. cbn [eval]. rewrite add_lit_val, add_val. fold a. fold v120. change (snorm 24) with 24.
    rewrite (Z.mod_small (a + v120)) by lia. apply Z.mod_small. lia. }
  assert (V121 : bv_unsigned (eval rho (wsub_get s_in 121)) = v121 - (a + 24)).
  { rewrite s_in_121. cbn [eval]. fold k2x. change (bv_unsigned (alu64 ALU_SUB (rw rho 121) (eval rho k2x)) = v121 - (a + 24)).
    rewrite sub_val, Vk2. fold v121. apply Z.mod_small. lia. }
  unfold Floop_sem. constructor; [|constructor; [|constructor]].
  - cbn [holds eval]. unfold rho_sub. cbn [rw]. rewrite add_val, V120, V121, s_in_14. cbn [eval]. fold n.
    rewrite Z.mod_small by lia. lia.
  - cbn [holds eval]. unfold rho_sub. cbn [rw]. rewrite V120, lit_unsigned. unfold two62.
    change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62). lia.
Qed.

Lemma F164_below : ltac2:(tb__ "0|0|
S2dS4S6aScS1eS1fS45A1A1S48A3S6A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma Floop_below : ltac2:(tb__ "0|0|
S2dS4S6aScS1eS1fS47A1A1S4aA3S6A3").
Proof using . vm_compute. reflexivity. Qed.
Lemma cuts_memset_strict : ltac2:(tb__ "0|0|
S2dS4S6bS12S22S4dA3S7A3").
Proof using . vm_compute. reflexivity. Qed.

Theorem memset_sum : ltac2:(tb__ "0|0|
S6eOF_;S9S62A1S61OF_;F_;S1aS69Vsegs;R3R2A3S6dVsegs;R4S68Vsegs;R3S3fR2A4S67Vsegs;R3S33R2S4bA5A4F_;Frho;FK;Fok;").
Proof using check_memset ent_164 ent_in.
  intros ok K rho Hok.
  apply (cfg_sound segs FUEL_MS cutpcs_memset NF cuts_memset exits_memset
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho Posts_memset) Hok).
  - rewrite cuts_memset_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_memset.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[]]]].
    +   apply exit_post; [left; reflexivity | exact HagE].
    +
      revert HagE. apply (exit_reenter segs ok K (fun rho' => agree_below NF rho rho') NF cuts_memset _ E_164 C_164_0 F164_sem s164).
      * right; left; reflexivity.
      * exact ent_164.
      * exact s164_id.
      * intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
      * exact F164_below.
      * exact glue_164.
    +
      revert HagE. apply (exit_reenter segs ok K (fun rho' => agree_below NF rho rho') NF cuts_memset _ E_in C_loop_0 Floop_sem s_in).
      * right; right; left; reflexivity.
      * exact ent_in.
      * exact s_in_id.
      * intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
      * exact Floop_below.
      * exact glue_in.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_memset : list vnode := ltac2:(tb__ "0|1|
S0S2fS30S3fZ6SbZ0A1M0A3S0S2fS30S44Z4G0A3S0S2fS30S46Z2SaP79A1A3S3S2fA1A3A3A3").
Definition vexits_memset : list vnode := ltac2:(tb__ "0|2|
S0S2fS30S41Z0M0SbG0A1M1A3S0S2fS30S3bZ5G1A3S0S2fS30S3aZ3G1A3S3S2fA1A3A3A3").

Hypothesis echeck_memset : ltac2:(tb__ "0|0|
S2dS4S32Vsegs;S49S4cS33S52S53A6S6A3").

Theorem memset_sum_ex : ltac2:(tb__ "0|0|
S9S62A1S61OF_;F_;S1aS6cVsegs;S68Vsegs;R2S3fR1A4S67Vsegs;R2S33R1S4bA5A3Frho;FK;").
Proof using echeck_memset ent_164 ent_in.
  intros K rho.
  change Pre_memset with (vn_state (mkVN Pre_memset 6 (SLit 0))).
  apply (cfg_complete_auto segs FUEL_MS cutpcs_memset NF vcuts_memset vexits_memset
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho Posts_memset)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_memset.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[]]]].
    + apply eexit_post; [left; reflexivity | exact HgE].
    + revert HgE. apply (eexit_reenter segs K (fun rho' => agree_below NF rho rho') NF vcuts_memset _
                           (mkVN E_164 5 (SLit 0)) (mkVN C_164 4 (SLit 0)) F164_sem C_164_0 s164);
        [right; left; reflexivity | reflexivity | exact ent_164 | exact s164_id
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact F164_below | exact glue_164
        | cbn; lia | cbn; lia].
    + revert HgE. apply (eexit_reenter segs K (fun rho' => agree_below NF rho rho') NF vcuts_memset _
                           (mkVN E_in 3 (SLit 0)) (mkVN C_loop 2 (SVar 121)) Floop_sem C_loop_0 s_in);
        [right; right; left; reflexivity | reflexivity | exact ent_in | exact s_in_id
        | intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Floop_below | exact glue_in
        | cbn; lia | cbn; lia].
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

End MuslMemset.
