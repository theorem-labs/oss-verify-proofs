(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.

(* [comment removed for export] *)
Module Icpt_memchr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "rw"; "holds"; "agree_below"; "eval"; "SAlu"; "SLit"; "SVar"; "sprop_below"; "SPNot"; "sobj"; "sprop_eqb"; "ss_next"; "sv"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@Corelib.Init.Logic"; "eq"; "and"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "lt"; "modulo"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA"; "FirstNul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "ok_frameA"; "stableA"; "jpredA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr.MCI"; "Jf"; "Jmc"; "Jz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "Posts_mci"; "GEU65"; "Pre_mci"; "ENDA"; "P_mci"; "big_facts"; "facts_mci"; "rip8_facts"; "sX"; "s_call"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Icpt_memchr.ZF"; "mciZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform StrBytes MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memchrA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations. Import MCHAddr. Import RegionAddr.
Close Scope bv_scope. Open Scope Z_scope.

Lemma Forall_holds_agree : ltac2:(tb__ "0|1|
S20S0S0SfS1A1S4R4R3R2A3S13S10S3eS1S9R5A1R2A3S11A3S1eS1S3R5A1M0R3A3S1eS1G0R4A3F_;F_;F_;FF;Fr2;Fr1;Fn;").
Proof.
  intros n r1 r2 F Hag Hb HF. apply Forall_forall. intros p Hp.
  apply (proj1 (holds_agree n r1 r2 p Hag (proj1 (forallb_forall _ _) Hb p Hp))). exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.
Lemma agree_below_le' : ltac2:(tb__ "0|0|
S20S20S0S0S40R4R3A2S4R4R3R2A3S4R6R4R3A3F_;F_;Fr2;Fr1;Fm;Fn;").
Proof. intros n m r1 r2 Hle (A & B & C). split; [intros i Hi; apply A; lia|]. split; assumption. Qed.
Lemma SPA_add_facts : ltac2:(tb__ "0|0|
S2aS0SfS15Q40A1A1SfS1A1S3bS21S1eS1S3R5A1R3A3S13S10S3eS1S9SdS3cR3A1A1A1R4A3S11A3S26S12R8R4R7R6R3A6S26S12R9S47R6R5A2R8R7R4A6F_;F_;F_;Fw;FA;FF;Ftp;Frho;FJ;").
Proof. intros J rho tp F A w HF Hb [Hsm HJ]. split; [apply smatchA_add_facts; assumption | exact HJ]. Qed.

Lemma triple_pre : ltac2:(tb__ "0|1|
S21OF_;S22OS22S21R4R1A1R4F_;Fw;R3S24S12R6R5R3A4M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.
Lemma etriple_pre : ltac2:(tb__ "0|2|
S21OF_;M0OG0S21R4R1A1R4F_;Fw;R3S23S12R5R3A3M1F_;G1F_;F_;FQ;FX;FP;").
Proof. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.

Lemma holds_fact : ltac2:(tb__ "0|0|
S0SfS1A1S1S1eS1S3R3A1R2A3S13S10S3fS1ScR2A1R3A3S11A3S3R5R3A2F_;F_;Fq;Ffacts;Frho;").
Proof.
  intros rho facts q HF H. apply existsb_exists in H as (p & Hp & E). apply sprop_eqb_sound in E. subst p.
  exact (proj1 (Forall_forall _ _) HF _ Hp).
Qed.

Section ZF.
Variable r : valuation.
Let XB := bv_unsigned (rw r 18). Let XL := bv_unsigned (rw r 19). Let XO := bv_unsigned (rw r 20).
Let z := bv_unsigned (rw r 16). Let A := bv_unsigned (rw r 17). Let n := bv_unsigned (rw r 14).
Definition mciZ : Prop := ltac2:(tb__ "0|2|
S14S18S17Vz;Z10A2VA;A2S14S18VA;S19Z2M0Z3eA2M1A2S14S18S17VXO;VA;A2VXL;A2S14S18VXL;S19G0Z28A2A2S14S18S17VXB;VXL;A2S19G0Z2fA2A2S14S1aVz;Vn;A2S18Vn;G1A2A2A2A2A2A2A2").
Lemma two62_eq : two62 = 2 ^ 62. Proof. reflexivity. Qed.
Lemma facts_mciZ : ltac2:(tb__ "0|0|
S1eS1S3Vr;A1S36A3S42F_;").
Proof.
  intros HF. unfold facts_mci in HF.
  apply Forall_cons_iff in HF as [F1 HF]. apply Forall_cons_iff in HF as [F2 HF]. apply Forall_cons_iff in HF as [F3 HF].
  apply Forall_cons_iff in HF as [F4 HF]. apply Forall_cons_iff in HF as [F5 HF]. apply Forall_cons_iff in HF as [F6 HF].
  apply Forall_cons_iff in HF as [F7 HF]. apply Forall_cons_iff in HF as [F8 HF]. apply Forall_cons_iff in HF as [F9 HF].
  apply Forall_cons_iff in HF as [F10 HF]. apply Forall_cons_iff in HF as [F11 HF]. apply Forall_cons_iff in HF as [F12 HF].
  apply Forall_cons_iff in HF as [F13 HF]. apply Forall_cons_iff in HF as [F14 HF]. apply Forall_cons_iff in HF as [F15 HF].
  apply Forall_cons_iff in HF as [F16 HF]. apply Forall_cons_iff in HF as [F17 HF]. apply Forall_cons_iff in HF as [F18 HF]. apply Forall_cons_iff in HF as [F19 HF].
  apply Forall_cons_iff in HF as [F20 HF]. apply Forall_cons_iff in HF as [F21 HF].
  pose proof (urange (rw r 14)). pose proof (urange (rw r 16)). pose proof (urange (rw r 17)). pose proof (urange (rw r 18)).
  pose proof (urange (rw r 19)). pose proof (urange (rw r 20)).
  unfold vXB, vXL, vXO in *.
  cbn [holds branch_taken eval] in F1, F2, F3, F4, F5, F11, F12, F13, F14, F15, F16, F17, F21. unfold bv_ltu in F1. apply Z.ltb_lt in F1.
  rewrite add_lit_val in F21. change (snorm 16) with 16 in F21.
  rewrite lit_unsigned in F15. rewrite lit_unsigned in F17. change ((2 ^ 47 - 64) mod 2 ^ 64) with (2 ^ 47 - 64) in F17.
  rewrite add_lit_val in F2. change (snorm 8) with 8 in F2.
  rewrite lit_unsigned in F3. change (8 mod 2 ^ 64) with 8 in F3.
  rewrite two62_eq, lit_unsigned in F4. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F4.
  rewrite two62_eq, lit_unsigned in F5. change ((2 ^ 62) mod 2 ^ 64) with (2 ^ 62) in F5.
  rewrite add_val in F11. rewrite lit_unsigned in F14. change ((2 ^ 40) mod 2 ^ 64) with (2 ^ 40) in F14.
  rewrite add_val, lit_unsigned in F16. change ((2 ^ 47) mod 2 ^ 64) with (2 ^ 47) in F16.
  unfold mciZ. subst XB XL XO z A n.
  assert (E2 : (bv_unsigned (rw r 16) + 8) mod 2 ^ 64 = bv_unsigned (rw r 16) + 8).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 8) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 8) with ((bv_unsigned (rw r 16) + 8 - 2 ^ 64) + 1 * 2 ^ 64) in F2 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F2 by lia. lia. }
  rewrite E2 in F2.
  assert (E21 : (bv_unsigned (rw r 16) + 16) mod 2 ^ 64 = bv_unsigned (rw r 16) + 16).
  { destruct (Z_lt_le_dec (bv_unsigned (rw r 16) + 16) (2 ^ 64)); [apply Z.mod_small; lia |].
    exfalso. replace (bv_unsigned (rw r 16) + 16) with ((bv_unsigned (rw r 16) + 16 - 2 ^ 64) + 1 * 2 ^ 64) in F21 by lia.
    rewrite Z_mod_plus_full, Z.mod_small in F21 by lia. lia. }
  rewrite E21 in F21.
  assert (E11 : (bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) mod 2 ^ 64 = bv_unsigned (rw r 20) + bv_unsigned (rw r 17)) by (apply Z.mod_small; lia).
  rewrite E11 in F11.
  assert (E16 : (bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) mod 2 ^ 64 = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)) by (apply Z.mod_small; lia).
  rewrite E16 in F16.
  repeat split; lia.
Qed.
End ZF.

Lemma rip8_facts_hold : ltac2:(tb__ "0|3|
S0SeS1fS13S1fS16Q40M0S5R3R2A2A2R1A3S18Z0R2A2S18S17S17S16G0S2R5P14A2A2R3A2Z8A2S16G0S2R5P13M1A2A2A2S18S16G0S2R6G1A2A2S19Z2M2Z28A2A2S18S17S16G0S2R7P12A2A2S16G0S2R7G1A2A2A2S19G2Z2fA2A2S1eS1S3R8A1S37R7A1A3F_;F_;F_;F_;F_;Fk;Fn;Fr;").
Proof.
  intros r n k Hn Hk H1 H2 H3.
  pose proof (urange (rw r 18)) as R18. pose proof (urange (rw r 19)) as R19. pose proof (urange (rw r 20)) as R20.
  assert (U8 : bv_unsigned (eval r vXL8) = bv_unsigned (rw r 19) - 8).
  { unfold vXL8, vXL. apply (U_addc r (SVar 19) (-8)); [reflexivity | lia | lia]. }
  assert (UOn : bv_unsigned (eval r (SAlu ALU_ADD vXO n)) = bv_unsigned (rw r 20) + k).
  { unfold vXO. apply (U_add2 r (SVar 20) n); [reflexivity | exact Hn | lia]. }
  assert (UB8 : bv_unsigned (eval r (SAlu ALU_ADD vXB vXL8)) = bv_unsigned (rw r 18) + (bv_unsigned (rw r 19) - 8)).
  { unfold vXB. apply (U_add2 r (SVar 18) vXL8); [reflexivity | exact U8 | lia]. }
  assert (UBL : bv_unsigned (eval r (SAlu ALU_ADD vXB vXL)) = bv_unsigned (rw r 18) + bv_unsigned (rw r 19)).
  { unfold vXB, vXL. apply (U_add2 r (SVar 18) (SVar 19)); [reflexivity | reflexivity | lia]. }
  unfold rip8_facts.
  repeat (apply Forall_cons; [cbn [holds]; rewrite ?UOn, ?U8, ?UB8, ?UBL, ?Hn; try rewrite (U_lit64 r (2 ^ 40)) by lia;
                              try rewrite (U_lit64 r (2 ^ 47 - 8)) by lia; change (eval r vXB) with (rw r 18); change (eval r vXO) with (rw r 20); lia |]).
  apply Forall_nil.
Qed.

Section MCI.
Variable ok : world -> Prop.
Variable J0 : jpredA.
Hypothesis Hok : ok_frameA segs ok J0.
Hypothesis Hst0 : stableA segs NF J0.

Definition Jf (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S4S1dVrho1;R4A3S14S13G0R3Vtp;A3VJ0;Vrho1;Vtp;R2R1A4A2A2Lmd;Ltr;Lt;Lr;").
Definition Jz (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S13G0R3Vtp;A3VJ0;Vrho1;Vtp;R2R1A4A2Lmd;Ltr;Lt;L_;").
Definition Jmc (rho1 : valuation) (tp : list word) : jpredA := ltac2:(tb__ "0|1|
S0SfS15Q40A1A1M0SfS2cA1S2bS14S13G0R3Vtp;A3S14VJ0;Vrho1;Vtp;R2R1A4S25R4A1A2A2Lmd;Ltr;Lt;Lr;").

Lemma Jf_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S20S40S1dR1A2S29S12R2S2dR4R3A2A3F_;Fn;Ftp;Frho1;").
Proof.
  intros rho1 tp n Hn r r' t tr md md' Hag Hme (H1 & H2 & H3). split; [|split; [exact H2|]].
  - eapply agree_below_trans; [exact H1 | eapply agree_below_le'; [exact Hn | exact Hag]].
  - subst t. eapply Hst0; [apply agree_below_refl | exact Hme | exact H3].
Qed.
Lemma Jz_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S20S29S12R1S2fR3R2A2A3Fn;Ftp;Frho1;").
Proof. intros rho1 tp n r r' t tr md md' Hag Hme [-> H3]. split; [reflexivity|]. eapply Hst0; [apply agree_below_refl | exact Hme | exact H3]. Qed.
Lemma Jmc_stable : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S29S12S1dS2eR2R1A2A3Ftp;Frho1;").
Proof.
  intros rho1 tp r r' t tr md md' Hag Hme (-> & H3 & H4). split; [reflexivity|]. split.
  - eapply Hst0; [apply agree_below_refl | exact Hme | exact H3].
  - eapply FirstNul_agree; [| exact Hag | exact H4]. reflexivity.
Qed.
Lemma Jf_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2dR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' (_ & -> & HJ). eapply Hok; eauto. Qed.
Lemma Jz_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2fR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' [-> HJ]. eapply Hok; eauto. Qed.
Lemma Jmc_okf : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S28S12Vok;S2eR2R1A2A3Ftp;Frho1;").
Proof. intros rho1 tp r t tr ms md msv' (-> & HJ & _). eapply Hok; eauto. Qed.

Lemma FirstNul_call : ltac2:(tb__ "0|0|
S0SfSbA1S41S25R3A1S25S44S43R4R3R2A3S39A2A1F_;Fms;FR;Frho;").
Proof.
  intros rho R ms [H0 H1]. destruct shape_call as (_ & _ & _ & S16). unfold FirstNul.
  change (rw (rho_sub (rho_absorb rho R ms) s_call) 16) with (eval (rho_absorb rho R ms) (wsub_get s_call 16)). rewrite S16.
  cbn [eval rw rl rho_sub rho_absorb]. split; assumption.
Qed.

Section ClassFacts.
Variable r : valuation.
Hypothesis HFm : Forall (holds r) facts_mci.
Hypothesis H140 : ltac2:(tb__ "0|0|
S13S15Q40A1S2Vr;P8cA2S2Vr;P10A2A3").
Let z := bv_unsigned (rw r 16).

Lemma U_sX : ltac2:(tb__ "0|1|
S13S1fS16Q40M0S5Vr;S38A2A2S17S16G0S2Vr;P12A2A2S16G0S2Vr;P14A2A2A2A3").
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)).
  unfold sX, vXB, vXO. apply (U_add2 r (SVar 18) (SVar 20)); [reflexivity | reflexivity | lia].
Qed.
Lemma U_z1 : ltac2:(tb__ "0|1|
S13S1fS16Q40S5Vr;S6S3aS8P8cA1S7Z1M0A1A3A2A2S17Vz;G0A2A3").
Proof. pose proof (urange (rw r 16)). destruct (facts_mciZ r HFm) as (Z1 & Z2 & _). apply (U_addc r (SVar 140) 1 z); [cbn [eval]; rewrite H140; reflexivity | lia | lia]. Qed.
Lemma U_ENDA : ltac2:(tb__ "0|1|
S13S1fS16Q40M0S5Vr;S33A2A2S17S17S16G0S2Vr;P12A2A2S16G0S2Vr;P14A2A2A2Vz;A2A3").
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 17)). pose proof (urange (rw r 16)).
  assert (A2 : bv_unsigned (eval r (SAlu ALU_ADD sX (SAlu ALU_ADD (SVar 140) (SLit 1)))) = bv_unsigned (rw r 18) + bv_unsigned (rw r 20) + (z + 1)).
  { apply (U_add2 r _ _ _ _ U_sX U_z1). lia. }
  unfold ENDA. rewrite (U_addc r _ (-1) _ A2); lia.
Qed.
Lemma post_facts_hold : Forall (holds r) post_facts.
Proof.
  destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 18)). pose proof (urange (rw r 20)). pose proof (urange (rw r 16)).
  unfold post_facts. constructor; [|constructor; [|constructor]]; cbn [holds].
  - change (eval r vXB) with (rw r 18). rewrite U_ENDA. lia.
  - rewrite (U_addc r ENDA 1 _ U_ENDA) by lia. unfold vXB, vXL. pose proof (urange (rw r 19)).
    rewrite (U_add2 r (SVar 18) (SVar 19) (bv_unsigned (rw r 18)) (bv_unsigned (rw r 19)) eq_refl eq_refl) by lia. lia.
Qed.
Lemma U_m64 : ltac2:(tb__ "0|1|
S13S1fS16Q40S5Vr;S6S3aS8P8cA1S7N40A1A3A2A2S1bS1cVz;Z40M0A2S19Z2G0A2A2A3").
Proof. cbn [eval]. rewrite add_lit_val, H140. change (snorm (-64)) with (-64). reflexivity. Qed.
Lemma GEU65_S : ltac2:(tb__ "0|0|
S18S17Vz;Z1A2Z40A2S3Vr;SaS31A1A2F_;").
Proof.
  intros Hz. pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64, (U_lit64 r 18446744073709551551) by lia.
  replace ((z - 64) mod 2 ^ 64) with (z - 64 + 2 ^ 64) by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; rewrite Z.mod_small; lia).
  destruct (Z.ltb_spec 18446744073709551551 (z - 64 + 2 ^ 64)); [cbn; congruence | lia].
Qed.
Lemma GEU65_B : ltac2:(tb__ "0|0|
S18Z41S17Vz;Z1A2A2S3Vr;S31A2F_;").
Proof.
  intros Hz. destruct (facts_mciZ r HFm) as (Z1 & Z2 & _). pose proof (urange (rw r 16)). unfold GEU65. cbn [holds branch_taken]. unfold bv_ltu. rewrite U_m64, (U_lit64 r 18446744073709551551) by lia.
  rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec 18446744073709551551 (z - 64)); [lia | reflexivity].
Qed.
Lemma big_facts_hold : ltac2:(tb__ "0|0|
S18Z41S17Vz;Z1A2A2S1eS1S3Vr;A1S35A3F_;").
Proof.
  intros Hz. destruct (facts_mciZ r HFm) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7). pose proof (urange (rw r 16)). pose proof (urange (rw r 20)).
  pose proof U_z1 as U141. change (SAlu ALU_ADD (SVar 140) (SLit 1)) with N1 in U141.
  unfold big_facts. apply Forall_app. split.
  2:{ apply (rip8_facts_hold r N1 (z + 1) U141); lia. }
  constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds]; unfold vXO, vXL.
  - pose proof (urange (rw r 19)). rewrite (U_add2 r (SVar 20) _ (bv_unsigned (rw r 20)) (z + 1) eq_refl U141) by lia. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141. change (eval r (SVar 19)) with (rw r 19). lia.
  - rewrite U141, (U_lit64 r 1) by lia. lia.
Qed.
End ClassFacts.

Lemma to_post : ltac2:(tb__ "0|0|
S3bS45S0S0SfS15Q40A1A1S0S21S13S10S3dR7S34R6A3S11A3S13S10S46R7S1dA2S11A3S4S1dR7R6A3S4S1dR7R5A3S26S12S2dR8R7A2RbR6R7R5A6S27S12VJ0;S1dRaR8S30R6A7F_;F_;F_;F_;F_;Fw;FrhoR;Ftp;Frho1;Frho;Fsp;FG;").
Proof.
  intros G sp rho rho1 tp rhoR w Hent Hid Hag1 HagR HS.
  pose proof (SPA_entails segs (Jf rho1 tp) NF G P_mci sp rhoR tp w Hent Hid (Jf_stable rho1 tp NF (Pos.le_refl _)) HS) as [Hsm (Hag & _ & HJ)].
  exists (mkLeafA P_mci RsSymJump), (rho_sub rhoR sp). split; [left; reflexivity|]. split.
  - eapply agree_below_trans; [exact Hag1 | exact Hag].
  - split; [exact Hsm|]. eapply Hst0; [exact Hag | apply mat_equiv_refl | exact HJ].
Qed.

Theorem mci_sum : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S25R2A1S24S12Vok;S26S12VJ0;S32R3R2A5S27S12VJ0;S1dR3R2S30A6A4F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct shape_call as (HnC & HlenP & HnP & _). destruct shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbF). destruct shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct ids_mci as [IdS IdB].
  apply (triple_pre ok _ (Forall (holds rho) facts_mci)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_mci w Hsm) | intros HF0].

  eapply (runA_tr segs ok FUEL_MCI CUTS_MCI Pre_mci _ J0 rho tp); [exact run_call | exact HlenP | exact Hok | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_mci Hag1 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF0) as HF1.
  eapply triple_conseq with (P := SPA segs (Jf rho1 tp) E_call rho1 tp);
    [intros w [Hsm HJ]; split; [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_soundA segs ok (Jf rho1 tp) (Jmc rho1 tp) (Jmc rho1 tp) (Jf rho1 tp) E_call Pre_memchr0 s_call R_call Posts_memchr0 _ rho1 tp efr_call chk_call).
  - intros rho2 tp2. apply (triple_pre ok _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (memchr0_sum ok (Jmc rho1 tp) rho2 tp2 (Jmc_okf rho1 tp) (Jmc_stable rho1 tp) HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [exact (proj1 HLK)|]. split; [reflexivity | exact HJ'].
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite imp_call. rewrite HnC in Hag'.
    apply (triple_pre ok _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_mci Hag' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF1) as HF'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }

    eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_mci T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HF' H140)]. }
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_S _ (Jf rho1 tp) rho' tp);
        [exact run_S | exact HlS | apply Jf_okf | rewrite HnS; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XS rhoR R_S G_S tp w xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post G_S sp_S rho rho1 tp rhoR w ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HF' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HF' H140) | apply (big_facts_hold rho' HF' H140); rewrite Hz'; lia]. }
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_B _ (Jf rho1 tp) rho' tp);
        [exact run_B | exact HlB | apply Jf_okf | rewrite HnB; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply triple_conseq with (P := SPA segs (Jf rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 1 (SLit (-2128)) _ tp w split_rip HS) | intros w Hw; exact Hw |].
      apply (call_soundA segs ok (Jf rho1 tp) (Jz rho1 tp) (Jz rho1 tp) (Jf rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp efr_rip chk_rip).
      * intros rho2 tp2. exact (region_sum ok (Jz rho1 tp) rho2 tp2 (Jz_okf rho1 tp) (Jz_stable rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (triple_pre ok _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_mci)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply triple_conseq with (P := SPA segs (Jf rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (runA_tr segs ok FUEL_MCI CUTS_MCI T_ripF _ (Jf rho1 tp) rho'' tp);
          [exact run_B2 | exact HlTF | apply Jf_okf | rewrite HnTF; apply Jf_stable; unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros n Hg w HS. apply Hg. apply (SPA_axforms segs _ XB rhoR R_B G_B tp w xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post G_B sp_B rho rho1 tp rhoR w ent_B IdB Hag1 Hag3 HS).
Qed.

Theorem mci_sum_ex : ltac2:(tb__ "0|0|
S0SfS15Q40A1A1S25R2A1S23S12S26S12VJ0;S32R3R2A5S27S12VJ0;S1dR3R2S30A6A3F_;Ftp;Frho;").
Proof.
  intros rho tp HFN.
  destruct shape_call as (HnC & HlenP & HnP & _). destruct shape_imp as (HnI & HlS & HnS & HlB & HnB & Hf140 & HbS & HbB).
  destruct shape_rip as (HnRS & HnTr & HlTF & HnTF & HnE & HbF). destruct shape_ret as (HnRS' & HnRB & HgeS & HgeB). destruct ids_mci as [IdS IdB].
  apply (etriple_pre _ (Forall (holds rho) facts_mci)); [intros w [Hsm _]; exact (smatchA_facts segs rho tp Pre_mci w Hsm) | intros HF0].

  eapply (erunA_tr segs FUEL_MCI CUTS_MCI Pre_mci _ J0 rho tp); [exact run_call | exact HlenP | rewrite HnP; exact Hst0 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state]. rewrite HnP in Hag1.
  pose proof (FirstNul_agree NF rho rho1 ltac:(reflexivity) Hag1 HFN) as HFN1.
  pose proof (Forall_holds_agree NF rho rho1 facts_mci Hag1 ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF0) as HF1.
  eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) E_call rho1 tp);
    [intros w [Hsm HJ]; split; [exact Hsm | split; [apply agree_below_refl | split; [reflexivity | exact HJ]]] | intros w Hw; exact Hw |].

  apply (call_completeA segs (Jf rho1 tp) (Jmc rho1 tp) (Jmc rho1 tp) (Jf rho1 tp) E_call Pre_memchr0 s_call R_call Posts_memchr0 _ rho1 tp efr_call chk_call).
  - intros rho2 tp2. apply (etriple_pre _ (FirstNul rho2)); [intros w [_ (_ & _ & H)]; exact H | intros HFN2].
    exact (memchr0_sum_ex (Jmc rho1 tp) rho2 tp2 (Jmc_stable rho1 tp) HFN2).
  - intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity|]. split; [exact HJ|]. apply FirstNul_call. exact HFN1.
  - intros L rho' rhoL tpL tr ms md tr' md' HinL Hsm _ HLK (-> & HJ' & _). split; [exact (proj1 HLK)|]. split; [reflexivity | exact HJ'].
  - intros L rho' tpL [<-|[]] Hag'. cbn [la_state]. rewrite imp_call. rewrite HnC in Hag'.
    apply (etriple_pre _ (tpL = tp /\ Forall (holds rho') (ss_facts (ax_S T_imp))));
      [intros w [Hsm (_ & E & _)]; split; [exact E | exact (smatchA_facts segs _ _ _ w Hsm)] | intros [-> HFi]].
    pose proof (Forall_holds_agree NF rho1 rho' facts_mci Hag' ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HF1) as HF'.
    assert (H140 : rw rho' 140 = rw rho' 16) by exact (holds_fact rho' _ _ HFi Hf140).
    assert (Hz' : rw rho' 16 = rw rho 16).
    { destruct Hag1 as (A1 & _ & _). destruct Hag' as (A2 & _ & _). rewrite <- (A2 16%positive ltac:(reflexivity)), <- (A1 16%positive ltac:(reflexivity)). reflexivity. }
    eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_impF rho' tp);
      [intros w HS; exact (SPA_add_facts _ rho' tp facts_mci T_imp w HF' ltac:(rewrite HnI; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
    destruct (Z_lt_le_dec (bv_unsigned (rw rho 16) + 1) 65) as [HzS|HzB].
    +
      assert (HFS : Forall (holds rho') factsS).
      { unfold factsS. constructor; [apply (GEU65_S rho' H140); rewrite Hz'; lia | exact (post_facts_hold rho' HF' H140)]. }
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_S rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsS T_impF w HFS ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_S _ (Jf rho1 tp) rho' tp);
        [exact run_S | exact HlS | rewrite HnS; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnS in HagR.
      intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XS rhoR R_S G_S tp w xf_S) in HS.
      assert (Hag3 : agree_below NF rho1 rhoR).
      { eapply agree_below_trans; [exact Hag' | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
      exact (to_post G_S sp_S rho rho1 tp rhoR w ent_S IdS Hag1 Hag3 HS).
    +
      assert (HFB : Forall (holds rho') factsB).
      { unfold factsB. constructor; [apply (GEU65_B rho' HF' H140); rewrite Hz'; lia |].
        apply Forall_app. split; [exact (post_facts_hold rho' HF' H140) | apply (big_facts_hold rho' HF' H140); rewrite Hz'; lia]. }
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_B rho' tp);
        [intros w HS; exact (SPA_add_facts _ rho' tp factsB T_impF w HFB ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
      eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_B _ (Jf rho1 tp) rho' tp);
        [exact run_B | exact HlB | rewrite HnB; apply Jf_stable; unfold NF; lia |].
      intros L2 rhoE [<-|[]] HagE. cbn [la_state]. rewrite HnB in HagE.
      eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) E_ripS rhoE tp);
        [intros w HS; exact (SPA_split segs _ rhoE E_rip 1 (SLit (-2128)) _ tp w split_rip HS) | intros w Hw; exact Hw |].
      apply (call_completeA segs (Jf rho1 tp) (Jz rho1 tp) (Jz rho1 tp) (Jf rho1 tp) E_ripS Pre_rip s_rip R_rip Posts_rip _ rhoE tp efr_rip chk_rip).
      * intros rho2 tp2. exact (region_sum_ex (Jz rho1 tp) rho2 tp2 (Jz_stable rho1 tp NF)).
      * intros tr ms md Hsm (_ & _ & HJ). split; [reflexivity | exact HJ].
      * intros L rho'' rhoL tpL tr ms md tr' md' HinL Hsm (HagE' & _ & _) HLK [-> HJ']. split; [| split; [reflexivity | exact HJ']].
        eapply agree_below_trans; [exact HagE' |]. eapply agree_below_le; [| exact (proj1 HLK)]. rewrite HnRS. apply Pos.leb_le in HnE. unfold NF in *; lia.
      * intros L rho'' tpL [<-|[]] Hag''. cbn [la_state]. rewrite imp_rip. rewrite HnRS in Hag''. apply Pos.leb_le in HnE.
        apply (etriple_pre _ (tpL = tp)); [intros w [_ (_ & E & _)]; exact E | intros ->].
        assert (HF'' : Forall (holds rho'') (SPEq (SVar 140) (SVar 16) :: facts_mci)).
        { apply (Forall_holds_agree 141 rho' rho''); [| OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | constructor; [exact (holds_fact rho' _ _ HFi Hf140) | exact HF']].
          eapply agree_below_trans; [exact HagE | eapply agree_below_le; [exact HnE | exact Hag'']]. }
        eapply etriple_conseq with (P := SPA segs (Jf rho1 tp) T_ripF rho'' tp);
          [intros w HS; exact (SPA_add_facts _ rho'' tp _ T_rip w HF'' ltac:(rewrite HnTr; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) HS) | intros w Hw; exact Hw |].
        eapply (erunA_tr segs FUEL_MCI CUTS_MCI T_ripF _ (Jf rho1 tp) rho'' tp);
          [exact run_B2 | exact HlTF | rewrite HnTF; apply Jf_stable; unfold NF; lia |].
        intros L3 rhoR [<-|[]] HagR. cbn [la_state]. rewrite HnTF in HagR.
        intros w HS. exists w. split; [apply wsteps_refl|]. apply (SPA_axforms segs _ XB rhoR R_B G_B tp w xf_B) in HS.
        assert (Hag3 : agree_below NF rho1 rhoR).
        { eapply agree_below_trans; [exact Hag' |]. eapply agree_below_trans; [eapply agree_below_le; [| exact HagE]; unfold NF; lia |].
          eapply agree_below_trans; [eapply agree_below_le; [| exact Hag'']; unfold NF; lia | eapply agree_below_le; [| exact HagR]; unfold NF; lia]. }
        exact (to_post G_B sp_B rho rho1 tp rhoR w ent_B IdB Hag1 Hag3 HS).
Qed.
End MCI.
End Icpt_memchr.

(* [comment removed for export] *)
Module Asan_memcpy_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "holds"; "rw"; "ss_facts"; "eval"; "ss_next"; "SLit"; "sprop_below"; "SVar"; "agree_below"; "SAlu"; "SPBranch"; "SPNot"; "soff"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "SHB"; "ACEIL"; "@Corelib.Lists.ListDef"; "Forall"; "@Corelib.Init.Datatypes"; "list"; "bool"; "cons"; "true"; "nil"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "True"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "la_state"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "pow"; "sub"; "lt"; "modulo"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "ok_frameA"; "stableA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy"; "FT"; "Posts_mc"; "Pre_mc0"; "E_src"; "E_dst"; "base_mc"; "E_real"; "Pre_mc1"; "Pre_mc2"; "E_Ld_bk"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "R_dst"; "R_real"; "R_src"; "cuts_mc"; "s_dst"; "s_real"; "s_src"; "vcuts_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Asan_memcpy_proof"; "clsZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof"; "opZ"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "cur"; "F_L"; "xor_facts"; "gs"; "lastd"; "lasts"; "ord1"; "ord2"; "vBd"; "vBs"; "vLd"; "vLs"; "hi_fact"; "lo_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "add"; "HSE"; "vN"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "vnodeA"; "withGA"; "vna_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_XOR"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "Posts_memcpyA"; "Pre_memcpyA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import RegionAddr AMCAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma base_mc_Z : ltac2:(tb__ "0|4|
S1S13S0S2R1A1S37A3S19S4fR2PfP10P11A4S19S4fR2P13P34P35A4S19S19S22Z1S29Q40M0S3R2P12A2A2M1A2S22G1S24Z2M2Z28A2A2A2S19S19S22S23S12Z900A2S29G0S3R2PaA2A2M3A2S22G3S24G2Z3fA2A2A2S1aS50S27G3Z10A2Z0A3A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold base_mc in HF. apply Forall_app in HF as [HD HF]. apply Forall_app in HF as [HS HN].
  pose proof (urange (rw rho 18)) as RN. pose proof (urange (rw rho 10)) as R10.
  have_fact N1 HN (SPUle (SLit 1) vN). have_fact N2 HN (SPUle vN (SLit (2 ^ 40))).
  have_fact N3 HN (SPUle (SLit (ACEIL + 2304)) (SVar 10)). have_fact N4 HN (SPUle (SVar 10) (SLit (2 ^ 63))).
  have_fact N5 HN (SPAlign 10 4).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia.
  rewrite (U_lit64 rho (ACEIL + 2304)) in N3 by (unfold ACEIL; lia). rewrite (U_lit64 rho (2 ^ 63)) in N4 by lia.
  cbn [eval] in N1, N2, N3, N4. destruct N5 as [_ N5]. change (2 ^ 4) with 16 in N5.
  split; [exact (opnd_Z rho 15 16 17 HD)|]. split; [exact (opnd_Z rho 19 52 53 HS)|]. repeat split; lia.
Qed.

Ltac split_mid HF HX HT :=
  cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Lemma FT_Z : ltac2:(tb__ "0|1|
S1S13S0S2R1A1S32A3S19S4fR2PfP10P11A4S19S4fR2P13P34P35A4S19S22Z1S29Q40S3R2P12A2A2M0A2S22G0S24Z2Z28A2A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. unfold FT in HF. apply Forall_app in HF as [_ HB].
  destruct (base_mc_Z rho HB) as (ZD & ZS & ZN & _). auto.
Qed.

Lemma opZ_sub : ltac2:(tb__ "0|1|
S1S4cS51S51S51S6aR3S2aA2M0G0G0S1aS15S4dR7S2aA2S17A3S4fR9R7R6R5A4S4fS4bRaR9A2R8R7R6A4F_;F_;F_;F_;F_;Fio;Fil;Fib;Fs;Frho;").
Proof.
  intros rho s ib il io Hb Hl Ho Hid HZ.
  assert (E : forall v, (v < NF)%positive -> rw (rho_sub rho s) v = rw rho v).
  { intros v Hv. rewrite rw_sub, (wsub_get_id s NF v Hid Hv). reflexivity. }
  unfold opZ in *. cbv zeta in *.
  rewrite (E ib Hb), (E il Hl), (E io Ho), (E 18%positive eq_refl). exact HZ.
Qed.

Section Glue.
Variable rho : valuation.

Lemma glue_Ls_in : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS42A1A1A3S13S0S2S4bVrho;S3fA2A1S53S5bS5dS57A3A3F_;").
Proof.
  intros HF. unfold E_Ls_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_in).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 19)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 53)) as R53.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E19, ?E52, ?E53; unfold HSE in *; lia.
Qed.

Lemma glue_Ls_bk : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS41A1A1A3S13S0S2S4bVrho;S3eA2A1S53S5bS5dS57A3A3F_;").
Proof.
  intros HF. unfold E_Ls_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 19 52 53 rho ZS ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZS as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ls_bk).
  assert (ZS' : opZ rho' 19 52 53) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ls_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E19 : rw rho' 19 = rw rho 19) by reflexivity.
  assert (E52 : rw rho' 52 = rw rho 52) by reflexivity. assert (E53 : rw rho' 53 = rw rho 53) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 19 52 53 rho' ZS' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E19, ?E52, ?E53, ?E141; unfold HSE in *; try lia.
Qed.

Lemma glue_Ld_in : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS40A1A1A3S13S0S2S4bVrho;S3dA2A1S53S5aS5cS56A3A3F_;").
Proof.
  intros HF. unfold E_Ld_in in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_Ld_bk : ltac2:(tb__ "0|0|
S13S0S2Vrho;A1S4S1eS3bA1A1A3S13S0S2S4bVrho;S3cA2A1S53S5aS5cS56A3A3F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT.
  destruct (FT_Z rho HT) as (ZD & ZS & ZN).
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_Ld_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_Ls_in : ltac2:(tb__ "0|0|
S1aS28Q40A1S5S4bVrho;S3fA2S52A2S5Vrho;S55A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ls_bk : ltac2:(tb__ "0|0|
S1aS28Q40A1S5S4bVrho;S3eA2S52A2S5Vrho;S63S52S7Z1A1A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_in : ltac2:(tb__ "0|1|
S1aS28Q40A1S5S4bVrho;S3dA2S63S52S7S24Z2Z3eA2A1M0A2A2S5Vrho;S63S55G0A2A2A3").
Proof. reflexivity. Qed.
Lemma meas_Ld_bk : ltac2:(tb__ "0|2|
S13S0S2Vrho;A1S4S1eS3bA1A1A3S22S29Q40M0S5Vrho;S63S52S7S23S24Z2Z3eA2M1Z1A2A1A2A2A2S29G0S5S4bVrho;S3cA2S63S52S7G1A1A2A2A2A2F_;").
Proof.
  intros HF. unfold E_Ld_bk in HF. split_mid HF HX HT. apply Forall_app in HX as [HL _].
  have_fact A3 HL (SPUle cur (SLit (2 ^ 61 - 1))). rewrite (U_lit64 rho (2 ^ 61 - 1)) in A3 by lia.
  change (eval rho cur) with (rw rho 140) in A3. pose proof (urange (rw rho 140)) as R140.
  assert (E1 : bv_unsigned (rw (rho_sub rho s_Ld_bk) 140) = bv_unsigned (rw rho 140) + 1).
  { rewrite rw_sub. cbn [wsub_get s_Ld_bk Pos.eqb]. unfold add, cur. apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  unfold add, cur.
  rewrite (U_addc rho (SVar 140) (2 ^ 62 + 1) (bv_unsigned (rw rho 140)) eq_refl) by lia.
  rewrite (U_addc (rho_sub rho s_Ld_bk) (SVar 140) (2 ^ 62) (bv_unsigned (rw rho 140) + 1) E1) by lia.
  lia.
Qed.
End Glue.

Lemma FT_of_E : ltac2:(tb__ "0|0|
S35S20S1S13S0S2R1A1S4S1eS35A1A1A3S13S0S2R2A1S32A3F_;Fr;TE;").
Proof. intros E r HF. cbn [ax_S ss_facts E_src mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst : ltac2:(tb__ "0|0|
S1S13S0S2R1A1S4S1eS36A1A1A3S13S0S2R2A1S32A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_dst mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1S13S0S2R1A1S4S1eS38A1A1A3S13S0S2R2A1S32A3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Lemma next_E : ltac2:(tb__ "0|0|
S19S69S2aS6S1eS35A1A1A2S19S69S2aS6S1eS36A1A1A2S69S2aS6S1eS38A1A1A2A2A2").
Proof. repeat split; cbv; congruence. Qed.
Lemma FT_of_E_cls : ltac2:(tb__ "0|0|
S14S0A1S1S13S0S2R1A1S4S1eS6dR2S35A2A1A1A3S13S0S2R2A1S32A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_src mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.
Lemma FT_of_Edst_cls : ltac2:(tb__ "0|0|
S14S0A1S1S13S0S2R1A1S4S1eS6dR2S36A2A1A1A3S13S0S2R2A1S32A3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_dst mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Definition clsZ (rho : valuation) (ib il : positive) : Prop := ltac2:(tb__ "0|2|
S1bS22S64S29Q40M0S3Vrho;Vib;A2A2M1A2S22S23G1S29G0S3Vrho;Vil;A2A2A2S25S11Z8A2A2A2").
Lemma hi_fact_holds : ltac2:(tb__ "0|0|
S1S51S22S64S29Q40S3R2R1A2A2A2S13S0S2R3A1S16S0S5eS9R2A1A1S18S0A1A3A3F_;Fib;Frho;").
Proof. intros rho ib H. constructor; [|constructor]. unfold hi_fact. cbn [holds]. rewrite (U_lit64 rho HSE) by (unfold HSE; lia). exact H. Qed.
Lemma lo_fact_holds : ltac2:(tb__ "0|1|
S1S51S51S22S23S29Q40M0S3R3R2A2A2S29G0S3R3R1A2A2A2S25S11Z8A2A2S13S0S2R4A1S16S0S5fS9R3A1S9R2A1A2S18S0A1A3A3F_;Fil;Fib;Frho;").
Proof.
  intros rho ib il H. pose proof (urange (rw rho ib)). pose proof (urange (rw rho il)). constructor; [|constructor]. unfold lo_fact, add. cbn [holds].
  rewrite (U_add2 rho (SVar ib) (SVar il) (bv_unsigned (rw rho ib)) (bv_unsigned (rw rho il)) eq_refl eq_refl) by (unfold SHB in H; lia).
  rewrite (U_lit64 rho (SHB - 8)) by (unfold SHB; lia). exact H.
Qed.

Lemma FTbT1 : ltac2:(tb__ "0|0|
S1fS66S1fR1S6cA3S1aS15S67S0S8S6S1eS68S49S6bS21R2A1S35S45A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 FT_below_T). Qed.
Lemma FTbT2 : ltac2:(tb__ "0|0|
S1fS66S1fR1S6cA3S1aS15S67S0S8S6S1eS68S47S6bS21R2A1S36S43A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[]]. exact (proj1 (proj2 FT_below_T)). Qed.
Lemma FTbT3 : ltac2:(tb__ "0|0|
S1fS66S1fR1S73A3S1aS15S67S0S8S6S1eS68S48S74S21R2A1S38S44A5A1A1A1S32A3S17A3F_;FL;").
Proof. intros L [<-|[<-|[]]]; [exact (proj1 (proj2 (proj2 FT_below_T))) | exact (proj2 (proj2 (proj2 FT_below_T)))]. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ltac2:(tb__ "0|0|
S2eS10Vok;VJ;A3").
Hypothesis Hst : stableA segs NF J.

Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_mc_sound : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S20S66S20R1S46A3S1S61S10Vok;S2bS10S6fS1SaS2aR6R1A3Lr;VJ;A2R3R1R4A5S2cS10VJ;S2aR5R4S33A6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELM cutpcs_mc NF cuts_mc exits_mc (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_mc) tp HokG HstG check_mc); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply exit_postA. in_nth 0.
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 2]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  -
    apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2 cuts_mc _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 3]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             cuts_mc _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memcpy_sumA ok' Jq rho1 tp1 Ho Hs).
    + intros L [<-|[<-|[]]]; [in_nth 4 | in_nth 5].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_in CLs_0 (F_L vBs vLs lasts) s_Ls_in tp);
      [in_nth 6 | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ls_bk CLs_0 (F_L vBs vLs lasts) s_Ls_bk tp);
      [in_nth 6 | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below | intros r tp' tr md _ HF; exact (glue_Ls_bk r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_in CLd_0 (F_L vBd vLd lastd) s_Ld_in tp);
      [in_nth 7 | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_mc _ E_Ld_bk CLd_0 (F_L vBd vLd lastd) s_Ld_bk tp);
      [in_nth 7 | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below | intros r tp' tr md _ HF; exact (glue_Ld_bk r HF)].
Qed.

Theorem asan_memcpy_core_sum1 : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S61S10Vok;S2bS10VJ;S39R2R1A5S2cS10VJ;S2aR2R1S33A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc1). left; reflexivity.
Qed.

Theorem asan_memcpy_core_sum2 : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S61S10Vok;S2bS10VJ;S3aR2R1A5S2cS10VJ;S2aR2R1S33A6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_mc_sound rho tp Pre_mc2). right; left; reflexivity.
Qed.
End Sum.

Lemma etriple_SPA_pure' : ltac2:(tb__ "0|2|
S2dS20S1S14S28Q40A1A1M0S62OF_;S14S31A1M1S30R7R5R4R2R1A4S60S10S2bS10S1G0G1S30S19RcR4R3R2R1A4S19S1aG1R2R7A3S1aS30R1R6A3A2A2Lm;Lt;Lp;Lr;R7R6R5A5R4A3F_;Fmd;Ftr;S60S10S2bS10R6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H w [Hsm Hk]. destruct w as [tr [ms md]]. apply (H tr md Hk). split; [exact Hsm|]. cbn. auto.
Qed.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Hypothesis HclsS : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S14S31A1S30VJ;R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;").

Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_mc_complete : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S6eS66S6eR1S4aA3S1S60S10S2bS10S6fS1SaS2aR6R1A3Lr;VJ;A2S70R3A1R1R4A5S2cS10VJ;S2aR5R4S33A6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT.
  destruct ids_mc as (I1 & I2 & I3 & I4).
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_mc) tp HstG); [ | exact echeck_mc | | exact HinT].
  { intros m Hm. unfold vcuts_mc in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_mc Posts_mc (mkVNA P_amc 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_src rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsS rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_hi Pre_rip s_src R_src Posts_rip FT Hst fr_src_hi cc_src_hi (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_hi 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 19 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_src_lo Pre_rip_lo s_src R_src Posts_rip FT Hst fr_src_lo cc_src_lo (proj1 next_E) (FT_of_E_cls _) FT_below_E FTbT1
                   vcuts_mc _ (mkVNA E_src_lo 120 (SLit (2 ^ 61))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 119 (SLit (2 ^ 61))); split; [in_nth 2|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 19 52 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_dst rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_hi Pre_rip s_dst R_dst Posts_rip FT Hst fr_dst_hi cc_dst_hi (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_dst_lo Pre_rip_lo s_dst R_dst Posts_rip FT Hst fr_dst_lo cc_dst_lo (proj1 (proj2 next_E)) (FT_of_Edst_cls _) FT_below_E FTbT2
                   vcuts_mc _ (mkVNA E_dst_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T2 79 (SLit (2 ^ 63))); split; [in_nth 3|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_memcpyA s_real R_real Posts_memcpyA FT Hst fr_real cc_real (proj2 (proj2 next_E)) FT_of_Ereal FT_below_E FTbT3
             vcuts_mc _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memcpy_sumA_ex Jq rho1 tp1 Hs).
    + intros L [<-|[<-|[]]].
      * exists (mkVNA T3a 39 (SLit (2 ^ 63 + 8))). split; [in_nth 4|]. split; [reflexivity|]. meas_lit.
      * exists (mkVNA T3b 39 (SLit (2 ^ 63 + 8))). split; [in_nth 5|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_in 151 gs) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_in tp);
      [in_nth 6 | reflexivity | exact ent_Ls_in | exact I1 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ls_bk 151 (add cur (SLit 1))) (mkVNA CLs 150 cur) (F_L vBs vLs lasts) CLs_0 s_Ls_bk tp);
      [in_nth 6 | reflexivity | exact ent_Ls_bk | exact I2 | exact HstG | exact FLs_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ls_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ls_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_in 101 (add gs (SLit (2 ^ 62)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_in tp);
      [in_nth 7 | reflexivity | exact ent_Ld_in | exact I3 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_Ld_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_mc _ (mkVNA E_Ld_bk 101 (add cur (SLit (2 ^ 62 + 1)))) (mkVNA CLd 100 (add cur (SLit (2 ^ 62)))) (F_L vBd vLd lastd) CLd_0 s_Ld_bk tp);
      [in_nth 7 | reflexivity | exact ent_Ld_bk | exact I4 | exact HstG | exact FLd_below
      | intros r tp' tr md _ HF; split; [exact (glue_Ld_bk r HF) | right; split; [cbn [vna_var]; exact (meas_Ld_bk r HF) | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem asan_memcpy_core_sum1_ex : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S60S10S2bS10VJ;S39R2R1A5S2cS10VJ;S2aR2R1S33A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc1 with (vna_state (mkVNA Pre_mc1 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). left; reflexivity.
Qed.

Theorem asan_memcpy_core_sum2_ex : ltac2:(tb__ "0|0|
S1S14S28Q40A1A1S60S10S2bS10VJ;S3aR2R1A5S2cS10VJ;S2aR2R1S33A6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_mc2 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_mc2 with (vna_state (mkVNA Pre_mc2 200 (SLit 0))).
  apply (cfg_mc_complete rho tp). right; left; reflexivity.
Qed.
End SumEx.

Lemma soff_var' : ltac2:(tb__ "0|1|
S1S51S26S29Q40M0S3R2R1A2A2S24Z2Z3fA2A2S1aS50SeR3S9R2A1A2S29G0S3R3R2A2A2A3F_;Fi;Frho;").
Proof.
  intros rho i Hi. unfold soff. cbn [eval]. rewrite bv_signed_U.
  destruct (Zsigned_spec (bv_unsigned (rw rho i))) as [[_ X]|[Y X]]; [exact X|]. pose proof (urange (rw rho i)). lia.
Qed.

Section Public.
Variable rho : valuation.
Let a := bv_unsigned (eval rho dst). Let b := bv_unsigned (eval rho src). Let n := bv_unsigned (rw rho 18).

Lemma pre_disjoint : ltac2:(tb__ "0|1|
S14S28Q40A1A1M0S62S1bS2bS10S1G0S14S31A1S30S1cL_;L_;L_;L_;S34Vrho;R2R1A6S1dS2dS2dS2bS10R1S34Vrho;R3R2A6LJ;A2A2S26Vn;S24Z2Z3fA2A2S1bS22S23Va;Vn;A2Vb;A2S1bS22S23Vb;Vn;A2Va;A2S1aS50Vn;Z0A3A2A2F_;F_;Fw;Ftp;").
Proof.
  intros tp w HS Hn.
  assert (Hsm : smatchA segs rho tp Pre_mc0 w) by (destruct HS as [[H _]|[J [H _]]]; exact H).
  destruct Hsm as (Hsm & _). destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hpd & _) & _).
  cbn [ss_objs ax_S Pre_mc0 mkA objs_mc app pairwise_disjoint] in Hpd.
  destruct Hpd as (_ & _ & _ & HD & _). apply Forall_inv in HD.
  unfold ranges_disjoint, obj_range, obj_lo_of, obj_hi_of, O_dst, O_src in HD. cbn [ob_base ob_lo ob_hi fst snd] in HD.
  rewrite !soff_lit_small in HD by lia.
  assert (Es : soff rho vN = n) by (unfold vN; apply soff_var'; subst n; lia). rewrite !Es in HD.
  subst a b. lia.
Qed.

Lemma pre_Z : ltac2:(tb__ "0|5|
S13S0S2Vrho;A1S37A3S19S1aS50Va;S23S29Q40M0S3Vrho;PfM1A2A2S29G0S3Vrho;P11M2A2A2A2A3S19S1aS50Vb;S23S29G0S3Vrho;P13M3A2A2S29G0S3Vrho;P35M4A2A2A2A3S19S4fVrho;G1P10G2A4S19S4fVrho;G3P34G4A4S19S22Z1Vn;A2S22Vn;S24Z2Z28A2A2A2A2A2A2A2F_;").
Proof.
  intros HF. destruct (base_mc_Z rho HF) as (ZD & ZS & ZN & _).
  split; [exact (V_opd 15 16 17 rho ZD ZN)|]. split; [exact (V_opd 19 52 53 rho ZS ZN)|]. auto.
Qed.

Lemma xor_fact_Z : ltac2:(tb__ "0|0|
SfS50S1aS50S29Q40S5Vrho;R2A2A2R1A3S22S23R2Vn;A2S25S24Z2Z40A2Z1A2A2S2Vrho;SdScS72SbS71R4S7ZffffffffffffffffA1A3S65A3A1A2F_;F_;Fx;Fe;").
Proof.
  intros e x He Hx. cbn [holds branch_taken]. unfold bv_ltu.
  rewrite (U_xor_m1 rho e 18446744073709551615 eq_refl). rewrite He. change (eval rho vN) with (rw rho 18).
  unfold M64v. rewrite Z.ltb_lt. subst n. lia.
Qed.

Lemma facts1 : ltac2:(tb__ "0|1|
S13S0S2Vrho;A1M0S37A3S22S23Va;Vn;A2Vb;A2S13S0G0S16S0S58S54A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord1, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho dst vN a n eq_refl eq_refl) by (subst a n; lia). fold b. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma facts2 : ltac2:(tb__ "0|1|
S13S0S2Vrho;A1M0S37A3S22S23Vb;Vn;A2Va;A2S13S0G0S16S0S59S54A3A3F_;F_;").
Proof.
  intros HF Hab. destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN). pose proof ZD as ZD'. pose proof ZS as ZS'.
  unfold opZ in ZD', ZS'. cbv zeta in ZD'. cbv zeta in ZS'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 19)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 53)).
  pose proof (urange (rw rho 18)). unfold ord2, xor_facts.
  constructor.
  { cbn [holds]. unfold add at 1. rewrite (U_add2 rho src vN b n eq_refl eq_refl) by (subst b n; lia). fold a. lia. }
  constructor. { apply (xor_fact_Z src b eq_refl). subst b n. lia. }
  constructor. { apply (xor_fact_Z dst a eq_refl). subst a n. lia. }
  constructor.
Qed.

Lemma F1_below : ltac2:(tb__ "0|0|
S1aS15S67S0S8S6S1eS34A1A1A1S16S0S58S54A3A3S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma F2_below : ltac2:(tb__ "0|0|
S1aS15S67S0S8S6S1eS34A1A1A1S16S0S59S54A3A3S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma SPA_cases : ltac2:(tb__ "0|0|
S2dS14S28Q40A1A1S62S2bS10R3S34Vrho;R2R1A6S1bS2bS10R4S39Vrho;R3R2A6S2bS10R4S3aVrho;R3R2A6A2F_;Fw;Ftp;FJ;").
Proof.
  intros J tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_mc0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_mc0 mkA] in HF.
  destruct (pre_Z HF) as (Ea & Eb & ZD & ZS & ZN).
  destruct (pre_disjoint tp w (or_intror (ex_intro _ J Hw)) ltac:(lia)) as [H|[H|H]]; [left | right | exfalso; lia].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts1 HF H) | exact F1_below].
  - destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (facts2 HF H) | exact F2_below].
Qed.
End Public.

Theorem asan_memcpy_core_sum : ltac2:(tb__ "0|2|
S62OF_;S2dS1S14S28Q40A1A1M0S2eS10R4R3A3S2fS10S2aR4A3S1G0S14S31A1M1S30R9R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S30RaR4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S61S10R8S2bS10R7S34R6R5A5S2cS10R7S2aR6R5S33A6A4F_;F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD HS.
  eapply triple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply triple_disj; [apply asan_memcpy_core_sum1 | apply asan_memcpy_core_sum2]; assumption.
Qed.

Theorem asan_memcpy_core_sum_ex : ltac2:(tb__ "0|2|
S2dS1S14S28Q40A1A1M0S2fS10S2aR3A3S1G0S14S31A1M1S30R8R4R3R2R1A4S4eR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S1G0G1S30R9R4R3R2R1A4S4eR5P13P34A3F_;Fmd;Ftr;Ft;Fr;S60S10S2bS10R6S34R5R4A5S2cS10R6S2aR5R4S33A6A3F_;F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD HS.
  eapply etriple_conseq; [intros w Hw; exact (SPA_cases rho J tp w Hw) | intros w Hw; exact Hw |].
  apply etriple_disj; [apply asan_memcpy_core_sum1_ex | apply asan_memcpy_core_sum2_ex]; assumption.
Qed.
End Asan_memcpy_proof.

(* [comment removed for export] *)
Module Asan_memsetZ_proof.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sprop"; "holds"; "ss_facts"; "eval"; "ss_next"; "agree_below"; "rw"; "sprop_below"; "SLit"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Lists.ListDef"; "Forall"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "LQA"; "jpredA"; "stableA"; "ok_frameA"; "@Corelib.Init.Logic"; "and"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memsetZ"; "FT"; "Posts_ms"; "E_reg"; "E_real"; "Pre_ms0"; "Pre_ms1"; "s_L_bk"; "s_L_in"; "F_L"; "E_L_bk"; "E_L_in"; "R_real"; "R_reg"; "base_ms"; "cuts_ms"; "s_real"; "s_reg"; "vcuts_ms"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof"; "clsZ"; "opZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub_id_below"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy"; "cur"; "gs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "withGA"; "ax_add_facts"; "vna_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region"; "P_ret"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full"; "Pre_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy"; "liftA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ"; "P_msz"; "Pre_mszA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue MuslWL MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgGlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n4.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.Str_memsetZ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Asan_memsetZ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr AMSZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Local Notation "'UU' rho e" := (bv_unsigned (eval rho e)) (at level 10, rho at level 9, e at level 9).
Ltac have_fact H HF f := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.

Lemma base_ms_Z : ltac2:(tb__ "0|1|
S1SfS2S3R1A1S28A3S19S30R2PfP10P11A4S19S33Z1S11Q40S8R2P12A2A2M0A2S33G0S34Z2Z28A2A2A2A2F_;Frho;").
Proof.
  intros rho HF. pose proof (urange (rw rho 18)) as RN.
  have_fact N1 HF (SPUle (SLit 1) vN). have_fact N2 HF (SPUle vN (SLit (2 ^ 40))).
  unfold vN in N1, N2. rewrite (U_lit64 rho 1) in N1 by lia. rewrite (U_lit64 rho (2 ^ 40)) in N2 by lia. cbn [eval] in N1, N2.
  split; [|lia].
  apply (opnd_Z rho 15 16 17). unfold opnd_facts.
  have_fact A1 HF (SPUle (add vOd vN) vLd). have_fact A2 HF (SPUle vOd vLd). have_fact A3 HF (SPUle vN vLd).
  have_fact A4 HF (SPUle vLd (SLit (2 ^ 40))). have_fact A5 HF (SPUle (SLit 4096) vBd).
  have_fact A6 HF (SPUle (add vBd vLd) (SLit (2 ^ 47 - 8))). have_fact A7 HF (SPUle vBd (SLit (2 ^ 47 - 8))). have_fact A8 HF (SPAlign 15 3).
  unfold vBd, vLd, vOd in *. repeat (constructor; [assumption|]). constructor.
Qed.

Lemma FT_Z_ms : ltac2:(tb__ "0|1|
S1SfS2S3R1A1S1bA3S19S30R2PfP10P11A4S19S33Z1S11Q40S8R2P12A2A2M0A2S33G0S34Z2Z28A2A2A2A2F_;Frho;").
Proof. intros rho HF. unfold FT in HF. apply Forall_cons_iff in HF as [_ HB]. exact (base_ms_Z rho HB). Qed.

Ltac split_mid HF HX HT := cbn [ax_S ss_facts mid_state mkA] in HF; apply Forall_app in HF as [HX HT].

Section Glue.
Variable rho : valuation.

Lemma glue_L_in : ltac2:(tb__ "0|0|
SfS2S3Vrho;A1S4S12S25A1A1A3SfS2S3S31Vrho;S22A2A1S23A3F_;").
Proof.
  intros HF. unfold E_L_in in HF. split_mid HF HX HT.
  destruct (FT_Z_ms rho HT) as (ZD & ZN).
  destruct (in_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 142)) as R142. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_L_in).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity. assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  pose proof (Z.div_mod (bv_unsigned (rw rho 15)) 8 ltac:(lia)) as D. pose proof (urange (rw rho 17)) as R17.
  change F_L with (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.F_L vBd vLd lastd).
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 142)) (bv_unsigned (rw rho 141)));
    try reflexivity; rewrite ?E18, ?E15, ?E16, ?E17; unfold HSE in *; lia.
Qed.

Lemma glue_L_bk : ltac2:(tb__ "0|0|
SfS2S3Vrho;A1S4S12S24A1A1A3SfS2S3S31Vrho;S21A2A1S23A3F_;").
Proof.
  intros HF. unfold E_L_bk in HF. split_mid HF HX HT.
  destruct (FT_Z_ms rho HT) as (ZD & ZN).
  change F_L with (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy.F_L vBd vLd lastd) in HX |- *.
  destruct (bk_facts_Z 15 16 17 rho ZD ZN HX) as (G1 & G2 & G3 & G4 & G5). cbv zeta in *.
  destruct ZD as (S1 & S2 & S3 & S4 & S5). cbv zeta in *.
  pose proof (urange (rw rho 140)) as R140. pose proof (urange (rw rho 141)) as R141.
  set (rho' := rho_sub rho s_L_bk).
  assert (ZD' : opZ rho' 15 16 17) by (subst rho'; apply opZ_sub; [reflexivity | reflexivity | reflexivity | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | repeat split; assumption]).
  assert (E18 : rw rho' 18 = rw rho 18) by reflexivity.
  assert (E140 : bv_unsigned (rw rho' 140) = bv_unsigned (rw rho 140) + 1).
  { subst rho'. rewrite rw_sub. cbn [wsub_get s_L_bk Pos.eqb]. unfold add, cur.
    apply (U_addc rho (SVar 140) 1 (bv_unsigned (rw rho 140)) eq_refl); lia. }
  assert (E15 : rw rho' 15 = rw rho 15) by reflexivity.
  assert (E16 : rw rho' 16 = rw rho 16) by reflexivity. assert (E17 : rw rho' 17 = rw rho 17) by reflexivity.
  assert (E141 : rw rho' 141 = rw rho 141) by reflexivity.
  apply (F_L_intro 15 16 17 rho' ZD' ltac:(rewrite E18; exact ZN) (bv_unsigned (rw rho 140) + 1) (bv_unsigned (rw rho 141)));
    rewrite ?E18, ?E15, ?E16, ?E17, ?E141; unfold HSE in *; try lia.
Qed.

Lemma meas_L_in : ltac2:(tb__ "0|0|
S1aS10Q40A1S5S31Vrho;S22A2S35A2S5Vrho;S36A2A3").
Proof. reflexivity. Qed.
Lemma meas_L_bk : ltac2:(tb__ "0|0|
S1aS10Q40A1S5S31Vrho;S21A2S35A2S5Vrho;S43S35SaZ1A1A2A2A3").
Proof. reflexivity. Qed.
End Glue.

Lemma FT_of_Ereg : ltac2:(tb__ "0|0|
S1SfS2S3R1A1S4S12S1dA1A1A3SfS2S3R2A1S1bA3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_reg mid_state mkA] in HF. exact HF. Qed.
Lemma FT_of_Ereal : ltac2:(tb__ "0|0|
S1SfS2S3R1A1S4S12S1eA1A1A3SfS2S3R2A1S1bA3F_;Fr;").
Proof. intros r HF. cbn [ax_S ss_facts E_real mid_state mkA] in HF. exact HF. Qed.
Lemma next_E_ms : ltac2:(tb__ "0|0|
S19S41SeS6S12S1dA1A1A2S41SeS6S12S1eA1A1A2A2").
Proof. split; cbv; congruence. Qed.
Lemma FT_below190 : forallb (sprop_below 190) FT = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FL_below190 : forallb (sprop_below 190) F_L = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S19S1aScS40S2S9S6S12S3eS2bS44S42S1dS27A5A1A1A1S1bA3SdA3S1aScS40S2S9S6S12S3eS2aS47S45S46A1S1eS26A5A1A1A1S1bA3SdA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma ids_ms : ltac2:(tb__ "0|0|
S19S1aScS32S22SeA2SdA3S1aScS32S21SeA2SdA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma FT_of_Ereg_cls : ltac2:(tb__ "0|0|
SbS2A1S1SfS2S3R1A1S4S12S3cR2S1dA2A1A1A3SfS2S3R2A1S1bA3F_;Fr;FF;").
Proof. intros F r HF. cbn [ax_S ss_facts E_reg mid_state mkA ax_add_facts ax_setS add_facts] in HF. apply Forall_app in HF as [_ HF]. apply Forall_app in HF as [_ HF]. exact HF. Qed.

Section Sum.
Variable ok : assn.
Variable J : jpredA.
Hypothesis Hok : ok_frameA segs ok J.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1SbS2eA1S2dVJ;R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").

Lemma cfg_ms_sound : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S13S3fS13R1S29A3S1S38S0Vok;S14S0S3bS1S7SeR6R1A3Lr;VJ;A2R3R1R4A5S15S0VJ;SeR5R4S1cA6A4FrhoT;F_;FT;Ftp;Frho;").
Proof.
  intros rho tp T HinT rhoT. destruct ids_ms as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  assert (HokG : ok_frameA segs ok (withGA (fun r => agree_below NF rho r) J)).
  { intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto. }
  apply (cfg_soundA segs FUELS cutpcs_ms NF cuts_ms exits_ms (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_ms) tp HokG HstG check_ms); [|exact HinT].
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply exit_postA. in_nth 0.
  - apply triple_SPA_pure. intros tr0 md0 [_ HJ0].
    eapply triple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_reg rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_reg_hi Pre_rip s_reg R_reg Posts_rip FT Hst fr_reg_hi cc_reg_hi (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   cuts_ms _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 1]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply triple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA ok J NF rho tp E_reg_lo Pre_rip_lo s_reg R_reg Posts_rip FT Hst fr_reg_lo cc_reg_lo (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   cuts_ms _ Hok);
          [intros ok' Jq rho1 tp1 Ho Hs; exact (region_sum_lo ok' Jq rho1 tp1 Ho Hs) | intros L [<-|[]]; in_nth 1]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA ok J NF rho tp E_real Pre_mszA s_real R_real Posts_mszA FT Hst fr_real cc_real (proj2 next_E_ms) FT_of_Ereal FT_below190
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_T)) | or_intror F => match F with end end)
             cuts_ms _ Hok).
    + intros ok' Jq rho1 tp1 Ho Hs. exact (memsetZ_sumA ok' Jq Ho Hs rho1 tp1).
    + intros L [<-|[]]. in_nth 2.
  - apply (exit_reenterA segs ok _ NF cuts_ms _ E_L_in CL_0 F_L s_L_in tp);
      [in_nth 3 | exact ent_L_in | exact I1 | exact HstG | exact FL_below190 | intros r tp' tr md _ HF; exact (glue_L_in r HF)].
  - apply (exit_reenterA segs ok _ NF cuts_ms _ E_L_bk CL_0 F_L s_L_bk tp);
      [in_nth 3 | exact ent_L_bk | exact I2 | exact HstG | exact FL_below190 | intros r tp' tr md _ HF; exact (glue_L_bk r HF)].
Qed.

Theorem asan_memset_core_sum1 : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S38S0Vok;S14S0VJ;S20R2R1A5S15S0VJ;SeR2R1S1cA6A4Ftp;Frho;").
Proof.
  intros rho tp.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ms1 rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_ms_sound rho tp Pre_ms1). left; reflexivity.
Qed.
End Sum.

Section SumEx.
Variable J : jpredA.
Hypothesis Hst : stableA segs NF J.
Hypothesis HclsD : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1SbS2eA1S2dVJ;R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;").
Ltac meas_lit := intros r r'; unfold vmeasIA; cbn [vna_var vna_rank eval]; rewrite ?u64_lit by lia; lia.

Lemma cfg_ms_complete : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S3aS3fS3aR1S2cA3S1S37S0S14S0S3bS1S7SeR6R1A3Lr;VJ;A2S3dR3A1R1R4A5S15S0VJ;SeR5R4S1cA6A3FrhoT;F_;Fn;Ftp;Frho;").
Proof.
  intros rho tp n HinT rhoT. destruct ids_ms as [I1 I2].
  assert (HstG : stableA segs NF (withGA (fun r => agree_below NF rho r) J)).
  { apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst]. }
  apply (cfg_complete_autoIA segs FUELS cutpcs_ms NF vcuts_ms vexits_ms (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_ms) tp HstG); [ | exact echeck_ms | | exact HinT].
  { intros m Hm. unfold vcuts_ms in Hm. repeat (destruct Hm as [<-|Hm]; [cbv; congruence|]). destruct Hm. }
  intros E rhoE HinE. destruct HinE as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply (eexit_post_IA0 segs J NF rho vcuts_ms Posts_ms (mkVNA P_ms 0 (SLit (2 ^ 64 - 1)))). in_nth 0.
  - apply etriple_SPA_pure'. intros tr0 md0 [_ HJ0].
    eapply etriple_conseq; [intros w [Hsm [HJ' _]]; exact (conj Hsm HJ' : SPA segs _ E_reg rhoE tp w) | intros w Hw; exact Hw |].
    destruct (HclsD rhoE tp tr0 md0 HJ0) as [Hhi|Hlo].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_reg_hi Pre_rip s_reg R_reg Posts_rip FT Hst fr_reg_hi cc_reg_hi (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   vcuts_ms _ (mkVNA E_reg_hi 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 79 (SLit (2 ^ 63))); split; [in_nth 1|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (hi_fact_holds rhoE 15 Hhi) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
    + eapply etriple_conseq; [ | intros w Hw; exact Hw
        | apply (call_exitA_ex J NF rho tp E_reg_lo Pre_rip_lo s_reg R_reg Posts_rip FT Hst fr_reg_lo cc_reg_lo (proj1 next_E_ms) (FT_of_Ereg_cls _) FT_below190
                   (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj1 FT_below_T)) | or_intror F => match F with end end)
                   vcuts_ms _ (mkVNA E_reg_lo 80 (SLit (2 ^ 63))) eq_refl);
          [intros Jq rho1 tp1 Hs; exact (region_sum_lo_ex Jq rho1 tp1 Hs)
          | intros L [<-|[]]; exists (mkVNA T1 79 (SLit (2 ^ 63))); split; [in_nth 1|]; split; [reflexivity|]; meas_lit]].
      intros w [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | exact (lo_fact_holds rhoE 15 16 Hlo) | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  - apply (call_exitA_ex J NF rho tp E_real Pre_mszA s_real R_real Posts_mszA FT Hst fr_real cc_real (proj2 next_E_ms) FT_of_Ereal FT_below190
             (fun L HinL => match HinL with or_introl E => ltac:(subst L; exact (proj2 FT_below_T)) | or_intror F => match F with end end)
             vcuts_ms _ (mkVNA E_real 40 (SLit (2 ^ 63 + 8))) eq_refl).
    + intros Jq rho1 tp1 Hs. exact (memsetZ_sumA_ex Jq Hs rho1 tp1).
    + intros L [<-|[]]. exists (mkVNA T3 39 (SLit (2 ^ 63 + 8))). split; [in_nth 2|]. split; [reflexivity|]. meas_lit.
  - apply (eexit_reenter_IA segs _ NF vcuts_ms _ (mkVNA E_L_in 101 gs) (mkVNA CL 100 cur) F_L CL_0 s_L_in tp);
      [in_nth 3 | reflexivity | exact ent_L_in | exact I1 | exact HstG | exact FL_below190
      | intros r tp' tr md _ HF; split; [exact (glue_L_in r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_in r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
  - apply (eexit_reenter_IA segs _ NF vcuts_ms _ (mkVNA E_L_bk 101 (add cur (SLit 1))) (mkVNA CL 100 cur) F_L CL_0 s_L_bk tp);
      [in_nth 3 | reflexivity | exact ent_L_bk | exact I2 | exact HstG | exact FL_below190
      | intros r tp' tr md _ HF; split; [exact (glue_L_bk r HF) | right; split; [cbn [vna_var]; rewrite (meas_L_bk r); lia | cbn; lia]]
      | cbn; lia | cbn; lia].
Qed.

Theorem asan_memset_core_sum1_ex : ltac2:(tb__ "0|0|
S1SbS10Q40A1A1S37S0S14S0VJ;S20R2R1A5S15S0VJ;SeR2R1S1cA6A3Ftp;Frho;").
Proof.
  intros rho tp.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_ms1 rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_ms1 with (vna_state (mkVNA Pre_ms1 200 (SLit 0))).
  apply (cfg_ms_complete rho tp). left; reflexivity.
Qed.
End SumEx.

Lemma SPA_ms01 : ltac2:(tb__ "0|0|
S16S1SbS10Q40A1A1S39S14S0R4S1fR3R2R1A6S14S0R5S20R4R3R2A6F_;Fw;Ftp;Frho;FJ;").
Proof.
  intros J rho tp w Hw. pose proof (SPA_facts_hold segs J rho Pre_ms0 tp w Hw) as HF. cbn [ax_S ss_facts Pre_ms0 mkA] in HF.
  destruct (base_ms_Z rho HF) as (ZD & ZN). pose proof ZD as ZD'. unfold opZ in ZD'. cbv zeta in ZD'. unfold HSE in *.
  pose proof (urange (rw rho 15)). pose proof (urange (rw rho 17)). pose proof (urange (rw rho 18)).
  destruct Hw as [Hsm HJ]. split; [|exact HJ]. apply smatchA_add_facts; [exact Hsm | | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc].
  constructor; [|constructor]. unfold xor_fact.
  apply (xor_fact_Z rho dst (bv_unsigned (rw rho 15) + bv_unsigned (rw rho 17))).
  - exact (V_opd 15 16 17 rho ZD ZN).
  - lia.
Qed.

Theorem asan_memset_core_sum : ltac2:(tb__ "0|1|
S39OF_;S16S1SbS10Q40A1A1M0S18S0R4R3A3S17S0SeR4A3S1G0SbS2eA1S2dR9R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S38S0R7S14S0R6S1fR5R4A5S15S0R6SeR5R4S1cA6A4F_;F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst HD.
  eapply triple_conseq; [intros w Hw; exact (SPA_ms01 J rho tp w Hw) | intros w Hw; exact Hw | apply asan_memset_core_sum1; assumption].
Qed.

Theorem asan_memset_core_sum_ex : ltac2:(tb__ "0|1|
S16S1SbS10Q40A1A1M0S17S0SeR3A3S1G0SbS2eA1S2dR8R4R3R2R1A4S2fR5PfP10A3F_;Fmd;Ftr;Ft;Fr;S37S0S14S0R5S1fR4R3A5S15S0R5SeR4R3S1cA6A3F_;F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst HD.
  eapply etriple_conseq; [intros w Hw; exact (SPA_ms01 J rho tp w Hw) | intros w Hw; exact Hw | apply asan_memset_core_sum1_ex; assumption].
Qed.
End Asan_memsetZ_proof.

(* [comment removed for export] *)
Module Lib_finalize_shape_dup1.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "prod"; "nat"; "app"; "None"; "false"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SVar"; "SPUle"; "SLit"; "sobj"; "SAlu"; "cell"; "FcsrFrm0"; "mkSS"; "SPAlign"; "DUnknown"; "mkObj"; "ss_objs"; "ss_regs"; "sstate"; "SPUlt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "ALU_XOR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1"; "vSZ"; "vH"; "vCAPl"; "z0"; "vP"; "vSRC"; "vK"; "tv0"; "p_fit"; "X_ad"; "vHD"; "O_F"; "O_W"; "O_ar"; "O_src"; "ad_facts"; "am_np"; "vLS"; "vU"; "X_nohead"; "ndO"; "ra_an"; "vUc"; "C_loop"; "C_slow"; "base_fit"; "nd0"; "ndL"; "ndS"; "pN"; "vI"; "vNXl"; "E_m"; "O_hdr"; "O_slot"; "P_ok"; "Pre_ad"; "bd_m"; "g100_facts"; "ndKc"; "ndMok"; "p_new"; "slow_facts"; "ug_facts"; "vAR"; "vCAP"; "vUg"; "CH"; "C_K"; "C_exit"; "C_open"; "FUEL_ad"; "K_facts"; "P_fail"; "Pre_ad_S"; "Pre_m"; "T_mnull"; "T_mok"; "X_K0"; "X_K1"; "X_K2"; "X_fit"; "X_fit3"; "X_nofit"; "X_nofit2"; "X_nofitO"; "X_open"; "X_ret"; "X_ret3"; "X_sret"; "X_sret3"; "ahd"; "am_loop"; "am_ok"; "am_open"; "bd_K"; "bd_loop"; "bd_open"; "bd_slow"; "c8"; "cutpcs_ad"; "ghK"; "loop_facts"; "loop_regs"; "nP"; "ndF"; "ndK"; "ndM"; "nsrc"; "ok_facts"; "pad_fit"; "slow_regs"; "tv_m"; "used_fit"; "vDp"; "vNX"; "xit_facts"; "xit_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "NDA"; "AOpen"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "batom"; "BI"; "ASv"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "e32"; "POT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "pre_fregs"; "setregs"; "NF"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "mkA"; "A_globals"; "shb"; "leavesA_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1.ADAddr"; "ad_K"; "ad_loop"; "ad_ret"; "ad_retF"; "ad_slow"; "ad_xit"; "ad_entry"; "ad_open"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1.AA"; "aa_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nd.Lib_finalize_shape_dup1.RA.ReallocAddr"; "malloc_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "NPOSTM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxCellA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
Module RA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ng.Lib_realloc. End RA.
Module AA. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc. End AA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ADAddr.
  Definition ad_entry : Z := 0x90724.
  Definition ad_open : Z := 0x9b978.
  Definition ad_slow : Z := 0x9b9fc.
  Definition ad_K : Z := 0x9ba28.
  Definition ad_loop : Z := 0x90740.
  Definition ad_xit : Z := 0x90780.
  Definition ad_ret : Z := 0x907fc.
  Definition ad_retF : Z := 0x907dc.
End ADAddr.
Import ADAddr.
Import RA.ReallocAddr.
Definition c8 := RA.c8. Definition spm := RA.spm. Definition vUD := RA.vUD. Definition two47 := RA.two47. Definition two40 := RA.two40.
Definition O_F := AA.O_F. Definition O_W := AA.O_W. Definition O_ar := AA.O_ar. Definition O_hdr := AA.O_hdr.
Definition vAR := AA.vAR. Definition vHD := AA.vHD. Definition vDp := AA.vDp.

Definition FUEL_ad : nat := 500%nat.
Definition vSRC : sv := SVar 13. Definition vSZ : sv := SVar 14. Definition vLS : sv := SVar 16.
Definition O_src : sobj := ltac2:(tb__ "0|0|
S15S24SdZ0A1S30S2S10A1S14A5").
Definition O_slot (p : sv) : sobj := ltac2:(tb__ "0|0|
S15Vp;SdZ0A1S1fS2S10A1S14A5").

Definition ad_facts : list sprop := ltac2:(tb__ "0|1|
S5SaSa5S0SaScSdZ1A1S1fA2S0SaScS1fS30A2S0SaScS30SdS98Z2Z20A2A1A2S0SaScSdZ1000A1S24A2S0SaScSfS1cS24S30A3SbP1eA1M0A2S0SaScS24G0A2S2SaA1A3A3A3A3A3A3A3").

Definition X_ad : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S0G0S1S9S9S24S30A4S2G0A1A3A3").
Definition Pre_ad_S : sstate := ltac2:(tb__ "0|1|
S12Sa2S8fS92S0S3S4S9A2M0S1S4S9UbS1fA4S0G0S1S4S9UcSdZ10A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eS90S7A9").
Definition Pre_ad : axst := mkA Pre_ad_S X_ad.
Definition tv0 : list (sv * sv) := ltac2:(tb__ "0|1|
S0S3S9S9A2M0S1S9S9S4bSdZ40A1A4S2G0A1A3").

Definition CH : list bitem := ltac2:(tb__ "0|5|
S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87Z2S89S1fA1M3A4S2G2A1M4A3Z60A4S0S86S88G1G0S0G2S1S1aS87Z4G3A4G4A3Z40A4S2S86A1A3A3").

Definition cutpcs_ad : list Z := ltac2:(tb__ "0|0|
S0S1aSa3S0S1aSa0S0S1aS9cS0S1aSa6S0S1aS9dS0S1aSa1S0S1aS9eS0S1aS9fS2S1aA1A3A3A3A3A3A3A3A3").
Definition leafA_at (S : axst) (pc : Z) (k : nat) : axst := ltac2:(tb__ "0|0|
Sa4S81Vk;S96S52S6fVS;Vpc;A4S43A4").
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.
Definition optAp (x : option axst) : axst := match x with Some a => a | None => Pre_ad end.

Definition X_open : axst := Eval vm_compute in leafA_at Pre_ad ad_open 0.
Definition nO : positive := Eval vm_compute in ss_next (ax_S X_open).
Definition C_open : axst := Eval vm_compute in open_stateA X_open vHD.
Definition vNX : sv := Eval vm_compute in SVar nO.
Definition vCAP : sv := Eval vm_compute in SVar (nO + 1).
Definition vU : sv := Eval vm_compute in SVar (nO + 2).
Definition am_open : amode := ltac2:(tb__ "0|0|
S85S29S7eS4cS2S3S9S9A2A1A4").
Definition bd_open : list bitem := CH ++ POT vU.

Definition X_nohead : axst := Eval vm_compute in leafA_at Pre_ad ad_slow 0.

Definition X_nofitO : axst := Eval vm_compute in leafA_at C_open ad_slow 0.
Definition X_fit : axst := Eval vm_compute in leafA_at C_open ad_loop 0.
Definition X_nofit : axst := Eval vm_compute in leafA_at C_open ad_slow 1.

Definition vUg : sv := SVar 108.
Definition slow_regs : list sv := ltac2:(tb__ "0|1|
S8fS17S82S32A1A1S0S3S4S9A2M0S1S4S9UbSbP65A1A4S0G0S1S4S9UdSbP66A1A4S0G0S1S4S9UeSbP67A1A4S0G0S1S4S9UfSbP68A1A4S0G0S1S4S9U10SbP69A1A4S0G0S1S4S9U11SbP6aA1A4S0G0S1S4S9U5SbP6bA1A4S2G0A1A3A3A3A3A3A3A3A2").
Definition slow_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => negb (sprop_eqb f (SPBranch BC_EQ vHD (SLit 0)))) (ss_facts (ax_S X_nohead)).
Definition ug_facts : list sprop := ltac2:(tb__ "0|0|
S0SaScSdZ10001A1SfS1cS4dSfS1cS1fSdZ10A1A3A3A2S0SaScS4dSdS98Z2Z28A2A1A2S2SaA1A3A3").
Definition C_slow : axst := ltac2:(tb__ "0|0|
S93S12Sa0S7aS8eS11S6S9A1S16S82S32A1A1S5SaS4aS49A3P6dS7A9S28A2").
Definition bd_slow : list bitem := POT vUg ++ CH.
Definition am_np : amode := AHead vHD false.

Definition X_K0 : axst := Eval vm_compute in leafA_at C_slow ad_K 0.
Definition vK : sv := SVar 110.
Definition K_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSdZ10000A1M0S25A2S0SaScSfS1cS1fSdZ10M1A1A3S25A2S0SaScS25SfS1cS1fG0A3A2S0SaScS25SdS9aS98Z2Z20A2G1A2A1A2S0SaScSdZ1A1S8cS25A1A2S2SaA1A3A3A3A3A3").

Definition ghK : sprop := SPEq (SVar 111) (SLit 0).
Definition C_K : axst := ltac2:(tb__ "0|2|
S93S12S9cS8fS17S82S59A1M0A1S0S3S4S9A2M1S1S4S9U14S25A4S2G1A1A3A2S8eS11S6S9A1S16G0A1S0SaS70S5SaS53S5SaS4aS49A3A3A3P70S7A9S28A2").

Definition X_K1 : axst := X_K0.
Definition X_K2 : axst := Eval vm_compute in leafA_at C_slow ad_K 1.
Definition s_K1 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSdZ10000A1A4S2G0A1A3A3").
Definition s_K2 : wsub := ltac2:(tb__ "0|1|
S0S3S1bS9A2M0S1S1bS9P6fSdZ0A1A4S0G0S1S1bS9P6eSfS1cS1fSdZ10A1A3A4S2G0A1A3A3").
Definition bd_K : list bitem := ltac2:(tb__ "0|3|
S5S86S0S86S88Z1M0Z0M1S0S3S1aS87A2M2S1S1aS87G0S89S8cS25A1A1A4S2G2A1A3G1A4S0S86S8aG1G0S9bZ2S8bA2A3S2S86A1A3A3S8dS1fA1A3").

Definition E_m : axst := Eval vm_compute in leafA_at C_K malloc_pc 0.
Definition Pre_m : axst := Pre_malloc AE_A [] UStopLe.
Definition s_m : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9PfS7dA4S97PaS82S3fA1S82S56A1A3A3").
Definition R_m : list sobj := Eval vm_compute in optR (entails_frA E_m Pre_m s_m).
Definition pN : positive := Eval vm_compute in pos_add_nat (ss_next (ax_S E_m)) 10.
Definition blkN : sv * sv := ltac2:(tb__ "0|0|
S1S9S9SbS3cA1S8cS25A1A4").
Definition T_mnull : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_null AE_A [] UStopLe).
Definition T_mok0 : axst := Eval vm_compute in T_afterA Pre_m E_m s_m R_m (L_malloc_ok AE_A [] UStopLe).
Definition mok_facts : list sprop := tv_factsA blkN.
Definition T_mok : axst := ax_add_facts mok_facts T_mok0.

Definition bd_m : list bitem := ltac2:(tb__ "0|0|
S5S86S0S86S8aZ0Z1S8bA3S2S86A1A3S8dS1fA1A3").
Definition tv_m : list (sv * sv) := blkN :: tv0.

Definition bd_m2 : list bitem := POT vSZ.

Definition X_sret : axst := Eval vm_compute in leafA_at T_mok ad_loop 0.

Definition vH : sv := SVar 101.  Definition vNXl : sv := SVar 102.  Definition vCAPl : sv := SVar 103.
Definition vUc : sv := SVar 104. Definition vP : sv := SVar 105.    Definition vI : sv := SVar 106.
Definition am_loop : amode := ltac2:(tb__ "0|1|
S85S20S3eS21S0S3S9S9A2M0S1S9S9S23S1fA4S2G0A1A3A4").
Definition ra_an : Z := 0x90728.
Definition nsrc : sv := ltac2:(tb__ "0|0|
SfS1eS24SdZffffffffffffffffA1A3").
Definition nP : sv := SAlu ALU_XOR vP (SLit 18446744073709551615).
Definition loop_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9S3dS0S9S77S0S9S73S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition g100_facts : list sprop :=
  Eval vm_compute in List.filter (fun f => match f with
     | SPEq (SAlu ALU_SLL (SVar 100) _) _ | SPUle (SVar 100) _ | SPUle (SAlu ALU_SLL (SVar 100) _) _ | SPUle _ (SAlu ALU_SLL (SVar 100) _) => true
     | _ => false end) (ss_facts (ax_S X_nohead)).
Definition loop_facts : list sprop := ltac2:(tb__ "0|5|
S0SaS19S3dS1fA2S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3M0SbP1eA1M1A2S0SaScS20G1A2S0SaScSdZ1000A1M2S20A2S0SaS13P65Z4M3A2S0SaScSfS1cS20SdZ20A1A3S23A2S0SaScSfS1cS23S1fA3M4G0A2S0SaScG2S23A2S0SaScG4G1A2S0SaScS23G1A2S0SaS13P69G3A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition C_loop : axst := ltac2:(tb__ "0|1|
S93S12S9dS72S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS71S5SaS45S2eA3A3P79S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").
Definition bd_loop : list bitem := POT vUc.

Definition p_fit : sv := Eval vm_compute in nth 10 (ss_regs (ax_S X_fit)) (SLit 0).
Definition base_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS29SdZ20A1A3S31A3").
Definition pad_fit : sv := ltac2:(tb__ "0|0|
SfS1dS27S38A3").
Definition used_fit : sv := ltac2:(tb__ "0|0|
SfS1cSfS1cS79S1fA3S31A3").
Definition fit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS38S27A2S0SaScS27SfS1cS38SdZfA1M0A3A2S0SaScSdZ1000A1S27A2S0SaScS27SbP1eA1M1A2S0SaScSfS1cS27S1fA3M2SfS1cS29S8cS4cA1A3A2S0SaScG2G1A2S0SaScSfS1cS29SdZ20A1A3S27A2S0SaScS7cSfS1cS31SfS1cS1fG0A3A3A2S2SaA1A3A3A3A3A3A3A3A3").
Definition X_fit3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_fit p_fit vSZ) (fit_facts ++ ss_facts (ax_S X_fit)).

Definition nofit_fact : sprop := ltac2:(tb__ "0|0|
ScSdZ10001A1SfS1cS31SfS1cS1fSdZ10A1A3A3A2").
Definition X_nofit1 : axst := Eval vm_compute in drop_lastA X_nofit (removelast (ss_objs (ax_S X_nofit))).
Definition X_nofit2 : axst := Eval vm_compute in ax_with_facts X_nofit1 (nofit_fact :: ss_facts (ax_S X_nofit1)).

Fixpoint find_idxb {T} (f : T -> bool) (l : list T) (k : nat) : nat :=
  match l with [] => k | x :: r => if f x then k else find_idxb f r (S k) end.
Definition iN : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) (SVar pN)) (ss_objs (ax_S X_sret)) 0%nat.
Definition sel_sret : list nat := Eval vm_compute in (List.filter (fun j => negb (Nat.eqb j iN)) (seq 0 (length (ss_objs (ax_S X_sret))))) ++ [iN].
Definition X_sret1 : axst := Eval vm_compute in optAp (apply_axforms X_sret [AXSelect sel_sret; AXSplit (length sel_sret - 1) (SLit 24)]).
Definition iH : nat := Eval vm_compute in (length (ss_objs (ax_S X_sret1)) - 2)%nat.
Definition jU : nat := Eval vm_compute in
  find_idxb (fun c => sv_eqb (c_off c) (SLit 16)) (ob_cells (nth iH (ss_objs (ax_S X_sret1)) O_src)) 0%nat.
Definition optSC (x : option (sstate * cell)) : sstate * cell := ltac2:(tb__ "0|2|
S8S3S18S10A2M0A1G0Lx;Vx;G0R1Lr;S1S18S10S55S6eZ0M1SdG1A1A2A4X8x2").
Definition rcU : sstate * cell := Eval vm_compute in optSC (AxCellA.recellv_at (ax_S X_sret1) iH jU vSZ).
Definition used_new : sv := c_val (snd rcU).
Definition X_sret1r : axst := Eval vm_compute in ax_setS X_sret1 (fst rcU).
Definition ohN : sobj := Eval vm_compute in nth iH (ss_objs (ax_S X_sret1r)) O_src.
Definition otN : sobj := Eval vm_compute in nth (S iH) (ss_objs (ax_S X_sret1r)) O_src.
Definition objsN : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_sret1r))).
Definition X_sret2 : axst := Eval vm_compute in drop_lastA X_sret1r (objsN ++ [ohN]).
Definition p_new : sv := ltac2:(tb__ "0|0|
SfS1cSbS3cA1SdZ20A1A3").
Definition new_facts : list sprop := ltac2:(tb__ "0|2|
S0SaScSfS1cS48S1fA3M0SfS1cSbS3cA1S8cS25A1A3A2S0SaScG0SbP1eA1M1A2S0SaScS48G1A2S2SaA1A3A3A3").
Definition X_sret3 : axst := Eval vm_compute in ax_with_facts (carve_stateA X_sret2 p_new vSZ) (new_facts ++ ss_facts (ax_S X_sret2)).

Definition xit_regs : list sv := ltac2:(tb__ "0|0|
S0S9SbP6bA1S0S9SdS34A1S0S9SbPaA1S0S9SbP17A1S0S9SbP18A1S0S9SbP6dA1S0S9SbP6eA1S0S9SbP6fA1S0S9SbP1cA1S0S9SbP1dA1S0S9S23S0S9SbP70A1S0S9SbP71A1S0S9SbP7cA1S0S9SbP7dA1S0S9SbP7eA1S0S9SbP72A1S0S9SbP73A1S0S9SbP26A1S0S9SbP27A1S0S9SbP28A1S0S9S24S0S9SbP2aA1S0S9S1fS0S9S95S0S9SbP2dA1S0S9SbP2eA1S0S9SbP2fA1S0S9SbP74A1S0S9SbP75A1S0S9SbP76A1S0S9SbP77A1S2S9A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition xit_facts : list sprop := ltac2:(tb__ "0|3|
S0SaScS35S21A2S0SaScSdZ10000A1S21A2S0SaScS21SdS99S98Z2Z28A2Z21A2A1A2S0SaScSfS1cS20S8cS21A1A3SbP1eA1M0A2S0SaScS20G0A2S0SaScSdZ1000A1M1S20A2S0SaS13P65Z4M2A2S0SaScG1S23A2S0SaScSfS1cS23S1fA3G0A2S0SaScS23G0A2S0SaS13P69G2A2S2SaA1A3A3A3A3A3A3A3A3A3A3A3").
Definition C_exit : axst := ltac2:(tb__ "0|1|
S93S12Sa1S80S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS20A1S0SeS2dS2SeA1M0A3A3A3A3S5SeS94S0SeS40S20S3eS21S35A4S0SeS41S23A1G0A3A3A3A3S5SaS7fS5SaS45S2eA3A3P83S7A9S0S3S9S9A2S1S9S9S20S8cS21A1A4S28A3A2").

Definition X_ret : axst := Eval vm_compute in leafA_at C_exit ad_ret 0.
Definition iS : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) vP) (ss_objs (ax_S X_ret)) 0%nat.
Definition iHd : nat := Eval vm_compute in find_idxb (fun o => sv_eqb (ob_base o) vH &&& sv_eqb (ob_hi o) (SLit 24)) (ss_objs (ax_S X_ret)) 0%nat.
Definition sel_ret : list nat := Eval vm_compute in
  (List.filter (fun j => negb (Nat.eqb j iS || Nat.eqb j iHd)) (seq 0 (length (ss_objs (ax_S X_ret))))) ++ [iHd; iS].
Definition X_ret1 : axst := Eval vm_compute in optAp (apply_axforms X_ret [AXSelect sel_ret]).
Definition objsR : list sobj := Eval vm_compute in removelast (removelast (ss_objs (ax_S X_ret1))).
Definition ohR : sobj := Eval vm_compute in nth (length objsR) (ss_objs (ax_S X_ret1)) O_src.
Definition osR : sobj := Eval vm_compute in nth (S (length objsR)) (ss_objs (ax_S X_ret1)) O_src.
Definition X_ret2 : axst := Eval vm_compute in drop_lastA X_ret1 (objsR ++ [ohR]).
Definition X_ret3 : axst := Eval vm_compute in drop_lastA X_ret2 objsR.

Definition P_fail : axst := ltac2:(tb__ "0|1|
S93S12S9fS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSdZ0A1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cS29A1S0SeS2dS2SeA1A3A3A3A3S94A3S2eSa7S7A9S28A2").
Definition ok_facts : list sprop := ltac2:(tb__ "0|5|
S0SaScSdZ1000A1M0SbP8cM1A1M2A2S0SaScSfS1cG2S1fA3SbP1eA1M3A2S0SaS13G1Z4A2S0SaScG0SbP8dA1M4A2S0SaScG4G3A2S2SaA1A3A3A3A3A3").
Definition P_ok : axst := ltac2:(tb__ "0|1|
S93S12S9eS8fS91S90A1S0S3S4S9A2M0S1S4S9UaSbP8cA1A4S0G0S1S4S9U1SdS34A1A4S0G0S1S4S9U15S24A4S0G0S1S4S9U17S1fA4S0G0S1S4S9U18S95A4S2G0A1A3A3A3A3A3A2S8eS11S6S9A1S5SeS0SeS2aS2S10A1A1S0SeS2bS0SeS2cSbP8dA1A1S0SeS2dS2SeA1A3A3A3A3S94A3S5SaS78S2eA3P8eS7A9S28A2").
Definition am_ok : amode := AHead (SVar 141) true.

Definition s_fit : wsub := ltac2:(tb__ "0|0|
S97P64S82S5dA1S82S36A1A3").
Definition s_sret : wsub := ltac2:(tb__ "0|0|
S97P64S82S65A1S82S36A1A3").
Definition s_nofit : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cS31A4S97P64S82S5fA1S82S37A1A3A3").
Definition s_nohead : wsub := ltac2:(tb__ "0|0|
S0S3S1bS9A2S1S1bS9P6cSdZ10000A1A4S97P64S82S32A1S82S37A1A3A3").
Definition s_ret : wsub := ltac2:(tb__ "0|0|
S97P64S82S63A1S82S42A1A3").

Definition ahd : amode := AHead vHD true.
Definition nd0 : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S4eS66A4").
Definition ndO : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6cS69A4").
Definition ndS : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6dS2fA4").
Definition ndKc : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6aS2fA4").
Definition ndM : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndMok : ndesc := ltac2:(tb__ "0|0|
S84S7bS2S3S3S9S1aA2S9A2A1S44S2fA4").
Definition ndL : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S6bS67A4").
Definition ndF : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S2fA4").
Definition ndK : ndesc := ltac2:(tb__ "0|0|
S84S26S2S3S3S9S1aA2S9A2A1S2S86A1S68A4").
Definition z0 : sv := SLit 0.
Definition cutsE : list edescA := ltac2:(tb__ "0|4|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S43S39A4S1S1aS9Z64S22A4A4S0G2S1G0G1S1S81S83S51S33A4S1S1aS9Z5aS22A4A4S0G2S1G0G1S1S81S83S37S3bA4S1S1aS9Z50S22A4A4S0G2S1G0G1S1S81S83S4fS46A4S1S1aS9Z4bS22A4A4S0G2S1G0G1S1S81S83S57S76A4S1S1aS9Z41S22A4M3A4S0G2S1G0G1S1S81S83S58S47A4G3A4S0G2S1G0G1S1S81S83S36S3aA4S1S1aS9Z32SfS1dS1fS3dA3A4A4S0G2S1G0G1S1S81S83S50S3aA4S1S1aS9Z2dS22A4A4S2G2A1A3A3A3A3A3A3A3A3").
Definition exitsE : list edescA := ltac2:(tb__ "0|7|
S0S3S3S81S83A2M0S3S1aS9A2M1A2M2S1G0G1S1S81S83S61S39A4S1S1aS9Z5fS22A4M3A4S0G2S1G0G1S1S81S83S32S39A4G3A4S0G2S1G0G1S1S81S83S60S33A4S1S1aS9Z55S22A4M4A4S0G2S1G0G1S1S81S83S5cS33A4G4A4S0G2S1G0G1S1S81S83S5eS33A4G4A4S0G2S1G0G1S1S81S83S5aS3bA4S1S1aS9Z4eS22A4M5A4S0G2S1G0G1S1S81S83S5bS3bA4G5A4S0G2S1G0G1S1S81S83S3fS46A4S1S1aS9Z46S22A4A4S0G2S1G0G1S1S81S83S64S47A4S1S1aS9Z3cS22A4A4S0G2S1G0G1S1S81S83S62S3aA4S1S1aS9Z28S22A4A4S0G2S1G0G1S1S81S83S54S74A4S1S1aS9Z0S22A4M6A4S0G2S1G0G1S1S81S83S42S75A4G6A4S2G2A1A3A3A3A3A3A3A3A3A3A3A3A3").
End Lib_finalize_shape_dup1.

