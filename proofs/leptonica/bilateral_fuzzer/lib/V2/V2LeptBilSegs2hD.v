From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib LeptExec LeptExecW LeptExecFP LeptExecX LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal FpBound FpSiteC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptBilSegs V2LeptBilSegs2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition HR (datat wpl h : Z) : list (Z * Z) := [(datat, (4 * (wpl * (h + 22)))%Z)].
Definition HKT : list reg := [5; 6; 7; 16; 17; 28]%bv.
Definition HST : list reg := [5; 6; 7; 14; 15; 16; 17; 28]%bv.

Definition hgeo (s datas datat wpl w h spat rng kval : Z) : Prop :=
  (4096 + 320 <= s <= 2 ^ 47)%Z /\ (s mod 16 = 0)%Z /\
  (1 <= w)%Z /\ (1 <= h)%Z /\ (w + 22 <= 20000)%Z /\ (h + 22 <= 20000)%Z /\ wpl = wpl_of (w + 22) 8 /\ (4 * (wpl * (h + 22)) <= 67108864)%Z /\
  (4096 <= datas)%Z /\ (datas + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z /\ (datas mod 4 = 0)%Z /\
  (4096 <= datat)%Z /\ (datat + 4 * (wpl * (h + 22)) <= 2 ^ 47)%Z /\ (datat mod 4 = 0)%Z /\
  (4096 <= spat)%Z /\ (spat + 44 <= 2 ^ 47)%Z /\ (spat mod 4 = 0)%Z /\ (4096 <= rng)%Z /\ (rng + 1024 <= 2 ^ 47)%Z /\ (0 <= kval <= 255)%Z /\
  (datat + 4 * (wpl * (h + 22)) <= datas \/ datas + 4 * (wpl * (h + 22)) <= datat)%Z /\
  (datat + 4 * (wpl * (h + 22)) <= s - 320 \/ s <= datat)%Z /\
  (datat + 4 * (wpl * (h + 22)) <= spat \/ spat + 44 <= datat)%Z /\
  (datat + 4 * (wpl * (h + 22)) <= rng \/ rng + 1024 <= datat)%Z /\
  (datat + 4 * (wpl * (h + 22)) <= bc_chalf \/ bc_chalf + 8 <= datat)%Z.

Definition hframe (s datas datat wpl w h : Z) (M : word -> option byte) : Prop :=
  rdn SEGS M (Z_to_bv 64 (s - 240)) 8 = Some (Z_to_le_bytes 8 wpl) /\
  rdn SEGS M (Z_to_bv 64 (s - 224)) 8 = Some (Z_to_le_bytes 8 datas) /\
  rdn SEGS M (Z_to_bv 64 (s - 216)) 8 = Some (Z_to_le_bytes 8 h) /\
  rdn SEGS M (Z_to_bv 64 (s - 208)) 8 = Some (Z_to_le_bytes 8 datat) /\
  rdn SEGS M (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 bc_cptr) /\
  rdn SEGS M (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) /\
  rdn SEGS M (Z_to_bv 64 (s - 184)) 8 = Some (Z_to_le_bytes 8 w).

Definition hmem0 (s datas datat wpl w h spat rng : Z) (M : word -> option byte) : Prop :=
  rd_bytes M datas (4 * (wpl * (h + 22))) /\ store_ok SEGS M (Z_to_bv 64 datat) (Z.to_nat (4 * (wpl * (h + 22)))) = true /\
  kcell_ok spat 11 M /\ kcell_ok rng 256 M /\ img_none M bc_chalf 8 /\ hframe s datas datat wpl w h M.

Definition hfix (regs : bvmap 5 word) (s kval spat rng wpl : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (s - 320) /\ getr regs 8 = Z_to_bv 64 (-10) /\ getr regs 9 = Z_to_bv 64 kval /\
  getr regs 18 = Z_to_bv 64 10 /\ getr regs 19 = Z_to_bv 64 (- 2 ^ 31) /\ getr regs 20 = Z_to_bv 64 1 /\
  getr regs 21 = Z_to_bv 64 spat /\ getr regs 22 = Z_to_bv 64 3 /\ getr regs 23 = Z_to_bv 64 rng /\ getr regs 24 = Z_to_bv 64 1 /\
  getr regs 25 = Z_to_bv 64 wpl /\ getr regs 26 = Z_to_bv 64 (2 ^ 64 - 1 - rng) /\ getr regs 27 = Z_to_bv 64 1 /\
  getr regs 29 = Z_to_bv 64 11.

Lemma hfix_keep : forall (regs regs' : bvmap 5 word) (s kval spat rng wpl : Z),
  hfix regs s kval spat rng wpl -> regs_agree (fun r => In r HPL) regs regs' -> hfix regs' s kval spat rng wpl.
Proof.
  intros regs regs' s kval spat rng wpl HF RA.
  assert (K : forall r, ~ In r HPL -> getr regs' r = getr regs r) by exact RA.
  unfold hfix in *. rewrite !K by (unfold HPL; notin_list). exact HF.
Qed.

Lemma hkt_hpl : forall r : reg, In r HKT -> In r HPL.
Proof. intros r Hr. unfold HKT, HPL in *. simpl in *. tauto. Qed.

Lemma hst_hpl : forall r : reg, In r HST -> In r HPL.
Proof. intros r Hr. unfold HST, HPL in *. simpl in *. tauto. Qed.
