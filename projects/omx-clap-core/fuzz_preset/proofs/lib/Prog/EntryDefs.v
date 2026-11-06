From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp WriterValue WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
pj_parse_c check_no_overread_c check_reject_clean_starved_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition ent_n (x : list byte) : Z := Z.of_nat (length x).
Definition ent_T (x : list byte) : list ev := snd (jr_run jr_strtod (zb x) []).
Definition ent_took (x : list byte) : Z := Z.of_nat (ncalls jr_strtod (zb x)).
Definition ent_c3 (cnt0 : Z) (x : list byte) : Z := cnt0 + 3 * ent_took x + ent_took x.

Definition ent_tree_dl (x : list byte) (D : list (Z * Z)) : Prop :=
  Permutation (map snd D) (map Z.of_nat (lsz (ent_T x))) /\ Z.of_nat (length D) = nlive (ent_T x).

Section R.
Variable F : ResForm.

Definition ent_b1 (b0 : rf_R F) (x : list byte) (E1 E2 E3 : list (Z * Z)) : rf_R F :=
  cno_free3 F (cno_mid F b0 (ent_n x) (ent_T x) (cno_ok x) E1 E2 E3) (ent_n x).

Definition ent_b2 (b0 : rf_R F) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) : rf_R F :=
  if cno_ok x then rf_run F (ent_b1 b0 x E1 E2 E3) (ent_T x)
  else rf_frees F (rf_run F (ent_b1 b0 x E1 E2 E3) (ent_T x)) Dp.

Definition ent_b3 (b0 : rf_R F) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) : rf_R F :=
  rf_free F (rf_malloc F (ent_b2 b0 x E1 E2 E3 Dp) (ent_n x + 1)) (ent_n x + 1).

Definition ent_brej (b0 : rf_R F) (x : list byte) (E1 E2 E3 Dp : list (Z * Z)) (trs : list ev) (Ds : list (Z * Z)) :
    rf_R F :=
  if ent_took x =? 0 then ent_b3 b0 x E1 E2 E3 Dp else rf_frees F (rf_run F (ent_b3 b0 x E1 E2 E3 Dp) trs) Ds.

End R.
