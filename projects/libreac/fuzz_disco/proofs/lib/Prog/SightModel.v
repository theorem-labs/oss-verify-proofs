From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import RcModel CtrlParsed disco_classify_c.
Import ListNotations.
Open Scope Z_scope.

Definition sighting_facts (S F U : list byte) (len st : Z) : Prop :=
  50 <= len /\
  bytes_eqb (fld S 0 6) (fld F 6 6) = true /\
  bytes_eqb (fld S 0 6) U = false /\
  (st = 0 -> fu S 20 4 = geo len) /\
  (st <> 0 -> geo len <= fu S 20 4) /\
  sighting_ok S /\
  ((fb F 16 = 0 /\ fb F 17 = 0) \/ fsum F = 0).
