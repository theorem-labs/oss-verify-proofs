From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcModel.
Import ListNotations.
Open Scope Z_scope.

Definition recsum (bs : list byte) : Z := psum bs (length bs) mod 128.

Definition stampck (bs : list byte) : Z := (- psum bs (length bs)) mod 128.

Definition dt1_bytes (f l a : Z) : list byte :=
  map (Z_to_bv 8) [4; f; 0; l + 5; 0; 2; 0; 254; l; 240; 65; 10; 0; 0; 18; 18; 5; 0; Z.shiftr a 8; a].
