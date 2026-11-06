From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16 YG0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoImg DiscoEntBodyStmt DiscoDcroParts DiscoDcroStrs DiscoDcroTjs DiscoDcroRo DiscoDcroHobs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AD2l.

Section d. Context {rc : YM05.RunCeil}.

Theorem dimg_consts_of_ro_all : forall B : asyms, dimg_consts_of_ro_stmt B.
Proof.
intro B. apply dcro_compose; [apply dcro_strs | apply dcro_tjs | apply dcro_ro | apply dcro_hobs].
Qed.

Theorem dimg_consts_of_ro_tfib : dimg_consts_of_ro_stmt AD2l.TfibB.
Proof. exact (dimg_consts_of_ro_all AD2l.TfibB). Qed.

End d.
