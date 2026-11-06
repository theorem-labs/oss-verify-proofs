From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16 YG0f YCbj.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YD2l.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntBodyStmt YDcroParts YDcroStrs YDcroTjs YDcroRo YDcroHobs.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section d. Context {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.

Theorem dimg_consts_of_ro_all : forall B : asyms, dimg_consts_of_ro_stmt (PI := PB_tfib) B.
Proof.
intro B. apply dcro_compose; [apply dcro_strs | apply dcro_tjs | apply dcro_ro | apply dcro_hobs].
Qed.

Theorem dimg_consts_of_ro_tfib : dimg_consts_of_ro_stmt (PI := PB_tfib) YD2l.TfibB.
Proof. exact (dimg_consts_of_ro_all YD2l.TfibB). Qed.

End d.
