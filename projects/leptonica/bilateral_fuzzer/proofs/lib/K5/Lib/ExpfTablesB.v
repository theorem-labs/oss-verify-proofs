(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal ExpfModelB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_ExpfTablesB () := "K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53Lib:ExpfModelB8bil_cellC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z6of_natC69OSSVerify5KrLib2K53Lib6FpReal3FBbC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53Lib6FpReal:FBb_forallC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Fpu:fmt_singleK47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K53Lib;ExpfTablesB;DEN_SPATIALC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib2K53Lib;ExpfTablesB9DEN_RANGEC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib;ExpfTablesB:DEN_RANGE1C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53Lib6FpReal7p_one_sC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib:ExpfModelB:gauss_cellC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53Lib;ExpfTablesB;DEN_GAUSS_DC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition DEN_SPATIAL : Z := 1112014848.   (* [comment removed for export] *)
Definition DEN_RANGE : Z := 1128792064.     (* [comment removed for export] *)
Definition DEN_RANGE1 : Z := 1073741824.    (* [comment removed for export] *)

Lemma bil_spatial_FB : forall i, 0 <= i < 11 -> FB fmt_single 1 (bil_cell DEN_SPATIAL i).
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "h01ip;1p;2p;3p;5g0000j1;Tg000Nj1:j24Tg001Mj11Tg001lj29Tg002Fj17Tg002fj33Tg003\j25Tg0048j36Tg004Tj32Tg004nj58Tf0R0#1#1p=0g005kR1g006X#;R2g007=R3#:g008@R4#1#0#0#0#0#0R5g008_R6g009?R7'9g009_R8%70,439312X08154536=267dD8o"). Qed.
Lemma bil_range_FB : forall i, 0 <= i < 256 -> FB fmt_single 1 (bil_cell DEN_RANGE i).
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "h01ip;1p;2p;3p;5g0000j1;Tg000Nj1:j28Tg001lj22Tg002Fj19Tg002fj34Tg003\j23Tg0048j35Tg004Tj36Tg004nj57Tg001Mj10Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g005kR1g006X#;R2g00:>R3#:g008@R4#1#1#1#1#1#1#1#1R5g008_R6g009?R7'2g009_R8%90,839412X08134535=667dD7o"). Qed.
Lemma bil_range1_FB : forall i, 0 <= i < 256 -> FB fmt_single 1 (bil_cell DEN_RANGE1 i).
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "h01ip;1p;2p;3p;5g0000j1;Tg000Nj1:j28Tg001lj22Tg002Fj19Tg002fj34Tg003\j23Tg0048j35Tg004Tj36Tg004nj57Tg001Mj10Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g005kR1g006X#;R2g00;?R3#:g008@R4#1#1#1#1#1#1#1#1R5g008_R6g009?R7'2g009_R8%90,839412X08134535=667dD7o"). Qed.

Lemma bil_spatial_centre : bil_cell DEN_SPATIAL 0 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "p;1p;2p;3g00<Aj11Tg00<fj10Tg0000j17Tg001lj26Tg000Nj25Tg004Tj34Tf0R0#0#0p=3%00#0#0#0p=2g00=KR0g006X#1#1#1#1#1#1#0#3#2#2#2#2#2#7'6g007=g00=i'5g00>G540do"). Qed.
Lemma bil_range_centre : bil_cell DEN_RANGE 0 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "p;1p;2p;3g00<Aj11Tg00<fj10Tg0000j17Tg001lj26Tg000Nj25Tg004Tj34Tf0R0#0#0p=3%00#0#0#0p=2g00=KR0g006X#1#1#1#1#1#1#0#3#2#2#2#2#2#7'6g00:>g00=i'5g00>G540do"). Qed.
Lemma bil_range1_centre : bil_cell DEN_RANGE1 0 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "p;1p;2p;3g00<Aj11Tg00<fj10Tg0000j17Tg001lj26Tg000Nj25Tg004Tj34Tf0R0#0#0p=3%00#0#0#0p=2g00=KR0g006X#1#1#1#1#1#1#0#3#2#2#2#2#2#7'6g00;?g00=i'5g00>G540do"). Qed.

Definition DEN_GAUSS_D : Z := 4641240890982006784.   (* [comment removed for export] *)
Lemma bil_gauss_FB : forall q, 0 <= q < 801 -> FB fmt_single 1 (gauss_cell DEN_GAUSS_D p_one_s q).
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "h01ip;1p;2p;3p;5g0000j1;Tg00?Aj2:j34Tg001Mj10Tg001lj29Tg002Fj17Tg002fj33Tg003\j25Tg0048j36Tg004Tj32Tg004nj58Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g005kR1g006X#;R2g00@BR3g00>GR4':g008@R5#0#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1R6g008_R7g009?R8'9g009_R9%7094349312X09155636=278dD8o"). Qed.
Lemma bil_gauss_centre : gauss_cell DEN_GAUSS_D p_one_s 0 = p_one_s.
Proof.
ltac2:(KReplay.run1 (kr_t_ExpfTablesB ()) [] "p;1p;2p;3g00<Aj11Tg00<fj10Tg0000j17Tg001lj26Tg00?Aj35Tg004Tj34Tf0R0#0#0p=3%00#0#0#0p=2g00=KR0g006X#1#1#1#1#1#1#0#3#2#2#2#2#2#7'6g00@Bg00>GR1g00=i35=401do"). Qed.
