(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface LibBudget.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocIfaceStmt () := "K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib2CJ?MallocIfaceStmt>mng_size_classC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition MNG_UNIT : Z := 16.
Definition MNG_IB : Z := 4.
Definition MNG_BIG : Z := 131052.
Definition MNG_NMAX : Z := LIB_NMAX.
Definition MNG_MALLOC_STACK : Z := 8192.
Definition MNG_PGSZ : Z := 4096.

Definition mng_size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8;
   9; 10; 12; 15;
   18; 20; 25; 31;
   36; 42; 50; 63;
   72; 84; 102; 127;
   146; 170; 204; 255;
   292; 340; 409; 511;
   584; 682; 818; 1023;
   1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095;
   4680; 5460; 6552; 8191].
Definition mng_size_class_tab (i : Z) : Z := nth (Z.to_nat i) mng_size_classes 0.
Definition mng_clz32 (m : Z) : Z := 31 - Z.log2 m.

Definition mng_size_class (n : Z) : Z :=
  let n := Z.shiftr (n + MNG_IB - 1) 4 in
  if n <? 10 then n else
  let n := n + 1 in
  let i := (28 - mng_clz32 n) * 4 + 8 in
  let i := if mng_size_class_tab (i + 1) <? n then i + 2 else i in
  if mng_size_class_tab i <? n then i + 1 else i.

Definition mng_round_up_pg (x : Z) : Z := x + Z.land (- x) (MNG_PGSZ - 1).

Definition mng_round_big (n : Z) : Z := mng_round_up_pg (n + MNG_IB + MNG_UNIT).

Example mng_size_class_24 : mng_size_class 24 = 1.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocIfaceStmt ()) ["AC_1"] "p;1p;2g0000j11Tg000Nj20Tg000hg001F#1'0o"). Qed.
Example mng_size_class_32 : mng_size_class 32 = 2.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocIfaceStmt ()) ["AC_1"] "p;1p;2g001kj12Tg0000j11Tg000Nj20Tg000hg001F#2#1'0o"). Qed.
Example mng_size_class_65536 : mng_size_class 65536 = 44.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocIfaceStmt ()) ["AC_1"] "p;1p;2p;3g001kj11Tg002Pj13Tg0000j12Tg000Nj26Tg0035j15Tg004;j34Tf0#1#1p=0g000hR0g001F#1R1#3#3#0#2R2'6%11#0#0#0#0#0#0#0#2#5=402do"). Qed.

Section Consts.
Variable SEGS : list Segment.
Variable L : Layout.

Record mi_consts_ok (MI : MallocIface SEGS L) : Prop := MI_CONSTS_OK {
  mc_size_class : forall n, size_class MI n = mng_size_class n;
  mc_big : BIG MI = MNG_BIG;
  mc_nmax : NMAX MI = MNG_NMAX;
  mc_round_big : forall n, round_big MI n = mng_round_big n;
  mc_stack : MALLOC_STACK MI = MNG_MALLOC_STACK;

  mc_room : forall A n, room_for MI A n <->
      ((0 <= n < MNG_BIG /\
        count_class_f (size_class MI) (BIG MI) (live MI A) (mng_size_class n) + 1 <= caps MI A (mng_size_class n) /\
        count_class_f (size_class MI) (BIG MI) (live MI A) (mng_size_class n + 1) + 1 <= caps MI A (mng_size_class n + 1))
       \/ (MNG_BIG <= n <= MNG_NMAX /\
           big_bytes_f (round_big MI) (BIG MI) (live MI A) + mng_round_big n <= bigcap MI A))
}.
End Consts.

End AC_1.
