(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk SimInv ExitSim ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_RefReadLib () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC49OSSVerify5KrLib7SeqExec>rdn_wbytes_hitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition kfootprint (E : env) (K : kentry) : option (Z * Z) :=
  match K with
  | KWord a w _ => Some (estart E a, Z.of_nat w)
  | KZero a n => Some (estart E a, elenZ E n)
  | KBlob a n _ => Some (estart E a, elenZ E n)
  | KImg lo hi => Some (lo, hi - lo)%Z
  | _ => None
  end.

Definition kfoot_far (E : env) (K : kentry) (wa wn : Z) : Prop :=
  match kfootprint E K with
  | None => True
  | Some (s, n) => (s + n <= wa \/ wa + wn <= s)%Z
  end.

Lemma rdn_wbytes_self : forall segs m (a : word) bs,
  (bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RefReadLib ()) [] "h01ah12bsh21mh34segsp;1p;2p;5g0000j14Tg000Pj10Tg0015j12Tg001Sj11Tg0026j1<Tg002Xj2;Tg003Bj2:Tg003bj17Tg004Bj26Tg004_j13Tg005=j25Tg005Zj28Tg0066j59Tg0071#4g0080#0R0#0#0R1#0#0#0R2#2R3#1R4%21#1R1#<[%41f1R5,;3f0R3,:1#7'6%30%32'5'8f4P5f3f2P3D9UW1X04W2W3o"). Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
