(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRelSpec BMmapSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bap04 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c6ARocqVerifyHarness?AgentSubmission3bpB2HF5Bap04;grant_ok_naI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC6ARocqVerifyHarness?AgentSubmission3bpB2HF8BMmapSim?place_ok_unpackK47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition grant_ok_na (hint : word) (m : Model) (a : word) (n : Z) : bool :=
  place_ok (m_vmmaps m) a n.

Lemma grant_ok_na_unpack : forall hint m a n,
  grant_ok_na hint m a n = true ->
  bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\
  bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Bap04 ()) [] "h01Hh11ah24hinth31mh41np;1p;4p;3g0000j10Tg000Uj16Tg0013j12Tg001Vj41Tg002Sj35Tg002mj14Tg003dj43Tg004h#0#0#0#0#0#0#6#2R0g005Mg006Cg006af3R1f2R2f1R3f0R4C1g007A35%41P2P3P4C3W0W4X10W3W2o"). Qed.

Definition gap_floor : Z := 0x100000000.

Definition cand (N : Z) (j : nat) : Z := gap_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

