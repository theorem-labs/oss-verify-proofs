(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code"; "segs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.StrAddr"; "memcpy_entry"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "cons"; "nil"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy_hdr"; "Posts_mh"; "Pre_mh"; "P_mh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "check_cfg"; "check_ecfg"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "FUELC"; "cutpcs_memcpy"; "cuts_memcpy"; "exits_memcpy"; "vcuts_memcpy"; "vexits_memcpy"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr"; "FUELH"; "cutpcs_mh"; "cuts_mh"; "exits_mh"; "vcuts_mh"; "vexits_mh"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Str_memcpy__G1.Str_memcpy"; "Posts_memcpy"; "Pre_memcpy"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
Require Stdlib.ZArith.ZArith.
Require Stdlib.NArith.NArith.
Require Stdlib.Lists.List.
Require Stdlib.Bool.Bool.
Require Stdlib.PArith.PArith.
Require Stdlib.micromega.Lia.
Require stdpp.bitvector.bitvector.
Require LinuxProcessSemantics.LinuxProcessSem.BvBase.
Require LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.State.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.Riscv.Prelude.
Require LinuxProcessSemantics.Riscv.Instr.
Require LinuxProcessSemantics.Riscv.Decode.
Require LinuxProcessSemantics.Riscv.DecodeC.
Require LinuxProcessSemantics.Riscv.Sem.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.LiaFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStepFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Str_memcpy_hdr.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.

Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Pre_mh : sstate := MuslMemcpyHdr.Pre_mh memcpy_entry.
Definition Posts_mh : list leaf := MuslMemcpyHdr.Posts_mh memcpy_entry.

Lemma check_mh : ltac2:(tb__ "0|0|
S8S4S18S0S20S21S1A1S2S22S1A1S23S1A1A6S5A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma echeck_mh : ltac2:(tb__ "0|0|
S8S4S19S0S20S21S1A1S2S24S1A1S25S1A1A6S5A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_ecfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem memcpy_hdr_sum : ltac2:(tb__ "0|0|
S17OF_;S3SaA1S9OF_;F_;SeSdS0R3R2A3S16S0R4ScS0R3S13R2A4SbS0R3S2R2S12A5A4F_;Frho;FK;Fok;").
Proof. exact (MuslMemcpyHdr.memcpy_hdr_sum segs memcpy_entry check_mh). Qed.
Theorem memcpy_hdr_sum_ex : ltac2:(tb__ "0|0|
S3SaA1S9OF_;F_;SeS15S0ScS0R2S13R1A4SbS0R2S2R1S12A5A3Frho;FK;").
Proof. exact (MuslMemcpyHdr.memcpy_hdr_sum_ex segs memcpy_entry echeck_mh). Qed.
Definition P_mh : sstate := MuslMemcpyHdr.P_mh memcpy_entry.
Lemma Posts_mh_eq : ltac2:(tb__ "0|0|
S8S3SfA1S12S6SfS11S14S10A2S7SfA1A3A3"). Proof. reflexivity. Qed.
End Str_memcpy_hdr.

Module Str_memcpy.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.PArith.PArith Stdlib.micromega.Lia.
Import stdpp.bitvector.bitvector.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Code.

Import ListNotations.
Import StrAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition Pre_memcpy : sstate := MuslMemcpy.Pre_memcpy memcpy_entry.
Definition Posts_memcpy : list leaf := MuslMemcpy.Posts_memcpy memcpy_entry.

Lemma check_memcpy : ltac2:(tb__ "0|0|
S8S4S18S0S1aS1bS1A1S2S1cS1A1S1dS1A1A6S5A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma echeck_memcpy : ltac2:(tb__ "0|0|
S8S4S19S0S1aS1bS1A1S2S1eS1A1S1fS1A1A6S5A3").
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_ecfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem memcpy_sum : ltac2:(tb__ "0|0|
S17OF_;S3SaA1S9OF_;F_;SeSdS0R3R2A3S16S0R4ScS0R3S27R2A4SbS0R3S2R2S26A5A4F_;Frho;FK;Fok;").
Proof. exact (MuslMemcpy.memcpy_sum segs memcpy_entry check_memcpy). Qed.
Theorem memcpy_sum_ex : ltac2:(tb__ "0|0|
S3SaA1S9OF_;F_;SeS15S0ScS0R2S27R1A4SbS0R2S2R1S26A5A3Frho;FK;").
Proof. exact (MuslMemcpy.memcpy_sum_ex segs memcpy_entry echeck_memcpy). Qed.
End Str_memcpy.
