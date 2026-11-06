(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "loc"; "LMem"; "footprint"; "layout"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "VmMaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "ledger_ok"; "mc_img_hi"; "mc_img_lo"; "mconsts"; "topL"; "vm_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "astate"; "sptr"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fp_mem_range : ltac2:(tb__ "0|2|
S10S8S14SbS15S2S12R5R4R3A3SdR7R4A2S16SaS5S2A2S9S5S2S6R4A1R3A4S7R6A1A3S0Z0R4A2S3S0S13ScR9R6A2M0A2S3S0S1G0R5A2M1S11R9A1A2S4S0G1SfRaA1A2S0SeRaA1G0A2A2A2A2F_;F_;F_;F_;Fn;Fp;Fvm;Fs;FL;FC;").
Proof.
  intros C L s vm p n HV HL Hin Hn. rewrite (vm_ok_top L s vm HV).
  destruct HV as (_ & _ & _ & Hcov & _). destruct (Hcov p n Hin) as (e & He & E1 & E2).
  destruct (HL e He) as (G1 & G2 & G3). lia.
Qed.
