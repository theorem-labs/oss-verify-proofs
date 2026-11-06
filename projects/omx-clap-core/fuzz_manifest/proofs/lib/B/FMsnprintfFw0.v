(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfFw0.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* The symbolic entry state of musl __fwritex (fm 0x8ed08) on the snprintf FILE, called from printf_core's out():
   frame base (atom 2) = sp0, musl vfprintf's entry sp; __fwritex entered with sp = sp0 + OSP_FW, a0 = src (atom 10),
   a1 = l (atom 11), a2 = f = sp0 + FO. Extra atoms: 33 = b (bytes in the internal buffer), 34 = the cookie's s,
   35 = the cookie's n. Only the FILE fields __fwritex and sn_write read are chunks. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YE3e YE3f YE3g YE6g YE39 YE2p YE3i YE3h YF0m YE22 YF0x YE20 YE2y YE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfI FMsnprintfK.
Import ListNotations.
Open Scope Z_scope.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition fw_chunks : list YP09.chunk :=
[ YP09.mkChunk FO (CVal 4 (SLit 0));
  YP09.mkChunk (FO + 32) (CVal 8 (SOff 2 (IBO + 80)));
  YP09.mkChunk (FO + 40) (CVal 8 (SAlu ALU_ADD (SOff 2 IBO) (SOff 33 0)));
  YP09.mkChunk (FO + 56) (CVal 8 (SOff 2 IBO));
  YP09.mkChunk (FO + 72) (CVal 8 (SLit A_SNW));
  YP09.mkChunk (FO + 88) (CVal 8 (SOff 2 IBO));
  YP09.mkChunk (FO + 144) (CVal 4 (SLit 0xffffffff));
  YP09.mkChunk (FO + 152) (CVal 8 (SOff 2 CKO)) ].
Definition fw_regions : smem :=
[ YP09.mkRegion (Some 2%nat) (- SNK_STK) 0 (- SNK_STK) OSP_FW [];
  YP09.mkRegion (Some 2%nat) FO (FO + 0xe8) (FO + 40) (FO + 64) fw_chunks;
  YP09.mkRegion (Some 2%nat) CKO (CKO + 16) CKO (CKO + 16)
    [YP09.mkChunk CKO (CVal 8 (SOff 34 0)); YP09.mkChunk (CKO + 8) (CVal 8 (SOff 35 0))] ].
Definition fw_sr : list sv := sr_set (sr_set sr_atoms (2%bv : bv 5) (SOff 2 OSP_FW)) (12%bv : bv 5) (SOff 2 FO).
Definition fw_facts : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (33%nat, mkAF 0 80 0); (11%nat, mkAF 0 (2 ^ 31) 0);
  (10%nat, mkAF 1 (2 ^ 47) 0); (34%nat, mkAF 1 (2 ^ 47) 0); (35%nat, mkAF 0 (2 ^ 31) 0) ] [] [].
Definition fw0 : sstate := mkSS A_FWX fw_sr fw_regions None fw_facts.
Definition RUN (s : sstate) := sym_runN tfibsegs tfibmusl_tbl FUEL s.
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition FW_ROOM : sv := SAlu ALU_SUB (SLit 0) (SOff 33 (-80)).
End s.
