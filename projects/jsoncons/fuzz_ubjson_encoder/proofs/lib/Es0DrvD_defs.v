(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry Es0LibStdioCall
  HeapIface DrvKit Es0Drv_defs Es0DrvG_defs Es0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0DrvD_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init9Datatypes4prod01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry01C13~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K47Corelib7Numbers7BinNums1Z03K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knTcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs8kn_afterC13~~~K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sr_updC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs:relay_ok_bC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5wposKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs7keep_pfC13~~~I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive?sr_after_call_jC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6DrvKit7ksubl_bC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs:keep_allocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_lC13~~~C47Corelib5Lists7ListDef3nthC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K47Corelib4Init5Logic3and01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rT00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rT10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rT01C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rT11C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knTeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4sr01C13~~~K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5srTm0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLH1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knV0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rVC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knU0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4sr00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4sr10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3srVC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3srRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs6srS_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rLB1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5flag1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rLB2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4srLBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rLc1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5flag0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4rLc2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4srP0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLr1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLp1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLr2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLp2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLc1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLH2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5knLc2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3knRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs6flagsKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knR2C13~~~I47Corelib4Init9Datatypes3nat00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib<callee_savedC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs4knX0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3srQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3knQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs3scPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5rS_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5dec_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs5rS_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rYC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvD_defs2rZC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_T : list Z := (0x348cc :: 0x346b8 :: STOPS)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_T scr ss [].
(* [comment removed for export] *)
Definition STOPS_P : list Z := [0x9bdf8; 0xa0ffc; 0x9dddc; 0x9dc9c; 0x349e4]%Z.
Definition STOPS_R : list Z := (0x348f0 :: STOPS_P)%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_P scr ss [].
Definition runR (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_R scr ss [].

(* [comment removed for export] *)
Definition knTc (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0.
Definition rT00 := Eval vm_compute in runT scr0 (SS 0x34814 srT0 [] (knTc 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runT scr0 (SS 0x34814 srT0 [] (knTc 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runT scr0 (SS 0x34814 srT0 [] (knTc 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runT scr0 (SS 0x34814 srT0 [] (knTc 1 32767 1 67108857) 81).
Definition sr00 : list expr := Eval vm_compute in s_regs (fst (fst rT00)).
Definition sr01 : list expr := Eval vm_compute in s_regs (fst (fst rT01)).
Definition sr10 : list expr := Eval vm_compute in s_regs (fst (fst rT10)).
Definition sr11 : list expr := Eval vm_compute in s_regs (fst (fst rT11)).
(* [comment removed for export] *)
Definition calls_x : expr := Eval vm_compute in nth 21 sr11 (ELit 0).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_case_entry (K : kentry) : bool :=
  existsb (kentry_eqb K) [KRange (EVar 73) 0 0; KRange (EVar 73) 1 32767; KRange (EVar 79) 0 0; KRange (EVar 79) 1 67108857].
Definition uncase (kn : list kentry) : list kentry := List.filter (fun K => negb (is_case_entry K)) kn.
Definition knTe : list kentry := Eval vm_compute in uncase (kn_after rT11 (knTc 1 32767 1 67108857)).

(* [comment removed for export] *)
Definition knTk : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knTe.

(* [comment removed for export] *)
Definition srTm0 : list expr := Eval vm_compute in sr_upd sr11 (ridx 21) (EVar 81).
Definition srU0 : list expr := Eval vm_compute in sr_after_call_j srTm0 (map ridx c_kept) 82.
(* [comment removed for export] *)
Definition knU0 : list kentry := Eval vm_compute in kn_blk2 92 ++ knTk.
Definition rU := Eval vm_compute in runT scr0 (SS 0x34878 srU0 [] knU0 114).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
(* [comment removed for export] *)
Definition srV0 : list expr := Eval vm_compute in sr_after_call_j srU (map ridx callee_kept) 114.
Definition knV0 : list kentry := Eval vm_compute in keep_rd knU0.
Definition rV := Eval vm_compute in runT scr0 (SS 0x3488c srV0 [] knV0 146).
Definition srV : list expr := Eval vm_compute in s_regs (fst (fst rV)).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
(* [comment removed for export] *)
Definition srLH : list expr :=
  [ELit 0; EVar 85; spx (-208); ELit 67584; ELit 831552; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 824848; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition knLH1 : list kentry := Eval vm_compute in keep_rd knTk.
(* [comment removed for export] *)
Definition shared_pos : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_b (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_pos.
(* [comment removed for export] *)
Definition IMG_LIB : list (Z * Z) := [(0x10000, 0xc9630); (0xca7b8, 0xcaf68); (0xcaf70, 0xcaf9c); (0xcafa0, 0xeb088); (0xeb2a8, 0xeb448); (0xeb7f0, 0xec000)]%Z.
Definition keep_lib (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW kn.

(* [comment removed for export] *)
Definition rLB1 := Eval vm_compute in runT scr0 (SS 0x348cc srLH [] knLH1 102).
Definition srLB : list expr := Eval vm_compute in s_regs (fst (fst rLB1)).
Definition knLc1 : list kentry := Eval vm_compute in kn_after rLB1 knLH1.
(* [comment removed for export] *)
Definition srLr0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLB (map ridx c_kept) 102) (ridx 10) (ELit 0).
Definition knLr1 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc1.
(* [comment removed for export] *)
Definition rLc1 := Eval vm_compute in runT scr0 (SS 0x348e0 srLr0 [] knLr1 134).
Definition srP0 : list expr := Eval vm_compute in s_regs (fst (fst rLc1)).
Definition knLp1 : list kentry := Eval vm_compute in kn_after rLc1 knLr1.
(* [comment removed for export] *)
Definition rP := Eval vm_compute in runP scr0 (SS 0x3499c srP0 [] knLp1 134).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knLp1.
(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 18446744073709551591).
Definition rQ := Eval vm_compute in runP scr0 (SS 0xa1a24 srQ0 [] knP 134).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition scP : stdio_res := Eval vm_compute in the_sc (stdio_call 134 srQ knQ).
Definition srR0 : list expr := Eval vm_compute in sc_sr scP.
Definition knR0 : list kentry := Eval vm_compute in sc_kn scP.
Definition rR := Eval vm_compute in runR scr0 (SS (sc_ret scP) srR0 [] knR0 166).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition IMG_PF : list (Z * Z) := [(0x10000, 0xb94a8); (0xb94ac, 0xb94d0); (0xb94d8, 0xc9630); (0xcaf70, 0xcaf9c); (0xcafa0, 0xeb448); (0xeb7f0, 0xeb830); (0xebc30, 0xec000)]%Z.
Definition keep_pf (kn : list kentry) : list kentry := kn_keep 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW kn.
Definition wposK (e : expr) : kentry := KWord (SA (ELit 0) 0xb94d0) 8 e.
Definition flagsK : kentry := KWord (SA (ELit 0) 0xb94a8) 4 (ELit 5).
(* [comment removed for export] *)
Definition knR2 : list kentry := Eval vm_compute in keep_pf (keep_lib (-208) [(48%nat, 65536%Z)] [] knR).
Definition knLH2 : list kentry := wposK (EVar 101) :: KRange (EVar 101) 0xeb830 0xeb836 :: flagsK :: knR2.

(* [comment removed for export] *)
Definition rLB2 := Eval vm_compute in runT scr0 (SS 0x348cc srLH [] knLH2 102).
Definition knLc2 : list kentry := Eval vm_compute in kn_after rLB2 knLH2.
Definition knLr2 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc2.
Definition rLc2 := Eval vm_compute in runT scr0 (SS 0x348e0 srLr0 [] knLr2 134).
Definition knLp2 : list kentry := Eval vm_compute in kn_after rLc2 knLr2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srS0 : list expr := sr_upd srLH (ridx 19) (ELit 0).
Definition rS_tk := Eval vm_compute in runT (SCR [true] [] []) (SS 0x348f0 srS0 [] knLH2 102).
Definition rS_ft := Eval vm_compute in runT (SCR [false] [] []) (SS 0x348f0 srS0 [] knLH2 102).
Definition srS_tk : list expr := Eval vm_compute in s_regs (fst (fst rS_tk)).
Definition srS_ft : list expr := Eval vm_compute in s_regs (fst (fst rS_ft)).
Definition dec_x : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).

(* [comment removed for export] *)
Definition srX0 : list expr := Eval vm_compute in sr_after_call_j srS_ft (map ridx c_kept) 102.
Definition knX0 : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2.
Definition rX := Eval vm_compute in runT scr0 (SS 0x3490c srX0 [] knX0 134).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
(* [comment removed for export] *)
Definition srY0 : list expr :=
  Eval vm_compute in sr_upd (sr_upd (sr_upd (sr_upd srX (ridx 8) (ELit 0)) (ridx 10) (ELit 0)) (ridx 1) (EVar 134)) (ridx 11) (EVar 135).
Definition rY := Eval vm_compute in runT scr0 (SS 0x34738 srY0 [] knX0 136).
Definition srY : list expr := Eval vm_compute in s_regs (fst (fst rY)).
(* [comment removed for export] *)
Definition srZ0 : list expr := Eval vm_compute in sr_after_call_j srY (map ridx c_kept) 136.
Definition knZ0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knX0.
Definition rZ := Eval vm_compute in runT scr0 (SS 0x34740 srZ0 [] knZ0 168).
Definition srZ : list expr := Eval vm_compute in s_regs (fst (fst rZ)).
Definition knZ : list kentry := Eval vm_compute in kn_after rZ knZ0.

(* [comment removed for export] *)
Definition flag1 : list sentry := [SE (SA (ELit 0) 0xc9614) 1 (ELit 1)].
Definition flag0 : list sentry := [SE (SA (ELit 0) 0xc9614) 1 (ELit 0)].

(* [comment removed for export] *)
Lemma tgt_itinerary_ok :
  (s_pc (fst (fst rT00)), snd (fst rT00)) = (0x348cc%Z, []) /\ (s_pc (fst (fst rT10)), snd (fst rT10)) = (0x348cc%Z, [])
  /\ (s_pc (fst (fst rT01)), snd (fst rT01)) = (0x9dddc%Z, []) /\ (s_pc (fst (fst rT11)), snd (fst rT11)) = (0x9dddc%Z, [])
  /\ ksubl_b (kn_after rT00 (knTc 0 0 0 0)) knTe = true /\ ksubl_b (kn_after rT01 (knTc 0 0 1 67108857)) knTe = true
  /\ ksubl_b (kn_after rT10 (knTc 1 32767 0 0)) knTe = true /\ ksubl_b (kn_after rT11 (knTc 1 32767 1 67108857)) knTe = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0
  /\ ksubl_b knTe knLH1 = true /\ ksubl_b knV0 knLH1 = true /\ kn_after rV knV0 = knV0 /\ kn_after rU knU0 = knU0
  /\ relay_ok_b (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_b (sr_upd sr10 (ridx 21) (EVar 81)) = true
  /\ relay_ok_b srV = true /\ relay_ok_b srR = true /\ relay_ok_b (sr_upd srS_tk (ridx 21) (EVar 81)) = true
  /\ kn_vars_lt 82 knLH1 = true /\ sr_vars_lt 82 srTm0 = true
  /\ (s_pc (fst (fst rU)), snd (fst rU), s_log (fst (fst rU))) = (0xac48c%Z, [], [])
  /\ (s_pc (fst (fst rV)), snd (fst rV), s_log (fst (fst rV))) = (0x348cc%Z, [], [])
  /\ (s_pc (fst (fst rLB1)), snd (fst rLB1), s_log (fst (fst rLB1))) = (0x349e4%Z, [], flag1)
  /\ (s_pc (fst (fst rLB2)), snd (fst rLB2), s_log (fst (fst rLB2)), s_regs (fst (fst rLB2))) = (0x349e4%Z, [], flag1, srLB)
  /\ (s_pc (fst (fst rLc1)), snd (fst rLc1), s_log (fst (fst rLc1))) = (0x3499c%Z, [], flag0)
  /\ (s_pc (fst (fst rLc2)), snd (fst rLc2), s_log (fst (fst rLc2)), s_regs (fst (fst rLc2))) = (0x3499c%Z, [], flag0, srP0)
  /\ kn_after rLc1 knLr1 = knLp1 /\ kn_after rLc2 knLr2 = knLp2 /\ kn_after rLB1 knLH1 = knLc1 /\ kn_after rLB2 knLH2 = knLc2
  /\ knLr2 = knLc2 /\ ksubl_b knLp2 knLH2 = true /\ ksubl_b knLH2 knLp2 = true /\ ksubl_b knR (wposK (ELit 0xeb830) :: flagsK :: knR2) = true
  /\ keep_pf knLH2 = KRange (EVar 101) 0xeb830 0xeb836 :: knR2
  /\ kn_vars_lt 102 knLH2 = true /\ kn_vars_lt 81 knR2 = true
  /\ relay_ok_b (sr_after_call_j srP0 (map ridx callee_saved) 134) = true /\ ksubl_b knLH2 knX0 = true
  /\ keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2 = knX0
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0xa1a20%Z, [])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0xa0ffc%Z, [])
  /\ stdio_call 134 srQ knQ = Some scP /\ (sc_ret scP, sc_f scP, sc_fd scP, sc_wb scP, sc_wp scP, sc_s scP, sc_l scP)
                                           = (0xa1a44%Z, 0xb94a8%Z, 1%Z, ELit 0xeb830, ELit 0xeb831, ELit 0x10cf0, ELit 1)
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x348f0%Z, [])
  /\ (s_pc (fst (fst rS_tk)), snd (fst rS_tk), s_log (fst (fst rS_tk))) = (0x348cc%Z, [SCBr true BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rS_ft)), snd (fst rS_ft), s_log (fst (fst rS_ft))) = (0x9dc9c%Z, [SCBr false BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rX)), snd (fst rX), s_log (fst (fst rX))) = (0x346b8%Z, [], []) /\ nth 10 (s_regs (fst (fst rX))) (ELit 1) = ELit 0
  /\ (s_pc (fst (fst rY)), snd (fst rY), s_log (fst (fst rY))) = (0x9dc9c%Z, [], [])
  /\ (s_pc (fst (fst rZ)), snd (fst rZ), s_log (fst (fst rZ))) = (0x9bdf8%Z, [], []).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0DrvD_defs ()) ["FPX_1"] "p%0p%1p%2p&0p;1p;2p;3p;4p;<g0000k10;Tg000Pj2STg0010j11Tg001Uj10Tg002:j1yTg002Zj36Tg0034j1;Tg004Bj15Tg005Pj13Tg005oj18Tg006Mk40[Tg007[j3OTg008kj2zTg00:;j2<Tg00;Jk20ATg00<Zk406Tg00=jk305Tg00?:j2PTg00@Jj3JTg00AZj4?Tg00B:k30ETg00CJj37Tg00Cjk10`Tg00DLk40_Tg00EZj1RTg00F8m<0]Tg00GNk20DTg00H0k30\Tg00I>k400Tg00JPj24Tg00Jkj2_Tg00KEj3ETg00Kbj4~Tg00Lnj2WTg00N=k10ZTg00N[k30YTg00O>S00k10XTg00PJk309Tg00QXj1sTg00Rjk20>Tg00T6k20WTg00UBk10=Tg00VPk10VTg00W]k10UTg00Xlk10RTg00YOk40OTg00Ykk30NTg00[>k20CTg00\Gk40MTg00]Xk30PTg00^mk10QTg00`>k10LTg00aMk10STg00b]k10TTg00cmk10hTg00e=k10gTg00fLk10fTg00g[k40eTg00h7k10KTg00iDk30HTg00jRk40BTg00jmk10ITg00l9k30JTf0R0#0#0p=@%10#0#0p=t%10#1p=K%00#1p==%10#0#0#8p=\g00lVR1f2R2f1R3P0C?p=o%10#0p=D%10#1#1#0p=j%00#0#8#;p=U%00#Rp=ug00m4S01%;080H3p=d%00#0#0p=L%00#0#0#0p=B%00#0#0#8p=:%30#3#3p=|%30#3p>0?%30#3#3#3#3#3#3#3p=k%30#3#3#3p=pQ01@0H30p>02%10#0#0#1p=i%80#;p=C%00#8p=w%00#1#0#0p=v%10#8p>07g00m`R4%53;70p>0<%52%53=740574p=Qf3R5%53=7409742574p=[f4R6A743097429745574p=I%55A74309742574p=}%00#0#0#0#0#0#0#0p=T1<52?J30p=>%10#1#0#0p>0b1<52%80#;7J3p>08%10#0#0#0#8p=g%00#0#0#0#8p=Y%R2,<5?J30p=G%10#1#1p=n%10#1#1#1p=f%R0,<3p>0@%10#0#0#0p=m%;09J23p>0a%82,<5?J30p=V%80,<3p>0G%83/P0p>04%00#0#1#0p>03%03#0#8/P0p=c%13#0#0#0#8/P0p=bg00nnR7?730p=]A7730977297759776p=21P23=770p=lA77309772p=aAJ523=770p>0Ff5R8P6P1P5P2P3C?P0C?p=`%10#1#1#1#1#1#1#1p=r%00#0#1#1p=q%00#0#R,<3p>0^%00#0#1#1#0#0#1#1p={%R5,<6?J23=770p=9%05#R,<6?J23=770p=Xf6R9?J86AJ523=770577p>01%15#0#0#0#R,<6?J23=770p=HP2P4P3P0C?p=hP6P51_23P0H0Bp=AP9P8P6P5P2P3P0H0BH0Bp=Mg010>R:?E30p=FP1P5&0I2B0J:30C?p=eP9P8P1P6&0I5B0J:23C?&0K0C?p=ZP6P5P2P3C?=680p>0dA6523/40p>0:A6986A6523/40'4p=Ng011QR5g0121R9762A6539/40'4p=x20C23=659/40p=^A6539/40p>0cg012QR0$0;R3,S1R2g013cR8#1R6#0R;#1S02#@R<#tR=#0R>#KS03#0#=#\S04%y0R?5o3R@;6@S05Q05%08RA#0RB#1RC#1RD#1S06#0S07#1S08#1#DS09#j#K#\=o3?RE=62ES0:Q0:A6599RF&0;4RGg014HRH#;RI%=>#j#Ug014fR>#5RJ%0<R<#uS0;'dS0<%0BRK#0RL#1S0=#LS0>#@#B#US0?%0;RM#1RN#0RO#1S0@#1#BS0A#0S0B#DS0C#@#:S0D#;S0E%3>RP#3RQ#3RR#3RS#3S0F#|RT$0?S0G#3RU#5%3URU%3URU%3U#k#kRU#3RV#3RW#3RX#3RY#3RZ#3R[#3R\#|#kS0H$0?#p#k#kR]#3R^#3R_#3R`#3Ra#pRb#3Rc#5RdQ0H#5Re%5`R`+02%8;R;#;S0I+02RfPdPI%0DRD#1S0J#1S0K#1#D#KS0L#0#i#URgPIg015ES0MP>PP%5bH0[PIPI%16Rb#0R>#0Rh#1#CP`%8AS0N#;Ri-02eRj%0ORO#D#K#BS0O#DS0P#@S0Q#wRk#;S0R%3cRc#3S0S#5Rl%1ARA#1Rm#1S0T#0S0U#0Rn#DS0V#1S0W#1#B#v$07S0X#;RoPI%5US0Y%5VS0Z%5WS0[%5XS0\PY%y4RY-0<\9QZ[C[DIDIDIDIC}C[DIS0]Q0]36S0^&0;7R[Q0S#3RZ#3S0_#3S0`$0?S0a#3S0b#3S0c#|S0d#3S0e#5R\%0LS0f#0S0g#0S0h#0S0i#0RX#0S0j#@RW#8RV%BWRW#L#BRU#0Rp#B#T#T#:Rq3OS0k%8LRL,z\S0lPI%1>S0m#0S0n#KS0o#0S0p#0S0q#0R>#0S0r#DRr#0S0s#1Rs#0S0t#:S0uPS%88Rt#;RuC>S0vPI%K>#=S0w#=#:S0xPT%1=S0y#=#D$0bH08S0zPI%1rS0{#0Rr#gS0|PTPgC>S0}PI%gsS0~PT%YrS10#;C>S11PIPkPPPuC>RrPJ%uOPTPIC>ROPJ%0MS12#0Rs#0Rg#0S13PTPoCGRoPJ%0nS14PT%5aCGRaPJ%0mS15#0S16#0S17#0S18PTPdCGRnPJ%0AR=#1S19#0S1:#@S1;PTPfCGRfPJ%0=S1<#0R>#0Rv#0RwPTP`CGRxPJ%0DS1=#0S1>PTPeCGRDPJ%0CS1?#0S1@#0S1A#0S1BPTPjCGRjPJ%1KS1C#0S1D#0S1E#0S1FPT%1<RC#1#=#=#K#:S1G#;CGRy%1bRb#1S1H#nRz#n#fR{#8S1I9O`HR`%1{R{#K#fS1J#1R|#0R}#0$07S1K9OdHR~%5cS1L%8zRz7OHRc%5^R^?OHzS1M%5_S1N?OHzS1O%5]%n|R|#87O;S1P%f}#j#B#T#:9OeVS1Q1zeLS1R1<eHR}%8WRW+0AS1S20@JUR;%8pP}PWH06S1T1<IWQ02#1S02#m#T#:P}PWH06S1UPJ%LbS1VPTPICGS1WPJ%0hRh#0S1XPTPICGS1YPJP<PTPICGS1ZPJPgPTPICGS1[PJQ17PTQ0f#8R<,dJCGS17PJPvPT%=C#v#=#UCGS1\PJQ1APTPiCGS1]PJQ0gPT%8KRK#;RC-02JCGS1^PJPhPTQ0K#0S0K#1#j#D#K#UCGS1_1zJLS1`%B{#T#T#T#:R{=OJqS1a%8URU-0A;S1bPJPHPTPiC>S1cPJPKPT%5PC>S1dPJPLPT%5QC>S1ePJQ12#8RiPTPIC>S1f%5RRq%mp#T#T#:Rp7O{S1g%5SRb?O{pS1hP;PU1<qHRp%8wH06S1iP;PU1<bHPLH06S1j1zqKS1k1zbKS1l%86:0apTS1mPqPKPT%tX#BH08S1nPqPLPTPBH08S1oPqPiPT%8hRh#;C>S1pPqP<PT%CAS1qC>S1rPqP>PT%C=CVS1sPq%8sS1tPT%;LC>S1u1<qh@05CRS1vPqQ0gPTQ0ICVS0IPqQ1APT%;VS0gCVRVPqPvPT%CmCVRmPqPgPT%CMCVRMPqQ1XPTQ0T#CCVRgPqQ1VPTPICVRhPqQ0hPT%CNCVRLPqQ1FPTPbCVRbPqQ1BPTPICVRsPqQ1>PTPICVR=Q0V#L#T-0GI%tNS0V#L#B#:+0ARNQ0W#0R<#1S0W#1#D#BRi#wS0h,PWS1w%1iQ0X+04RiQ0O#0#i004kRkQ0Q$07RBQ0@#0#fRX#=#KRK#YS0@Q0r#=Rp$03%1p#=#:'cS0rPI%gKRKPT%;KC>S0QPI%1XRX#0RK#0#K#:PSQ0F#5RpC>S0F%iK%nXRX#Y'cS0OQ0B#0RK#=R6#YRU,bXS0BPIPUPTQ0q#1RU#DRX#0R;#@R{#gR]#;C>S0q%1K#D#:RK,b6S0X1<IK@05CQS1xQ0DQ0C#1RK#Y'PS0DQ0A#1#i#:,bKRKQ0s#@#:Q0uQ0t#\Q0~Q10Q0|Q0{#D#:Q0xQ0w#D#:%=URU#=R6#=#:Rz%16R6#YR_,PzS0w1<I_@05CQS0{%1URU#0Rz#@#:,b6S0t%1zRz#@#=%gzRz+04S0sPIPzPTPqC>S0A%1URU#0Rq#@%gq'cS0C%1U%Y{R{'bS1yPIP{PTQ0gC>S0g%n;#:R;,P]S1z1<I;@05CRS1{%1X#BQ0p#1RX#L#i#:'cS0p%nX#j#:S1|Q0m#m#T#:S0m'PQ1J#89Opt%y7']RpD2D2D2RX3l3l3l3l3l3aD2D2S0u3lD2D2D2D2D2D2D2D2D2D2D2D2D2RC']3aD2D2D2D2S0~Q0~36S10Q0kQ0lQ0vQ0zQ0}Q11PrPOPoPaPnPfPxPDPjPyQ0N,<ePPQ1LAJ}P^1<etPPQ1NPCH0F5acH0F9a`~D2D2D2D2S1NQ1N56[S1Lg015eRC$0;Re,S2R}P2PeP3Q19#1S0N#LS0l#D#v#=#\P?%yCR^E`RR;6RS0kP2PeP@P^C?S0|Q0|56}S0xP2PeQ0y#1R;#1S0y#t#\=o3?S1JQ0P#DS0P#wR],<IR{@0EPu=7C^C?RU=6}US1}1S}GRqP}PGPUPIQ03#1Rz#L#UQ0<Q0?Q0EQ0a#5Q0bQ0cPd%5ZS0cQ0cPdQ0dP\Q0e#3R\#5%3\R\%3\R\%3\R\Q0_#5S0_Q0`#5Q0RPlPI%f|S0`#1S0e#nS0d#1#f#rS0b#r#rR|#0#CS0aQ0YQ0ZQ0[Q0\%3\R\%3\R\%3\R\%3\R\00<Y3QC[DIDI3QC[C[C}C[DIC?S03Q0336S1~P2Pe%q;#\=o3?S20B0E{PI=7C^C?RC=6}CS21P}PGPC%3\R\#3S22%Dz#:S23#;S24Q0<Q0?Q0EQ22#3#pRz%3zRz%3zRzPdQ0cPIPI%3z#pRz#5S0<%3zRz#5S25%3zRz#5S26%3zRz#5S27%3zRz#5S28%3zRz#5S29Q0_PIQ0RPlPIQ0aQ0YQ0ZQ0[Q0\%|z#kRz%3zRz%3zRz%3zS2:;QY3QDIDIDIDIDI3QC[C}C?S2;Q2;56qS2<AJ{PIRzPrPOPoPaPnPfPxPDPjPyP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ1ZQ1[Q17Q1\Q1]Q1^Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0IPVPmPMPgPhPLPbPsP=PNQ1wPiPk1PB]S2=Q0rQ0QQ0FQ0OQ0BQ0qQ0XQ1xQ0D1]KXD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2S2>Q2>56[S2?%=<R<#1RX#0R]#1S2@#B-0GIS2A%5\R\7JTS2BQ0o#1RB#B#=#DR;#@S0o#wR6%K;#w5O\R\PI%=<R<#=S2C#:R;PSQ1qC>S2DPI%0]S2E#gS2FPT%tB#q#BH08S2GPI%1XRX#0S2H#YS2IPT%;6RBC>S2JPIQ0W#qR]#1S0W#:S2KPS%1|#CS2LC>S2MPI%1XS2N#YRXPT%1w#r#\S2O#;C>S2PPI%1<R<#gPTPIC>S2QPI%Y<R<PTPIC>S2RPI%0]R]#:R|PSQ2LC>S2LPrPOPoPaPnPfPxPDPjPyP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ1ZQ1[Q17Q1\Q1]Q1^Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0IPVPmPMPgPhPLPbPsP=PN1PW;S2SQ2C#1/c<S2CQ2E#@Q2F'cS2FQ2@Q2I'bS2IQ2H/bXS2HQ2N/b|S2N%1]Q2K'cS2KQ0W#1Q0h'cS0hPiPkQ2=Q0rQ0QQ0FQ0OQ0BQ0qQ0XQ1xQ0DPKQ0wQ0{Q0tQ0sQ0AQ0CQ1yQ0gQ1zQ1{Q0pQ1|/P6S1|/]p3aD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2R]3aD2D2R|,]zS0WQ0W56[S2@AJ{PuR{Q0vQ0zQ0}Q11PrPOPoPaPnPfPxPDPjPyP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ1ZQ1[Q17Q1\Q1]Q1^Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0IPVPmPMPgPhPLPbPsP=PNQ1wPiPkQ2=Q0P#1Q0@+04Q0uD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2S0uQ0u56[S0@1]{|R{=6[{R|Q2GQ2JQ2MQ2PQ2QQ2RQ2LPzP]D2D2R],]\RX=6[XS0PQ2BQ2D/]]7a\S2BQ2B56[S1w%1vS11#1S0}#vRv#v#:=o3?R]=62]S0zQ2O=o3?R<=62<S2Og0175RS$0`S0vP;Pt%mv#\S2EPBQ0o$07S0o#;S2TPBQ0j#CQ0=#i#KS0=#mS2U#0#CRvPu%m>S2V#u,dJS2WQ2:#3R>Q2E#;Q2WQ0?Q0E%3>#pS0EQ0E#3S0EQ0E#3S0E%;_S0?PuPuQ0E#pR_#5%3_R_%3_R_%3_R_%3_R_%3_R_%3_R_PvPuPIQ2U#1#CS2UPuPvPuPIPuPu%|_#kR_%3_R_%3_R_%3_00<Y3QC[DIDI3Q3Q3QDI3QC[C}Q2GQ2A?JTBQ2JQ2MQ2PPJQ11#0RY#0#uPTQ0MPQPHPTH0_S11C>PJ%0wS2M#@PT%;;S2JPJQ06#1PT%1Y#j#f#UPJQ08#LPTQ2UPJQ07#@S07#@PTQ2JPJQ0K#@PTPuPJQ0J#BPTQ0`#0#CPJQ1=PTQ0e#CPJQ1>#0S1>#@PTQ1?#1RY#CPJ%1YRwPTQ0}#1RQ#i#j#U1<I6PPQ1t#;R6Q0j-0@JPPP6PJ%0YRYPTPIPJQ1@#1R6#BPTPuPJ%@YRY#@PTPIPJ%BwPTQ0f#1#q$03#K#CPJP6PTPIPJQ1F#LPTPIQ1<#1S1<#LS1F#uR6,<JPTQ0i#RRw,dJQ1A#D-0^JPTQ0d#q#{#{#{#=#CPJQ1B#0S1B#@PTQ0b#0#r#r#CPJQ1EPTQ0V#K#{#{#UPJQ1C#1RP#0S1C#@S0V#0R_PT%mY#i#CPJQ13#0S13PTQ11PJQ1D#1S1D#BPTQ0?PJQ1DPTPIPJQ1CPT1dJ6PJ%1PRPPT%R_,dJPJ%BPPTQ12#t#uRP,dJPJQ0T#1R_PTQ0\PJ%L_S0\PTQ0[PJQ0UPTQ0ZPJQ14#0S14PTQ0YPJQ15#1R_PTQ0aPJ%L_R_PTPIPJQ16PTQ1qPJQ18#0S18PTPIPJQ0NPTPuPJQ0lPTQ0?PJQ1:PTQ0=#0#j#CPJQ1;#0R6PTQ2JPJQ1<PT&03Q$03#UQ2QQ2RQ2LQ2DPJQ14PTPIPJQ0\PTPIPJQ13PTPI1<JPPTPI20@J_PTPIPJQ2VPTQ0>#RR_,dJRPPJQ18PTQ11PJQ0lPTPlPJP6PTQ0RPJQ1FPTPIPJQ2MPTQ0_PJQ07PTQ0cPJQ1>PTPdPJPYPTQ0y#=#D#UPJQ1BPTPPPJQ1VPTQ26PJQ1H#LPTQ251<JwPTQ0<1<J_PTPIPJQ02#LPTQ29PJQ1XPTQ28PJQ0n#@PTQ27PJQ0VPTQ24PzPrPOPoPaPnPfPxPDPjPyP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ1ZQ1[Q17Q1\Q1]Q1^Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0IPVPmPMPgPhPLPbPsP=PNQ2SQ2CQ2FQ2IQ2HQ2NQ2KQ0hPiPkQ2=Q0rQ0QQ0FQ0OQ0BQ0qQ0XQ1xQ0DPKQ0wQ0{Q0tQ0sQ0AQ0CQ1yQ0gQ1zQ1{Q0pQ1|Q0oQ0m;lpD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D9D9DXD9K01D9DXD9D9D9D9D9D9D9D9D9D9K01D9D9D9D2DHDXDHDXDHDXDHDXDHDXDHDXDHD9DHDHDHD9DXDXDHD9K01D9DHD9D9D9DHK01DHD9DHD9D9D9D9DHD93aD2N<0]-0DSRp;6pS2P1S11RK/S1Rk/S4Ri/S4RN/S4R=/S4RsPKP1P1P1Q2EP;C?PtC?=hkBQ2T5hi=hNv=h=uRv;6vS2TQ23=o3?R;=62;S23P2PeP3Q04P9g018KRbQ01%R8#;80\lR8PIH00=70?P^E`RL=6}LS01P2PeP3Q09#=#q#\RhQ0MPbP8PIH00=70?P^E`R8=6}8S09P2PeP3Q1GP?P^E`Rg=6}gS1GA64IIS2EP2PeP3PhP?P^E`RM=6}MS0oP2PeP3Q0L#f#:P?P^E`Rm=6}mS0L'4S0m'4S1|'4S0p'4S1{'4S1z'4S0g'4S1y'4S0C'4S0A'4S0s'4S0t,4FS0{,4FS0w,4FS0D,4FS1x'4S0X,4FS0q,4FS0B,4FS0O,4|S0F'4S0Q'4S0r'4S2='4S0h'4S2K'4RV'4Rc'4R~'4R`'4Ry,4FRj,4FRD,4FRx,4FRf,4FRn,4FRa,4FRo'4RO'4Rr,4FRz,4FRT'4RJ,4FR_,4FRw,4FRP'4RY'4Rd'4R6'41_2@RQQ05P6PQQ0:Pd1_2ERdQ0:PYPdPFPP1_59R5PFPwP5PFP_P5PFPJP5Q0^PTPGQ0]PFPzP5PFPrP5Q10POP[Q0~Q1LPoP[Q1NPFPaP5PFPnP5PFPfP5PFPxP5PFPDP5PFPjP5PFPyP5Q0kP`1_}RQ0xP~P}Q0|Q1}PcP}PUQ1~PVPqQ03Q21Q2KP}PCQ2<Q0hPqQ2;Q2?Q2=P[Q2>Q2@Q0rP[Q0WQ0@Q0QP[Q0uP|Q0F1_[{R{P|Q0OP{PFQ0BP5PFQ0qP5PFQ0XP5Q0PQ1x1_[XPFQ0DP5PFQ0wP5PFQ0{P5PFQ0tP5Q1wQ0sP[Q2BQ0zQ0AP2P]Q2OQ0CP2P<Q2PQ1yQ0vPpQ2TQ0gPsPvQ23Q1zP2P;Q01Q1{P}PLQ09Q0pP}P8Q1GQ1|P}PgQ2EQ0mP4PIQ0oQ0LP}PM1_}mDADADADADADADADADADADAFMFMFMFMFMDADADADADADADADAFMFMFMFMDADAFMDAFMFMFMFMP2P31S:3R:g019=R8g01:NRL3ERp,F3P3PpCeP@P2P3g01;ZRp9E:8R5,F3P3P5CeP@P2P3g01<fR@9E:8R5,F3P3P5CePEP2P3g01>2R59E:8RF,F3P3PFCePEPHPHPHPHC~,WLg01?>RLPHPHPtQ1KC~,W@PtQ1IPHPHC~,WpPtQ1IPtQ1KC~,W5PGg01@J&0ZARAQ19#8g01AV40Y$0XR5<09lg01B2Rtg01C?Rpg01DLRHP[g01EXR@/WHPHP[g01FbRHg01GlRE'WPEg01I8@095l#sg01JD@095l#sg01KP#sg01L[#sg01Mf@095l#s20>Zp20WZtP}P2PeP3AE:8HRH,F3RtP3PHPtFZPRP}P2PeP3AE:8@R@,F3RRP3P@PRFZQ0|P}P2PeP3g01O4RR9E:8R@,F3RtP3P@PtFZP2PeQ1Jg01P@C?RtPqP}PGP2PeP3g01QMR@9E:8RH,F3RZP3PHPZFZ&0=ZC?P}PGPtg01RYC?P}P2PeP3g01SeRt9E:8RZ,F3RHP3PZPHFZP2PeQ20g01U1C?RHPqP}PGP2PeP3g01V>Rq9E:8RZ,F3R5P3PZP5FZ&0=5C?P}PGPHg01WJRHC?P[g01XV,Wtg01YcP[g01[0Rt,Wqg01\=RqP[1WRpg01]JP[g01^WRR,W@g01_dR@P[PtP@g01a1&0VBg01b<g01cJRB577']P[&0URA77\BQ2200>RQ0S00>B&0RAg01dVRAQ00g01e5H0O>0NH>#sg01fIRH-0CRP[Q0;1SA1R[PAP1Q0HPWC?%y[R[37P[PRH0MPHP2P3g01gU9E:8RH,F3P3PHCeP]P2P3g01h_9E:8R],F3P3P]CeP<Q0vg01iig01k460P>g01l?R>-0DSPsPKP1P1P1&0Q>&0L>C?&0S>C?&0T>5hk&0h>5hi&0g>5hN&0f>5h=PvP2P3g01mJ9E:8Rv,F3P3PvCeP;P}P2PeP3g01nT9E:8R;,F3RvP3P;PvFZP2PeP3Q04P9Pbg01oaR9PIH00=70?P^E`P}P2PeP3g020n9E:8Rv,F3R;P3PvP;FZP2PeP3PhQ0MPbP9PIH00=70?P^E`P}P2PeP3g022;9E:8R^,F3R?P3P^P?FZPgP4P4Q0G&0=?PuH0ePIP}P2PeP3g023E9E:8RI,F3RuP3PIPuFZPMP}P2PeP3g024O9E:8R8,F3R:P3P8Ce&0K:PmJ0dH0:FNFNFNFNFN3x3xH0:3^9^Rq9^qRH0:FNFNFNFNFN+0c3x3x3xFN7^p5^LH0:7^L7^L7^L3^FNFNdo"). Qed.

End FPX_1.
