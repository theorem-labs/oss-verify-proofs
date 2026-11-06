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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Eu0MainEntry Eu0LibStdioCall
  HeapIface DrvKit Eu0Drv_defs Eu0DrvG_defs Eu0DrvC_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0DrvD_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib4Init9Datatypes4prod01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry01C13~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knTcC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs8kn_afterC13~~~K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sr_updC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs:relay_ok_bC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_regsC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5wposKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs7keep_pfC13~~~I45stdpp9bitvector;definitions2bv00C47Corelib5Lists7ListDef3mapC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymDrive?sr_after_call_jC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6DrvKit7ksubl_bC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs:keep_allocC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_lC13~~~C47Corelib5Lists7ListDef3nthC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K47Corelib4Init5Logic3and01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes3nat01K47Corelib4Init9Datatypes4bool02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rT00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rT10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rT01C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rT11C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knTeC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4sr01C13~~~K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5srTm0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLH1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knV0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rVC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knU0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4sr00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4sr10C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3srVC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3srRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs6srS_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rLB1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5flag1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rLB2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4srLBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rLc1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5flag0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4rLc2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4srP0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLr1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLp1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLr2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLp2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLc1C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLH2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5knLc2C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3knRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs6flagsKC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knR2C13~~~I47Corelib4Init9Datatypes3nat00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<RefMemcpyLib<callee_savedC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs4knX0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3srQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3knQC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs3scPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5rS_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5dec_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs5rS_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rYC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvD_defs2rZC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_T : list Z := (0x34dd4 :: 0x34bc0 :: STOPS)%Z.
Definition runT (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_T scr ss [].
(* [comment removed for export] *)
Definition STOPS_P : list Z := [0x9d974; 0xa2b78; 0x9f958; 0x9f818; 0x34eec]%Z.
Definition STOPS_R : list Z := (0x34df8 :: STOPS_P)%Z.
Definition runP (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_P scr ss [].
Definition runR (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_R scr ss [].

(* [comment removed for export] *)
Definition knTc (clo chi plo phi : Z) : list kentry := KRange (EVar 73) clo chi :: KRange (EVar 79) plo phi :: knT0.
Definition rT00 := Eval vm_compute in runT scr0 (SS 0x34d1c srT0 [] (knTc 0 0 0 0) 81).
Definition rT01 := Eval vm_compute in runT scr0 (SS 0x34d1c srT0 [] (knTc 0 0 1 67108857) 81).
Definition rT10 := Eval vm_compute in runT scr0 (SS 0x34d1c srT0 [] (knTc 1 32767 0 0) 81).
Definition rT11 := Eval vm_compute in runT scr0 (SS 0x34d1c srT0 [] (knTc 1 32767 1 67108857) 81).
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
Definition rU := Eval vm_compute in runT scr0 (SS 0x34d80 srU0 [] knU0 114).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
(* [comment removed for export] *)
Definition srV0 : list expr := Eval vm_compute in sr_after_call_j srU (map ridx callee_kept) 114.
Definition knV0 : list kentry := Eval vm_compute in keep_rd knU0.
Definition rV := Eval vm_compute in runT scr0 (SS 0x34d94 srV0 [] knV0 146).
Definition srV : list expr := Eval vm_compute in s_regs (fst (fst rV)).

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
(* [comment removed for export] *)
Definition srLH : list expr :=
  [ELit 0; EVar 85; spx (-208); ELit 67584; ELit 838592; EVar 86; EVar 87; EVar 88;
   EVar 79; EVar 82; EVar 89; EVar 90; EVar 91; EVar 92; EVar 93; EVar 94; EVar 95; EVar 96;
   EVar 83; EVar 84; ELit 831888; EVar 81; ELit 0; ELit 18446744073709551614; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 97; EVar 98; EVar 99; EVar 100].
(* [comment removed for export] *)
Definition knLH1 : list kentry := Eval vm_compute in keep_rd knTk.
(* [comment removed for export] *)
Definition shared_pos : list nat := [2; 3; 4; 8; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition relay_ok_b (sr : list expr) : bool :=
  forallb (fun i => expr_eqb (nth i sr (ELit 0)) (nth i srLH (ELit 0)) && expr_vars_lt 82 (nth i sr (ELit 0))) shared_pos.
(* [comment removed for export] *)
Definition IMG_LIB : list (Z * Z) := [(0x10000, 0xcb1b0); (0xcc338, 0xccae8); (0xccaf0, 0xccb1c); (0xccb20, 0xecc08); (0xece28, 0xecfc8); (0xed370, 0xee000)]%Z.
Definition keep_lib (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 65536 bls vbnd [3%nat; 4%nat] IMG_LIB IMG_RW kn.

(* [comment removed for export] *)
Definition rLB1 := Eval vm_compute in runT scr0 (SS 0x34dd4 srLH [] knLH1 102).
Definition srLB : list expr := Eval vm_compute in s_regs (fst (fst rLB1)).
Definition knLc1 : list kentry := Eval vm_compute in kn_after rLB1 knLH1.
(* [comment removed for export] *)
Definition srLr0 : list expr := Eval vm_compute in sr_upd (sr_after_call_j srLB (map ridx c_kept) 102) (ridx 10) (ELit 0).
Definition knLr1 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc1.
(* [comment removed for export] *)
Definition rLc1 := Eval vm_compute in runT scr0 (SS 0x34de8 srLr0 [] knLr1 134).
Definition srP0 : list expr := Eval vm_compute in s_regs (fst (fst rLc1)).
Definition knLp1 : list kentry := Eval vm_compute in kn_after rLc1 knLr1.
(* [comment removed for export] *)
Definition rP := Eval vm_compute in runP scr0 (SS 0x34ea4 srP0 [] knLp1 134).
Definition srP : list expr := Eval vm_compute in s_regs (fst (fst rP)).
Definition knP : list kentry := Eval vm_compute in kn_after rP knLp1.
(* [comment removed for export] *)
Definition srQ0 : list expr := Eval vm_compute in sr_upd srP (ridx 10) (ELit 18446744073709551591).
Definition rQ := Eval vm_compute in runP scr0 (SS 0xa35a0 srQ0 [] knP 134).
Definition srQ : list expr := Eval vm_compute in s_regs (fst (fst rQ)).
Definition knQ : list kentry := Eval vm_compute in kn_after rQ knP.
Definition scP : stdio_res := Eval vm_compute in the_sc (stdio_call 134 srQ knQ).
Definition srR0 : list expr := Eval vm_compute in sc_sr scP.
Definition knR0 : list kentry := Eval vm_compute in sc_kn scP.
Definition rR := Eval vm_compute in runR scr0 (SS (sc_ret scP) srR0 [] knR0 166).
Definition srR : list expr := Eval vm_compute in s_regs (fst (fst rR)).
Definition knR : list kentry := Eval vm_compute in kn_after rR knR0.

(* [comment removed for export] *)
Definition IMG_PF : list (Z * Z) := [(0x10000, 0xbb028); (0xbb02c, 0xbb050); (0xbb058, 0xcb1b0); (0xccaf0, 0xccb1c); (0xccb20, 0xecfc8); (0xed370, 0xed3b0); (0xed7b0, 0xee000)]%Z.
Definition keep_pf (kn : list kentry) : list kentry := kn_keep 0 (-208) 1056 [(48%nat, 65536%Z)] [] [3%nat; 4%nat] IMG_PF IMG_RW kn.
Definition wposK (e : expr) : kentry := KWord (SA (ELit 0) 0xbb050) 8 e.
Definition flagsK : kentry := KWord (SA (ELit 0) 0xbb028) 4 (ELit 5).
(* [comment removed for export] *)
Definition knR2 : list kentry := Eval vm_compute in keep_pf (keep_lib (-208) [(48%nat, 65536%Z)] [] knR).
Definition knLH2 : list kentry := wposK (EVar 101) :: KRange (EVar 101) 0xed3b0 0xed3b6 :: flagsK :: knR2.

(* [comment removed for export] *)
Definition rLB2 := Eval vm_compute in runT scr0 (SS 0x34dd4 srLH [] knLH2 102).
Definition knLc2 : list kentry := Eval vm_compute in kn_after rLB2 knLH2.
Definition knLr2 : list kentry := Eval vm_compute in keep_lib (-208) [(48%nat, 65536%Z)] [] knLc2.
Definition rLc2 := Eval vm_compute in runT scr0 (SS 0x34de8 srLr0 [] knLr2 134).
Definition knLp2 : list kentry := Eval vm_compute in kn_after rLc2 knLr2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srS0 : list expr := sr_upd srLH (ridx 19) (ELit 0).
Definition rS_tk := Eval vm_compute in runT (SCR [true] [] []) (SS 0x34df8 srS0 [] knLH2 102).
Definition rS_ft := Eval vm_compute in runT (SCR [false] [] []) (SS 0x34df8 srS0 [] knLH2 102).
Definition srS_tk : list expr := Eval vm_compute in s_regs (fst (fst rS_tk)).
Definition srS_ft : list expr := Eval vm_compute in s_regs (fst (fst rS_ft)).
Definition dec_x : expr := EAluw ALU_ADD (EVar 81) (ELit (-1)).

(* [comment removed for export] *)
Definition srX0 : list expr := Eval vm_compute in sr_after_call_j srS_ft (map ridx c_kept) 102.
Definition knX0 : list kentry := Eval vm_compute in keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2.
Definition rX := Eval vm_compute in runT scr0 (SS 0x34e14 srX0 [] knX0 134).
Definition srX : list expr := Eval vm_compute in s_regs (fst (fst rX)).
(* [comment removed for export] *)
Definition srY0 : list expr :=
  Eval vm_compute in sr_upd (sr_upd (sr_upd (sr_upd srX (ridx 8) (ELit 0)) (ridx 10) (ELit 0)) (ridx 1) (EVar 134)) (ridx 11) (EVar 135).
Definition rY := Eval vm_compute in runT scr0 (SS 0x34c40 srY0 [] knX0 136).
Definition srY : list expr := Eval vm_compute in s_regs (fst (fst rY)).
(* [comment removed for export] *)
Definition srZ0 : list expr := Eval vm_compute in sr_after_call_j srY (map ridx c_kept) 136.
Definition knZ0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knX0.
Definition rZ := Eval vm_compute in runT scr0 (SS 0x34c48 srZ0 [] knZ0 168).
Definition srZ : list expr := Eval vm_compute in s_regs (fst (fst rZ)).
Definition knZ : list kentry := Eval vm_compute in kn_after rZ knZ0.

(* [comment removed for export] *)
Definition flag1 : list sentry := [SE (SA (ELit 0) 0xcb194) 1 (ELit 1)].
Definition flag0 : list sentry := [SE (SA (ELit 0) 0xcb194) 1 (ELit 0)].

(* [comment removed for export] *)
Lemma tgt_itinerary_ok :
  (s_pc (fst (fst rT00)), snd (fst rT00)) = (0x34dd4%Z, []) /\ (s_pc (fst (fst rT10)), snd (fst rT10)) = (0x34dd4%Z, [])
  /\ (s_pc (fst (fst rT01)), snd (fst rT01)) = (0x9f958%Z, []) /\ (s_pc (fst (fst rT11)), snd (fst rT11)) = (0x9f958%Z, [])
  /\ ksubl_b (kn_after rT00 (knTc 0 0 0 0)) knTe = true /\ ksubl_b (kn_after rT01 (knTc 0 0 1 67108857)) knTe = true
  /\ ksubl_b (kn_after rT10 (knTc 1 32767 0 0)) knTe = true /\ ksubl_b (kn_after rT11 (knTc 1 32767 1 67108857)) knTe = true
  /\ sr_upd sr01 (ridx 21) (EVar 81) = srTm0
  /\ ksubl_b knTe knLH1 = true /\ ksubl_b knV0 knLH1 = true /\ kn_after rV knV0 = knV0 /\ kn_after rU knU0 = knU0
  /\ relay_ok_b (sr_upd sr00 (ridx 21) (EVar 81)) = true /\ relay_ok_b (sr_upd sr10 (ridx 21) (EVar 81)) = true
  /\ relay_ok_b srV = true /\ relay_ok_b srR = true /\ relay_ok_b (sr_upd srS_tk (ridx 21) (EVar 81)) = true
  /\ kn_vars_lt 82 knLH1 = true /\ sr_vars_lt 82 srTm0 = true
  /\ (s_pc (fst (fst rU)), snd (fst rU), s_log (fst (fst rU))) = (0xae008%Z, [], [])
  /\ (s_pc (fst (fst rV)), snd (fst rV), s_log (fst (fst rV))) = (0x34dd4%Z, [], [])
  /\ (s_pc (fst (fst rLB1)), snd (fst rLB1), s_log (fst (fst rLB1))) = (0x34eec%Z, [], flag1)
  /\ (s_pc (fst (fst rLB2)), snd (fst rLB2), s_log (fst (fst rLB2)), s_regs (fst (fst rLB2))) = (0x34eec%Z, [], flag1, srLB)
  /\ (s_pc (fst (fst rLc1)), snd (fst rLc1), s_log (fst (fst rLc1))) = (0x34ea4%Z, [], flag0)
  /\ (s_pc (fst (fst rLc2)), snd (fst rLc2), s_log (fst (fst rLc2)), s_regs (fst (fst rLc2))) = (0x34ea4%Z, [], flag0, srP0)
  /\ kn_after rLc1 knLr1 = knLp1 /\ kn_after rLc2 knLr2 = knLp2 /\ kn_after rLB1 knLH1 = knLc1 /\ kn_after rLB2 knLH2 = knLc2
  /\ knLr2 = knLc2 /\ ksubl_b knLp2 knLH2 = true /\ ksubl_b knLH2 knLp2 = true /\ ksubl_b knR (wposK (ELit 0xed3b0) :: flagsK :: knR2) = true
  /\ keep_pf knLH2 = KRange (EVar 101) 0xed3b0 0xed3b6 :: knR2
  /\ kn_vars_lt 102 knLH2 = true /\ kn_vars_lt 81 knR2 = true
  /\ relay_ok_b (sr_after_call_j srP0 (map ridx callee_saved) 134) = true /\ ksubl_b knLH2 knX0 = true
  /\ keep_alloc (-208) [(48%nat, 65536%Z)] [] knLH2 = knX0
  /\ (s_pc (fst (fst rP)), snd (fst rP)) = (0xa359c%Z, [])
  /\ (s_pc (fst (fst rQ)), snd (fst rQ)) = (0xa2b78%Z, [])
  /\ stdio_call 134 srQ knQ = Some scP /\ (sc_ret scP, sc_f scP, sc_fd scP, sc_wb scP, sc_wp scP, sc_s scP, sc_l scP)
                                           = (0xa35c0%Z, 0xbb028%Z, 1%Z, ELit 0xed3b0, ELit 0xed3b1, ELit 0x10cf0, ELit 1)
  /\ (s_pc (fst (fst rR)), snd (fst rR)) = (0x34df8%Z, [])
  /\ (s_pc (fst (fst rS_tk)), snd (fst rS_tk), s_log (fst (fst rS_tk))) = (0x34dd4%Z, [SCBr true BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rS_ft)), snd (fst rS_ft), s_log (fst (fst rS_ft))) = (0x9f818%Z, [SCBr false BC_NE dec_x (ELit 0)], [])
  /\ (s_pc (fst (fst rX)), snd (fst rX), s_log (fst (fst rX))) = (0x34bc0%Z, [], []) /\ nth 10 (s_regs (fst (fst rX))) (ELit 1) = ELit 0
  /\ (s_pc (fst (fst rY)), snd (fst rY), s_log (fst (fst rY))) = (0x9f818%Z, [], [])
  /\ (s_pc (fst (fst rZ)), snd (fst rZ), s_log (fst (fst rZ))) = (0x9d974%Z, [], []).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0DrvD_defs ()) ["FPX_1"] "p%0p%1p%2p&0p;1p;2p;3p;4p;<g0000k108Tg000Pj2UTg0010j11Tg001Uj10Tg002:j1sTg002Zj36Tg0034j1=Tg004Bj15Tg005Pj1PTg005nj13Tg006Mj18Tg006kk40\Tg0089j3NTg009Ij2xTg00:Yj2>Tg00;hk20@Tg00=8k405Tg00>Hk303Tg00?Xj2QTg00@hj3ITg00B8j4@Tg00BXk30ETg00Chj37Tg00DHk10aTg00Djk40`Tg00F8m<0^Tg00GNk20DTg00H0k30]Tg00I>j4{Tg00JPj24Tg00Jkj2eTg00KEj3ETg00Kbj4zTg00Lnj2YTg00N=k10[Tg00N[k30ZTg00O>S00k10YTg00PJk301Tg00QXj1rTg00Rjk20=Tg00T6k20XTg00UBk10;Tg00VPk10WTg00W]k10VTg00Xlk10UTg00YOk40RTg00Ykk30OTg00[>k20CTg00\Gk40NTg00]Xk30MTg00^mk10PTg00`>k10QTg00aMk10LTg00b]k10STg00cmk10TTg00e=k10gTg00fLk10fTg00g[k40eTg00h7k10KTg00iDk30ITg00jRk40BTg00jmk10HTg00l9k30JTf0R0#0#0p=<%00#1#1p>0A%10#0p=;%00#8p=Vg00lVR1f2R2f1R3P0C@p=n%10#1p=K%10#0#0p=X%00#0#0#8p=9%00#0#0#0p=C%00#0#8#=p=Tg00m4S01%=080I3p=h%00#0#0p=J%10#0#0#1p=a%00#1p=D%30#3#3p=u%30#3p>0>%30#3#3#3#3#3#3#3p=k%30#3#3#3p=pQ01@0I30p=}%10#0#0#0p=^%80#=p=B%10#1#0#0p=y%00#1#0#0p>0<%10#8p>06g00m`R4%53;70p>0:%52%53=740574p=Rf3R5%53=7409742574p=]f4R6A743097429745574p=H%55A74309742574p>09%00#0#0#0#0#0#0#0p=Z1>52?I30p=?1>52%80#=7I3p>07%10#0#0#0#8p=i%00#0#0#0#8p=[%00#Pp=v%P2,>5?I30p=G%10#1#1p=q%10#1#1#1p=c%10#1#1#0p=o%P0,>3p>0?%00#0#1#1p>04%=09I23p>0b%82,>5?I30p=S%80,>3p>0G%83/Q0p>02%13#0#0#0#8/Q0p=`%03#0#8/Q0p=mg00nnR7?730p=bA7730977297759776p=21Q23=770p=lA77309772p=gAI523=770p>0Ff5R8P6P1P5P2P3C@P0C@p=f%10#1#1#1#1#1#1#1p=t%00#0#P,>3p>0_%00#0#1#1#0#0#1#1p>00%P5,>6?I23=770p=:%05#P,>6?I23=770p=Wf6R9?I86AI523=770577p=~%15#0#0#0#P,>6?I23=770p=MP2P4P3P0C@p=jP6P51e23P0H0Bp=AP9P8P6P5P2P3P0H0BH0Bp=Lg010>R:?E30p=FP1P5&0H2B0J:30C@p=dP9P8P1P6&0H5B0J:23C@&0K0C@p=\P6P5P2P3C@=680p>0dA6523/40p=|A6986A6523/40'4p=Og011QR5g0121R9762A6539/40'4p=w20C23=659/40p=_A6539/40p>0cg012QR0$08R3,U1R2g013cR8#1R6#0R;#1S02#<R<#1R=#1R>$0AR?#1S03#0#;#;#VS04%s0R@5n3RA;6AS05Q05%08RB#0RC#1RD#1RE#1RF#KS06#XS07#;#;#K#9=n3@RG=62GS08Q08A6599RH&084RIg014HRJ#=RK%0?#C#Tg014fR?#5RL%0<S09#0S0:#PS0;'hS0<%0CR<#0RM#1S0=#JS0>#<#C#TS0?%0;RN#1RO#aS0@#DS0A#1S0B#1S0C#;S0D#<#9S0E#=S0F%3?RP#3RQ#3RR#3RS#3S0G#uRT$0>S0H#3RU#5%3URU%3URU%3U#k#kRU#3RV#3RW#3RX#3RY#3RZ#3R[#3R\#u#kS0I$0>#p#k#kR]#3R^#3R_#3R`#3Ra#pRb#3Rc#5RdQ0I#5Re%5`R`'}%8;R;#=S0J'}RfPdPK%0FS0K#1RF#X#;S0L#0#^#TRgPKg015ES0MP?PP%5bH0\PKPK%16Rb#0R?#0Rh#1#BP`%8BS0N#=Ri,}eRj%0ORk#1#^#yS0O#;S0P#<S0Q#VRl#=S0R%3cRc#3S0S#5Rm%1BRB#1Rn#1S0T#0Ro#1S0U#^S0V#1S0W#X$0<$06S0X#=RpPK%5US0Y%5VS0Z%5WS0[%5XS0\PY%s4RY-0:\9RZ[C]DHDHDHDHH09C]DHS0]Q0]36S0^&087R[Q0S#3RZ#3S0_#3S0`$0>S0a#3S0b#3S0c#uS0d#3S0e#5R\%0MS0f#0S0g#0S0h#0S0i#0RX#0S0j#<RW#8RV%CWRW#J#CRU#0Rq#C#Z#Z#9Rr3NS0k%8MRM,x\S0lPK%1?S0m#1S0n#0S0o#DS0p#1S0q#0R?#JRs#0S0r#1Rt#0S0s#9S0tPS%88Ru#=RvC?S0uPK%a?S0v#D#9S0wPT%;>S0x#D#K$0<H07S0yPK%1sS0z#0Rs#iS0{PTPgC?S0|PK%itS0}PT%[sS0~#=C?S10PKPlPPPvC?RsPL%0k#vPTPKC?RkPL%0NS11#0Rt#0Rg#0S12PTPpCGRpPL%<oS13PT%5aCGRaPL%0nS14#0S15#0S16#0S17PTPdCGRoPL%0BR>#1S18#0S19#<S1:PTPfCGRfPL%0>S1;#0R?#0Rw#0RxPTP`CGRyPL%0ES1<#0S1=#0S1>PTPeCGREPL%0DS1?#0S1@#0S1A#0S1BPTPjCGRjPL%1<S1C#0S1D#0S1E#0S1FPT%D=R=#K#^#9S1G#=CGRD%1bRb#1S1H#qRz#q#cR{#8S1I9N`JR`%1{R{#K#cS1J#1R|#0R}#0$06S1K9NdJR~%5cS1L%8zRz7NJRc%5^R^?NJzS1M%5_S1N?NJzS1O%5]%q|R|#87N;S1P%c}#o#C#Z#99NeVS1Q1xeMS1R1>eJR}%8WRW+0@S1S20?LUR;%8qP}PWH05S1T1>KWQ02#1S02#a#;#K#D#;#9P}PWH05S1UPL%JbS1VPTPKCGS1WPL%0hRh#0S1XPTPKCGS1YPLQ09PTPKCGS09PLPgPTPKCGS1ZPLQ16PTQ0f#8Rb,hLCGS16PLPwPT%0=#D$04#TCGS1[PLQ1APTPiCGS1\PLQ0gPT%8<R<#=R=,}LCGS1]PLPhPT%<FS1^#y#;#;#TCGS1_1xLMS1`%C{#Z#Z#Z#9R{=NLrS1a%8URU-0@;S1bPLPJPTPiC?S1cPLP<PT%5PC?S1dPLPMPT%5QC?S1ePLQ11#8RiPTPKC?S1f%5RRr%^q#Z#Z#9Rq7N{S1g%5SRF?N{qS1hP;PU1>rJRq%8xH05S1iP;PU1>FJPMH05S1j1xr<S1k1xF<S1l%86:0bqTS1mPrP<PT%XX#CH07S1nPrPMPTPCH07S1oPrPiPT%8hRh#=C?S1pPrPbPT%BBS1qC?S1rPrP?PT%B>CSS1sPr%8tS1tPT%=MC?S1u1>rh@03=RS1vPrQ0gPTQ0JCSS0JPrQ1APT%=VRVCSS0gPrPwPT%BnCSRnPrPgPT%BNCSRNPrQ1XPTQ0T#BCSRgPrQ1VPTPKCSRhPrQ0hPT%BOCSROPrQ1FPTPFCSRFPrQ1BPTPKCSRMPrQ1>PTPKCSRtQ0U#JS0U#<#Z-0GKQ0:#J#C#9+0@R>Q0W#0#;#CRb#VS0W,QWS0:%1bQ0X+02RbQ0O#0#a002lRlQ0Q$06RiQ0A#0#cRC#[S0AQ0p#0#cRX#<%1X#D#9'`S0pPK%iCRCPT%=CC?S0QPKQ0B#0RC#0RX$0A#9PSQ0G#5R<C?S0G%aX%qCRC#['mS0BQ0C#0RX#DRq#[R6,`CS0CPKP6PTQ0q#1R6#0RC#1RU#0R;#<R{#iR]#=C?S0q%1X#;#9RX,`qS0O1>KX@03=QS0XQ0EQ0D#1RX#['QS0EQ0@#XS0@#0#a#9,`XRXQ0r#<#9Q0tQ0s#;#VQ0}Q0~Q0{Q0z#;#9Q0wQ0v#;#9%0CRC#DRq#D#9Rz%1qRq#[R_,QzS0v1>K_@03=QS0z%1CRC#0Rz#<#9,`qS0s%1zRz#<#D%izRz+02S0rPKPzPTPrC?S0D%1CRC#0Rr#<%ir'mS0h%1C%[{R{'`S1wPKP{PTPVC?S1x%q;#9R;,Q]S1y1>K;@03=RS1z%1U#C%K6#a#9'mS1{Q0o#;R6$0ARU#0#o#9S0oQ0n#X#Z#9S0n'QQ1J#89N<u%s7'bR<D2D2D2R=3l3l3l3l3l3gD2D2S0t3lD2D2D2D2D2D2D2D2D2D2D2D2D2RR'b3gD2D2D2D2S0}Q0}36S0~Q0kQ0lQ0uQ0yQ0|Q10PsPkPpPaPoPfPyPEPjPDQ0N,>ePPQ1LAI}P^1>euPPQ1NPRH0F5gcH0F9g`~D2D2D2D2S1NQ1N56[S1Lg015eRR$08Re,U2R}P2PeP3Q18#1S0N#^S0l#0#C#D#9P@%sRR^EfR;;6;S0kP2PePAP^C@S0{Q0{56}S0wP2PeQ0x#1R]#1#;S0x#1#;#V=n3@S1JQ0P#;S0P#VRV,>KR{@0EPv=7R^C@RC=6}CS1|1U}IRrP}PIPCPKQ03#1Rz#0#;#TQ0<Q0?Q0FQ0a#5Q0bQ0cPd%5ZS0cQ0cPdQ0dP\Q0e#3R\#5%3\R\%3\R\%3\R\Q0_#5S0_Q0`#5Q0RPmPK%c|S0`#1S0e#qS0d#1#c#tS0b#t#tR|#0#BS0aQ0YQ0ZQ0[Q0\%3\R\%3\R\%3\R\%3\R\00:Y3RC]DHDH3RC]C]H09C]DHC@S03Q0336S1}P2Pe&0<]#;#V=n3@S1~B0E{PK=7R^C@RR=6}RS20P}PIPR%3\R\#3S21%Kz#9S22#=S23Q0<Q0?Q0FQ21#3#pRz%3zRz%3zRzPdQ0cPKPK%3z#pRz#5S0<%3zRz#5S24%3zRz#5S25%3zRz#5S26%3zRz#5S27%3zRz#5S28Q0_PKQ0RPmPKQ0aQ0YQ0ZQ0[Q0\%uz#kRz%3zRz%3zRz%3zS29;RY3RDHDHDHDHDH3RC]H09C@S2:Q2:56rS2;AI{PKRzPsPkPpPaPoPfPyPEPjPDP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ09Q1ZQ16Q1[Q1\Q1]Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0JQ0gPnPNPgPhPOPFPMPtP>Q0:PbPl1QiVS2<Q0pQ0QQ0GQ0BQ0CQ0qQ0OQ0XQ0E1bX=D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2S2=Q2=56[S2>Q0V#0R=#0RV#1Ri#0R]#1S0V#C-0GKS2?%5\R\7ITS2@%1U#D#;RU#<S2A#VRq%KU#V5N\R\PK%DVRV#DS2B#9RUPSQ1qC?S2CPK%0]S2D#iS2EPT%16#o#K#CH07S2FPK%1iRi#0S2G#[S2HPT%=qR6C?S2IPK%;=#KR=#1S2J#9R]PS%1|#BS2KC?S2LPK%1iRi#[R|PT%1?S2M#0S2N#1#D#;#c#9S2O#=C?S2PPK%1VRV#iPTPKC?S2QPK%[VRVPTPKC?S2RPK%0=R=#9R?PSQ2KC?S2KPsPkPpPaPoPfPyPEPjPDP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ09Q1ZQ16Q1[Q1\Q1]Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0JQ0gPnPNPgPhPOPFPMPtP>1QWUS2SQ2B#1/mVS2BQ2D#<Q2E'mS2EQ0VQ2H'`S2HQ2G/`|S2G1`i?S0V%1=/m]S2DQ2J#1Q0W'mS0WPbPlQ2<Q0pQ0QQ0GQ0BQ0CQ0qQ0OQ0XQ0EPXQ0vQ0zQ0sQ0rQ0DQ0hQ1wQ1xQ1yQ1zQ1{Q0o/QqS0o/b<3gD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2R]3gD2D2R=,bzS2JQ2J56[S2TAI{PvR{Q0uQ0yQ0|Q10PsPkPpPaPoPfPyPEPjPDP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ09Q1ZQ16Q1[Q1\Q1]Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0JQ0gPnPNPgPhPOPFPMPtP>Q0:PbPlQ2<Q0P#1Q0A+02Q0tD2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2S0tQ0t56[S0A1b{=R{=6[{R=Q2FQ2IQ2LQ2PQ2QQ2RQ2KPzP]D2D2R],b\R?=6[?S0PQ2@Q2C/b]7g\S2@Q2@56[S0:Q2M#1S2M#0S10#;#KR]#<#o#V=n3@Ri=62iS0|Q2O=n3@R|=62|S2Og0175RV$0aS0yPUPu%^]#9S0uP6Q2A$06S2A#=S2UP6Q0j#BQ0=#a#KS0=#^S2V#0#BR]PvQ2N#<S2N#v,hLS2WQ29#3RSQ0u#=Q2WQ0?Q0F%3S#pS0FQ0F#3S0FQ0F#3S0F%=_S0?PvPvQ0F#pR_#5%3_R_%3_R_%3_R_%3_R_%3_R_%3_R_P]PvPKQ2V#1#BS2VPvP]PvPKPvPv%u_#kR_%3_R_%3_R_%3_00:Y3RC]DHDH3R3R3RDH3RC]H09Q2FQ2??IT6Q2IQ2LQ2PPL%Xw#vPTQ0MPQPJPTH0`S2LC?PL%0xS2I#<PT%=URxPLQ06#JPTQ10#0#y#o#TPLQ1^PTQ2VPLQ0K#<S0K#<PTPxPLQ1<#1RQPTPvPL%CQPTQ0`#0#BPLQ1=PTQ0e#BPLQ1>#0S1>#<PTQ1?#1RQ#BPL%1QRwPTQ2M#XRY#1#c#D#T1>KqPPQ1t#=RqQ0j-0?LPPPqPL%0QRQPTPKPLQ1@#1Rq#CPTPvPL%<QRQ#<PTPKPL%CwPTQ0f#X#y#;#K#BPLPqPTPKPLQ1F#JPTPKQ1;#1S1;#JS1F#vRq,>LPTQ0i#PRw,hLQ1A#;-0_LPTQ0d$04$00$00$00#D#BPLQ1B#0S1B#<PTQ0b#0#t#t#BPLQ1EPTQ0@#K$04$00#TPLQ1C#1RP#0S1C#<S0@#0R_PT%^Q#a#BPLQ12#0S12PTQ2LPLQ1D#1S1D#CPTQ0?PLQ1DPTPKPLQ1CPT1hLqPL%1PRPPT%P_,hLPL%CPPTQ11#X#vRP,hLPLQ0T#1R_PTQ0\PL%J_S0\PTQ0[PLQ0UPTQ0ZPLQ13#0S13PTQ0YPLQ14#1R_PTQ0aPL%J_R_PTPKPLQ15PTQ1qPLQ17#0S17PTPKPLQ0lPTPvPLQ0N#JS0NPTQ0?PLQ19PTQ0=#0#o#BPLQ1:#0RqPTPxPLQ1;PT%0Y#C#D#TQ2QQ2RQ2KQ2CPLQ13PTPKPLQ0\PTPKPLQ12PTPK1>LPPTPK20?L_PTPKPLQ2NPTQ0>#PR_,hLRPPLQ17PTQ2LPLQ0NPTPmPLPqPTQ0RPLQ1FPTPKPLQ2IPTQ0_PLQ0KPTQ0cPLQ1>PTPdPLPQPTQ0x#<#TPLQ1BPTPPPLQ1VPTQ25PLQ1H#JPTQ241>LwPTQ0<1>L_PTPKPLQ02#JPTQ28PLQ1XPTQ27PLQ0m#JPTQ26PLQ0@PTQ23PzPsPkPpPaPoPfPyPEPjPDP`P~PcQ1MQ1OQ1PQ1QQ1RQ1SQ1TQ1UQ1WQ1YQ09Q1ZQ16Q1[Q1\Q1]Q1_Q1`Q1aQ1bQ1cQ1dQ1eQ1fQ1gQ1hQ1iQ1jQ1kQ1lQ1mQ1nQ1oQ1pQ1rQ1sQ1uQ1vQ0JQ0gPnPNPgPhPOPFPMPtP>Q2SQ2BQ2EQ2HQ2GQ0VQ2DQ0WPbPlQ2<Q0pQ0QQ0GQ0BQ0CQ0qQ0OQ0XQ0EPXQ0vQ0zQ0sQ0rQ0DQ0hQ1wQ1xQ1yQ1zQ1{Q0oQ2AQ0n;l<D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D2D:D:DWD:F~D:DWD:D:D:D:D:D:D:D:D:D:F~D:D:D:D2DMDWDMDWD:DWDMDWDMDWD:DWDMD:DMDMDMD:DWDWDMD:F~D:DMD:D:D:DMF~DMD:DMD:DMD:DWD:D:3gD2N<0^-0DVR<;6<S2P1U11RX/U1Rl/U4Rb/U4R>/U4Rt/U4RMPXP1P1P1Q0uPUC@PuC@=jl6Q2U5jb=j>]=jtvR];6]S2UQ22=n3@RU=62US22P2PeP3Q04P9g018KRFQ01%P8#=80]mR8PKC{=70@P^EfRO=6}OS01P2PeP3Q07#<$04#9RhQ0MPFP8PKC{=70@P^EfR8=6}8S07P2PeP3Q1GP@P^EfRg=6}gS1GA64KKS0uP2PeP3PhP@P^EfRN=6}NS2AP2PeP3Q0L#o#;#VP@P^EfRn=6}nS0L'4S0n'4S0o'4S1{'4S1z'4S1y'4S1x'4S1w'4S0h'4S0D'4S0r'4S0s,4HS0z,4HS0v,4HS0E,4HS0X'4S0O,4HS0q,4HS0C,4HS0B,4=S0G'4S0Q'4S0p'4S2<'4S0W'4S2D'4Rc'4R~'4R`'4RD'4Rj,4HRE,4HRy,4HRf,4HRo,4HRa,4HRp,4HRk'4Rs'4Rz,4HRT,4HRL'4R_,4HRw,4HRP,4HRQ'4Rd'4Rq'4RY'41e2ARxQ05PYPxQ08Pq1e2GRqQ08PdPqPHPQ1e59R5PHPPP5PHPwP5PHP_P5Q0^PLPIQ0]PHPTP5PHPzP5Q0~PsP[Q0}Q1LPkP[Q1NPHPpP5PHPaP5PHPoP5PHPfP5PHPyP5PHPEP5PHPjP5Q0kPD1e};Q0wP`P}Q0{Q1|P~P}PCQ1}PcPrQ03Q20Q2DP}PRQ2;Q0WPrQ2:Q2>Q2<P[Q2=Q2TQ0pP[Q2JQ0AQ0QP[Q0tP=Q0G1e[{R{P=Q0BP{PHQ0CP5PHQ0qP5PHQ0OP5Q0PQ0X1e[?PHQ0EP5PHQ0vP5PHQ0zP5PHQ0sP5Q0:Q0rP[Q2@Q0|Q0DP2PiQ2OQ0hP2P|Q2PQ1wQ0yP<Q2UQ1xPMP]Q22Q1yP2PUQ01Q1zP}POQ07Q1{P}P8Q1GQ0oP}PgQ0uQ0nP4PKQ2AQ0LP}PN1e}nDADADADADADADADADADADAFLFLFLFLFLDADADADADADADADAFLFLFLFLDADAFLDAFLFLFLFLP2P31U:3R:g019=R8g01:NRO3ER<,F3P3P<CdPAP2P3g01;ZR<9E:8R5,F3P3P5CdPAP2P3g01<fRA9E:8R5,F3P3P5CdPGP2P3g01>2R59E:8RH,F3P3PHCdPGPJPJPJPJCz,YOg01?>ROPJPJPuQ1KCz,YAPuQ1IPJPJCz,Y<PuQ1IPuQ1KCz,Y5PIg01@J&0[BRBQ18#8g01AV40Z$0YR5<01mg01B2Rug01C?R<g01DLRJP[g01EXRA/YJPJP[g01FbRJg01GlRG'YPGg01I8@015m#rg01JD@015m#rg01KP#rg01L[#rg01Mf@015m#r20=Z<20XZuP}P2PeP3AE:8JRJ,F3RuP3PJPuF\P;P}P2PeP3AE:8ARA,F3R;P3PAP;F\Q0{P}P2PeP3g01O4R;9E:8RA,F3RuP3PAPuF\P2PeQ1Jg01P@C@RuPrP}PIP2PeP3g01QMRA9E:8RJ,F3RZP3PJPZF\&0;ZC@P}PIPug01RYC@P}P2PeP3g01SeRu9E:8RZ,F3RJP3PZPJF\P2PeQ1~g01U1C@RJPrP}PIP2PeP3g01V>Rr9E:8RZ,F3R5P3PZP5F\&0;5C@P}PIPJg01WJRJC@P[g01XV,Yug01YcP[g01[0Ru,Yrg01\=RrP[1Y;<g01]JP[g01^WR;,YAg01_dRAP[PuPAg01a1&0W6g01b<g01cJR6577'bP[&0V;A77\6Q2100=;Q0S00=6&0UBg01dVRBQ00g01e5H0R>0OJS#rg01fIRJ-0C;P[Q0;1UB1R[PBP1Q0IPWC@%s[R[37P[P;H0NPJP2P3g01gU9E:8RJ,F3P3PJCdPiP2P3g01h_9E:8Ri,F3P3PiCdP|Q0yg01iig01k460MSg01l?RS-0DVPMPXP1P1P1&0PS&0QSC@&0LSC@&0SS5jl&0TS5jb&0gS5j>&0fS5jtP]P2P3g01mJ9E:8R],F3P3P]CdPUP}P2PeP3g01nT9E:8RU,F3R]P3PUP]F\P2PeP3Q04P9PFg01oaR9PKC{=70@P^EfP}P2PeP3g020n9E:8R],F3RUP3P]PUF\P2PeP3PhQ0MPFP9PKC{=70@P^EfP}P2PeP3g022;9E:8R^,F3R@P3P^P@F\PgP4P4Q0H&0;@PvH0ePKP}P2PeP3g023E9E:8RK,F3RvP3PKPvF\PNP}P2PeP3g024O9E:8R8,F3R:P3P8Cd&0K:PnJ0dC|FOFOFOFOFO3w3wC|3_9_;r9_r;C|FOFOFOFOFO+0c3w3w3wFO7_<5_OC|7_O7_O7_O3_FOFOdo"). Qed.

End FPX_1.
