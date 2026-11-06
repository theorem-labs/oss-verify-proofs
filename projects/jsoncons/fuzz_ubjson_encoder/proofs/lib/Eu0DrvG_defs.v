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
  HeapIface DrvKit Eu0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0DrvG_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs8kn_afterC13~~~K47Corelib4Init9Datatypes4list02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5kdiffC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sr_updC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5summGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs7keep_rdC13~~~C47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_nextC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_lC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_spC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5srC0LC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs7srRe_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srRmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srGaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srGbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srGcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srGdC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4rC0LC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs4knC0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5cellRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4knLPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knLP6C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rPaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs6want_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rPbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knLPpC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knRDpC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srPbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srPaC13~~~K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srRDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs6rRe_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knRe0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rRmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5len_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs6rRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs7knRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5cellCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs7srRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srGLC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rGaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knLPgC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs6cap2_xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs3MSOC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rGbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knGb0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs5knGc0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rGcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rGdC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4knRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3scRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs3rRbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0DrvG_defs4srRbC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_L : list Z := (0x34ad4 :: STOPS)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_L scr ss [].
(* [comment removed for export] *)
Definition STOPS_Q : list Z := [0x9d974; 0xa2b78; 0x9f958; 0x9f818; 0x34eec]%Z.
Definition runQ (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_Q scr ss [].
Definition no_sc : stdio_res := SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [].
Definition the_sc (o : option stdio_res) : stdio_res := match o with Some r => r | None => no_sc end.

(* [comment removed for export] *)
Definition kn_blk2 (v : nat) : list kentry := [KRange (EVar v) 4096 (2 ^ 47); KAlign (EVar v) 16]%Z.
(* [comment removed for export] *)
Definition keep_rd (kn : list kentry) : list kentry := kn_keep_g 0 0 0 [] [] [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.

(* [comment removed for export] *)
Definition below_frame (K : kentry) : bool :=
  match K with KWord (SA (EVar 0) off) _ _ => (off <? -128)%Z | _ => false end.
Definition knLP6 : list kentry := Eval vm_compute in List.filter (fun K => negb (below_frame K)) keepB.
Definition knLP : list kentry := kn_blk 48 65536 ++ knLP6.
(* [comment removed for export] *)
Definition cellR : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x34b34).
Definition cellC : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x34b48).
Definition knRD : list kentry := cellR :: knLP.

(* [comment removed for export] *)
Definition srLP : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 838592; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 766345; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.
(* [comment removed for export] *)
Definition srRD : list expr :=
  [ELit 0; ELit 732980; EAlu ALU_ADD (EVar 0) (ELit (-144)); ELit 67584; ELit 838592; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; ELit 3; ELit 766345; EVar 71; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 766345; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runL scr0 (SS 0x34aa0 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPp : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP.
(* [comment removed for export] *)
Definition rPa := Eval vm_compute in runL (SCR [false; false] [] []) (SS 0x34ad4 srLP [] knLPp 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition knRDp : list kentry := Eval vm_compute in kn_after rPa knLPp.
(* [comment removed for export] *)
Definition rPb := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x34ad4 srLP [] knLPp 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
(* [comment removed for export] *)
Definition want_x : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRe0 : list expr := sr_upd srRD (ridx 10) (EVar 72).
Definition knRe0 : list kentry := KRange (EVar 72) 1 65536 :: knRD.
Definition rRe_tk := Eval vm_compute in runL scr0 (SS 0xaefb4 srRe0 [] knRe0 73).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
Definition knRe_tk : list kentry := Eval vm_compute in kn_after rRe_tk knRe0.
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx callee_kept) 73.
Definition rRm := Eval vm_compute in runL scr0 (SS 0x34acc srRm0 [] knRe_tk 105).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
(* [comment removed for export] *)
Definition len_x : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition srRf0 : list expr := sr_upd srRD (ridx 10) (ELit 0).
Definition rRe_ft := Eval vm_compute in runL scr0 (SS 0xaefb4 srRf0 [] knRD 73).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition knRe_ft : list kentry := Eval vm_compute in kn_after rRe_ft knRD.

(* [comment removed for export] *)
Definition srGL : list expr := Eval vm_compute in sr_upd srRe_ft (ridx 10) (ELit 0).
Definition knGbase : list kentry := cellC :: knLP.
Definition knG (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbase.

(* [comment removed for export] *)
Definition knLPg : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP.
Definition rGa := Eval vm_compute in runL (SCR [true] [] []) (SS 0x34ad4 srLP [] knLPg 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition knGa : list kentry := Eval vm_compute in kn_after rGa knLPg.
(* [comment removed for export] *)
Definition cap2_x : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa.
Definition rGb := Eval vm_compute in runL scr0 (SS 0x34af4 srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx callee_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keep_rd knGb0.
Definition rGc := Eval vm_compute in runL scr0 (SS 0x34b10 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knGc0.
Definition rGd := Eval vm_compute in runL scr0 (SS 0x34b18 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).
Definition knGd : list kentry := Eval vm_compute in kn_after rGd knGd0.

(* [comment removed for export] *)
Definition knLPr : list kentry := KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP.
(* [comment removed for export] *)
Definition scr_refuse : scripts := SCR [false; false; false; true; false] [] [].   (* [comment removed for export] *)
Definition rRa := Eval vm_compute in runQ scr_refuse (SS 0x34ad4 srLP [] knLPr 71).
Definition srRa : list expr := Eval vm_compute in s_regs (fst (fst rRa)).
Definition knRa : list kentry := Eval vm_compute in kn_after rRa knLPr.
Definition scR : stdio_res := Eval vm_compute in the_sc (stdio_call 71 srRa knRa).
Definition srRb0 : list expr := Eval vm_compute in sc_sr scR.
Definition knRb0 : list kentry := Eval vm_compute in sc_kn scR.
Definition rRb := Eval vm_compute in runQ scr0 (SS (sc_ret scR) srRb0 [] knRb0 103).
Definition srRb : list expr := Eval vm_compute in s_regs (fst (fst rRb)).
Definition knRb : list kentry := Eval vm_compute in kn_after rRb knRb0.

(* [comment removed for export] *)
Definition summG (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), s_log (fst (fst r))).
Definition kdiff (a b : list kentry) := List.filter (fun K => negb (existsb (kentry_eqb K) b)) a.
Lemma loop_itinerary_ok :
  summG rC0L = (0xaefb0%Z, [], 70%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34b34%Z)]) /\ kn_after rC0L knC0 = cellR :: knC0
  /\ kdiff knLP knC0 = [] /\ kn_vars_lt 6 knLP6 = true
  /\ (nth 21 srC0L (ELit 0), nth 9 srC0L (ELit 0), nth 19 srC0L (ELit 0), nth 12 srC0L (ELit 0), nth 11 srC0L (ELit 0), nth 10 srC0L (ELit 0), nth 17 srC0L (ELit 0))
     = (ELit 65536, EVar 48, ELit 0, ELit 65536, ELit 766345, ELit 3, ELit 63)
  /\ summG rPa = (0xaefb0%Z, [SCBr false BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34b34%Z)])
  /\ summG rPb = (0xaefb0%Z, [SCBr true BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34b34%Z)])
  /\ kn_after rPb knLPp = knRDp /\ knRDp = cellR :: knLPp
  /\ srPb = sr_upd srPa (ridx 12) want_x /\ srPa = sr_upd (sr_upd srRD (ridx 12) (ELit 65536)) (ridx 23) (EVar 48)
  /\ want_x = EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit (-1)) (EVar 70))
  /\ summG rRe_tk = (0xae008%Z, [], 73%nat, []) /\ kn_after rRe_tk knRe0 = knRe0 /\ keep_rd knRe0 = knRe0
  /\ (nth 10 srRe_tk (ELit 0), nth 11 srRe_tk (ELit 0), nth 12 srRe_tk (ELit 0), nth 1 srRe_tk (ELit 0), nth 2 srRe_tk (ELit 0))
     = (EAlu ALU_ADD (EVar 48) (EVar 70), ELit 766345, EVar 72, ELit 0x34acc%Z, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRm = (0x34ad4%Z, [], 105%nat, []) /\ len_x = EAlu ALU_ADD (EVar 70) (EVar 72)
  /\ (nth 9 srRm (ELit 0), nth 23 srRm (ELit 0), nth 21 srRm (ELit 0), nth 18 srRm (ELit 0), nth 2 srRm (ELit 0))
     = (EVar 48, EVar 48, EVar 38, EVar 2, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRe_ft = (0xaefb0%Z, [], 73%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34b48%Z)]) /\ knRe_ft = cellC :: knLP
  /\ (nth 10 srRe_ft (ELit 0), nth 17 srRe_ft (ELit 0)) = (ELit 3, ELit 57) /\ sr_vars_lt 71 srGL = true
  /\ summG rGa = (0x9f958%Z, [SCBr true BC_EQ (EVar 70) (EVar 38)], 71%nat, [])
  /\ kn_after rGa knLPg = knLPg /\ nth 10 srGa (ELit 0) = cap2_x /\ nth 21 srGa (ELit 0) = cap2_x /\ cap2_x = EMd M_MUL (ELit 2) (EVar 70)
  /\ nth 1 srGa (ELit 0) = ELit 0x34af4%Z /\ nth 2 srGa (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGb = (0xae008%Z, [], 103%nat, []) /\ kn_after rGb knGb0 = knGb0
  /\ (nth 10 srGb (ELit 0), nth 11 srGb (ELit 0), nth 12 srGb (ELit 0), nth 1 srGb (ELit 0)) = (EVar 81, EVar 48, EVar 70, ELit 0x34b10%Z)
  /\ kdiff knGb0 knGc0 = []
  /\ summG rGc = (0x9f818%Z, [], 135%nat, []) /\ kn_after rGc knGc0 = knGc0 /\ nth 10 srGc (ELit 0) = EVar 48
  /\ nth 1 srGc (ELit 0) = ELit 0x34b18%Z /\ nth 2 srGc (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGd = (0xaefb0%Z, [], 167%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34b34%Z)])
  /\ (nth 10 srGd (ELit 0), nth 11 srGd (ELit 0), nth 12 srGd (ELit 0), nth 17 srGd (ELit 0), nth 9 srGd (ELit 0), nth 21 srGd (ELit 0), nth 19 srGd (ELit 0))
     = (ELit 3, ELit 766345, ELit 65536, ELit 63, EVar 81, cap2_x, EVar 70)
  /\ (s_pc (fst (fst rRa)), s_next (fst (fst rRa))) = (0xa2b78%Z, 71%nat)
  /\ stdio_call 71 srRa knRa = Some scR /\ (sc_ret scR, sc_f scR, sc_fd scR, sc_s scR, sc_l scR) = (0xa3824%Z, 0xbaf38%Z, 2%Z, ELit 0, ELit 0)
  /\ (sc_wb scR, sc_wp scR, sc_sp scR) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), EAlu ALU_ADD (EVar 0) (ELit (-576)))
  /\ summG rRb = (0x9d974%Z, [], 103%nat, s_log (fst (fst rRb))) /\ nth 10 srRb (ELit 0) = ELit 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0DrvG_defs ()) ["FPX_1"] "p%0p%1p%2p&0p;1p;2p;3p;4p;<g0000k10<Tg000Pj2`Tg0010j10Tg001Uj11Tg002:k107Tg002Zj12Tg0039j19Tg004Gj34Tg004aj3PTg0061j16Tg006Oj3qTg007_j2zTg008oj2?Tg00:>k20>Tg00;Nk404Tg00<^j1>Tg00=lk30;Tg00?<j1OTg00?Zk30KTg00@hj4uTg00B:j4@Tg00BZk10^Tg00C<k40[Tg00DJm<0ZTg00E`k20ITg00FBj23Tg00F]j2NTg00G7j2pTg00HFj35Tg00Hfk20GTg00J3k20XTg00K?k10WTg00K]k30FTg00L@k10ETg00MLk30?Tg00NZj1lTg00Ogk10UTg00Q6j4XTg00QRk20TTg00R^k303Tg00S;k10QTg00TGk10VTg00UUk30kTg00Vjk10jTg00X;k10iTg00YJk10hTg00ZZk10gTg00[ik10fTg00]8k10eTg00^Hk10dTg00_Xk10cTg00`hk10aTg00b5k30bTg00cEk30PTg00dSj2xTg00eck40DTf0R0#1#0p=8%10#1#1p=w%10#1#0#1p=e%00#0#0#6p==g00f>R1f2R2f1R3P0C@p=\%20#2p=_%20#2#2#2p>08%20#2#2#2#2#2#2#2p=T%O0,?3p>0B%00#0p=E%00#1p=<%00#0#6#>p=Gg00f\R4f3R5@0b23;50p=ff5R6f4R7P5g00glR8P2P3C@P0C@p=R%10#1#1#1#1#1#1#1p=s%10#1p=L%10#1#1#1p=c%00#0#0#0p=D%00#0#0#0#0#0#0#0p=V%00#0#0p=U%O2,?5?P30p=Zg00hKR9@0P30p=~%00#0#1#1p=o%00#0#1#0p=i1?52?P30p=S%10#0#0#0p=I%60#>p=7%62,?5?P30p=^%60,?3p=}%10#0#0p=]%00#6p>00%10#6p>0:%00#1#0#0p>0A%10#1#0#0p=Q%00#0#0#0#6p=h%60,x3p>0_%63/x0p>0Og00i7R:Aq523;50p=g%02#6/x3=5:0p=KA5:3095:2p=v1x23=5:0p>091?75?P23=5:0p=YAP523=5:0p>0N1x751x23=5:055:p>0MA5:3095:295:595:7p=AA5:30p>0Lg00jGR;,`0p=nf7P;f6R<P;P6P;P;P;P7P5C@P2C@P3C@P0C@p=dP7P;P5P;P2P3C@P0C@p=ag00kUR=?530p=t%>0:0P93p=W%93=5;0p>0@%92%93=5;055;p=mA5;3095;295;595;7p=JA5;30p>0JA4;30p=HP;P;P3P0C@p>06%00#Op={A5;3095;2p>0]%10#O,?3p>0\%O5,?7?P23=5:0p=:%05#O,?7?P23=5:0p=;AP<67AP523=5:055:p=r%O5,?7%63#>7P2=5:0p=[%15#O,?7?P23=5:0p=CP5P;P;P;P2P3C@P0C@p>0HP7P8P1P5P2P3C@P0C@p>0Y1N;0p=bP7P51N23P0H0Dp=BP<P6P7P5P2P3P0H0DH0Dp=MP;P3g00lgP0CXp=kP;P3g00n4P0CXp=yP;P3g00oCP0CXp=|P;P3g010OP0CXp>02P;P3g011[P0CXp>05P;P3g012gP0CXp>0=%l3=420p>0SP;P3g0143P0CXp=jP2P;P3P0C@p>0RA4<67A4523/30'3p=F1330,32p>0CA4523/30p>0`%l2=453/30p>01&0<=R0,`1R5/`8R3&0<4R2'`R<P3P2P5g015?R7#0R6#1R9#0R>#1S00#1#8S01#w#e#8#=R?&07=R=5\0S02g015dR@#2RA#2RB#2RC#2RD#2RE#2S03#_RF#2RG#2RH#2RI#2RJ#2RK$08RL#2S04#2RM#2S05#2RN#2S06#2S07#2#_$08RO#2RP#2RQ#2S08#2S09#2S0:#2S0;#2S0<#2RR#_#TRS#_$08#T#TRT%9@R@%06RU#0RV#1S0=#0S0>#0S0?#0RW+0BRXPF%17RY#0RZ#1R[#ES0@#1S0A#<R\#8S0B#0S0C#e#GR]&074R4CfR^ERS0DQ0D34&0<:R_APXF]R]%9SRS%0VR`#0Ra#0S0E#0Rb#0S0F#0Rc#0S0G#ERd#6Re%1YRf#1Rg#1S0H#1S0I#1S0J#1#sRh#L#cRi#1Rj#0#L#c#8#D#V#=3qS0K%6`Rk,zSS0Lg016CRl,?SRm%DdRd#6Rn+0>S0M%Ud#DRd-0B@Ro%0dRp#6PmPnH04S0N%>lRq/?n%1[S0O#1S0P#0S0Q#<#8#e#8#=PmPnH04S0RP@%0gS0S#0S0T#0S0UPFPqCZS0VP@%0fRf#0S0W#0Rg#0S0XPFPqCZS0YP@Q0@#0RmPFPqCZS0ZP@%0ZR[#0S0[#0Rr#0S0\PFPqCZS0]P@%19Rs#0S0^#0S0_#0S0`PF%6aS0a#>Rt,~@CZS0bP@%E>Ru#0RvPF%0\R\#<#o#GCZS0cP@%1URw#0S0d#0S0e#0RxPF%66S0f#>R6CZS0gP@Q0EPF%6VRV#>Ry,~@CZS0hP@PgPF%1wRw#1Rz#0S0i#1S0j#o#i#8#GCZS0k1z@kS0l%Dh#V#V#V#=Rh%0pR{#0R|#E#V#V#=S0m5q@S0n%6dRd-0>oS0oP@PlPFP6CSS0pP@PVPF%9ACSS0qP@PkPF%9BS0rCSS0sP@Q0[#6S0tPFPqCSS0u%9CR}%Ip#V#V#=Rp7qhS0v%9DR~?qhpS0wPoPd1?}lRp%0vS0x#6H04S0yPoPd1?~lPkH04S0z1z}VS0{1z~VS0|%7YRY9PpFS0}P}PVPF%1c#D#GCSS0~P}PkPF%7UCSS10P}Q0tPF%6gRg#>S0tCSS11P}Q0aPF%79S0aCSS12P}PuPF%7>S13C^S14P}%6rS15PF%>kCSS161?}g@0;yCS17P}Q0EPF%7ZC^S18P}PxPF%>eRZC^S19P}%6vS1:PF%7sCSS1;P}Q0\PF%6[S1<#>C^S1=P}Q0X#6S1>PF%1sRs#6S1?#>CSS1@P}Q0UPFPqC^S1AP}PbPF%1[R[#7C^S1BP}PWPFP~C^S1CP}%0xR~PFPqC^S1DP}%0wS1E#ES1FPFPqC^S1G%0sS1H#1Rs#0S1I#D#V,}q%0mS1J#U#D#=+0>S1K%]s#<Rs#0#8#DRm$00S1L&0:m%]s$0A$0:Rs%0[S1M#1S1N#I#Q$0A$0:%8[S1O#<R[#<Rm#0#cRw#h%1fS1P#1Rf#0Rv#0S1Q#1Rg#0S1R#cRr#0$0A%1r#<#=Pq%1w#=RwPF%>w%1mRm#0Rw#0Rr#<#I,}qPD%9ERE%1r#i%wwRw#h%]w%1mRm#0Rw#<Rr#hR>PqP>PF%1gS1S#1Rg#0R>#1RU#0Rc#ERV#1#=Rp#>%]r%1w#8#=Rw1?qw@0;yB%8mRm#E#=Rw%1mRm#D+0_%]m%][S1T#0#8#<#=Q1S#0#V%0>R>#<R[#<#=Rm%1[R[#hRr1?qr@0;yB%I[%1>R>#0R[#E#=+0O%1[R[#U$0:%1[#=R[PqP[PFP}%1>R>#0R}#U%1}#=%Q>%hVRVPqPVPFPZ%wc#=Rc1?qc@0;yC%]U#D%Lg#8#<#=+0O%1vS1U#0S1V#0S1W#LS1X#0#L#I%IfS1Y#U#D#=PE%67S1Z%6i&07:RiCg3K3v609pDY3K3KDY4093v609m3K3K3v3KDY3K3KH0NDY3KI0MS1[609n3vDADADADADADADADADADADARm+0LS1\Q1\34S1]A4_iiS1^g016aS1_g017ARp;4pS1`1`;;RE#nRf#nRv#nRg#nRU#nRCPUPgPvPfPE%>nRcPSPqPc%>sRsGdPYQ0I#7S1aDaS1bQ1b34S1cP3P2P5g017aS1dg018AS1e%9RRRg0193RZ%O7#>%9TR740K'~RVPcCuQ1dg019_R>P7PRCu/t=R}'t9\0?%2TRTP^ERS1fQ1f54<S1gP3P2P5PpQ1ePVPcCu/t}9\0?PTP^ERS1hQ1h54<S1i%wjRj#69q7lPRPn%6|R|PmCg5v]S1jQ1j54_S1kQ1k&0<;R]PqQ0_#8#L#Q#e#GR[%O~S1l,W@Rd%1`S1m#0S1n#0S1o#0S1p#0S1q#0S1r#D#GS1s%>wS1t%9IRw%9JR`%9KRKP6PSPYPsPqPqPqPqQ1aQ0rP7PYPRPsPS%9OS1u%9PS1v%9QS1wQ08#9S08Q09#9Q0:Q0;Q0<&07;S09+0@3mDJDJDJDJRQ-0JVDJDJDJS0;Q0;34S0:PqP[PdQ1sQ1tPwP`PKP6PSPYPs20JcQDJDJDJS0<Q0<54]S1x1HVVS1yP3P2P5Q01#U#D#<#==\0=RQ%2TRK#2R`P4ERRw=4<wS01%9KRKQ1ZPnQ1\CgS1zQ1z54_S1{Q1{PvPfPE1~S7PsPK%L\R\#0Rd#0#L#G%Ob,W@RbGdS1|Q1|54gS1}P3P2P5%8d#8$00=\0=%2`#_S1~#2S20#2S21#2#_Rd#2S22#2S23#2S24#2S25#2S26#2S27#2S28#2#_#TS29#2S2:#2S2;#2S2<#2S2=#_R[P4ERS2>Q2>54<S2?1~7KRK/HKS2@PvPfPEPSPSPRQ0rPbGdRP=4gPS2AP3P2P5Q02P`PXPFQ0B#1#i#GR`P4CfERS0BQ0B54<S2BPXPFP`PmH0NS2CQ2C54_S2DQ0W#1R`#7-06YS0WQ0W54ES2EQ1`P3P2P5%1z#QRz#8#8#L#=PpP>P7PRCu/t=5\0PTP4ERR>=4<>S2FP7Pn%6{R{PRPnP{PmCgCgRm=4_mS2GB0KZ67RZ/HZR{%e\#GR\/H\S2H1HbbROP3P2P5PQQ2=P4ERRQ=4<QS2I%9dRdPeQ0m1zdk00LmCgRk=4_kRePfPE206dSP7Q0C#<Ro#E#GDaRh=4vhS0CQ1^P3P2P5%Ez#o#==\0=%_[$08#T#T#TR[P4ERRz=4<zS0m1HSSS2J%8o#GRo/HoS2KP3P2P5Q02%T[#T#T#TP^ERR[=4<[S02PUPgPvPfPEPYPsPcQ1aPdGdS1aPZP7DaS2LQ2L54CS2M1`18S2NP1P8%1uRu#<S2O#<#8#c#=PTC@S2PQ2P34S2Qg01:QS2R$0^S2SQ2RQ1I#cS1I#0S2T#<#LS2U#=RdQ0f%QuS2V#E#<#i$00S2WQ0=#1S0=#0S2X#ES2Y#0S2Z#OS2[,W@Ru%1aS2\#0S2]#1Ra#{,W@S2^PuQ1:#>S1:PqPq%0~S2_#0S2`#OS2a,W@R~Q2W#>P~Q1sQ1tQ1~Q20Q21%>dS1tQ1E#7PqQ22#9Q23Q24Q25Q26Q27Q28%>rS22Q1Z#>Q1X#8#8#8#GS1XPqPsPSQ1uQ1vQ1wQ08Q29Q2:Q2;Q2<Q093m3m40]DJDJ3m3m3mDJ+0@3mDJ-0@TQ2T#1Rs#0S2T#1S20#1#=S1~,?qS21PFQ0U#0S0U#{,W@S24%1sRs#0S23#D,}qS26PFPu%1sS25#hS28,?qS27PFPu20\@aPAQ13P@Q2\#1Ra#0Rs#0S2\PAQ1M#0S1MP@PsPAQ1N#7RsP@%1aRaPA%1`#7S1NP@PaPAQ1P#0Ra#1#7S1PP@Q1qPAQ1OP@Q1pPAPsP@Q1o#1RrPA%0`#7P@PrPAPtP@Q1n#1Rr#0R`#0S1nPAQ0_P@P`PAQ1NP@%1rRrPAPsP@PrPA%0aS1N#7S0_P@Q1m#1S1m#0Rr#0Rs#0S1oPAQ0T#1P@PsPAQ0[#1Rs#0#7P@%1rS0[PAPtP@Q0e#1Rr#IPFQ0=#1S0=#1R`#1#<#e#<P@%DrPFQ1tP@%IxPFQ0^P@Q2`PF%0j#8#<#7P@%U`PF%1j#cS2`P@Q0=#US0=PFQ0d#1S0d#7P@Q2X#IPFQ2V#w#e#GP@Q0[PAQ0@#7S0@P@Q1m#1Rj#0R`#0S1mPAQ0O#0Rx#7RrP@P`PAQ0tP@%1jRjPAQ0tP@PjPAQ15#>S15P@%0WS0O#0RjPA%7sS0[P@Q0OPAQ0P#7S0PP@%1WS2VPAPrP@Q0>#1RW#1R`#0S0>#0S2XPFPqP@PjPFPyP@%0WRW#0S0^#0S1tPFPyP@Q1YPAPrP@Q2ZPFQ2]#0Ry#L#i#L#7P@Q1U#1RjPAQ0PP@PjPAQ0[P@Q1VPAQ15P@Q1WPAQ0tP@Q1SPAQ0tP@Q1RPAPrP@Q1Q#<PAQ0@P@Q0?#1Rr#0S0?#0RjPFPqP@Q0I#DPF%>|S0IP@Q2aPFQ00#E#{S00,W@P@Q2VPAPtP@PjPAQ0S#1P@Q0?PAQ0H#0Rj#7P@%1rRrPAPtP@PrPAQ0_P@Q1tPAQ1PP@Q0^PAQ1>#>P@%1WRWPAQ0Q#7P@PWPAQ0A#7RWP@Q2XPAPtP@Q0>PA%7aP@%1`R`PAPWP@P`PA%0xRx#7P@Q2[PA%1s#7P@Q1mPFQ2`#wRs#E#Q#Q#Q#Q#Q#Q#e#7P@Q1oPF%1s#c#sRs#0#s#s#7P@Q0J#UPFQ1T#L#o#o#o#GP@%EyPFQ0d#URy#8#i#<P@Q0GPFQ22P@Q0E#IPFPqP@Q2\PFP~P@Q1nPFQ24P@Q1rPFQ0i#0#{R`,W@Q2T#0RW#I,}qPFPq%hWRW,?qPFPqPqQ1I#1Ra#IRt#=RrPD%1s#s#s#7%0aRa#<Rs#I,}qS1IPFQ1:%hsRs,?qS1:PFPu1?qdS2TPDQ0aQ2_-0B@PFPqP@PyPFPqP@Q1FPFPqP@P`PFPqP@Q2YPFPqP@Q0=PFQ0`#{R`,W@RyP@Q0OPFQ1dPBPlPFH0[RlP@Q1pPFPRP@Q0FPFPYP@%EjPFP7P@Q0UPFQ0rP@Q1NPFPSP@Q0XPFQ22P@PxPFQ2O#1#<#I#<#GP@Q1JPFPyP@Q1MPFPlP@Q1FPF%9NP@Q0xPFQ05#9P@Q00PF%9MP@P`PFQ0IPXPFQ07#9Q1l,?@PFQ06#9P@Q0\PFP6P@Q1H#EPFQ0A#1#i#Q#GP7P|P|PRP|P|Q0KQ0LQ0MQ0NQ0RQ0VQ0YQ0ZQ0]Q0bQ0cQ0gQ0hQ0kQ0lQ0nQ0oQ0pQ0qQ0sQ0uQ0vQ0wQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q14Q16Q17Q18Q19Q1;Q1=Q1@Q1AQ1BQ1CQ1DQ1GQ1KPnPdQ2U#8$00PWQ20#UQ1~Q23#]Q28Q25#]%1a#D%8tQ1LQ1[3K7Kr7Ks3K3KI0M3vDADADADADADADADADADADACgCgD:D;FrDYDYD:D:D;D:D;D;D;D:D:D:D:D:D:D:DYD;D:FrFrDYFrD:D;D;D:D:D[D:D;D;DYDCD;DCD:DCD;DCD:DCD;DCD[DCDYD:D;D:D:D:D:DCD;DCD;D:D;D;D;D;DCD:DCD;DCD:DCD:D;D[D;D[D:D[D;DCD[DCD;DCD[DCD;DCD[DCD;DCD[FrFrN<0Z+0IRs;4sS1K1`11Rr/`1Rt#nRa#nRWPaPtPrP1P1P1Q2WPdC@Q0fC@PqPqDaRd;4dS0fPEPuQ2^P~H0HR~=4f~S2^P3P2P5P0Q0j#1#i#L#8#8$00P=Q2=I0YS2=Q2TPDQ0aQ1IPFPqQ1:PFQ1XQ27PFPqQ26PFPqQ21PFPqP4CfCfCfCfCfCfC@R4=4<4S211H66S26'3S27'3S1X'3S1:'3S1I'3S0a'3S2T'3S0j,3OS2W'3S1G'3S1~,3eS28'3S1['3S1L'3S25'3S23'3S20'3S2U'3S1D,3{S1C,3{S1B'3S1A'3S1@'3S1='3S1;'3S19'3S18'3S17'3S16'3S14'3S12'3RF'3RD'3R='3Ru'3Rn'3R|'3RR'3RX'3R`'3Rl'3Ry'3Rx'3Rj'3RY'3P<Q0DQ1]PYP_Q1\Q1^Pj1N_iRjQ1`PxQ1_/NpRxQ1cPyPCQ1bQ1gPlP<Q1fQ1iP`P<Q1hQ1kPXQ1j,N_RXQ1kPRPXQ0:P|P]Q0;Q1xPnP]Q0<Q1yPu%bVQ01P=1N<wQ1{PDQ1z,N_RDQ1{PFPDQ1}Q12PgQ1|Q2?Q14P<Q2>Q2@Q16%bKQ2AQ171NgPQ2BQ18P<Q0BQ2DQ19P_Q2CQ2EQ1;PEQ0WQ1`Q1=PxQ2FQ1@1N<>Q2GQ1AP_PmP{Q1B%bZRmP{Q1CPmP{Q1DPmQ2HQ2U%b\POQ20%bbRbQ2IQ231N<QPeQ251N_kRkQ0CQ1L1NvhQ1^Q1[PjQ0mQ281N<zPeQ1~PkQ2JQ1G%bSQ2KQ2W%boPOQ0jPbQ02Q2TP<P[Q2MQ0aPCQ2LQ2QQ1IQ2NQ2PQ1KQ1:Q2SPsQ0fQ1XPWPdQ2^Q27PfP~Q21Q26P<P4%b6DBDBDBDBDBDBDBFMFMFMFMFMFMFMDBFMDBDBDBFMDBDBFMFMDBDBFMDBDBDBFMDBDBP<g01;gR4Q0DP_g01=3Rs,p4g01>>R4=5:sP_g01?KRb00GsPiQ1_Q03g01@W+0XPpPCPUPgPvPfPE1kNq1kGq1kMq1kJq1kIqGd1kHq1kLqDaQ1bP<g01AdP3P2P5Q1dQ1eg01BoRsPcCu/t}9\0?PTP^ERP<g01D=ROP3P2P5PpQ1ePsPcCu/t}9\0?PTP^ERP_g01EHR^,pOg01FUROP_POA5:4^P]g01Gbg01HnR^&0W9R9Q1<g01J:R440F$0ERO<0?sP]P^g01JV@0?OcQ1?>0F94$0E<0?SP;PsPVP<g01KbRV#lPwP_g01M0Rw,pVPwP_&0UwPwPgPvPfPE1yHq1yIq1yJq1yAq1yBqGdQ1|P<g01N=#lQ2>P;g01OHPKPgPvPfPE1|GqQ07/|q1|NqQ04/|q1|BqGdPPP<g01PUQ0BP_g01Qcg01S2=5:bPEP;PHg01T?RbPqCXP;PLPbPqCX+06Q0WQ1_g01UN-0TTPpP<g01VZRp#lP>P_g01WeR>,ppP>P;202Hqg01Y2R>P;202NqP>P;P>PZ202Aq/H\202Bqg01Z@,W@R@'HP<g01[JR\PQP_g01\URQ,p\PQPvPfPE205Hq205Iq+06205Jq205AqDaPhP_g01]bRh-0GQPiP<g01^oRi#lPzP_1pihPh20=Hq/HS20=Aq/Ho20=Bq/H@g01`:>0S<[PCPUPgPvPfPE1jHq1jIq1jJq1jLq1jGqGd1jNq1jMqDaPgP;Q1aP>C@>0RU7Q2NP1P8g01aER81`80R7g01bXRUg01ci4038030R>$0Q&0V>C@Q2PQ2Sg01e4g01f@60kTQ2Rg01gLRT+0IPWPaPtPrP1P1P1&0jT&0iTC@&0hTC@&0gT&0fTDaPdPfPE&0eT&0dT&0cTH0HP~P<g01hWR<#lP3P2Q2=B037U<:0380$0aC@P;PHg01ibPqCX/H6FFFFFF40C40CH0`FFFFH0140CFFFFFFFFH01FFFFFFFFFFFFH01H01FFFFH01do"). Qed.

End FPX_1.
