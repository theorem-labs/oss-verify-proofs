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
  HeapIface DrvKit Es0Drv_defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0DrvG_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~I47Corelib4Init5Logic2eq00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K47Corelib7Numbers7BinNums1Z02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs8kn_afterC13~~~K47Corelib4Init9Datatypes4list02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5kdiffC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:kn_vars_ltC13~~~K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24ridxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sr_updC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5summGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs7keep_rdC13~~~C47Corelib5Lists7ListDef3nthC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SymRun:sr_vars_ltC13~~~C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26s_nextC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_sC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_lC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_spC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~I47Corelib4Init9Datatypes3nat00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5srC0LC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs7srRe_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srRmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srGaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srGbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srGcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srGdC13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5mulop01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4rC0LC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs4knC0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5cellRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4knLPC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knLP6C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rPaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs6want_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rPbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knLPpC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knRDpC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srPbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srPaC13~~~K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srRDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs6rRe_tkC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knRe0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rRmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5len_xC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs6rRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs7knRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5cellCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs7srRe_ftC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srGLC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rGaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knLPgC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs6cap2_xC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs3MSOC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rGbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knGb0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs5knGc0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rGcC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rGdC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4knRaC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3scRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs3rRbC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0DrvG_defs4srRbC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS_L : list Z := (0x345cc :: STOPS)%Z.
Definition runL (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS_L scr ss [].
(* [comment removed for export] *)
Definition STOPS_Q : list Z := [0x9bdf8; 0xa0ffc; 0x9dddc; 0x9dc9c; 0x349e4]%Z.
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
Definition cellR : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x3462c).
Definition cellC : kentry := KWord (SA (EVar 0) (-136)) 8 (ELit 0x34640).
Definition knRD : list kentry := cellR :: knLP.

(* [comment removed for export] *)
Definition srLP : list expr :=
  [ELit 0; EVar 7; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 831552; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 759305; EVar 48; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.
(* [comment removed for export] *)
Definition srRD : list expr :=
  [ELit 0; ELit 725944; EAlu ALU_ADD (EVar 0) (ELit (-144)); ELit 67584; ELit 831552; EVar 11; EVar 12; EVar 13;
   ELit 2; EVar 48; ELit 3; ELit 759305; EVar 71; ELit 0; ELit 0; ELit 0; ELit 0; ELit 63;
   EVar 2; EVar 70; ELit 3; EVar 38; ELit 759305; EVar 29; EVar 30; EVar 31; EVar 32; EVar 33;
   EVar 34; EVar 35; EVar 36; EVar 37]%Z.

(* [comment removed for export] *)
Definition rC0L := Eval vm_compute in runL scr0 (SS 0x34598 srC0 [] knC0 70).
Definition srC0L : list expr := Eval vm_compute in s_regs (fst (fst rC0L)).

(* [comment removed for export] *)
Definition knLPp : list kentry := KRange (EVar 70) 0 67108863 :: KRange (EVar 38) 65536 67108864 :: knLP.
(* [comment removed for export] *)
Definition rPa := Eval vm_compute in runL (SCR [false; false] [] []) (SS 0x345cc srLP [] knLPp 71).
Definition srPa : list expr := Eval vm_compute in s_regs (fst (fst rPa)).
Definition knRDp : list kentry := Eval vm_compute in kn_after rPa knLPp.
(* [comment removed for export] *)
Definition rPb := Eval vm_compute in runL (SCR [false; true] [] []) (SS 0x345cc srLP [] knLPp 71).
Definition srPb : list expr := Eval vm_compute in s_regs (fst (fst rPb)).
(* [comment removed for export] *)
Definition want_x : expr := Eval vm_compute in nth 12 srPb (ELit 0).

(* [comment removed for export] *)
Definition srRe0 : list expr := sr_upd srRD (ridx 10) (EVar 72).
Definition knRe0 : list kentry := KRange (EVar 72) 1 65536 :: knRD.
Definition rRe_tk := Eval vm_compute in runL scr0 (SS 0xad438 srRe0 [] knRe0 73).
Definition srRe_tk : list expr := Eval vm_compute in s_regs (fst (fst rRe_tk)).
Definition knRe_tk : list kentry := Eval vm_compute in kn_after rRe_tk knRe0.
(* [comment removed for export] *)
Definition srRm0 : list expr := Eval vm_compute in sr_after_call_j srRe_tk (map ridx callee_kept) 73.
Definition rRm := Eval vm_compute in runL scr0 (SS 0x345c4 srRm0 [] knRe_tk 105).
Definition srRm : list expr := Eval vm_compute in s_regs (fst (fst rRm)).
(* [comment removed for export] *)
Definition len_x : expr := Eval vm_compute in nth 19 srRm (ELit 0).
(* [comment removed for export] *)
Definition srRf0 : list expr := sr_upd srRD (ridx 10) (ELit 0).
Definition rRe_ft := Eval vm_compute in runL scr0 (SS 0xad438 srRf0 [] knRD 73).
Definition srRe_ft : list expr := Eval vm_compute in s_regs (fst (fst rRe_ft)).
Definition knRe_ft : list kentry := Eval vm_compute in kn_after rRe_ft knRD.

(* [comment removed for export] *)
Definition srGL : list expr := Eval vm_compute in sr_upd srRe_ft (ridx 10) (ELit 0).
Definition knGbase : list kentry := cellC :: knLP.
Definition knG (lo hi : Z) : list kentry := KRange (EVar 70) lo hi :: knGbase.

(* [comment removed for export] *)
Definition knLPg : list kentry := KRange (EVar 70) 65536 33554432 :: KRange (EVar 38) 65536 33554432 :: knLP.
Definition rGa := Eval vm_compute in runL (SCR [true] [] []) (SS 0x345cc srLP [] knLPg 71).
Definition srGa : list expr := Eval vm_compute in s_regs (fst (fst rGa)).
Definition knGa : list kentry := Eval vm_compute in kn_after rGa knLPg.
(* [comment removed for export] *)
Definition cap2_x : expr := Eval vm_compute in nth 10 srGa (ELit 0).
(* [comment removed for export] *)
Definition srGb0 : list expr := Eval vm_compute in sr_after_call_j srGa (map ridx c_kept) 71.
Definition knGb0 : list kentry := Eval vm_compute in kn_blk2 81 ++ keep_alloc MSO [(48%nat, 65536%Z)] [] knGa.
Definition rGb := Eval vm_compute in runL scr0 (SS 0x345ec srGb0 [] knGb0 103).
Definition srGb : list expr := Eval vm_compute in s_regs (fst (fst rGb)).
(* [comment removed for export] *)
Definition srGc0 : list expr := Eval vm_compute in sr_after_call_j srGb (map ridx callee_kept) 103.
Definition knGc0 : list kentry := Eval vm_compute in keep_rd knGb0.
Definition rGc := Eval vm_compute in runL scr0 (SS 0x34608 srGc0 [] knGc0 135).
Definition srGc : list expr := Eval vm_compute in s_regs (fst (fst rGc)).
(* [comment removed for export] *)
Definition srGd0 : list expr := Eval vm_compute in sr_after_call_j srGc (map ridx c_kept) 135.
Definition knGd0 : list kentry := Eval vm_compute in keep_alloc MSO [] [] knGc0.
Definition rGd := Eval vm_compute in runL scr0 (SS 0x34610 srGd0 [] knGd0 167).
Definition srGd : list expr := Eval vm_compute in s_regs (fst (fst rGd)).
Definition knGd : list kentry := Eval vm_compute in kn_after rGd knGd0.

(* [comment removed for export] *)
Definition knLPr : list kentry := KRange (EVar 70) 67108864 67108864 :: KRange (EVar 38) 67108864 67108864 :: knLP.
(* [comment removed for export] *)
Definition scr_refuse : scripts := SCR [false; false; false; true; false] [] [].   (* [comment removed for export] *)
Definition rRa := Eval vm_compute in runQ scr_refuse (SS 0x345cc srLP [] knLPr 71).
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
  summG rC0L = (0xad434%Z, [], 70%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3462c%Z)]) /\ kn_after rC0L knC0 = cellR :: knC0
  /\ kdiff knLP knC0 = [] /\ kn_vars_lt 6 knLP6 = true
  /\ (nth 21 srC0L (ELit 0), nth 9 srC0L (ELit 0), nth 19 srC0L (ELit 0), nth 12 srC0L (ELit 0), nth 11 srC0L (ELit 0), nth 10 srC0L (ELit 0), nth 17 srC0L (ELit 0))
     = (ELit 65536, EVar 48, ELit 0, ELit 65536, ELit 759305, ELit 3, ELit 63)
  /\ summG rPa = (0xad434%Z, [SCBr false BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3462c%Z)])
  /\ summG rPb = (0xad434%Z, [SCBr true BC_LTU want_x (ELit 65536); SCBr false BC_EQ (EVar 70) (EVar 38)], 71%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3462c%Z)])
  /\ kn_after rPb knLPp = knRDp /\ knRDp = cellR :: knLPp
  /\ srPb = sr_upd srPa (ridx 12) want_x /\ srPa = sr_upd (sr_upd srRD (ridx 12) (ELit 65536)) (ridx 23) (EVar 48)
  /\ want_x = EAlu ALU_ADD (EVar 38) (EMd M_MUL (ELit (-1)) (EVar 70))
  /\ summG rRe_tk = (0xac48c%Z, [], 73%nat, []) /\ kn_after rRe_tk knRe0 = knRe0 /\ keep_rd knRe0 = knRe0
  /\ (nth 10 srRe_tk (ELit 0), nth 11 srRe_tk (ELit 0), nth 12 srRe_tk (ELit 0), nth 1 srRe_tk (ELit 0), nth 2 srRe_tk (ELit 0))
     = (EAlu ALU_ADD (EVar 48) (EVar 70), ELit 759305, EVar 72, ELit 0x345c4%Z, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRm = (0x345cc%Z, [], 105%nat, []) /\ len_x = EAlu ALU_ADD (EVar 70) (EVar 72)
  /\ (nth 9 srRm (ELit 0), nth 23 srRm (ELit 0), nth 21 srRm (ELit 0), nth 18 srRm (ELit 0), nth 2 srRm (ELit 0))
     = (EVar 48, EVar 48, EVar 38, EVar 2, EAlu ALU_ADD (EVar 0) (ELit (-128)))
  /\ summG rRe_ft = (0xad434%Z, [], 73%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x34640%Z)]) /\ knRe_ft = cellC :: knLP
  /\ (nth 10 srRe_ft (ELit 0), nth 17 srRe_ft (ELit 0)) = (ELit 3, ELit 57) /\ sr_vars_lt 71 srGL = true
  /\ summG rGa = (0x9dddc%Z, [SCBr true BC_EQ (EVar 70) (EVar 38)], 71%nat, [])
  /\ kn_after rGa knLPg = knLPg /\ nth 10 srGa (ELit 0) = cap2_x /\ nth 21 srGa (ELit 0) = cap2_x /\ cap2_x = EMd M_MUL (ELit 2) (EVar 70)
  /\ nth 1 srGa (ELit 0) = ELit 0x345ec%Z /\ nth 2 srGa (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGb = (0xac48c%Z, [], 103%nat, []) /\ kn_after rGb knGb0 = knGb0
  /\ (nth 10 srGb (ELit 0), nth 11 srGb (ELit 0), nth 12 srGb (ELit 0), nth 1 srGb (ELit 0)) = (EVar 81, EVar 48, EVar 70, ELit 0x34608%Z)
  /\ kdiff knGb0 knGc0 = []
  /\ summG rGc = (0x9dc9c%Z, [], 135%nat, []) /\ kn_after rGc knGc0 = knGc0 /\ nth 10 srGc (ELit 0) = EVar 48
  /\ nth 1 srGc (ELit 0) = ELit 0x34610%Z /\ nth 2 srGc (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit MSO)
  /\ summG rGd = (0xad434%Z, [], 167%nat, [SE (SA (EVar 0) (-136)) 8 (ELit 0x3462c%Z)])
  /\ (nth 10 srGd (ELit 0), nth 11 srGd (ELit 0), nth 12 srGd (ELit 0), nth 17 srGd (ELit 0), nth 9 srGd (ELit 0), nth 21 srGd (ELit 0), nth 19 srGd (ELit 0))
     = (ELit 3, ELit 759305, ELit 65536, ELit 63, EVar 81, cap2_x, EVar 70)
  /\ (s_pc (fst (fst rRa)), s_next (fst (fst rRa))) = (0xa0ffc%Z, 71%nat)
  /\ stdio_call 71 srRa knRa = Some scR /\ (sc_ret scR, sc_f scR, sc_fd scR, sc_s scR, sc_l scR) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z, ELit 0, ELit 0)
  /\ (sc_wb scR, sc_wp scR, sc_sp scR) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EVar 0) (ELit (-522)), EAlu ALU_ADD (EVar 0) (ELit (-576)))
  /\ summG rRb = (0x9bdf8%Z, [], 103%nat, s_log (fst (fst rRb))) /\ nth 10 srRb (ELit 0) = ELit 2.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0DrvG_defs ()) ["FPX_1"] "p%0p%1p%2p&0p;1p;2p;3p;4p;<g0000k10<Tg000Pj2\Tg0010j10Tg001Uj11Tg002:k107Tg002Zj12Tg0039j1:Tg004Gj34Tg004aj3LTg0061j16Tg006Oj3qTg007_j2yTg008oj2<Tg00:>k20?Tg00;Nk405Tg00<^j1;Tg00=lk30;Tg00?<j1MTg00?Zk30LTg00@hj4tTg00B:j4=Tg00BZk10^Tg00C<k40[Tg00DJm<0ZTg00E`k20ITg00FBj23Tg00F]j2NTg00G7j2pTg00HFj35Tg00Hfk20GTg00J3k20XTg00K?k10WTg00K]k30FTg00L@k10ETg00MLk30@Tg00NZj1oTg00Ogk10VTg00Q6j4VTg00QRk20TTg00R^k30=Tg00S;k10nTg00TGk10mTg00UUk30lTg00Vjk10kTg00X;k10jTg00YJk10iTg00ZZk10hTg00[ik10gTg00]8k10eTg00^Hk10dTg00_Xk10cTg00`hk10bTg00b5k30fTg00cEk30RTg00dSj2vTg00eck40DTf0R0#1#0p=D%10#0#0#0p=H%00#1p=9%10#0#0#6p=hg00f>R1f2R2f1R3P0C=p=Z%20#2p=]%20#2#2#2p>04%20#2#2#2#2#2#2#2p=R%M0,<3p>0C%00#0p=B%10#0#1#1p=l%00#0#6#;p=Gg00f\R4f3R5@0f23;50p=cf5R6f4R7P5g00glR8P2P3C=P0C=p=P%10#1#1#1#1#1#1#1p=n%10#1p=[%10#1#1#1p=j%10#1#1#0p=m%00#0#0#0p=E%00#0#0#0#0#0#0#0p=S%00#0#0#6p=>%00#0#0p=X%M2,<5?L30p=Wg00hKR9@0R30p=|%00#1#0#0p=}1<52?L30p=Q%60#;p=7%62,<5?L30p=_%60,<3p=x%00#6p>0`%10#6p>0:%00#0#0#0#6p=e%00#0#1#0p=w%10#1#1p>01%10#0#0p=^%60,v3p>0_%63/v0p>0Q%10#1#0#0p>0Pg00i7R:Aq523;50p=d%02#6/v3=5:0p=KA5:3095:2p=u1v23=5:0p>091<75?L23=5:0p=UAL523=5:0p>0O1v751v23=5:055:p>0NA5:3095:295:595:7p=@A5:30p>0Mg00jGR;,\0p=if7P;f6R<P;P6P;P;P;P7P5C=P2C=P3C=P0C=p=`P7P;P5P;P2P3C=P0C=p=ag00kUR=?530p=s%;0:0R93p=T%:3=5;0p>0A%:2%:3=5;055;p=fA5;3095;295;595;7p=IA5;30p>0KA4;30p=JP;P;P3P0C=p>08%00#0#1#1p>0J%00#Mp={A5;3095;2p>0]%10#M,<3p>0\%00#0#1#1#0#0#1#1p=z%05#M,<7?L23=5:0p=8AL<67AL523=5:055:p=r%M5,<7?L23=5:0p=?%M5,<7%63#;7L2=5:0p=Y%15#M,<7?L23=5:0p=AP5P;P;P;P2P3C=P0C=p>0HP7P8P1P5P2P3C=P0C=p>0Y1N;0p=bP7P51N23P0H0Dp=CP<P6P7P5P2P3P0H0DH0Dp=OP;P3g00lgP0CVp=gP;P3g00n4P0CVp=~P;P3g00oCP0CVp>00P;P3g010OP0CVp>03P;P3g011[P0CVp>06P;P3g012gP0CVp>0>%o3=420p>0SP;P3g0143P0CVp=kP2P;P3P0C=p>0UA4<67A4523/30'3p=F1330,32p>0BA4523/30p>0a%o2=453/30p>02&0<=R0,\1R5/\8R3&0<4R2'\R<P3P2P5g015?R7#0R6#1R9#0R>#1S00#DS01#D#H#9#D#hR?&07=R=5Z0S02g015dR@#2RA#2RB#2RC#2RD#2RE#2S03#]RF#2RG#2RH#2RI#2RJ#2RK$04RL#2S04#2RM#2S05#2RN#2S06#2S07#2#]$04RO#2RP#2RQ#2RR#2RS#2S08#2S09#2RT#2RU#]#RRV#]$04#R#RRW%:@R@%06RX#0RY#1S0:#0S0;#0S0<#0RZ+0CR[PF%17R\#0R]#1R^#BS0=#0S0>#1R_#1S0?#BS0@#0S0A#l#GR`&074R4CcRaEPS0BQ0B34&0<:RbAL[F`R`%:VRV%0YRc#0S0C#0S0D#0Rd#0S0E#0Re#0S0F#BRf#6Rg%1\Rh#1Ri#1S0G#1S0H#1S0I#1#nRj#[#jRk#1Rl#0#j#m#E#S#>3qS0J%6cRm,yVS0Kg016CRn,<VRo%EfRf#6Rp+0?S0L%Xf#ERf-0C@Rq%0fRr#6PoPpH05S0M%;nRs/<p%1^S0N#1S0O#0S0P#B#S#>PoPpH05S0QP@%0iS0R#0S0S#0S0TPFPsCWS0UP@%0hRh#0S0V#0Ri#0S0WPFPsCWS0XP@Q0>PFPsCWS0YP@%0]Ro#0S0Z#0R^#0S0[PFPsCWS0\P@%19Rt#0S0]#0S0^#0S0_PFQ0C#6S0`#;Ru,|@CWS0aP@%B>S0b#0RvPF%9_R_#}#9#GCWS0cP@%1XRw#0S0d#0S0e#0RxPF%66S0f#;R6CWS0gP@Q0DPF%6YRY#;Ry,|@CWS0hP@PiPF%1wRw#0Rz#[S0i#9#m#l#GCWS0j1y@mS0k%Ej#S#S#S#>Rj%0rR{#0R|#B#S#S#>S0l5q@S0m%6fRf-0?qS0nP@PnPFP6CQS0oP@PYPF%:ACQS0pP@PmPF%:BS0qCQS0rP@Q0Z#6S0sPFPsCQS0t%:CR}%Hr#S#S#>Rr7qjS0u%:DR~?qjrS0vPqPf1<}nRr%0vS0w#6H05S0xPqPf1<~nPmH05S0y1y}YS0z1y~YS0{%7\R\9LrFS0|P}PYPF%1e#E#GCQS0}P}PmPF%7XCQS0~P}Q0sPF%6iRi#;S0sCQS10P}Q0`PF%79S0`CQS11P}Q0bPF%7>S0bC_S12P}%6^S13PF%;mCQS141<}i@0;yCS15P}Q0DPF%7]C_S16P}PxPF%;gS17C_S18P}%6vS19PF%7tCQS1:P}Q0[PF%6oS1;#;C_S1<P}Q0W#6S1=PF%1tRt#6S1>#;CQS1?P}Q0TPFPsC_S1@P}PdPF%1oRo#7C_S1AP}PZPFP~C_S1BP}%0xR~PFPsC_S1CP}%BzS1DPFPsC_S1E%BtS1F#DRt#0S1G#B#S,xs%DoS1H#0S1I#X#E#>+0?S1J%1tRt#0S1K#m#ER]$0`S1L&0:]%1t#E#}$0:Rt%0oRo#0S1M#l#E#}$0:%1oRo#0#jR]#9#[Ri#e%1hRh#0S1N#1S1O#1S1P#0R^#0R>#BRX#9Re#0#}%1e#9#>Ps%1i#>RiPF%;i%1]R]#0Ri#9#H,xsPD%:ERE%1i#w&01]R]#e%^]%1o#ER]#0Ri#0Re#9RY#eRrPsPrPF%1>R>#DRr#0Rf#BRq#1#>Rj#;%^Y%1e#D#>Re1<se@0;yB%DiRi#B#>Re%1iRi#E+0_%^i%1]#D#9#>%^X#E%9>R>#9RX#9#>R]%1XRX#eRi1<si@0;yB%HX%1>R>#0RX#B#>+0Q%1XRX#X$0:%1X#>RXPsPXPFP}%1>R>#0R}#X%1}#>&0P>%eqRqPsPqPFQ17&01f#>Rf1<sf@0;yC%^r#E%1^R^#0#w#9#>+0Q%1^#j#H%1hS17#0S1Q#0S1R#0S1S#S#>PE%67S1T%6k&07:RkCd3K3u609jDU3K3KDU4093u609]3K3K3u3KDU3K3KH0ODU3KI0NS1U609p3uD@D@D@D@D@D@D@D@D@D@D@R]+0MS1VQ1V34S1WA4bkkS1Xg016aS1Yg017ARj;4jS1Z1\;;RE#iRh#iR^#iRr#iRC#iRfPCPrP^PhPE%;pRqPVPsPq%;tRtG`P\Q0H#7S1[DaS1\Q1\34S1]P3P2P5g017aS1^g018AS1_%:URUg0193R>%M7#;%:WR740L'|R}PqCtQ1^g019_S1`P7PUCt/s=RX's9Z0?%2WRWPaEPS1aQ1a54<S1bP3P2P5PjQ1_P}PqCt/sX9Z0?PWPaEPS1cQ1c54<S1d&01lRl#69q7nPUPp%6|R|P]Cd5u`S1eQ1e54bS1fQ1f&0<;R`PsQ0_#^#m#m#GS1g%M~S1h,T@RY%1cS1i#0S1j#0S1k#0S1l#0S1m#0S1n#E#GS1o%;eS1p%:IRe%:JRc%:KRKP6PVP\PtPsPsPsPsQ1[Q0qP7P\PUPtPV%:OS1q%:PS1r%:QS1s%:RS1t%:SQ08Q09&07;S1u-0AT3fDIDIDIDIRT-0K}DIDIDIS09Q0934S08PsQ1gPYQ1oQ1pPePcPKP6PVP\Pt20KqTDIDIDIS1gQ1g54`S1v1J}}S1wP3P2P5Q01#w#}#9#h=Z0=RT%2WRK#2RcP4EPRe=4<eS01%:KRKQ1TPpQ1VCdS1xQ1x54bS1yQ1yP^PhPE1|V7PtPK%[_R_#BRY#9#G%Md,T@RdG`S1zQ1z54rS1{P3P2P5%1Y#h=Z0=%2c#]S1|#2S1}#2S1~#2#]RY#2S20#2S21#2S22#2S23#2S24#2S25#2S26#2#]#RS27#2S28#2S29#2S2:#2S2;#]RSP4EPS2<Q2<54<S2=1|7KRK/JKS2>P^PhPEPVPVPUQ0qPdG`RR=4rRS2?P3P2P5Q02PcP[PFQ0@#1#E#GRcP4CcEPS0@Q0@54<S2@P[PFPcP]H0OS2AQ2A54bS2BQ0V#1Rc#7-08\S0VQ0V54ES2CQ1ZP3P2P5%DwS2D#mRw#[#l#hPjQ1`P7PUCt/s=5Z0PWP4EPRQ=4<QS1`P7Pp%6{R{PUPpP{P]CdCdR]=4b]S2EB0L>67R>/J>R{%l_#GR_/J_S2F1JddS2GP3P2P5PTQ2;P4EPRT=4<TS2H%:YRYPgQ0l1yYm00M]CdRm=4bmRgPhPE208YVP7Q0A#0RP#0#D#GDaRO=4^OS0AQ1XP3P2P5%9w$0J#h=Z0=%]S$04#R#R#RRSP4EPRw=4<wS0l1JVVS2I%^P#GRP/JPS2JQ2GP3P2P5Q02%RS#R#R#RPaEPRS=4<SS02PCPrP^PhPEP\PtPqQ1[PYG`S1[P>P7DaS2KQ2K54fS2L1\18S2MP1P8Q0w#1#n#hPWC=S2NQ2N34S2Og01:QS2P$0^S2QQ2PQ1G$01S1G#9#[S2R#>RYQ0f%1vS2S#[S2T#0#9#9#9#>S2UQ0:#1S0:#0S2V#BS2W#0S2X#MS2Y,T@RvQ0C#1S0C#0S2Z#1S2[#{,T@S2\PvQ19#;S19PsPs%0~S2]#0S2^#MS2_,T@R~Q2U#;P~Q1oQ1pQ1|Q1}Q1~%;YS1p%7zPsQ20#:Q21Q22Q23Q24Q25Q26%;iS20Q1T#;Q1P#H#w#D#GS1PPsPtPVQ1qQ1rQ1sQ1tQ27Q28Q29Q2:Q1u3f3f40]DIDI3f3f3fDI+0A3fDI-0AWQ1G#1Rt#0S1G#1S1}#1#>S1|,<sS1~PFQ0T#0S0T#{,T@S22%1tRt#0S21#E,xsS24PFPv%1tS23#eS26,<sS25PFPvQ2[-0\@PAQ0bP@Q0C#1Rt#0Ri#0S0CPAQ1MP@PiPA%7oRoP@%1tRtPA%1c#7RiP@PtPAQ1O#7S1OP@Q1mPAQ1HP@Q1lPAPoP@Q1k#1RtPA%0c#7P@PtPAPuP@Q1j#1Rt#0Rc#0S1jPAQ0^P@PcPAPiP@%1tRtPAPoP@PtPAQ1N#0S0^#7S1kP@Q1i#1Rt#0Ro#0Ri#0S1iPAQ0S#1P@PiPAQ0Z#1Ri#0#7P@%1oS0ZPAPuP@Q0e#1Ro#HPFQ0:#1Rc#1Rz#1#9#[#9#9P@%EoPFQ1pP@%HxPFQ0]P@Q2^PF%0l#D#9#7P@%XzPF%1l#jRlP@%XcS2^PFQ0d#1Rc#7P@Q2V#HPFQ2T#D#9#m#GP@Q0ZPAQ0=#7S0ZP@%1tRt#0Rz#0S2TPAQ0N#0Rx#7RoP@PzPAQ0sP@%1tRtPAQ0sP@PtPAQ13#;S13P@%0ZS0N#0RtPA%7iS2VP@Q0NPAQ0O#7S0OP@%1ZS0dPAPoP@Q0;#1RZ#1Rz#0S0;#0S0]PFPsP@PtPFPyP@%0ZRZ#0S1p#0S0:PFPyP@Q17#HPAPoP@Q2XPFQ2Z#0Ry$0P#l#7P@Q1Q#1Rt#1S1QPAQ0OP@Q1QPAQ2VP@%0tRtPAQ13P@PtPAQ0sP@Q1R#1RtPAQ0sP@PtPAPoP@Q1SPAQ0ZP@Q0<#1Ro#0S0<#0RtPFPsP@Q0H#EPF%;|S0HP@Q2_PFQ00#B#{S00,T@P@Q0dPAPuP@PtPAQ0R#1P@Q0<PAQ0G#0Rt#7P@%1oRoPAPuP@PoPAQ1kP@Q0:PAQ1OP@Q1pPAQ1=#;P@%1ZRZPAQ0P#7P@PZPAQ0=#1#7RZP@Q0]PAPuP@Q0;PAQ1N#7P@%1zRzPAPZP@PzPA%0xRx#7P@Q2YPA%1i#7P@Q2TPF&01lRl$0J#z#z#z#9#7P@Q1iPF%1l#j#nRl#0#n#n#7P@Q0I#XPFQ1I#[#z#z#GP@%ByPF%XcRc#D#w#9P@Q0FPFQ20P@Q0D#HPFPsP@Q0CPFP~P@Q1jPFQ22P@Q1nPFQ2D#0#{Ry,T@Q1G#0Ri#H,xsPFPs%eiRi,<sPFPsPsQ1K#BRz#HRZ#>RuPD%1l#n#n#7%0zRz#9Rl#H,xsS1KPFQ19%elRl,<sS19PFPv1<sYRoPDQ0`Q2]-0C@PFPsP@PcPFPsP@Q1DPFPsP@PyPFPsP@Q2WPFPsP@Q2^PFQ0_#{Ry,T@RcP@Q0NPFQ1^PBPnPFH0[RnP@Q1lPFPUP@Q0EPFP\P@%BtPFP7P@Q0TPFQ0qP@Q0^PFPVP@Q0WPFQ20P@PxPFQ2S#B#H#w#GP@Q0>PFPcP@Q1MPFPnP@Q1DPF%:NP@Q0wPFQ05#:P@Q00PF%:MP@PyPFQ0HP[PFQ07#:Q1h,<@PFQ06#:P@Q0[PFP6P@Q1FPFQ0?#1#D#D#D#GP7P|P|PUP|P|Q0JQ0KQ0LQ0MQ0QQ0UQ0XQ0YQ0\Q0aQ0cQ0gQ0hQ0jQ0kQ0mQ0nQ0oQ0pQ0rQ0tQ0uQ0vQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q11Q12Q14Q15Q16Q18Q1:Q1<Q1?Q1@Q1AQ1BQ1CQ1EQ1JPpPYQ2R#hPiQ1}#XQ1|Q21#^Q26Q23#^%1z#E%DZQ1LQ1U3K7Ku7Kl3K3KI0N3uD@D@D@D@D@D@D@D@D@D@D@CdCdD8D8FrDUDUD?D?D8D8D8D8D8D?D?D?D?D?D?D?DUD8D?FrFrDUFrD?D8D8D?D?DYD?D8D8DUDAD8DAD?DAD8DAD?DAD8DADYDADUD?D8DAD8DAD8DAD8DAD8D?D8D8D8D8DAD?DAD8DAD?DAD?D8DYD8DYD?DYD8DADYDAD8DADYDAD8DADYDAD8DADYFrFrN<0Z+0IRl;4lS1J1\11Ru/\1RZ#iRz#iRiPzPZPuP1P1P1Q2UPYC=Q0fC=PsPsDaRY;4YS0fPEPvQ2\P~H0HR~=4h~S2\P3P2P5P0Q0i#1#l#j#>P=Q2;I0YS2;PoPDQ0`Q1KPFPsQ19PFQ1PQ25PFPsQ24PFPsQ1~PFPsP4CcCcCcCcCcCcC=R4=4<4S1~1J66S24'3S25'3S1P'3S19'3S1K'3S0`'3S0i'3S2U'3S1E'3S1|'3S26,3gS1U'3S1L'3S23'3S21'3S1}'3S2R'3S1C'3S1B,3{S1A,3{S1@'3S1?'3S1<'3S1:'3S18'3S16'3S15'3S14'3S12'3S11'3RF'3RD'3Ro'3R='3Rv'3Rp'3R|'3RU'3R['3Ry'3Rn'3Rc'3Rx'3Rt'3R\'3P<Q0BQ1WP\PbQ1VQ1XPt1NbkRtQ1ZPxQ1Y/NjRxQ1]PcPfQ1\Q1bPnP<Q1aQ1dPyP<Q1cQ1fP[Q1e,NbR[Q1fPUP[Q08P|P`Q09Q1vPpP`Q1gQ1wPv%b}Q01P=1N<eQ1yPoQ1x,NbRoQ1yPDPoQ1{PFPrQ1zQ2=Q11P<Q2<Q2>Q12%bKQ2?Q141NrRQ2@Q15P<Q0@Q2BQ16PbQ2AQ2CQ18PEQ0VQ1ZQ1:PxQ1`Q1<1N<QQ2EQ1?PbP]P{Q1@%b>R]P{Q1AP]P{Q1BP]Q2FQ1C%b_Q2GQ2R%bdRdQ2HQ1}1N<TPgQ211NbmRmQ0AQ231N^OQ1XQ1LPtQ0lQ1U1N<wPgQ26PmQ2IQ1|%bVQ2JQ1E%bPQ2GQ2UPdQ02Q0iP<PSQ2LQ0`PfQ2KQ2OQ1KQ2MQ2NQ1JQ19Q2QPlQ0fQ1PPiPYQ2\Q25PhP~Q1~Q24P<P4%b6DCDCDCDCDCDCDCFOFOFOFOFOFOFODCFODCDCDCFODCDCFOFODCDCFODCDCDCFODCDCP<g01;gR4Q0BPbg01=3Rl,p4g01>>R4=5:lPbg01?KRd00GlPkQ1YQ03g01@W+0XPjPfPCPrP^PhPE1gNs1gGs1gMs1gJs1gIsG`1gHs1gLsDaQ1\P<g01AdP3P2P5Q1^Q1_g01BoRlPqCt/sX9Z0?PWPaEPP<g01D=RmP3P2P5PjQ1_PlPqCt/sX9Z0?PWPaEPPbg01EHRa,pmg01FURmPbPmA5:4aP`g01Gbg01HnRa&0W9R9Q1;g01J:R440F$0ERm<0@lP`Pag01JV@0@mqQ1>>0F94$0E<0@VP;PlP}P<g01KbR}#oPePbg01M0Re,p}PePb&0VePePrP^PhPE1~Hs1~Is1~Js1~As1~BsG`Q1zP<g01N=#oQ2<P;g01OHPKPrP^PhPE200GsQ07000s200NsQ04000s200BsG`PRP<g01PUQ0@Pbg01Qcg01S2=5:dPEP;PHg01T?RdPsCVP;PLPdPsCV+08Q0VQ1Yg01UN-0TWPjP<g01VZRj#oPQPbg01WeRQ,pjPQP;203Hsg01Y2RQP;203NsPQP;PQP>203As/J_203Bsg01Z@,T@R@'JP<g01[JR_PTPbg01\URT,p_PTP^PhPE206Hs206Is+08206Js206AsDaPOPbg01]bRO-0GTPkP<g01^oRk#oPwPb1pkOPO20>Hs/JV20>As/JP20>Bs/J@g01`:>0S<SPfPCPrP^PhPE1kHs1kIs1kJs1kLs1kGsG`1kNs1kMsDaPrP;Q1[PQC=>0UC7Q2MP1P8g01aER81\80R7g01bXRCg01ci40=80=0RQ$0n&0mQC=Q2NQ2Qg01e4g01f@60lWQ2Pg01gLRW+0IPiPzPZPuP1P1P1&0kW&0jWC=&0iWC=&0hW&0gWDaPYPhPE&0eW&0dW&0cWH0HP~P<g01hWR<#oP3P2Q2;B0=7C<:0=80$0bC=P;PHg01ibPsCV/J6FFFFFF40B40BH0aFFFFH0240BFFFFFFFFH02FFFFFFFFFFFFH02H02FFFFH02do"). Qed.

End FPX_1.
