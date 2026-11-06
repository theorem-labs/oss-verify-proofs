(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry Es0LibStdioCall DrvKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0Drv_defs () := "K47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6DrvKit7ksubl_bC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Es0MainEntry7kn_mainC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs5kn_d0C13~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs3srBC13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib7Numbers7BinNums8positive03I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs2rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs2rBC13~~~K47Corelib7Numbers7BinNums1Z01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Es0Drv_defs3MSOC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xac48c; 0xaca0c; 0xacf80; 0xac390; 0x9bdf8; 0xa0ffc; 0x9dddc; 0x9dc9c; 0x349e4; 0x3499c]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xb9000) 0x33000;
   KImg 0x10000 0xb95c0;
   KImg 0xb95c1 0xb9609; KImg 0xc9609 0xcaf70; KImg 0xeb048 0xeb068;
   KWord (SA (ELit 0) 0xcaf78) 8 (ELit 0xcaf78);
   KWord (SA (ELit 0) 0xcaf98) 4 (EVar 5);
   KImg 0xcafa4 0xcaff0; KImg 0xcaff8 0xcb010; KWord (SA (ELit 0) 0xcb010) 8 (ELit 0xeb308); KImg 0xcb018 0xcb030;
   KBlob (SA (ELit 0) 0xcb030) (ELit 8) 2;
   KImg 0xcb040 0xcb050; KImg 0xcb058 0xcb0c8; KImg 0xeb080 0xeb2a8; KImg 0xeb2a8 0xeb2b0;
   KBlob (SA (ELit 0) 0xeb2b0) (ELit 8) 2;
   KImg 0xeb2b8 0xeb2c0;
   KImg 0xeb2d1 0xeb2d8; KWord (SA (ELit 0) 0xeb2d8) 8 (EVar 3);
   KImg 0xeb2e0 0xeb2e8; KImg 0xeb2f8 0xeb300; KWord (SA (ELit 0) 0xeb300) 8 (ELit 4096);
   KImg 0xeb308 0xeb338; KBlob (SA (ELit 0) 0xeb338) (ELit 8) 3; KImg 0xeb340 0xeb448; KImg 0xeb7f0 0xec000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Es0Drv_defs ()) ["FPX_1"] "p;2p;3g0000j22Tg000Jj21Tg001Sj30Tg001mR0g002MR1'2g002mg004<'1=001do"). Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x34544 sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xad438 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xcaf9c); (0xcafa0, 0xeb448); (0xeb7f0, 0xec000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xb2000, 0xb9000); (0xb9000, 0xec000)]%Z.
(* [comment removed for export] *)
Definition keep_alloc (so : Z) (bls : list (nat * Z)) (vbnd : list (nat * Z)) (kn : list kentry) : list kentry :=
  kn_keep 0 so 16384 bls vbnd [3%nat; 4%nat] IMG_CLIENT IMG_RW kn.
(* [comment removed for export] *)
Definition MSO : Z := -128.
Definition keepB : list kentry := Eval vm_compute in keep_alloc MSO [] [] knB.
(* [comment removed for export] *)
Definition kn_blk (v : nat) (n : Z) : list kentry :=
  [KRange (EVar v) 4096 (2 ^ 47 - 8388608 - n); KAlign (EVar v) 16; KWr (SA (EVar v) 0) n;
   KDisj (SA (EVar 0) (-8388608)) 16777216 (SA (EVar v) 0) n;
   KDisj (SA (ELit 0) 0x10000) 0xdc000 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xad434%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0x9dddc%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0Drv_defs ()) ["FPX_1"] "p;1p;2p;4p;3g005Hj1GTg005hj24Tg006Hj13Tg006mj1=Tg007Kj1ATg007kj42Tg001Sj36Tg008Kj17Tg0090j1;Tg00:>j1FTg00;Lj1KTg00;jj3ETg00=8j2@Tg0000j2>Tg00=Sj4DTg00=nj3<Tg00>Kj1CTg00?Wj3BTg00@4j1JTg00AAj1?Tg00A`j4ITf0R0#7#3p=H%70#7p=9%30#7p=8%30#3p=1f2g00B<R1f1R2P0C2p=5%?0#?p=0P1P2g00CJP0CIp=:g00DTR0g00E2R2#GR3'4R4P0P3g00FDR5#3R6#H#9#8#8#1#1#9#8#1#=%A2R2C2R7;67g00FiR8#GR9,44R:P4P9P0P3%36R6#7#9#8#9#8#9#8#9#1#=P2C2%A8C2R8;68R21411R;/41R</41R=/41R>P1P1%36#1#1R6#3#1#1#1#1#=#;R?P?C2%75#=#;55;g00H9R5#0R?#F55<R@g00HXRA%F5R5%K6#;3E55=R6;66RB'@1>47P2PB1>:81>>6CDCDP0P3g00IDR61463RBg00JWR2g00Kh3<RC7<3#CAB63CC2=647P4P9P0P3g00M19<B2R29<63RB#CAB632C2%JBC2=6:8P1P1%0?#0#0#0R1g00N:#;R8':%01#0#0#0R1#0R:#?/:8C21::855;1:1855<1:?855=g00NX#;9EA595=@56>'@'@do"). Qed.

End FPX_1.
