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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Eu0MainEntry Eu0LibStdioCall DrvKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0Drv_defs () := "K47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6DrvKit7ksubl_bC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<Eu0MainEntry7kn_mainC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs5kn_d0C13~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4prod01K47Corelib7Numbers7BinNums8positive01K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3fstC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25s_logC13~~~K47Corelib4Init9Datatypes3nat02C47Corelib5Lists7ListDef3nthI89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs3srBC13~~~I47Corelib7Numbers7BinNums1Z00I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib7Numbers7BinNums8positive03I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26sentry00C13~~~K47Corelib4Init9Datatypes3nat01K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs2rAC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs2rBC13~~~K47Corelib7Numbers7BinNums1Z01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;Eu0Drv_defs3MSOC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition STOPS : list Z :=
  [0xae008; 0xae588; 0xaeafc; 0xadf0c; 0x9d974; 0xa2b78; 0x9f958; 0x9f818; 0x34eec; 0x34ea4]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).

(* [comment removed for export] *)
Definition c_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition kn_image_d : list kentry :=
  [KWr (SA (ELit 0) 0xba000) 0x34000;
   KImg 0x10000 0xbb140;
   KImg 0xbb141 0xbb189; KImg 0xcb189 0xccaf0; KImg 0xecbc8 0xecbe8;
   KWord (SA (ELit 0) 0xccaf8) 8 (ELit 0xccaf8);
   KWord (SA (ELit 0) 0xccb18) 4 (EVar 5);
   KImg 0xccb24 0xccb70; KImg 0xccb78 0xccb90; KWord (SA (ELit 0) 0xccb90) 8 (ELit 0xece88); KImg 0xccb98 0xccbb0;
   KBlob (SA (ELit 0) 0xccbb0) (ELit 8) 2;
   KImg 0xccbc0 0xccbd0; KImg 0xccbd8 0xccc48; KImg 0xecc00 0xece28; KImg 0xece28 0xece30;
   KBlob (SA (ELit 0) 0xece30) (ELit 8) 2;
   KImg 0xece38 0xece40;
   KImg 0xece51 0xece58; KWord (SA (ELit 0) 0xece58) 8 (EVar 3);
   KImg 0xece60 0xece68; KImg 0xece78 0xece80; KWord (SA (ELit 0) 0xece80) 8 (ELit 4096);
   KImg 0xece88 0xeceb8; KBlob (SA (ELit 0) 0xeceb8) (ELit 8) 3; KImg 0xecec0 0xecfc8; KImg 0xed370 0xee000;
   KRange (EVar 5) 1 4194303;
   KImg 0 0x1000].
Definition kn_d0 : list kentry := kn_stack ++ kn_auxv ++ kn_image_d.

Lemma kn_d0_sub : ksubl_b kn_main kn_d0 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0Drv_defs ()) ["FPX_1"] "p;2p;3g0000j22Tg000Jj21Tg001Sj30Tg001mR0g002MR1'2g002mg004<'1=001do"). Qed.

(* [comment removed for export] *)
Definition ssA0 : sym_state := SS 0x34a4c sr_main [] kn_d0 38.
Definition rA := Eval vm_compute in run scr0 ssA0.
Definition srA : list expr := Eval vm_compute in s_regs (fst (fst rA)).
Definition knA : list kentry := Eval vm_compute in kn_after rA kn_d0.

(* [comment removed for export] *)
Definition srB0 : list expr := sr_upd srA (ridx 10) (ELit 3).
Definition ssB0 : sym_state := SS 0xaefb4 srB0 [] knA 38.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_CLIENT : list (Z * Z) := [(0x10000, 0xccb1c); (0xccb20, 0xecfc8); (0xed370, 0xee000)]%Z.
(* [comment removed for export] *)
Definition IMG_RW : list (Z * Z) := [(0xb4000, 0xba000); (0xba000, 0xee000)]%Z.
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
   KDisj (SA (ELit 0) 0x10000) 0xdcdb0 (SA (EVar v) 0) n].
Definition knC0 : list kentry := Eval vm_compute in kn_blk 48 65536 ++ keepB.
Definition srC0 : list expr := sr_after_call_j srB (map ridx c_kept) 38.

(* [comment removed for export] *)
Lemma drv_itinerary_ok :
  (s_pc (fst (fst rA)), snd (fst rA)) = (0xaefb0%Z, [])
  /\ (s_pc (fst (fst rB)), snd (fst rB), s_log (fst (fst rB))) = (0x9f958%Z, [], [])
  /\ (nth 10 srB (ELit 0), nth 21 srB (ELit 0), nth 20 srB (ELit 0), nth 18 srB (ELit 0), nth 2 srB (ELit 0))
     = (ELit 65536, ELit 65536, ELit 3, EVar 2, EAlu ALU_ADD (EVar 0) (ELit MSO)).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0Drv_defs ()) ["FPX_1"] "p;1p;2p;4p;3g005Hj1GTg005hj26Tg006Hj14Tg006mj1=Tg007Kj1ATg007kj42Tg001Sj38Tg008Kj1:Tg0090j19Tg00:>j1FTg00;Lj1JTg00;jj3ETg00=8j2@Tg0000j2?Tg00=Sj4DTg00=nj3<Tg00>Kj1CTg00?Wj3BTg00@4j1ITg00AAj1>Tg00A`j4HTf0R0#:#4p=7%:0#:p=3%40#4p=0f2g00B<R1f1R2P0C2p=5%>0#>p=1P1P2g00CJP0CHp=;g00DTR0g00E2R2#GR3'6R4P0P3g00FDR5#4R6#7#3#7#3#3#7#3#0#0#=%A2R2C2R7;87g00FiR8#GR9,64R:P4P9P0P3%46R6#3#3#3#0#7#7#:#7#0#=P2C2%A8C2R8;88R21611R;/61R</61R=/61R>P1P1%46#0#0R6#4#0#0#0#0#=#9R?P?C2%:5#=#955;g00H9R5#1R?#F55<R@g00HXRA%F5R5%J6#93E55=R6;86RB'@1?47P2PB1?:81?>6CDCDP0P3g00IDR61663RBg00JWR2g00Kh3<RC7<3#CAB63CC2=847P4P9P0P3g00M19<B2R29<63RB#CAB632C2%IBC2=8:8P1P1%1?#1#1#1R1g00N:#9R8';%11#1#1#1R1#1R:#>/;8C21;:855;1;1855<1;?855=g00NX#99EA595=@58>'@'@do"). Qed.

End FPX_1.
