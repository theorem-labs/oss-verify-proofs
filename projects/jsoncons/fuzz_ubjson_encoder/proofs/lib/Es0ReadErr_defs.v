(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Es0MainEntry SymDriveH4 Es0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Es0ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall4sc_lC13~~~K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2PXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs3srHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs3knHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs4scREC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0ReadErr_defs2rIC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition STOPS : list Z := [0xac48c; 0xaca0c; 0xacf80; 0xac390; 0x9b5a8; 0x9b734; 0x9f660; 0x9bdf8; 0xa0ffc]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0xec000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0xcb040; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; EVar 2; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].
Definition KEPT_RE : list nat := [2; 3; 4; 18]%nat.
Definition srRE0 : list expr := Eval vm_compute in sr_after_call_j srRE_base KEPT_RE 6.

(* [comment removed for export] *)
Definition knRE0 : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KRange (EVar 2) 0x7fff80000000 0x800000400000;
   KWr (SA (ELit 0) 0xb9000) 0x33000;
   KImg 0x10000 0xb95c0; KImg 0xb95c1 0xb9609; KImg 0xc9609 0xcaf70; KImg 0xeb048 0xeb068;
   KWord (SA (ELit 0) 0xcaf78) 8 (ELit 0xcaf78);
   KWord (SA (ELit 0) 0xcaf98) 4 (EVar 5);
   KImg 0xcafa4 0xcaff0; KImg 0xcaff8 0xcb010; KImg 0xcb018 0xcb030;
   KImg 0xcb040 0xcb050; KImg 0xeb080 0xeb2b0;
   KBlob (SA (ELit 0) 0xeb2b0) (ELit 8) 2;
   KImg 0xeb2b8 0xeb2c0; KImg 0xeb2d1 0xeb2d8; KImg 0xeb2e0 0xeb2e8; KImg 0xeb2f8 0xeb300;
   KWord (SA (ELit 0) 0xeb300) 8 (ELit 4096);
   KImg 0xeb308 0xeb338;
   KImg 0xeb808 0xec000;   (* [comment removed for export] *)
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x34770 srRE0 [] knRE0 39.
Definition rB := Eval vm_compute in run scr0 ssB0.
Definition srB : list expr := Eval vm_compute in s_regs (fst (fst rB)).
Definition knB : list kentry := Eval vm_compute in kn_after rB knRE0.
(* [comment removed for export] *)
Definition logM1 : list sentry :=
  [SE (SA (EVar 0) (-542)) 1 (ELit 32);
   SE (SA (EVar 0) (-544)) 2 (ELit 28271);
   SE (SA (EVar 0) (-552)) 8 (ELit 2338053693894893668);
   SE (SA (EVar 0) (-560)) 8 (ELit 7018141077071293539)].
Definition knC0 : list kentry := Eval vm_compute in fst (fst (carry logM1 knB [])).
Definition srC0 : list expr := Eval vm_compute in sr_after_call_j srB KEPT_MC 39.

(* [comment removed for export] *)
Definition ssC0 : sym_state := SS 0xa17d8 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xa17d8 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xa2348 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xa17d8 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xa17d8 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xa17d8 srH0 [] knH0 231.
Definition rH := Eval vm_compute in run scr0 ssH0.
Definition srH : list expr := Eval vm_compute in s_regs (fst (fst rH)).
Definition knH : list kentry := Eval vm_compute in kn_after rH knH0.
(* [comment removed for export] *)
Definition scRE : stdio_res := Eval vm_compute in
  match stdio_call 231 srH knH with Some r => r | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end.
Definition srI0 : list expr := Eval vm_compute in sc_sr scRE.
Definition knI0 : list kentry := Eval vm_compute in sc_kn scRE.

(* [comment removed for export] *)
Definition ssI0 : sym_state := SS (sc_ret scRE) srI0 [] knI0 263.
Definition rI := Eval vm_compute in run scr0 ssI0.
Definition srI : list expr := Eval vm_compute in s_regs (fst (fst rI)).
Definition knI : list kentry := Eval vm_compute in kn_after rI knI0.

Lemma itinerary_re :
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xac48c%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xacf80%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xac48c%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xac48c%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xac48c%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xa0ffc%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xa1ca8%Z, 0xb93b8%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x9bdf8%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Es0ReadErr_defs ()) ["FPX_1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10HTg000Pj2fTg0010j10Tg001Uj12Tg002:j1uTg002Zj3?Tg0034j11Tg003Sj1KTg004aj1;Tg005oj4aTg007Aj2ATg008Pj4{Tg009bj4zTg00;0j1CTg00;Nj3yTg00<\j19Tg00=:k103Tg00=\j3wTg00>jj3nTg00@:k40ETg00AHk20DTg00BXk200Tg00Chk30BTg00E8m<0?Tg00FNj2|Tg00G0j4DTg00GPj2FTg00Gkj2rTg00HEj3HTg00Hbj3pTg00J0k30=Tg00KEk10<Tg00LVk10;Tg00Mek108Tg00O5k109Tg00PEk10:Tg00QUk107Tg00Rdj35Tg00SDj3[Tg00TTj2\Tg00Udj4vTg00V?k304Tg00V\j1xTf0R0#2#0#0p=B%20#0p=6%00#2#0#0p=d%00#2#2#0p=T%00#9p=qg00WhR1f2R2f1R3P0CDp=L%20#2#2#2p=X%00#0#0#0p=7%00#0#0#9p=4%10#1p=e%10#1#1#1p=j%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p>01%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=ig00XFR4?w30p=bAp430p=@g00Y2R5?530p=I%90#;p=8g00ZDR6g00ZdS00P3P0Cap=o%00#0#0p=:%20#2#2#2#2#2#2#2p=R%20#2#2p=`%00#2p==%20#2p=>%00#0p=3%00#0#0#0#9p=Q%20#0#0#0p=G%10#1#1#1#1#1#1#1p>0Gg00[VR7%K2%K3=57035p=OA57309572p=g%K3=570p>02%00#Cp=l%20#0#0#2p=_%00#0#2#0p=^f3R8/A2?[30p>0F%20#2#0#0p=N%00#0#2#2p=M%00#0#0#0#0#0#0#0p=V%C0,A3p>0C%93/\0p=~%20#9p=mg00\dR9?530p>0Af4R:#0#9/\8%02#9/\3=590559p=c1A:8?[23=590p=<%03#9,\2=590p=}A59309592p=h%02#9/\3=590p=t1\:81\23=590559p>0@%08#C,A:?[23=590p=J%C8,A:%K37[2=590p=P%C8,A:%93#;7[2=590p=]%C8,A:?[23=590p=E%28#0#0#0#C,A:?[23=590p=UP7P7P3P0CDp=sP:P81r23P0Cvp=Wf6R;f5R<P:P8P2P3P0CvCvp>0>g00^4R=?H30p=YB04=30p=SP1P2%x3P0CDp=ZAH=30#xp>06P1P8P2P3CD=?:0p>05A?;<:A?823/F0'Fp=k&0H5R0,f1R8g00_GR3#0R2#2R<#0R;#2R:#BR>#0#6#d#T#qR?%u5R55L0R@;?@RA%2>#X#7#4=L05R>=?8>S01g00_lRBg00`LS02g00a>RC#1RD#1RE#eRF#1S03#1#eRG#e#jS04#1S05#jS06#1S07#1S08#1S09#1S0:#eS0;#1S0<#1S0=#1RH#1RI#1RJ#1RK#1RL#1RM$01#i#iRN#KROg00a]RP#;RQ'bRRPOCa%KERS/@O/APPDPBPQC{/I5'I9L0?RT=?8TS0>%23RU#2RV#2RW#0RX#2#8RY/oOP6g00b;S0?P6PCPFPOCz1bRQCa/I5'I9L0?RZ=?8ZS0@g00bmS0A%C3#;S0B;yO/@Y%93S0C#;R3'o/I59L0?R[=?8[S0D%:;R;#0S0E#2#R#6#q=L05R\=?8\S0Fg00cYR]$03S0G%2<R^#BS0H#6R_#0S0I#`R`#=#>S0J#4Ra%92S0K%2;Rb#>Rc#0#=#=#=#4Rd%KCRe%02R2#0Rf#2Rg#2Rh#0S0L#3S0M#0S0N#CS0O#;'@Ri1@eO%0fRj#2Rk#2Rl#2Rm#3S0P#C#;S0Q'@S0RPi%8;S0SPQPQ%22R2#0R;#0Rn#0S0T#0S0U#0S0V#0S0W#CS0X#;,@eRo%eN#j$01#i#i#iRN%;d%0kS0Y#3S0Z#3S0[#3#7#8%0URU#0Rk#2Rp#0Rq#2Rr#6#7Rs#6Rt#3#4S0\#;%1N#jRu%1uRu%1uRu%;aRv1bQRS0]%22R2#8'bRR,b3%juRu#K%1uRu%1uRu%1uRu%1uRu%1uRu%1uRu%0VRV#2S0^#0Rw#>Rx#3Ry#2Rz#=R{#0#>R|#QR}#;R~%6x#7Rx#6#G#8%1u#e$0GRu%1uRu%1uRu%1u%u73O3O9OLM9OJK9OHI7gQ7g33O3O3O5gQ3g+023O3g7go+02PQ%2`R`#0RI#2RH#2#4S0_PG%:XS0`#l#;,@eS0aPQ%2`R`#0RX#QPGPiPQ%2`R`#QS0bPGPiPe%2nRnPG%2;R;#0RK#>#6#T#6#8Pe%7nPGPvPeQ0TPGPRPeQ0WPGg00do%2WRW#2Rv#2Rn#2#RRJ#2RM#2#XRL#2#RRu#8S0W;wRPe%2hRhPGQ0WPe%:hS0WPG%8;PeQ0LPG%_c#>#G#8Pe%0gRg#2RcPGPQPe%0gRg#0S0L#0S0T#0R;PGQ0]Pe%:cRcPGPOPeQ0NPG%0jRh#2S0N#3RR#>#^#>#8PePgPGPQ%9M9nOPPe%:v#lPGPSH0FPeQ0XPG%3:#lR:#;,@ePe%6mPDPhPeP;PE%2URU#2R;#6#T#XPePcPG%0hRh#2Rc#>#^#T#X#=#N#_#N#_#_#=#^#7#T#dPeQ0OPG%3kRk#2#=#_#=#=#>#^#^#7#M#6#6#T#_#T#N#T#M#8PeQ0PPG%`uRu#M#M#M#M#M#M#M#=#8Pe%7lPG%2u#X#RRu#0#R#RPe%:nPG%BpRp#N#N#N#N#NPe%3RPG%3KRK#G#_Pe%3hRh#3RRPGP~Pe%:cPGPQPeQ0NPGPoPeQ0YPGQ0aPeQ0[PG%B2#lRo#;,@ePQ%0IRI#2#4PGPQPQ%QIRIPGPQPQ%2_R_#0Rc#3Rn#GRl#4RmPF%2u#R#R#8PQ%0nRn#=Ru#2#4PGQ0SPQ%QuRuPGPiPQPaPF%8<PeQ0VPGPQPePKPGPQPe%02R2#3RKPGPQPePoPGPQPeQ0MPGPQPeQ0WPG%:^#lR^#;,@eRoPeQ0TPGPBPEPPPGH0ER<PeQ0ZPGQ0=PePhPGQ0<Pe%:WPGQ0;PeQ0`PGPSPe%3wPGQ05Pe%7VPGP~Pe%:;PG%^b#7#GPe%:URUPGPoPe%0qRqPGP<PePKPGQ08PeQ0EPGQ07PeP:PGQ06#KPeP^PGPSPeQ0LPGQ0:PeQ0UPGQ09Pe%3kPGQ04PeQ0HPG%`U#6#6#G#8%9j-0De%7J#V#V#V#4RJ%3RRR#7Rj#:#7RU#0Rk#7#V#V#45ne20CeU%9U+00%Gk#V#V#49nSJQ0I#:#7#4,AQ%:p#7#4+001~jaQ0J#6PI%:HQ0_%BXQ0b%B`Pu%2n#7Pm%6l%>c#6#7Rc#q%mc%2_#7#d#m%6q#>#7#d#m%0r#XRr#=#>Rq#Q%3yRy#=R_#0#d%2_#=#4PQ%2q#4RqPG%;qPQ%2rRr#0Rq#0#>#4PFQ03#KR_%2q#^%`rRr#Q%Br%0sRs#=Rr#Q%Br%2s#6#4Q0\%Gt%By#71AQ}%8f<0BE%G|%2{R{#0R|#3#4'~%2|R|#:#m%B|%2{R{#0R|#:%2|#4%N{%BzRz#3R{#QR|PQP|PG%8R%B{%`z#4%0x#dQ0^#G#V#4Q0C%9L5n_%u9+0ADcD<Dc3}3h7t}3}3tDcD<D<3tI0@DcDcDc3h3h3hDJDPDPDPD<D<DPDPDJDJD]DEDPDEDPDPDPDEDEDED<DJDEDED<D<D<D<D<D<DEDUDUDEDED]D]D]DJD<D]D]D]D<3hDUDJDJDJDUDUDJDUDJDUDEDUD<D<D<N<0?,|]R};?}R91f11R_/f1RLP_P1P1P1PdPaCDQ0KCDRa;?aRd1f77Rx/f7RzPxP7Q0R,siPQCDR{;?{RR%`2#6#>#X#4=L05R2=?82RG'FR|'FRE'FRf'FRy'FRt'FRs'FRr'FRq,FA1r8@RcPAPqPcQ01PrP8P>Q0>PsP8PTQ0@PtP8PZQ0DPyP8P[Q0FPfP8P\P9PEQ0GP}PdP|PLPaPRPGPzP{1r82DWDWDWDWDWDWDWDWK0>P81f=0R=g00e[R{g00fl3HRG,Y01S0G5Z0P@P8g00h99H={RG,Y01S0G5Z0P@P8g00iF9H={R@,Y01S0@5Z0P>P8g00jS9H={R>,Y01S0>5Z0PBQ02g00k`R>=w4QR@P>CaAp4S>/APPDPBPQC{/I5'I9L0?P8g00lm9H={RB,Y01S0B5Z0P6Q00PYP>CaP6Q0?P6PCPFP>Cz1b@QCa/I5'I9L0?P8g00n:9H={R@,Y01S0@5Z0Q0AQ0B;y>/@Y/o3/I59L0?P8g00oG9H={R?,Y01S0?5Z0P\Q0Gg010Tg011b60=Ng0130RN,|]PLP_P1P1P1&0<N&0;NCD&08NCDPaPzPxP7&09N&0:N's&07NCDPxP7Ap4e>Q0Q'@,siPQCDP8P0g014?9H={R{-0601S0{P2I05FkFkFkFkFkdo"). Qed.


End FPX_1.
