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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import RunEnv
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib Eu0MainEntry SymDriveH4 Eu0LibStdioCall.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Eu0ReadErr_defs () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr02C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX25saddr01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr07C13~~~K47Corelib7Numbers7BinNums1Z03K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr05C13~~~K47Corelib7Numbers7BinNums1Z02I47Corelib4Init9Datatypes6option00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr04C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry06C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr08C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry05C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry07C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry03C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res01C13~~~K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C47Corelib4Init9Datatypes3fstK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr03C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall:stdio_callC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall6sc_retC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_fC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_fdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall5sc_wpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall4sc_lC13~~~K47Corelib4Init9Datatypes4list02K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry01C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry04C13~~~K47Corelib4Init5Logic3and01C47Corelib4Init9Datatypes3sndC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24s_pcC13~~~I47Corelib7Numbers7BinNums1Z00K4ELinuxProcessSemantics5Riscv5Instr5aluop01I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX28sidecond00C13~~~K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX24expr00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX26kentry00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX29sym_state00C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01K4ELinuxProcessSemantics5Riscv5Instr;branch_cond04K4ELinuxProcessSemantics5Riscv5Instr5mulop01I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0LibStdioCall9stdio_res00C13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8SymExec23SX27scripts00C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rBC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rCC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rDC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rEC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2PXC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rFC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rGC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs3srHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs3knHC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs4scREC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0ReadErr_defs2rIC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


Definition STOPS : list Z := [0xae008; 0xae588; 0xaeafc; 0xadf0c; 0x9d124; 0x9d2b0; 0xa11dc; 0x9d974; 0xa2b78]%Z.
Definition FUEL : nat := 5000.
Definition scr0 : scripts := SCR [] [] [].
Definition run (scr : scripts) (ss : sym_state) := sym_exec RSEGS FUEL true STOPS scr ss [].
Definition kn_after (r : sym_state * list sidecond * scripts) (kn : list kentry) : list kentry :=
  fst (fst (carry (s_log (fst (fst r))) kn [])).
Definition KEPT_MC : list nat := map ridx callee_kept.     (* [comment removed for export] *)
Definition KEPT_CS : list nat := map ridx callee_saved.    (* [comment removed for export] *)
Definition IHI : Z := 0xee000.
Definition BUF_LO : Z := -560.
Definition BUF_HI : Z := -480.

(* [comment removed for export] *)
Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

(* [comment removed for export] *)
Definition srRE_base : list expr :=
  [ELit 0; ELit 0; spx (-128); ELit 0x10800; ELit 0xccbc0; ELit 0; ELit 0; ELit 0;
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
   KWr (SA (ELit 0) 0xba000) 0x34000;
   KImg 0x10000 0xbb140; KImg 0xbb141 0xbb189; KImg 0xcb189 0xccaf0; KImg 0xecbc8 0xecbe8;
   KWord (SA (ELit 0) 0xccaf8) 8 (ELit 0xccaf8);
   KWord (SA (ELit 0) 0xccb18) 4 (EVar 5);
   KImg 0xccb24 0xccb70; KImg 0xccb78 0xccb90; KImg 0xccb98 0xccbb0;
   KImg 0xccbc0 0xccbd0; KImg 0xecc00 0xece30;
   KBlob (SA (ELit 0) 0xece30) (ELit 8) 2;
   KImg 0xece38 0xece40; KImg 0xece51 0xece58; KImg 0xece60 0xece68; KImg 0xece78 0xece80;
   KWord (SA (ELit 0) 0xece80) 8 (ELit 4096);
   KImg 0xece88 0xeceb8;
   KImg 0xed388 0xee000;   (* [comment removed for export] *)
   KRange (EVar 5) 1 4194303].

(* [comment removed for export] *)
Definition ssB0 : sym_state := SS 0x34c78 srRE0 [] knRE0 39.
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
Definition ssC0 : sym_state := SS 0xa3354 srC0 [] knC0 71.
Definition rC := Eval vm_compute in run scr0 ssC0.
Definition srC : list expr := Eval vm_compute in s_regs (fst (fst rC)).
Definition knC : list kentry := Eval vm_compute in kn_after rC knC0.
Definition srD0 : list expr := Eval vm_compute in sr_after_call_j srC KEPT_MC 71.

(* [comment removed for export] *)
Definition ssD0 : sym_state := SS 0xa3354 srD0 [] knC 103.
Definition rD := Eval vm_compute in run scr0 ssD0.
Definition srD : list expr := Eval vm_compute in s_regs (fst (fst rD)).
Definition knD : list kentry := Eval vm_compute in kn_after rD knC.
Definition PX : expr := EVar 113.
Definition knE0 : list kentry := KRange PX 0 131071 :: kn_cut 0 (-1152) (-1120) IHI knD.
Definition srE0 : list expr := Eval vm_compute in sr_after_call_j srD KEPT_CS 103.

(* [comment removed for export] *)
Definition ssE0 : sym_state := SS 0xa3ec4 srE0 [] knE0 135.
Definition scrE : scripts := SCR [false] [ELit 0] [].
Definition rE := Eval vm_compute in run scrE ssE0.
Definition srE : list expr := Eval vm_compute in s_regs (fst (fst rE)).
Definition knE : list kentry := Eval vm_compute in kn_after rE knE0.
Definition srF0 : list expr := Eval vm_compute in sr_after_call_j srE KEPT_MC 135.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ssF0 : sym_state := SS 0xa3354 srF0 [] knE 167.
Definition scrF : scripts := SCR [true; true] [] [].   (* [comment removed for export] *)
Definition rF := Eval vm_compute in run scrF ssF0.
Definition srF : list expr := Eval vm_compute in s_regs (fst (fst rF)).
Definition knF : list kentry := Eval vm_compute in kn_after rF knE.
Definition knG0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knF.
Definition srG0 : list expr := Eval vm_compute in sr_after_call_j srF KEPT_MC 167.

(* [comment removed for export] *)
Definition ssG0 : sym_state := SS 0xa3354 srG0 [] knG0 199.
Definition scrG : scripts := SCR [true] [] [].         (* [comment removed for export] *)
Definition rG := Eval vm_compute in run scrG ssG0.
Definition srG : list expr := Eval vm_compute in s_regs (fst (fst rG)).
Definition knG : list kentry := Eval vm_compute in kn_after rG knG0.
Definition knH0 : list kentry := Eval vm_compute in kn_cut 0 (-541) BUF_HI IHI knG.
Definition srH0 : list expr := Eval vm_compute in sr_after_call_j srG KEPT_MC 199.

(* [comment removed for export] *)
Definition ssH0 : sym_state := SS 0xa3354 srH0 [] knH0 231.
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
  (s_pc (fst (fst rB)), snd (fst rB)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst rC)), snd (fst rC)) = (0xae008%Z, [])
  /\ (s_pc (fst (fst rD)), snd (fst rD)) = (0xaeafc%Z, [])
  /\ (s_pc (fst (fst rE)), snd (fst rE))
     = (0xae008%Z, [SCBr false BC_LT (EAluw ALU_ADD PX (ELit 0)) PX;
                    SCReadBase (SA (EAlu ALU_ADD (EVar 2) PX) 0) 1 false (ELit 0)])
  /\ (s_pc (fst (fst rF)), snd (fst rF))
     = (0xae008%Z, [SCBr true BC_GEU (ELit 61) PX;
                    SCBr true BC_GE (EExt true 0 4 PX) (EAluw ALU_ADD (EAluw ALU_ADD PX (ELit 0)) (ELit 0))])
  /\ (s_pc (fst (fst rG)), snd (fst rG))
     = (0xae008%Z, [SCBr true BC_GEU (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) PX) (ELit 61)) (ELit 1)])
  /\ (s_pc (fst (fst rH)), snd (fst rH)) = (0xa2b78%Z, [])
  /\ stdio_call 231 srH knH = Some scRE
  /\ (sc_ret scRE, sc_f scRE, sc_fd scRE) = (0xa3824%Z, 0xbaf38%Z, 2%Z)
  /\ (sc_wb scRE, sc_wp scRE, sc_l scRE) = (EAlu ALU_ADD (EVar 0) (ELit (-560)), EAlu ALU_ADD (EAlu ALU_ADD (EVar 0) PX) (ELit (-540)), ELit 0)
  /\ (s_pc (fst (fst rI)), snd (fst rI)) = (0x9d974%Z, []).
Proof.
ltac2:(KReplay.run1 (kr_t_Eu0ReadErr_defs ()) ["FPX_1"] "p%0p&0p;1p;2p;3p;4p;<g0000k10ITg000Pj2dTg0010j10Tg001Uj11Tg002:j1sTg002Zj3>Tg0034j12Tg003Sj1ETg004aj19Tg005oj4bTg007Aj2ATg008Pj4}Tg009bj4{Tg00;0j1CTg00;Nj3zTg00<\j17Tg00=:k104Tg00=\j3xTg00>jj3mTg00@:k40FTg00AHk20ETg00BXk201Tg00Chk30CTg00E8m<0@Tg00FNj2|Tg00G0j4DTg00GPj2FTg00Gkj2uTg00HEj3GTg00Hbj3pTg00J0k30>Tg00KEk10=Tg00LVk10<Tg00Mek10;Tg00O5k10:Tg00PEk109Tg00QUk108Tg00Rdj35Tg00SDj3\Tg00TTj2^Tg00Udj4oTg00V?k305Tg00V\j1yTf0R0#1#0p=4%00#0#0#0p==%00#0#0#1p=v%00#0#0#7p=6g00WhR1f2R2f1R3P0CDp=I%00#1p=<%10#1#1#1p=K%00#7p=n%20#2p=e%20#2#2#2p=i%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p>02%20#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2#2p=hg00XFR4?x30p=cAp430p=Bg00Y2R5?530p=J%70#9p=;g00ZDR6g00ZdS00P3P0Cbp=q%00#0p=3%00#1#1#0p=X%10#1p=@%10#1#0#0p=H%00#0#1#0p=N%10#0#0#1p=Z%00#0#0#0#7p=Q%00#0#1#1p=M%10#0#0#0p=Y%20#2#2#2#2#2#2#2p>0Hg00[VR7%E2%E3=57035p=PA57309572p=f%E3=570p>03%00#0#0p=:%00#Cp=j%10#1#1#1#1#1#1#1p=`%00#1#0#0p=_f3R8/A2?\30p>0G%10#1#1p=w%10#0#0p=O%00#0#0#0#0#0#0#0p=L%C0,A3p>0D%73/^0p>00%10#7p=lg00\dR9?530p>0Bf4R:#0#7/^8%02#7/^3=590559p=a1A:8?\23=590p=8%03#7,^2=590p=~A59309592p=g%02#7/^3=590p=t1^:81^23=590559p>0A%C8,A:%73#97\2=590p=V%C8,A:%E37\2=590p=W%08#C,A:?\23=590p=U%C8,A:?\23=590p=?%18#0#0#0#C,A:?\23=590p=SP7P7P3P0CDp=rP:P81u23P0Cop=Tf6R;f5R<P:P8P2P3P0CoCop>0?g00^4R=?G30p=[B05=30p=RP1P2%y3P0CDp=]AG=30#yp>07P1P8P2P3CD=>:0p>06A>;<:A>823/F0'Fp=k&0I5R0,d1R8g00_GR3#0R2#1R<#0R;#1R:#1#4R>#0#=#v#6R?%s5R55I0R@;>@RA%1>#<#<#K#4#n=I05R>=>8>S01g00_lRBg00`LS02g00a>RC#2RD#2RE#eRF#2S03#2#eRG#e#iS04#2S05#iS06#2S07#2S08#2S09#2S0:#eS0;#2S0<#2S0=#2RH#2RI#2RJ#2RK#2RL#2RM$02#h#hRN#EROg00a]RP#9RQ'cRRPOCb%EERS/BO/APPDPBPQC}/J5'J9I0?RT=>8TS0>%13RU#1RV#1RW#0RX#1#;RY/qOP6g00b;S0?P6PCPFPOC{1cRQCb/J5'J9I0?RZ=>8ZS0@g00bmS0A%C3#9S0B;zO/BY%73S0C#9R3'q/J59I0?R[=>8[S0D%3;R;#1R\#<R]#X#K#6=I05R^=>8^S0Eg00cYR_$04S0F%1<R`#4Ra#1S0G#0S0H#KRb#0Rc#<#@S0I#6Rd%72S0J%H\R\#v#N#nRe%ECRf%02R2#0Rg#1Rh#1Ri#0S0K#3S0L#0S0M#CS0N#9'BRj1BfO%0gRk#1Rl#1Rm#1Rn#3S0O#C#9S0P'BS0QPj%0;S0R#;S0SPQPQ%12R2#0R;#0Ro#0S0T#0S0U#0S0V#0S0W#CS0X#9,BfRp%eN#i$02#h#h#hRN%9e%0lS0Y#3S0Z#3S0[#3#=#;%0URU#0Rl#1Rq#ZRr#<Rs#1Rt#1S0\#4S0]#3#6S0^#9%2N#iRu%2uRu%2uRu%9dS0_1cQRS0`%12R2#;'cRR,c3%iuRu#E%2uRu%2uRu%2uRu%2uRu%2uRu%2uRu%0VRV#1Rv#1S0a#0Rw#<Rx#1Ry#4Rz#0R{#0#@R|#QR}#9R~%1w#M#4S0b#4#Y#;%2u#e$0HRu%2uRu%2uRu%2u%s73P3P9PLM9PJK9PHI7fQ7f33P3P3P5fQ3f+033P3f7fp+03PQ%1cRc#0RI#1RH#1#6S0cPG%:XS0d#j#9,BfS0ePQ%1cRc#0RX#QPGPjPQ%1cRc#QS0fPGPjPf%1oRoPG%1;R;#0RK#@#4#X#4#;Pf%=oPGQ0_PfQ0TPGPRPfQ0WPGg00do%1WRW#1Ro#1RJ#1#`RM#1RL#1#KRu#1#`Rw#;S0W;xRPf%1iRiPGQ0WPf%:iS0WPG%;;PfQ0KPG%1\#K#_#;Pf%0hRh#1R\PGPQPf%0hRh#0S0K#0S0T#0R;PGQ0`Pf%:\R\PGPOPfQ0MPG%0kRi#1S0M#3RR#@#N#@#;PfPhPGPQ%7L9mOPPf%:o#jPGPSH0GPfQ0XPG%3:#jR:#9,BfPf%4nPDPiPfP;PE%1URU#1R;#4#X#KPfP\PG%0iRi#1R\#@#N#X#K#<#H#Z#H#Z#Z#<#N#=#X#_PfQ0NPG%3lRl#1#<#Z#<#<#@#N#N#=#M#4#4#X#Z#X#H#X#M#;PfQ0OPG%wwRw#M#M#M#M#M#M#M#<#;Pf%=mPG%1w#K#`Rw#0#`#`Pf%:JPG%Or#H#H#H#HPf%3RPG%3KRK#Y#ZPf%3iRi#3RRPGP~Pf%:\PGPQPfQ0MPGPpPfQ0YPGQ0ePfQ0[PG%42Rp#0#jR\#9,BfPQ%0IRI#1#6PGPQPQ%QIRIPGPQPQ%1bRb#YRr#6RJPF%1w#`#`#;PQ%0bRb#<Rw#1#6PGQ0SPQ%QwRwPGPjPQPdPF%;<PfQ0VPGPQPfPKPGPQPf%:2R2PGPQPfP\PGPQPfQ0LPGPQPfQ0WPG%:`#jR`#9,BfR\PfQ0TPGPBPEPPPGH0FRKPfQ0ZPGQ0=PfPiPGQ0<Pf%:WPGQ0;PfQ0dPGPSPf%:vPGQ05Pf%=VPGP~Pf%:;PG%1]#<#Y#_Pf%3URU#3R]PGP\Pf%0qRq#3PGPKPfP2PGQ08PfQ0RPGQ07#EPfP:PGQ06#EPfP`PGPSPfQ0KPGQ0:PfQ0UPGQ09Pf%3lPGQ04Pf%3aPG%@U#N#@#=%7k-0Ef%=M#L#L#L#6RM%3RRR#=Rk#:#=RU#0Ra#=#L#L#65mf20DfU%7U+01%Ya#L#L#69mSMQ0H#0#L#6,AQ%:]#=#6+01200kdQ0I#4PI%:HQ0c%OXQ0f%OcPw%1b#=PJ%4rQ0G#1#vRr#0#4#=RJ#n%lJ%Or#_#l%1q#Y#H#_#l%0s#KRs#Q%0x#KRx#0#_%1x#<#6PQ%1s#6RsPG%9sPQ%0tRt#0Rs#0#@#6PFQ03#ERx%1s#N%wtRt#Q%OtQ0\#0Rt#<Rs#Q%Os%1t#4#6Q0^Q0]#Y%0y#L1AQ}%;g<0CE%Y|%1{R{#0R|#3#6+00%1|R|#:#l%O|%1{R{#0R|#:%1|#6%H{%4zRz#3R{#QR|PQP|PG%;R%O{%wz#6Q0b#0#_Q0a#O#L#6Q0C%7u5mx%s9+0BDaD8Da3~3g7t}3~3tDaD8D83tI0ADaDaDa3g3g3gDVDWDWDWD8D8DUDWD?D?DVD?DWD?DWDWDWD?D?D?D8DUD?D?D8D8D8D8D8D8D?DSDSD?D?DVDVDVDUD8DVDVDVD83gDSDUDUDUDSDSDUDSDUDSD?DSD8D8D8N<0@,|_R};>}R91d11Rx/d1RuPxP1P1P1PePdCDQ0JCDRd;>dRe1d77Rz/d7R{PzP7Q0Q,rjPQCDRR;>RRG%@p#N#@#4#4#n=I05Rp=>8pR|'FRE'FRg'FRy'FRt'FRs'FRq'FRr'FRJ,FA1u8@RbPAPJPbQ01PrP8P>Q0>PqP8PTQ0@PsP8PZQ0DPtP8P[Q0EPyP8P^P9PgQ0FP}PePEPuPdPGP|P{PR1u8pDTDTDTDTDTDTDTDTK0?P81d=0R=g00e[RRg00fl3GR|,[01R0|5]0P@P8g00h99G=RR|,[01R0|5]0P@P8g00iF9G=RR@,[01R0@5]0P>P8g00jS9G=RR>,[01R0>5]0PBQ02g00k`R>=x4QR@P>CbAp4S>/APPDPBPQC}/J5'J9I0?P8g00lm9G=RRB,[01R0B5]0P6Q00PYP>CbP6Q0?P6PCPFP>C{1c@QCb/J5'J9I0?P8g00n:9G=RR@,[01R0@5]0Q0AQ0B;z>/BY/q3/J59I0?P8g00oG9G=RR?,[01R0?5]0P^Q0Fg010Tg011b60>Ng0130RN,|_PuPxP1P1P1&0=N&0<NCD&0;NCDPdP{PzP7&0:N&09N'r&08NCDPzP7Ap4f>Q0P'B,rjPQCDP8P0g014?9G=RRR-0701R0RPpI06FkFkFkFkFkdo"). Qed.


End FPX_1.
