(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocCode CanonCode RelocSites CanonSites.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RCode_1d000_1d348 () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02K45stdpp9bitvector;definitions2bv01K47Corelib7Numbers7BinNums1Z02K4ELinuxProcessSemantics5Riscv5Instr5instr04K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C35stdpp9decidable;prod_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d17cC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K4ELinuxProcessSemantics5Riscv5Instr5instr06c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d20cC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5instr05c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d210C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond03c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d214C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr08c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d2a8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop01c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d2acC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common5RelocARCode_1d000_1d3487W_1d2b0C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib6Common5Reloc9RelocCode9chunk_hasC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9CanonCode;rl_fetch_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib6Common5Reloc9CanonCode8cc_1cf84C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common5Reloc9RelocCode6cchunk00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9CanonCode8cc_1d20cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc9CanonCode8cc_1d2a8C1?~~~~~~~~~~~~~~~".
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d17c : bv 32 := 0x00008067.
Lemma D_1d17c : decode_any W_1d17c = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj31Tg003nj12Tg004Lj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00:Q#9R4P0P1g00;\R5#0R6#5#3R7g00<AR8g00<_R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=96=442d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d20c : bv 32 := 0x00052583.
Lemma D_1d20c : decode_any W_1d20c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;5p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj12Tg002mj15Tg003nj13Tg003Kj31Tg00?Ej58Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00@1#9R4P0P1g00A<g00>eR5g00;\R6#0R7#2R8#5R9%28#3g00<_R:31%08#3=19:%26#0#0#5g00<A;1:D8%07#3C7,62R734R:P3P3%:3P0g00=;P1g00=lC@,?2P4P7E<R7g00>ER4/;51=:7=445d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d210 : bv 32 := 0x0005c463.
Lemma D_1d210 : decode_any W_1d210 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj11Tg002mj15Tg003nj13Tg003Kj32Tg00Ahj48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00BT#9R4P0P1g00C_g00;\R5#0R6#1R7#5R8%17#3g00<_R732g00<A=287%15#0#1#5%06R6#0#3;27C8%36C7,62R634R7P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=76=442d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d214 : bv 32 := 0x00008067.
Lemma D_1d214 : decode_any W_1d214 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj31Tg003nj12Tg004Lj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00DQ#9R4P0P1g00;\R5#0R6#5#3R7g00<AR8g00<_R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=96=442d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d2a8 : bv 32 := 0x00050213.
Lemma D_1d2a8 : decode_any W_1d2a8 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003nj13Tg003Kj31Tg00E\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00FH#9R4P0P1g00GSg00;\R5#0R6#5R7#2R8%06#3R6g00<_R931%07#3=189%55#0#0#2g00<A;19C8P6C7,62R634R9P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=96=442d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d2ac : bv 32 := 0x00000513.
Lemma D_1d2ac : decode_any W_1d2ac = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj12Tg003nj13Tg003Kj31Tg00E\j48Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00H?#9R4P0P1g00GSg00;\R5#0R6#5R7#2R8%07#3g00<_R731g00<AR9=187%55#0#0#2?197C8%06#3C7,62R634R9P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=96=442d3>o"). Qed.
(* [comment removed for export] *)
Definition W_1d2b0 : bv 32 := 0x00008067.
Lemma D_1d2b0 : decode_any W_1d2b0 = Some (Jalr 0 1 0, 4%Z).
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) [] "p;2p;1p;3p;4p;6g0000j2BTg000Pj1ATg0012j19Tg001cj10Tg002Hj15Tg002mj13Tg003Kj31Tg003nj12Tg004Lj38Tg0058j47Tg005Xj26Tg006:j34j1:Tg006Tj4@Tg0072j2?Tg007Oj6<Tg007gj2;Tg008Aj2=Tg008_j3>Tg009GR0g00:3R1'BR2#AR3g00IJ#9R4P0P1g00;\R5#0R6#5#3R7g00<AR8g00<_R931%25=179%55#0#0#3?18938%06#2C7,62R634R9P3P3%:3P0g00=;P1g00=lC@,?2P4P6E<R6g00>ER4g00>eR2';1=96=442d3>o"). Qed.

Section F.
Context {RL : Reloc} {RC : RelocCode RL} {RS : RelocSites RL}.
Lemma F_1d17c : fetch_word rl_segs (rl (rl_delta 1094%positive) 0x1d17c) = Some W_1d17c.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g00JUj10Tg002Hj12Tg001cj11Tg003nj1;Tg000Pj17Tg005Xj26Tg007gj24Tg002mj15Tg00K4j29Tg00K^j3:Tg006:j3=Tg00Lcj8<Tf0R0#0#0#0#0p=>%00#0#0#0#0#0#0#0p=8%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3p,2RLp,2RCg00Mj#0#>#8#3#3#3#3#3g00NIR0g00;\R1#2#2#1#2#1#1#1#2#1#2#2#2#2#2#1#1#;R2g00:QR3g00OMR4#71640'4g00>ER4g00>eR5'4%11#1#1#1#1#5/939:02==45dG<o"). Qed.
Lemma F_1d20c : fetch_word rl_segs (rl (rl_delta 1095%positive) 0x1d20c) = Some W_1d20c.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g002Hj12Tg001cj14Tg003nj1:Tg000Pj18Tg005Xj27Tg007gj25Tg002mj16Tg00K4j29Tg00K^j3>Tg006:j3=Tg00Lcj8<Tg00JUj10Tf0R0#0#0p=@%00#0#0#0p=?%00#0#0#0#0#0#0#0p=;%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3%40#4p=1p,2RLp,2RCg00Mj#@#?#;#3#3#3#3#3g00PQR0g00;\R1#2#2#4#2#1#2#4#1#1#2#2#1#:R2g00@1R3g00OMR4#81740'5g00>ER4g00>eR5'5%41#1#1#6/939>02==45dG<o"). Qed.
Lemma F_1d210 : fetch_word rl_segs (rl (rl_delta 1095%positive) 0x1d210) = Some W_1d210.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g002Hj13Tg001cj14Tg003nj1:Tg000Pj18Tg005Xj27Tg007gj25Tg002mj16Tg00K4j29Tg00K^j3>Tg006:j3=Tg00Lcj8<Tg00JUj10Tf0R0#0#0p=@%00#0#0#0p=?%00#0#0#0#0#0#0#0p=;%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2%40#4p=1p,2RLp,2RCg00Mj#@#?#;#2#2#2#2#2g00PQR0g00;\R1#3#3#4#3#1#3#1#1#3#1#1#:R2g00BTR3g00OMR4#81740'5g00>ER4g00>eR5'5%41#1#1#6/939>02==45dG<o"). Qed.
Lemma F_1d214 : fetch_word rl_segs (rl (rl_delta 1095%positive) 0x1d214) = Some W_1d214.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g002Hj12Tg001cj14Tg003nj1:Tg000Pj18Tg005Xj27Tg007gj25Tg002mj16Tg00K4j29Tg00K^j3>Tg006:j3=Tg00Lcj8<Tg00JUj10Tf0R0#0#0p=@%00#0#0#0p=?%00#0#0#0#0#0#0#0p=;%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3%40#4p=1p,2RLp,2RCg00Mj#@#?#;#3#3#3#3#3g00PQR0g00;\R1#2#2#4#2#1#2#1#1#2#4#2#1#:R2g00DQR3g00OMR4#81740'5g00>ER4g00>eR5'5%41#1#1#6/939>02==45dG<o"). Qed.
Lemma F_1d2a8 : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2a8) = Some W_1d2a8.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g00JUj10Tg002Hj12Tg001cj11Tg003nj1<Tg000Pj1;Tg005Xj2:Tg007gj24Tg002mj16Tg00K4j27Tg00K^j35Tg006:j38Tg00Lcj89Tf0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3p,2RLp,2RCg00Mj#0#3#3#3#3#3#3g00QUR0g00;\R1#2#2#1#2#1#1#2#1#2#1#2#1#2#1#1#1#<R2g00FHR3g00OMR4#;1:40'4g00>ER4g00>eR5'4%11#1#1#1#1#6/739502=845dG9o"). Qed.
Lemma F_1d2ac : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2ac) = Some W_1d2ac.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g00JUj10Tg002Hj12Tg001cj11Tg003nj1<Tg000Pj1;Tg005Xj2:Tg007gj24Tg002mj16Tg00K4j27Tg00K^j35Tg006:j38Tg00Lcj89Tf0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=3p,2RLp,2RCg00Mj#0#3#3#3#3#3#3g00QUR0g00;\R1#2#2#1#2#1#1#2#1#2#1#2#1#2#2#1#1#<R2g00H?R3g00OMR4#;1:40'4g00>ER4g00>eR5'4%11#1#1#1#1#6/739502=845dG9o"). Qed.
Lemma F_1d2b0 : fetch_word rl_segs (rl (rl_delta 1098%positive) 0x1d2b0) = Some W_1d2b0.
Proof.
ltac2:(KReplay.run1 (kr_t_RCode_1d000_1d348 ()) ["F"] "p;1p;2p;3p;8g00JUj10Tg002Hj11Tg001cj13Tg003nj1<Tg000Pj1;Tg005Xj28Tg007gj25Tg002mj17Tg00K4j26Tg00K^j39Tg006:j3:Tg00Lcj8=Tf0R0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=2%30#3p=4p,2RLp,2RCg00Mj#0#2#2#2#2#2#2g00QUR0g00;\R1#1#1#3#1#4#1#3#1#3#1#1#4#4#<R2g00IJR3g00OMR4#;1840'5g00>ER4g00>eR5'5%31#4#4#7/639902=:45dG=o"). Qed.
End F.
