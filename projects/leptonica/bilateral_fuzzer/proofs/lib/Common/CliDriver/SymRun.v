(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SymRun () := "C46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rc69OSSVerify5KrLib6Common9CliDriver6SymRun9env_agreeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22evC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4list00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX22ebC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr01C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib5Arith8PeanoNat3Nat6ltb_ltK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun<expr_vars_ltC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C4ELinuxProcessSemantics5Riscv3Sem5alu64K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C4ELinuxProcessSemantics5Riscv7Prelude4sextK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr04C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem7mul_divK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr05C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr06C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27ext_valC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr07C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28blob_valC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr08C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_indC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics5Riscv5Instr5aluop00I4ELinuxProcessSemantics5Riscv5Instr5mulop00c69OSSVerify5KrLib6Common9CliDriver6SymRun=saddr_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6v_addiC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun<edenot_agreeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib6Common9CliDriver6SymRun:sr_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24ridxC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun;log_vars_ltC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun<adenot_agreeC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3iffK47Corelib4Init5Logic3and01C47Corelib4Init5Logic7and_indC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natc69OSSVerify5KrLib6Common9CliDriver6SymRun:flat_agreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes3nat01c69OSSVerify5KrLib6Common9CliDriver6SymRun:kn_vars_ltC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01c69OSSVerify5KrLib6Common9CliDriver6SymRun>kentry_vars_ltC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List?Forall_cons_iffK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry02C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S5elenZC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry03C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry08C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes6lengthI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List6Exists00c69OSSVerify5KrLib6Common9CliDriver6SymRun7vals_evC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env01C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC46Stdlib5Lists4List8app_nth1C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_knowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init9Datatypes4prod00C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun;st_ok_entryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;sym_exec_exC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25carryC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;carry_soundC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfC47Corelib4Init5Logic3notC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;regs_ok_updC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_updC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec6regupdC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7eqb_neqC45stdpp9bitvector;definitions5bv_eqK47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1N00C4ELinuxProcessSemantics5Riscv7Prelude;bvmap_emptyK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula01K46Stdlib9micromega5Tauto8GFormula0:K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S:ridx_rangeC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S>ridx_roundtripC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1C47Corelib4Init5Logic9False_indC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03c69OSSVerify5KrLib6Common9CliDriver6SymRun7sr_initC1?~~~~~~~~~~~~~~~C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib6ZArith4Znat5Nat2Z6inj_ltI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega5Tauto4kind02K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib6Common9CliDriver6SymRun6stk_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib6Common8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOk=store_ok_monoC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S?mem_denot_growsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymRun<stk_ok_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common7StoreOkDstore_ok_wrap_windowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec8wrap_memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3lebC4ELinuxProcessSemantics?LinuxProcessSem3RunAentry_stack_imageC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z6leb_gtC47Corelib4Init5Logic6eq_symC4ELinuxProcessSemantics?LinuxProcessSem;StackLayout<stack_to_memC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z7div_1_rC56Stdlib6ZArith6BinInt1Z4succC35stdpp7tactics<f_equal_helpK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C56Stdlib6ZArith6BinInt1Z:pow_succ_rC56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6NArith6BinNat1N6of_natC56Stdlib6NArith6BinNat1N3mulC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z4of_NC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_mulC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib6ZArith4Znat7nat_N_ZC56Stdlib6ZArith4Znat3N2Z7inj_mulC4ELinuxProcessSemantics5Riscv3Sem<branch_takenK4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr;branch_cond02C4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond06".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vals_ev (vals : list word) : nat -> word :=
  fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a _ => saddr_vars_lt b a
  | KDisj a1 _ a2 _ => saddr_vars_lt b a1 && saddr_vars_lt b a2
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
  end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma edenot_agree : forall b E E' e,
  env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP1"] "h01Hh11bh21nh32H0h44IHe1h54IHe2h62e1h72e2h82oph91eh:1mh;2sxh<1Eh=2E'h>2Hbh?2Hvh@3IHehA1ihB1khC1lhD2lohE1zp;3p;2p;1p;6p;4p;:p10000p4p710g000KR0p4p710p8g000ij3XTg001oj2>Tg002Gj1=Tg002lj1BTg003Jj1NTg003mj2@Tg0052j30Tg005Lj1STg005lj1:j2ETg0071j21Tg008:j2WTg008`j29Tg009:j1MTg00:Cj2CTg00:cj2UTg00;Fj1KTg00<Oj2?Tg00=Xj2RTg00>6j3QTg00>YR1j2PTg00?4j3<TP0j66Tg00?\j3HTg00@ej17Tg00AMj3;Tg00B5j33Tg00B`j3GTg00Cij44Tg00DSj3ITg00E\j3FTg00Fej4ATg00Goj4JTg00I8j4DTg00JCj4LTg00KLl:VTg00LWR0f1R2f0R3'?g00M7R430p=2f4R5f3R6f2R7'1112330p=511239067p=OA0034p=81172=063p=Tg00MWR8g00N6R9g00O>R:AX672P1f5R;,>3g00PG#=#=#=R<#=#=R=#=#BR>#NR?1@;21@5230[^28%B<#N#S\8R<%:6%:73012;7P?P;P6P5P6D5[P3f7R@,>31@@2f6RA/@250?[^28%:A%:;50<f9RB/23P?11B2RCf8RDP2CO[X9:g00PlREA0044R41W>2,9?W0%M3,2BP?PB%M2RFPDPFD5[eWE1C3B#8P11C23#81>72[RF1>231C72#8RG[1>67\G1U23P2n2001000000120000000X:8X28PF^:8^28P3P7f;RFP2O31>7FP;P6P3O2b0b3W0%K3,2BP?PB%K2RGPDPGD5[eX28g00QJRGf:RH/23P?PHP2PCCT[RCf<RI/23P?PIP2PFP2D5[RJf=RK/?61?K2RL'R#8RMf>RN/?5RO1?N7RP;Q3RQ%8O%8P'PRPP1f?RO/2;RR12O6RS11OART11O5RO5<@11NARU11N5RN5<@50?P3fARV/2@RWfBRX/2ARYP?11VBRZfC/1DR[9<F311XHR\11XDR]5<FR^50?X1?P?11V@RVA<F\3=0?^X1?A<HZV,9?11X@R^PAP3O1R_E611XBRXPDP2O1RDE6W3W0P2P3O2n2001000000120000000b0W0AH562,2KP?PKAH;57RBPIPBD5[eW5X7:W4X6:W8PQPPP1PRPS%B=R=%7TRB%7OR`5;@73>%7URa%7NRb5;@93=>50?P3P?PZ%73Rc%7[Rd5;F93=>%7\Re%7]Rf5;F93=>Rg50?X1?P?PVA;Fec93=>=0?gX1?%7ZRg%7VRh5;H93=>,9?P^P_E6PXPDE6X3YX0WP2P3O2n2001000000121000000b0X0MAG562,2KP?PKAG;57RiPIPiD5[eX5JX7:X4CX6:X8Gg00R6RGPQPPP1PRPSP>P@PTPOC4P>P@PUPNC450?P3P?PZP>PFP3P[C4P>PFP\P]C4R]50?X1?P?PVP>PFP\P3C4=0?]X1?P>PHPZPVC4,9?P^P_E6PXPDE6X3YX0WP2P3O2n2001000000120000000b0X0MAI562,2KP?PKAI;57R]PIP]D5[eX5JX7:X4CX6:W8PQPPP1PRPSP=P@PBP`C493=>P=P@PaPbC493=>50?P3P?PZP=PFPcPdC493=>P=PFPePfC493=>Rf50?X1?P?PVP=PFPePcC493=>=0?fX1?P=PHPgPhC493=>,9?P^P_E6PXPDE6X3YX0WP2P3O2n2001000000121000000b0X0MAF562,2KP?PKAF;57RMPIPMD5[eX5JX7:X4CX6:X8G%8LP?11I7RLPAP;P5P3CAPAP;P511K6CA50?X1?P;P5P6PLCA,9?11K7P2P3O1E6W0P5P6P7P2CJ,2KP?PKP;P5P6P7CJRKPIPKD5[eX@JX9:X28XD8X;0P<%:FP;P3P5O1P6P7CDP;1EI5P6P7CD50?XC<P51EF6P7P2CD,9?%:IP;E6X04P6P7P2P3CL,2IP?PIP5P6P7P2CLR7PFP7D5[eX28XAEXB8X;0P;M:VW>W?P2P3O2n2001000000121000000W0W9X=9W<W1o"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma adenot_agree : forall b E E' a,
  env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP2"] "h01bh11Eh22E'h31Hh42Hah51ap;3p;2p;1p;6g000ij3=Tg00Rbj2<Tg0052j31Tg002Gj10Tg002lj1;Tg003Jj1:Tg00Slj15Tg0071j22Tg00U5j14Tg00V=j23Tg008`j27Tg00W8j68Tg000Kj69Tg00XAj26Tg00MWg00N6R0g00YJf3R1f2R2f1R33=g00LWf4R4/<3g00M731g00PG#0#0#0#0#0#0#;#:R5%52R6,21R7f0R8%41R9'3%51,24/39515X05%42,37,751246f5P4P1P6P3P8E8E916421612515eW3W4W5X20W1W0o"). Qed.
End VP2.

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_agree : forall b E E' sr regs,
  env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP3"] "p'0h01ih13Hsrh21bi001bh32srh41Eh52E'h62HRh72Hah82Heh94Hnthh:2Hth;2IHh<2b0h=1eh>1rh?4regsh@1ti011np;1p;2p;3p;6p;4g005Lj1MTg002Gj15Tg00ZTj1ATg002lj19Tg003Jj1=Tg00[9j2FTg000ij3CTg00[ej21Tg00\lj3<Tg00^<j28Tg0071j24Tg0052j36Tg00_Ej3LTg00_hj3KTg009:j1JTg00`Uj1ETg008`j2;Tg00a\j1BTg00b<j37Tg00<Oj2:Tg00>6j3@Tg00>YR0j2DTg00b\j6?Tg00W8j6GTg00c>j2HTg000Kj6>Tg00d7j4ITg00LWR1f0R2g00M7R336p=0g00O>R4f2R5f1R6P2CIp=31:62=613p=2g00MWR7g00N6R8%M4R9g00PG#5R:#A#9R;%5:#5#5#5#5#9#=R:'Ff4R<f3R=;C5f5R>/15#0A<>=5%=;P:f7R?18>2R@'4RAf6RB/86,4?96:2X2:g00dSRCg00e15L;9K;2P1P1f9R;P1P4P2%JCRC%E5RD?3?CREn0100000020000RF'4f8RG/4F56:P214?C,;:P4f:RF/12#0f<RHA325CRI'2^07]1X39%B4RJ,1;#0P7A32JC,2HP21;13R3P3X07P2O1n0110100020010101X07W1f;/12#0f=/2I^07]1A7456,1H#0f>RH/:<RI11H=RH;@6%0I%0H'DP0f?R0/2>110<#0f@A74B>=35C'2P2fA/2?fB/1?#0P7fDA74F;=32C'2P>P6P;P5P2O2X07P2O1n0110100020010101W:W8P6P2O2n2001000000120000000b1X07W1W;X@9X=4PBP=E?A32?C,2F^07PFP;PGPEP>P2PDO1EGb9n0110000020000b<14B@96:Ae1H<2P6P2O1E>W>A<><=eW6W1W7W?W3X58W4W2o"). Qed.
End VP3.

Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma mem_denot_agree : forall b E E' base log,
  env_agree b E E' -> log_vars_lt b log = true -> mem_denot E base log = mem_denot E' base log.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP4"] "p'0h01Hh12H1h21bh33logh41Eh52E'h62H2h72H3h82Hah92IHh:1ah;2a0h<4baseh=1lh>1oh?1rh@1vhA1wi006e_addri015e_vali027e_widthi031sp;1p;3p;2p;6p;5g002Gj1:Tg002lj1DTg003Jj1@Tg00eMj1FTg005Lj1KTg000ij3JTg00eoj30Tg0052j31Tg008`j2?Tg00a\j1ETg00b<j3<Tg00Rbj28Tg00<Oj29Tg00=Xj2;Tg00gAj2>Tg00>6j3BTg00>YR0j2ATg00XAj25Tg0071j24Tg00hIj27Tg00iQj33Tg00W8j6HTg000Kj6=Tg00jKj6GTg00kTj3CTg00b\j5ITg00LWR1f1R2f0R3'>g00M7R431p=6A1134p=2g00MWR5g00N6R6g00PG#:#:#:R7#:#:#:#D#@R8%D7#@#F[R7g00l_R9#KR:f4R;f3R<f2R=3JP9f6R>/63A0>;2f5R??0;2517[X3:A11441?7<W0%E9R4,6?A0?<4A0;<4517[eP9f8R4/63A04>2f7R1?0>2517[f9R@A<9=2'6A<9<=RA90@1A041A517[[^=:P3g00YJg00O>f=RA/63f;RB=0A2f<RC?0B2517[f>RD/8;19D=';1>D2';#2f?RE/8?19E<';RF1>E=RG;B3%2F%2G'AP0f@RG/8>19G;';#216G<A0GD;15G114G?,7>33A0ED;15E114E?,7>33517P3fBR1/84191>';#2fCR1/6>fDR>f:RF'8RH19>4R4;B2%2H%24'AP0fER0/8B#2190@#2A001@150C140F,7B33A0>1@15>C14>F,7B33517P3fGRF/8A#2fHR1/9C#2P7fFR@=0FCR0fIR4/5G144D,7ERH533A01FARI151GRG141D,7E33RJ517X>7P815FERKA3I3H=17JX28P814FARH17E393IG=17JX2817DH930K,?7141AP4P1PFPAP>P3EHE=151EP4P1PFPEP>P2EGE=A01@CPBP?O1E=W6W1P2P3O2n2001000000121000000b1W7W1P2P3O2n2001000000121000000b0W0AC;<==<92,6DAC?;<=<9=R?90DCA0AC?517[eW9X?:W@XA5W:P=P2P3O3n01103000131100102101X;9P2DIW8W3W<X56W4W2o"). Qed.
End VP4.

Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP5"] "h02H0h12H2h21bh31Eh42E'h51Hh62H1h72H3h82H4h92Hah:1ah;1np;3p;2p;1p;4p;5p;6g000ij3JTg00Rbj2ITg0052j3DTg002Gj18Tg002lj1HTg003Jj1GTg00Slj13Tg0071j22Tg00U5j14Tg00mjj1>Tg00nHj2BTg00nej25Tg00>Yj26Tg00oAj2ATg00oZj4;Tg0105j5<Tg00W8j6FTg000Kj6CTg010Rj3@Tg011_j2ETg012Ij2?Tg012fj2=Tf2R0f1R1'Ef0R2'?p=1g00dSR3/=2p=71?01/=2p=01612,60p=:1=31/62p=9g00MWg00N6R3g00YJg00Plf4R4f3R5;J0g00LWf5R6/I0g00M73Dg00PG#8R7#8#8#8#8#8R8#HR9#GR:%35R;,24R<%44R=9192R>%>7%>8'BR8,5>%75R7A0>583:'9%34,26=19=R=#7R>15=8A0=587:7R7'6R='AX2:%45919<R<15<8%70A0<083:'9R<P=[R:P:P>P7P=f6R=%36'2%46519R7/58%74A07483:f7R7%3='2%4=519R:/58R?A0:68,96R@16?@,9:f8R:%37'2%47519?0=8,9=%77R@f9RA%3:'2%4:519RB?078R715B8?:@7,9Bf:RB%3A'2%4A519?0:8f;%3B'2%4B519R9#71598RB%7AR:A09A8R9'6RA'6P6PBPAP5P:P9P1P2C;C;C;W8X1@P2D<W7X0?P2D<W1X6>P2D<X0<R<P<C;126;P=P6P4P;P1P2EFECA@650A@450'AeW5W9W;W:X43W3W2o"). Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma log_flat_agree : forall b E E' log,
  env_agree b E E' -> log_vars_lt b log = true -> log_flat E log -> log_flat E' log.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP6"] "p'0h01Hh12H1h22Hlh33logh41Eh52E'h62H2h72H3h82Hah92Hfh:2Hrh;2Hwh<2IHh=1ah>2a0h?1bh@1lhA1rhB1vhC1wi006e_addri015e_vali027e_widthi031sp;1p;3p;2p;7p;4p;5g005Lj1GTg000ij3FTg013Bj20Tg0052j3?Tg00a\j1ETg00Rbj28Tg00<Oj27Tg00=Xj2:Tg00gAj2<Tg014Sj14Tg0152j26Tg00>YR0j21Tg00>6j3ATg015Lj1=Tg010Rj3;Tg015lj7DTg00oZj4@Tg00kTj3>Tg00b\j5CTg00b<j3BTg00LWR1f1R2f0R3'<g00M7R43?p=5g00l_R5?B23p=9A?134p=2f2R6%=37;2p=3g00MWR7g00N6R8%G5R9f3R:?F62P5f5R;/5310;210;6[[X39A?144g0173g00e1W2W0f4R4%E5R1'51041R1P1[[eP5f7R1/5310121016[[f8R<1962'519:6,0<194:,0<[[[^@9P3g00YJg00O>f<R=/5310=210=6[[f=R>/8417>6':1<>2':#2g017O#4#4#4#4#4#4#4#4R?,64A3>;410>6'1'1f?R@f6RA'817@4':RB1<@:RC;A2%2B%2C'1P0f@RC/8117C;':#215C4161?A3@<110@;'1'1P3fBR<f9RB'817<1':#2fCRD/51fDR1f;'8RE171BRF;A2%2E%2F'1P0fERF/8=#2f:RE,7F#216=?A31>=101E'1'1P3fGR=f>RG'8#2fHRH/7>#2P016@?A3HC@10H>'116C?fAR@=3HC10HG'1'1PE16@?fKRE?3D<10EC'1P0fLRE?31D10E@161?A3EF110E<'1'1P3fNfF;3FfORE/0116=?%==R=9;EHR?10EFRF'1P;P?PFP0fPR0?;H=fIRF%=HR<5;0[R@fQRD?;F<R<\?fJ=3DF\<PDP0PEPHP=fMPBFDP2n2001000000120000000P@P3P6O1b0P1P>P3O2C@C@W:W9P2P3O2n2001000000120000000W0W;P2P3O2n2001000000120000000W6W1P2P3O2n2001000000121000000b1W7W1P2P3O2n2001000000121000000b0W2W0A>4:6/92,5>A>;4:/96,0>A>A;4/9:,0>[[eW<XA9WBXC7W=P6P2P3O3n01103000131100102101X>5P2DCW8W3X58W4W?o"). Qed.
End VP6.

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma know_ok_agree : forall segs b E E' base kn,
  env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP7"] "p'0h01ih12HKh21bh33Hk1h41ni001nh51Hh61Ah71ai011ah81Bh92H1h:2H2h;2Hkh<1lh=1Ch>1Ph?1dh@2knhA1mi021mhB1EhC2E'hD3HK1hE3HK2hF2HahG2HbhH3Hk2hI2HrhJ2HvhK2IHhL1KhM2aehN2amhO4basehP3da1hQ3da2hR3dn1hS3dn2hT2hii032hihU1ki041khV2loi052lohW1rhX2rehY3rhihZ3rloh[4segsh\1vi061vh]1wi071wh^2wah_2wni082a1i092a2i0:1ei0;2n1i0<2n2p%0p&0p;1p;3p;2p;4p;7p;6p;5g005Lj1dTg002Gj1[Tg002lj1vTg003Jj1rTg00eMj1|Tg000ik309Tg017nj2LTg0195j4DTg0052j30Tg00a\j1~Tg01:Ej3]j43Tg01;Wj2}Tg01<8j2oTg00=Xk20<Tg00b<j3WTg00>6j3`Tg00>YR0j21Tg01=Cj3PTg01=dk408Tg001oj2NTg005lj16j27Tg01>Hj3fTg00Rbj2\Tg00<Oj2FTg014Sj1OTg0152j2ZTg00XAj2GTg0071j24Tg01?Sj4qTg00hIj2eTg015Lj1STg010Rj39Tg00oZj4@Tg015lk70;Tg00W8j6=Tg00jKk60:Tg01@Kj6aTg01@gj2mTg01B2j2RTg01C@j2TTg008:j2cTg01DOj2_Tg011_j2CTg00Slj1:Tg00U5j1;Tg012Ij28Tg00mjj1zTg00nHk207Tg00nej2^Tg01E1j3jTg01F<k106Tg01F\j2iTg01Ggj2lTg01I2k203Tg01IRj3hTg012fj2YTg01J]j2gTg01Khj4uTg01Lhj4kTg01N3j2bTg01NMk601Tg00b\k500Tg003mj2yTg01Nnj2{Tg00d7j4sTg00LWR1f0R2g00M7R330p=2f1R4/o2=013p=Bf4R5f3R6f2R7'y1y4230p=M1\42=013p=U%S29974p=Xf7R8f6R9f5R:P5P6Cq1e42,_730p=K1142,17p=A1_429067p=pA9674/12p=EP9P:P5P61474P2Eap=ng00dSR;/Y2p=Q1^42,17p=51842,c7p=V1467,C5/84/82,c:p=<1442,C7p=>1874/Y2p=?P8149:P5P61474P2Eap=Jg00PlR<1{74#S;02p=HP6P7P4P2Cs,_5909:p=I1C67/84/82,c5p=x1{42#Sp>05A0<42p=wP6P7P4P2Cs,_5p>04A0742,16p>021474,C6/82p=tg01ON#dg00MWR=g00N6S00Q00g00PG#[R>#[#[R?#[#[#[R@#vRA#rRB%v?R?#rRC#|RD[g01PMRE#dRFB09567PE1L92#2f8RGP9P5P4CDf9RHP9P:P7CD[[X@FA0133P8P:P6%~ER3CDR1A]G:5,}EW;W51L:3#2PGP:P5P3CD\1[e1L82#2PHP8P:P4CDf:R1P8P9P7CD[[1oG71LG4+0<#2P1PGP9AWE67CDS011o15R31L16RI;`4%23%2I'1P0f;RI/B:1LI5#2f=R3P1PHAWE9:CDP21B38f>RJ/L8#2g01QXp4p710RKp-0\2RL%d7RMP0AW6429P67P6P7O1AP564'1[RNP7P4O1AP672'1AW5749P56RO[P5P6O1AP:57'1\OP6P7P4P2H08P4n2001000000120000000W<X74W>W6PN^<M^74^>L^6KP2PEfARKf?RL;]3RMP1PHP9O5PKPLP3P1C3APEMH'1P0fBRMf@RNPJPIC3A]MNJ=PE1fCROPNPLf<RP=WEICDP2fDRQPMPNP3C3fERR?]OK=PE3PEfFRS?]OMPLPJP01N2SPBPSP4PRP4DM[^4=%dCRT\=RU%6Q%6O30fGRVPQPOPNC3PNfHRQ,N2PBPQP4PVP4DM[^4=%6V%6S50UPEfJRV/B2fLRWPVPQP4C3fMRQPVfIP7C3]3]1POg00YJRVg00O>RXfORYAf742'BfQRZPYPQAf674C31\Z5R[1FZ7R\;`4%2[R]%2\'1P0fRR\/U:S021F\6#2g017O#O#O#O#O#O#O#O#OR^,Z:AXZ9:%|TR_fTR`fPRa1GZ9P:PTP:14Z5GK3AP21U`8RbfURc/F9#2PB1GcHRd1ZH^ReAXc1HRfP_fXRgP`P2PHPTPH14cGRhGK3AX2BPB14c8RiP_PgP`fVRj/G1PHCqRkPT1eH2Cp9AefX2BP01ZG^PcPH%SGP_fWRlfSRmPdPGPTPGPiGKCEP_PkPT14jG,eHCp9AefP:1Z1^PgPP%SIP_fZRfPj1GgPPIPTPI14g1GKCEP0fYRe?X3PP_f[RkPl1Ge3PPPTPP14eIGK1Z3^AXeJ3P_f\RiPg1GfJP3PTP314fPGK3AP2AXkLJP_f^RdPf1GiNPLPTPL14iJGK1ZN^%SNR^99iKRnP_f_R_Pkf]Ro/GKPNPTPN14oLGKRT'1P:PnPTP0A9oK^%SKRT99oM[RpA9dMTRT\nAXdOM\TPdPoPiPKP^1N2_PBP_P4PdP4DM[^4=%6o%6i50UPSPRC@S03PHK0;P4n2001000000120000000PpP2P7O1b5P2C@C@W=W8P4P2O2n2001000000121000000W5W6P4P2O2n2001000000121000000P`P8PjPcP`P81N2lPBPlP4PjP4DM[^4=%6cS04%6`S0550UPJP3C@RpP2E=Fn1G`HPjPcP`PHPpP4J0:EaW:W9P4P2O2n2001000000121000000b1P\PYfNRRAf567C3eW3W1W\X]=W7P7P4P2O31m42,BQPYPQfKRS1m74C31\Y6R^1FY7RT;`4%2^%2T'1P01Ua51Fa6#2PYP:1RY5%Q2RT1Ra:752Pa1TZ8R^=VA4O11c?;R?,_CRn50D[^0<CEP21U\91Fm9#2PB14m8RqPmPH1CA2Rr1CA495T2RsP`PAPAPc%:IRt%;IRuP4E<O1=0Dn[^0<CEX2BPBPm%:GRv14`GS06,CARw99mHRxA>AcHRy95T2RzP`1CA7R{/8u=VA4O1=0Dn[^0<'1X2BP01CAq99mGA5T2wPmPAPAPc%:1Rw%;1P4E<O1=0Dn[^0<P`PAPAPjPtPuP4E<O1=0Dn\z^0<,1xP:A9c1yRxA>AlIRz95T2PjPAPAPg%:3%;3RqP4E<O1=0Dn[^0<A9jPzRzA>AgPR|95T2PlPAPAPe%:JS07%;JS08P4E<O1=0Dn[^0<PB%:PR},4lR~18rqRq#Q%z>%z@+07R@,^q%Q|A?q|@'13AX2BP4PjP}PgPlPjP}1N2ePBPeP4PgP4DM[^4=%6l%6j50UPNPLC@RqP:E=FnPzeP2C@W8W6P4P2O2n2001000000121000000P\PvP`PmP\Pv1N2cPBPcP4P`P4DM[^4=%6m%6\50UPPPIC@RzP4E=GJP\P8P`PmP\P8PzP2E=FnP\PG1R\81RmG95T2Pm1T`1=VA4O1=0Dn[^0<CEeW:W9P4P2O2n2001000000121000000b1PaPQPW1m67C3eW3W1X4XX7VP4P2O2Aj742,BYPZPYPQAj674C31FZ6Rn=`[4%2n,1]P0Q021F\5#2PZP91RZ:R]17Z5=HC]1R\995T2PDP\1TmG=VA4O1PCPC&064R]17m9P?FI[^0<'1CEP21Fc8#2PUQ04P2PGO1=HCyA>Aj195T2PDPjPAPAP~%;PR~P4DxO1RyPCPCP]P7P1O1P?FI[^0<5AxX<UPBPhPcP1Pr17jG-05CRx/wrPCPCP]17g1RnP?I04R[90Dy\s^0<'1CEX2BPBPc%:HRsA>AjHRy99c1Rz1wxyRxA>Al1R|95T2R>Pj18{~=VA4O1=0D[[^0<3AX2BP01CAhRh99cH17c8=HChA5T2yPDPcPAPAPlPtPuP4E<O1PCPCP]17lHP?FI[^0<'1PjPAPAPgP}P~P4E<O1=0D[\>^0<9AzxP:A9lI|A>AgI9HCnA>AePRn95T2PDPgPAPAPfQ07Q08P4E<O1PCPCP]17fPRPP?FI[^0<'1P017eI=HCnA>Af3Rn95T2PDPePAPAPk%:L%;LP4E<O1PCPCP]17k3R|P?FI[^0<PePJPnAHCPnA>AkJRk95T2PDPfPAPAPi%:N%;NP4E<O1PCPCP]17iJP?FI[^0<'1CEP2AHC|kA>AoNRk95T2PDPiPAPAPd%:M%;MRMP4E<O1PCPCP]17dNP?FI[^0<A9iKkRN17oL=HCkRkA>AdKRL95T2PDPoPAPAP_%:O%;OP4E<O1PCPCP]17_KP?FI[^0<R_'1PBPo%:KRK18rMRM#Q1^M@%QLA?ML@'13AX2BP:PiPKPdPoPiPKQ03PHE=GJPNePkP_P4P2C@C@W=W8P4P2O2n2001000000121000000W5W6P4P2O2n2001000000121000000P`PsPjPcP`PsPpP4E=GJQ06PjPcP`PGPpP2E=EaQ05P3EaP`PH1R`GRp17`8=HCp1RcH95T2PDPc1TjI=VA4O1PCPCP]17jHP?FI[^0<'1CEeW:X9bP4P2O2n2001000000121000000b1P\PYPRAj567C3eW3W1XU=X4XX7VP7P4P2O31i42,BQPYPQPS1i74C3P2PaPQPW1i67C3eW3W1XT<XV<P4P2O21l42,BQPYPQPS1l74C3PBPRP61^;6P<203r6P;H02X2BP2PQP6PYPRPQP61N2aPBPaP4PYP4DM[^4=%6R%6Q50UP8P9C@R;P4E=GJPaPQPW1l67C3eW3W1XN<XMXP4P2O2Ah742,BYPZPYPQAh674C3PBPaP51Y5r1Yr6'1X2BP2PYP5PZPaPYP51N2\PBP\P4PZP4DM[^4=%6a%6Y50UPHPGC@P4E=GJP\PYPRAh567C3eW3W1XY<XZ<XXXP7P4P2O31g42,BQPYPQPS1g74C3PBPR%:6RS%;5,8rRX#Q1^X@%Q6A?X6@'13A%Q4RX%S4,87R@/Y9PcPZPAPAP5%;GP6DxP7Cu#2[[^A=^?<'1X2BP2PQPSPYPRPQPSP;P4E=GJPQP6P71Y@:P`PaAVA^6P7Cu#2[\X^A=^?<CEePaPQPW1g67C3eW3W1X_<X^VP4P2O2P6P7P4P2Ck,BZPmPZPYP5P6P7P4CkC31\m:RY1\m6RW;`4%2Y%2W'1P01U`91U`51Tm8R01Tm:Rm7?9A?m50'bP21UjG1Ul8PBPlPw18ruRmPAPlPs%;HRsCtR07?1A?0Gm'bX2BPBPlPvPAPgPtPuCtRu18rsRs7?1A?sGu'bX2BP:PjPvPgPlPjPvPqP2E=GJPjPwPgPlPjPwPqP4E=GJ1Tj1R11TjGRj7?HA?j81'beWEWDP4P2O2n2001000000121000000b1P`PZPaP:P5P6P7CkC3eW3W1XS<XQVXR<XPVP6P7P4P2O4n011040008311011071062110110031101100104201051032010:1023010:105103211011004110810;10910<PIP:O2WGWJP4P2O2n2001000000121000000P3P9P2O2J01WHW3P4P2O2n2001000000121000000b;b5WIW1P4P2O2n2001000000121000000b5W;W5AWE74,LG#2Q01PIPGP8AWE56CD[[eWKXWFXLEP4I00WFW@WOWCWBW2W[o"). Qed.
End VP7.

(* [comment removed for export] *)
Section VP8. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma vals_app_agree : forall vals extra ebs,
  env_agree (length vals) (Env (vals_ev vals) ebs) (Env (vals_ev (vals ++ extra)) ebs).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP8"] "h01nh12Hnh21bh33ebsh45extrah54valsp;1p;2p;3p;4p;6g002Gj10Tg002lj1;Tg003Jj18Tg005Lj19Tg01Nnj2BTg001oj2@Tg01R5j11j2:Tg01S9j22Tg003mj27Tg01TAj36Tg0052j33Tg005lj15Tg008:j2=Tg00d7j44Tg008`j2<Tg01T^j6ATg000Kj6?Tg00oZj4>Tg00PG#0#0#0R0#0#0#0#;R1#8R2#9R3g00MWR4%;0#8#9[R0f0R5f3R6,B2'@R7f4R8#1f2R9'2f1R:'7A6286R;#1/29/7:532R<[^04%19/25#5A629:#1/25#5R=530P2P2P:P8g00dS,=1R1C4R>P2P9f5P1C4=325X221<2>P2P:P;P1C4P2P8P6P1P:P5EAE?1:8:1:;:532eP<eX17X041<0=C>W3X43W5o"). Qed.
End VP8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Context {fx : FPState}.   (* [comment removed for export] *)
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
  regs_ok E sr regs -> know_ok segs E base kn ->
  st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["Run"] "h04regsh11Eh22HKh32HRh44baseh52knh62nxh72pch83romh92srp;1p;2p;3p;4p;5g002Gj11Tg002lj17Tg003Jj1;Tg00eMj1CTg005Lj1ATg00ZTj1GTg00[9j2FTg00\lj34Tg0195j43Tg008:j25Tg01U;j52Tg00a\j1BTg01V4j5:Tg01WBj1@Tg01XIj1?Tg00eoj3>Tg0052j38Tg01YQj1=Tg013Bj26Tg01ZZj1<Tg00>Yj20Tg008`j2ETg00oZj49Tg01[cj4DTg00N6g00PG#1R0#1#1R1#1#1#1#7R2#;R3%71#;#C[R1g00Plg00O>#Ag01PM#Ag00MW%G0#7/F3R3f7R0f3R4f0R534p,4segsR6f8R7P0P4C3P3g01\=R8p,2fxR9P41520f9R:P7D2P9P5P0f6R;g00l_#BR<f5R=f4R>D:R?#@,52f:R@%??RA7>:P7D238%=?=4@516@AP6P@P:%<?C3'0'0'0X03f2R3P9P3152;P7P0D2R?=88?A4:=3R@16:<RAP6P:P7P>C3RB'0RC'01E8?P@PCf1PAPBg00e1P5C9C9C9P9P3P;P=P<P>P4D:R4#@,52%?4R29>:7P0D2988?%=4=4:316:2P6P:P7%<4C3'0'0'0eCDW2W3W0W6W5W9W7X81W4W1o"). Qed.

Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["Run"] "h01Eh12HKh22HRh33Hexh43Hsch54baseh64fuelh72knh82nxh92pch:4regsh;3romh<3scrh=4scr'h>3scsh?2srh@3ss'hA5stopsp;1p;2p;5p;7p;4p;3p;:p;Bg005Lj11Tg002Gj10Tg002lj12Tg003Jj16Tg00eMj1CTg00ZTj1;Tg00[9j2:Tg01]Dj24Tg00a\j15Tg01V4j53Tg01]dj78Tg01^oj47Tg0052j39Tg00\lj3BTg0195j4ATg01_Oj4@Tg008:j2<Tg01U;j5=Tg01`al:>Tg01ailB?Tg00MWR0g00PlR1#1g01c=R2g00O>#1g01PM#1g01dIR3g01eWR4#1R5g00N6g00PG#0R6#0#0R7#0#0#0#2R8#6R9%27#6#C[R7%;6#2/:91435R9/42p,4segsR6f=R:g00M7R;f<R<f;R=f:R>f9R?g00l_#5R@f8RAf7RBD3%54R4F8P9P2P3P5f6R5f5R3C7f4R9C739f1RC9B9>P6P3P9P>CAP6P3P5PAC@p,2fxRDP6fAP;f@f?f>R;P:P@P<P=D3P4P>P?PAPBP5P3PDP91<8;P5P3D=f3f0PBP5P3P;P:P<P=P9f2PCM:>MB?W4W1W2W3W:X;7W5W0X=2W>W@X80W7W?X91W<WAW6o"). Qed.

(* [comment removed for export] *)
Theorem carry_after : forall E base log kn hints kn' scs hs',
  carry log kn hints = (kn', scs, hs') ->
  log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
  know_ok segs E (mem_denot E base log) kn'.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["Run"] "h01Eh14baseh25hintsh33hs'h42knh53kn'h63logh73scsp;1p;2p;3p;4p;>g002Gj10Tg002lj14Tg003Jj12Tg00eMj16Tg005Lj11Tg01]Dj25Tg01fdj3<Tg01^oj43Tg0052j3;Tg013Bj2:Tg0195j47Tg01_Oj48Tg01gll>9Tg00N6g00PG#0#0#0R0#0#0#0#4#2%40#2#6[g00l_#1g01PM#1R0g00LW#1R1g01eW#1R21502R3/51f5R4f4R5f3R63<P3P1P0P2f2R2f1R3C3f0R7C33;f8R8f6R9':p,4segsR:f9R;P8P9C7P:P;f:R<P5C8P:f;P<P<P;P8f7P9P4P5P6P2P3P7M>9UUUUX31W7X50W2W4W6W1W0o"). Qed.

(* [comment removed for export] *)
Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["Run"] "h01Eh12HRh21Rh31rh42srp;1p;2p;3g005Lj16Tg002Gj10Tg00ZTj13Tg002lj11Tg003Jj12Tg00[9j25Tg00\lj34Tg00N6g00O>#6g00PG#0R0#3#1R1%00#0#0#0#0#1#2'5%21f3f2f1R134f0P1O1W1W3W2W4W0o"). Qed.

(* [comment removed for export] *)
Lemma regs_ok_set : forall E sr R (rd : reg) v e,
  regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
  regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["Run"] "h01Hh12H0h22b1h32b2h41nh51xh61yh71Eh82HRh92Hbh:2Hch;2Heh<3Hrdh=1Rh>1bh?1eh@2rdhA2srhB1vp;1p;2p;3p;8p;6g005Lj1FTg002Gj13Tg00ZTj1ATg002lj1<Tg003Jj11Tg00[9j2ETg00\lj37Tg01i@j2@Tg00_Ej3=Tg0052j30Tg01icj15Tg0071j2?Tg01j<j8>Tg00_hj36Tg00`Uj1;Tg01kPj3:Tg01lYj39Tg01mTj28Tg01n1j2DTg011_j22Tg01nRj3CTg01@Kj6BTg00LWR0f0R1g01o6R230p=4g00N6g00O>R3#FR4g00PG#3R5#A#<R6%35#3#3#3#3#<#1R5'ER7%16R8f5R9f4R:f3R;37g00dSR<g00e1R=1@6<d5=6R>908;#5f7R8f2R?'?=05;f8R@P8f6RAP9P:P;P?P1G>P0P4A669>RBP8%;9=:8;n0100000020000P0P7PBPAA9A9:n010000002000057@g00PlRBg00>YRCf1RD/81#4A0B?D#5RE[A0BD1#518?D#4[RF18;?#4\E1DD1P1n2001000000120000000X6BW5PF^6B^5BP11268RFA=6<=R=,26R<A0BF<R<P:g01oVRF%11RE%1DRGPC%1??0D112;?12;D50BRC[12?D12?150B%1;?0?D[RB%1:?0;?\CAC?D1P1n2001000000120000000W3W2W4PB^3G^2E^4FP1P6f9RFP=PDO4b1O1W:%5<eO3b1A66A=#4eA66A>#4P0A668=f;P0P4P1f:R4%;@=:4An0100000020000P0P7P1PFA9F@8n010000002000037X>0PDP2P1EB%;8=:F9A9@8A574P1b0b9b0W;W<W8X?3XB5W@W=WAW7o"). Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_init : list expr :=
  [ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

Section VP9. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_init : forall (sp : word) rest ebs,
  regs_ok (Env (vals_ev (sp :: rest)) ebs) sr_init
          (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP9"] "p'0h03Hr0h13Hlth21ni001nh34__x1h41rh51Hh67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<2b1h=2b2h>3ebsh?4Hlt0h@1bi011bhA4cstrhB1ehC4resthD2sphE1xp%0p&0p;1p;3p;2p;4p;7p;5p;6p;8p;<g002Gj1?Tg002lj1UTg003Jj1:Tg005Lj1MTg00ZTk107Tg00_Ej3>Tg00_hj3=Tg008`j2<Tg0052j39Tg0204j2hTg00mjj1FTg008:j2HTg01lYj3JTg009:k106Tg00`Uj1CTg011_j2@Tg01nRj3rTg020fj1qTg021Dj2oTg014SR0j10Tg021ej2YTg022Nj3lTg0237j3jTg023`j2iTg00a\j1gTg00b<j3BTg024Lj2XTg024jj1fTg025Hj4eTg025fj1dTg026Dj1cTg026oj2WTg027Rj4LTg028=j7VTg028aj5bTg029Ej6aTg029ik105Tg02:Kk204Tg02:mk203Tg02;Yk302Tg02<8j4|Tg01mTj2{Tg01i@j2NTg0071j2ITg000Kj7xj6sTg02<jj1wTg001oR1j22Tg02>=j1uTg015LR2j1ETg01@Kj6\Tg02?Tj2pTg02@Gj2[Tg00neR3j2ZTg012Ij2DTg02@fj4mTg02AMj1tTg012fj2]Tg02B2j2KTg02BUj6kTg00^<j2yTg00\lj3zTg00d7j4OTg01R5j1QTg01S9j2RTg00c>j2~Tg02C9k800Tg02C]l<`Tg02DBm<01Tg02Dgj3GTg00O>R4f1R5g02EJR6f0R7COp=}f4R8f3R9f2R:3B#Q/R5/I7p=Pf5R;AJ89:/~5;97p=1g00LWR<g00M7R=797p=AP5g02FNR>g02FmR?P?g02GMR@P7g02GmRAFVp=TP9P>P?P?P@P:P5P7L00p=S%Q5/R7p=_g01o6RB99<7p=^%E7,H5p=3P4P5P6P7CO,I:p=vA=:57=9<Bp=5%E5,H:==97=9<Bp=6AB;89#Q/R:P4%C5P6P7CO'Ip=41D89/D:/D5/D7p=8g00MWRCPCg00PlRDPDP0P2P2f6REg02HMRFP;P8PCPCPDPDP0P2P2P9PFP:P5P7M<`M<`p=7PCPDP1P2P3g02I1P;P8P9P:P5P7N<01p=nAGD89=GD:=GD5=GD7p=;g00PGR3#?R2#?#?R1#?#?RF#?#UR0#:RG%MG%U1#:#MS00\C&072R1#URH#:RIg00dSRJg00e1RK5>HRL9=H7RMP<1<<7A=H5L=9<7P<A=H9L=9<7PG1hHGRN%?1#FR1=>HK1H0JRO3JRP%F2RQ=>HKRRf7RSP8PGPSPEP;P<P4P5&06JR4%C8RT/}4n0100000020000DPE1]0P5A=H:LRU#Ag01oVRV%:7RW%:5RXg00>Y%::?9571@9:1@9559DRY[1@:51@:759D%:9?9:5[RZ%:8?99:\YAr:57P7n2001000000120000000W=W<W2PZ^=X^<W^2VP7PHP8PLg02ISRV%q3,oDg017ORW#0RX,YD5lD1YDW5jDg02J?'i%gVS013B%MVS02PD1XD:P5%fDCe%dDS03%cDRVPVP>P?P?PVP>P?P?g02JkRZPD1WD3RYg02KK1WD2CLR2PAFVPVP>P?P?PZDbEa&05?RZ1TV2CS204V@S04P7P:1<<=2037:#AdB02DJ5C|S05b7b9b:X3DX;D1{75#AA9D5:[^3D^;DP71@HL1@H;P:O3b6O4b5PK1NHJd9>HJ99I9PIPL%AMPGPPPRf9R2P5PGP2f8RAPSP4DPE1]0X4IA=HLL#AABGAS/_ERS/I4,<GW0P8P7P5Fxb5W0%^U%w9%C9%0XRU#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn#0Ro#0Rp#0Rq#0Rr#0Rs#0Rt#0Ru#0Rv#0Rw#0Rx'2PI13HTRTPGPPPRPAP7%C7=vS4E1X4IPIP8%^MX4IP5PT%u8S06EsA5HTL%C;PCPCPHPHP7PLC6125xPGPPPRf<R;%E:RT,HHRIPGP;f;R;f:RMPIP4E4E1]1]0P713HWRI=5HL12WxP<P=P<p-0R=P7g0173g02L2RWn0110100020000XB<PKPBP5E\PW1p0J9>0JR0=9G0/[7b5PGPPPRP;PIPGP;PMP2PIP4E4E1dW1W0PHPH%07RIPLC6R2%05RM/2xR;PCPGPPPRf@RB%0:R<,3HRSPGPBf?RBf>RAPSP4E4E1^1;^02P:13HXR2=5HL12Xx1<G0R0PGPPPRPBP2PGPBPAf=P2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRfDRB%0<RX,3HR;PGPBfCRBfBRSP;P4E4E1^1A^02P:13HUR2=5HL12Ux1<GBPGPPPRPBP2PGPBPSfAP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRfHRB%0XRU,3HRAPGPBfGRBfFR;PAP4E4E1^1S^02P:13H[R2=5HL12[xP0PGPPPRPBP2PGPBP;fEP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRfLRB%0UR[,3HRSPGPBfKRBfJRAPSP4E4E1^1;^02P:13H\R2=5HL12\xP0PGPPPRPBP2PGPBPAfIP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRfPRB%0[R\,3HR;PGPBfORBfNRSP;P4E4E1^1A^02P:13H]R2=5HL12]xP0PGPPPRPBP2PGPBPSfMP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRfTRB%0\R],3HRAPGPBfSRBfRR;PAP4E4E1^1S^02P:13H^R2=5HL12^xP0PGPPPRPBP2PGPBP;fQP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRfXRB%0]R^,3HRSPGPBfWRBfVRAPSP4E4E1^1;^02P:13H_R2=5HL12_xP0PGPPPRPBP2PGPBPAfUP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRf\RB%0^R_,3HR;PGPBf[RBfZRSP;P4E4E1^1A^02P:13H`R2=5HL12`xP0PGPPPRPBP2PGPBPSfYP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRf`RB%0_R`,3HRAPGPBf_RBf^R;PAP4E4E1^1S^02P:13HaR2=5HL12axP0PGPPPRPBP2PGPBP;f]P2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRfdRB%0`Ra,3HRSPGPBfcRBfbRAPSP4E4E1^1;^02P:13HbR2=5HL12bxP0PGPPPRPBP2PGPBPAfaP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRfhRB%0aRb,3HR;PGPBfgRBffRSP;P4E4E1^1A^02P:13HcR2=5HL12cxP0PGPPPRPBP2PGPBPSfeP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRflRB%0bRc,3HRAPGPBfkRBfjR;PAP4E4E1^1S^02P:13HdR2=5HL12dxP0PGPPPRPBP2PGPBP;fiP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRfpRB%0cRd,3HRSPGPBfoRBfnRAPSP4E4E1^1;^02P:13HeR2=5HL12exP0PGPPPRPBP2PGPBPAfmP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRftRB%0dRe,3HR;PGPBfsRBfrRSP;P4E4E1^1A^02P:13HfR2=5HL12fxP0PGPPPRPBP2PGPBPSfqP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRfxRB%0eRf,3HRAPGPBfwRBfvR;PAP4E4E1^1S^02P:13HgR2=5HL12gxP0PGPPPRPBP2PGPBP;fuP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRf|RB%0fRg,3HRSPGPBf{RBfzRAPSP4E4E1^1;^02P:13HhR2=5HL12hxP0PGPPPRPBP2PGPBPAfyP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRp+01ARB%0gRh,3HR;PGPBp+01@RBf~RSP;P4E4E1^1A^02P:13HiR2=5HL12ixP0PGPPPRPBP2PGPBPSf}P2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRp+01ERB%0hRi,3HRAPGPBp+01DRBp+01CR;PAP4E4E1^1S^02P:13HjR2=5HL12jxP0PGPPPRPBP2PGPBP;p+01BP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRp+01IRB%0iRj,3HRSPGPBp+01HRBp+01GRAPSP4E4E1^1;^02P:13HkR2=5HL12kxP0PGPPPRPBP2PGPBPAp+01FP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRp+01MRB%0jRk,3HR;PGPBp+01LRBp+01KRSP;P4E4E1^1A^02P:13HlR2=5HL12lxP0PGPPPRPBP2PGPBPSp+01JP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRp+01QRB%0kRl,3HRAPGPBp+01PRBp+01OR;PAP4E4E1^1S^02P:13HmR2=5HL12mxP0PGPPPRPBP2PGPBP;p+01NP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRp+01URB%0lRm,3HRSPGPBp+01TRBp+01SRAPSP4E4E1^1;^02P:13HnR2=5HL12nxP0PGPPPRPBP2PGPBPAp+01RP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRp+01YRB%0mRn,3HR;PGPBp+01XRBp+01WRSP;P4E4E1^1A^02P:13HoR2=5HL12oxP0PGPPPRPBP2PGPBPSp+01VP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRp+01]RB%0nRo,3HRAPGPBp+01\RBp+01[R;PAP4E4E1^1S^02P:13HpR2=5HL12pxP0PGPPPRPBP2PGPBP;p+01ZP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRp+01aRB%0oRp,3HRSPGPBp+01`RBp+01_RAPSP4E4E1^1;^02P:13HqR2=5HL12qxP0PGPPPRPBP2PGPBPAp+01^P2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRp+01eRB%0pRq,3HR;PGPBp+01dRBp+01cRSP;P4E4E1^1A^02P:13HrR2=5HL12rxP0PGPPPRPBP2PGPBPSp+01bP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRp+01iRB%0qRr,3HRAPGPBp+01hRBp+01gR;PAP4E4E1^1S^02P:13HsR2=5HL12sxP0PGPPPRPBP2PGPBP;p+01fP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRp+01mRB%0rRs,3HRSPGPBp+01lRBp+01kRAPSP4E4E1^1;^02P:13HtR2=5HL12txP0PGPPPRPBP2PGPBPAp+01jP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRAPCPGPPPRp+021RB%0sRt,3HR;PGPBp+020RBp+01oRSP;P4E4E1^1A^02P:13HuR2=5HL12uxP0PGPPPRPBP2PGPBPSp+01nP2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xRSPCPGPPPRp+025RB%0tRu,3HRAPGPBp+024RBp+023R;PAP4E4E1^1S^02P:13HvR2=5HL12vxP0PGPPPRPBP2PGPBP;p+022P2P4E4E1dW1W0PHPH%0IRIPLC6R2%0MRM/2xR;PCPGPPPRp+029RB%0uRv,3HRSPGPBp+028RAp+027RyPSP4E4E1^1;^02P:13HwR2=5HL12wxP0PGPPPRPAP2PGPAPyp+026P2P4E4E1dW1W0PHPH%0IPLC6%0M/2xPGPPPRp+02:RM%0vRL,3HRIPGPMPBPAPIP4E4E112LxPT%F3R3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8%FFRF'ZS07PL1D73XEDRLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPLPTO1S08O1S09O1S0:O1S0;O1S0<O1S0=O1S0>O1S0?O1S0@O1S0AO1S0BO1S0CO1S0DO1S0EO1S0FO1S0GO1R4O1RIO1RAO1RBO1R2O1RyO1R0O1RwO1R;O1RSO1RzO1R{O1R|O1R}O1R~O1PLPvP~PLPuP}PLPtP|PLPsP{PLPrPzPLPqPSPLPpP;PLPoPwPLPnP0PLPmPyPLPlP2PLPkPBPLPjPAPLPiPIPLPhP4PLPgQ0GPLPfQ0FPLPeQ0EPLPdQ0DPLPcQ0CPLPbQ0BPLPaQ0APLP`Q0@PLP_Q0?PLP^Q0>PLP]Q0=PLP\Q0<PLP[Q0;PLPUQ0:PLPXQ09PLP<Q08PLP:PT1<DTF7F7F7F7F7F7F7F7F7F7F7F7F7F7F7F7PxPF1<DFEnP7CmQ07%t9%E9,]JPMP8O1Q00Q01Q021XD5Q03PVPD1KDJg02LOPYCL,TVPZPVPDPY1KD3RYPYPYPYD;PYPYPYPYD;PYPYPYPYD;PYPYPYPYD;PYPYPYPYD;PYPYPYPYD;PYPYPYPYD;PYPYPYPYD;g02M61KDFCL,TVPZPVP>P?P?P@P9EkCSCSQ04Q05b7b9b:X3DX8=1]J7P5P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8P3P3P3P3D8/ZFP9[[^3D^8=P7PW%EEP:P9O4b6b>bAb?'[W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110001020111100P5P7O2W1W0X2CP7O1n0110000020111100P5P7O2W1W0X2CP7O1n0110000020111100P5P7O2W1W0X2CP7O1n0110000020111100P5P7O2W1W0X2CP7O1n0110000020111100P5P:O2b2b0P8Q06E\b1W0n0110100020101P7O1b0b@PGPPPRP9P7PGP9P:P51y67DPE1eW4ABG:5/_7PK1NH1d9>H1=JNOPK1NHQd9>HQ;J:7z6eW>WCWDo"). Qed.
End VP9.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
  forall (a : word) (n : nat),
    (bv_unsigned sp - K <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
    store_ok segs mem a n = true.

Section VP10. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma stk_ok_vaddi : forall segs mem sp K off n,
  stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
  (- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
  store_ok segs mem (v_addi sp off) n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP10"] "h04__x1h14__x2h24__x3h31Hh42H0h57__arithh64__ffh76__sat3h86__sat4h98__varmaph:5__with;4cstrh<2Hah=4__x4h>1zh?2H1h@2H2hA2HKhB2HshC1KhD3memhE1nhF3offhG4segshH2spp;1p;4p;2p;3p;7p;6p;8g005Lj1NTg002Gj17Tg002lj1FTg003Jj1DTg00eMj1hTg02M]j4cTg011_j22Tg012fj20Tg02N`j1?Tg015Lj1<Tg012Ij21Tg02O=j1RTg00mjj1MTg00nHj2eTg00nej25Tg00>YR0j2BTg00V=j2_Tg02P;j2=Tg02AMj1]Tg02PXj2\Tg02Q@j3[Tg00a\j1ZTg024Lj2@Tg025Hj4ATg025fj1YTg026Dj1XTg026oj2>Tg02Qdj2ETg00ZTj1WTg029ij1VTg02RGj3UTg02Dgj39Tg02:Kj2QTg008`j2PTg02:mj2OTg0052j3STg02;Yj3TTg02<8j4gTg008:j2fTg014Sj1:Tg021ej28Tg0237j3;Tg023`j2KTg00b<j3JTg024jj1dTg02B2j2HTg02Rjj3bTg027Rj4CTg02SMj7`Tg02T1j2aTg000Kj6LTg028=j7GTg02C9j8^Tg00dSR1f0R2'0p=3f2R3g02FNR4g02FmR5P5g02GMR6g00PlR7f1R8g02LOP2CCg02GmR9FGp=4f3R:P4P5P5P6P3P8P2G^p=6P8P4P5P5P6P2P9FGp=Ig01ON#Ng00PGR9#7R;#7R<#7R=#7#7#7R>#FR?#DR@%F=#D#h[g00MWf5R=f4RAP:P3Cc12?A,0:%?A/0:%<:,1A/01f7RB#R12?BRC#3%M;RD%M>R>'eRE,5C'BPAf8RCf6RF'_RGP=P712?CRH/1FRIf9RJ,2?RK/=C/02X>7%]=RC%<=RL#3RM1\D>RN151D%3>151E[[RO%3DRPg0173RQA[D>8UW<R>%3E\Q^<PRPP0f;RQ,2?RR#3RS15RERRf<,2?RT/=Qf:RU,1TRV'0P:f=RW,2?#3RXf>RY,2?/5ERZg02ISR[#ZR\%N[R]P71@73P81@7:R^CAR_%Y7R`%X7Ra1>7;R;,E7%W9,>7Rb54a%V5Rc1>79R9=U7;A979b54aC61Qa6RdP2P3g00LWReg00M7Rf'P1O23=SefdAT718CgRfb6b9b:X07X17X27%?8/031=83118:'0[^07^17^27P2PYf?Ref@,2?RgPUO4b5W4W3P8P2O2n2001000000120000000b7b8b;1f?I,2?RhPCPMPNPOP>PPP0PSPR%3V15VE'BP:g017ORi#:Rj#:Rk#:Rl#:Rm#:,87187m187l187iRi5;75;75;7g02J?Rl'K187k187j=;7i5;7/Kl=J[\5J[P]P7P71@7AP3%d7CAP8P^CAP`Pa1H71R^1>7<R<54aPcPaP7P9g02M6R[1H7D=b7?RDCC,IaPcPaA97;<=4a^PcPa1E7b=4a;PcPaA4ab9PcPaP4P5P5P6A979;R694a^P7P6P[PDCC,IaF`C6C6C6C6C6PdPfb6b9b:X07X17X27X=7%3:158E11:=/01%?=/0A10FA11=FR=#315=E'B[[[[[^07^17^27^=7P2%<WRWPePYPgPBP8PJPUPQO9b5X4ZX3XP8P2O2n2001000000121000000b7b8b;,aIRQEL1=HB12?GRG'0eP7PI%<F,12/0KX>7PCPMPNPOP>PPP0PSPR%<J,1V/0TP:P\P]P_P`PaA97;b=4a^PcA976b=4a9C6PdPfb6b9b:X07X17X271183R3/01113:/08[^07^17^27P2PWPYPgPJO4b5X4ZX3XP8P2O2n2001000000120000000b7b8b;PhPQEL11GL/0HeO4b3W@W?WAWBWEXF7XC7XH@WDWGo"). Qed.
End VP10.

Section VP11. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma stk_ok_lit : forall segs mem sp K z n,
  stk_ok segs mem sp K ->
  (bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
  store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP11"] "h04__x1h14__x2h24__x3h31Hh42H0h57__arithh64__ffh76__sat4h86__sat5h98__varmaph:5__with;4cstrh<1zh=2Hah>2H1h?2H2h@2H3hA2HshB1KhC3memhD1nhE4segshF2spp;1p;4p;2p;3p;7p;6p;8g005Lj1HTg002Gj16Tg002lj1DTg003Jj1BTg00eMj1eTg02M]j4\Tg011_j21Tg02P;j2:Tg012fj20Tg015Lj19Tg012Ij27Tg02O=j1JTg00mjj1ITg00nHj2cTg00nej23Tg00>YR0j2@Tg008:j2ZTg02AMj1YTg02PXj2XTg02Q@j3WTg00a\j1VTg024Lj2CTg025Hj4?Tg025fj1UTg026Dj1TTg026oj2<Tg02RGj3STg00ZTj1NTg029ij1MTg02:Kj2LTg008`j2KTg02:mj2OTg0052j3PTg02;Yj3QTg02<8j4RTg014Sj1=Tg021ej2;Tg0237j3ATg023`j2dTg00b<j3bTg024jj1aTg02B2j2FTg02Rjj3]Tg027Rj4>Tg02Dgj3GTg02SMj7[Tg02T1j2^Tg000Kj6ETg028=j7_Tg02C9j8`Tg00dSR1f0R2'0p=2g00PlR3f1R4g02LOP2C>p=8P4g02FNR5g02FmR6P6g02GMR7P2g02GmF_p=4f3R8P5P6P6P7f2R9P4P2G`p=5g01ON#Hg00PGR:#6R;#6R<#6R=#6#6#6R>#DR?#BR@%D=#B#e[g00MWf5R=f4RAP8P9C\11?A/:8/09%99,7811?='0%2ARBf7RC#J11?CRD#2%I;RE%I>R>'cRF,3D'@PAf6RD,Z?RGP=P3PDf9RH,1?RIf8':/02X<3%Y=RJ%9=#2RK1XE>RL131E%2>131F[[RM%2ERNg0173ROAWE>4UW=R>%2F\O^=NRNP0f;RO,1?RP#2RQ13PFRPf<,1?RR/:Of:RS'0P8f=RT,1?#2RUf>RV,1?/3FRWg02ISRX#VRY%HXRZP31C39P41C38R[C?R\%U3R]%T3R^1<3:R_1<3;R;5S3%N:,<3R:'8,4^R`%M6RaP`C51L^7R`P2P9g00LWRbg00M7Rc'K1O29=PbcdAQ314CRRcb6b9b:X03X13X231:24/091:49/08[^03^13^23P2PVf?f@,1?RbPOO4b5W4W3P4P2O2n2001000000120000000b7b8b;11?GRGPJPKPLPMP>PNP0PQPP%2S13SF'@P8g017ORO#=Rd#=#=Re#=,;31;3e1;3d1;3O5A35A35A3g02J?'d=bXYPZP3P3P[P9%a3R[C?P4P[C?P]P^1F31R11<3<R<'8,4^PaP^P3P;g02M6R[1F3E=]3?R?C>,4^PaP^181_,4^R1PaP^AG3_</8;,4^PaP^P5P6P6P7P1P3P_P[P?C>,4^F[C5C5C5C5P`Pcb6b9b:X03X13X23%29R?139F178=/0A13AF,@B[\?[[^03^13^23P2%9TRTPbPVPCP4PHPSO7b5X4WX3UP4P2O2n2001000000121000000b7b8b;,^DRCEEP3PD%9D,72/0IX<3PJPKPLPMP>PNP0PQPP%9H,7S/0RP8PYPZP\P]P^AG3_;/8:,4^R^PaP^C5P`Pcb6b9b:X03X13X231724/091749/08[^03^13^23P2PbPTPVPSO4b5X4WX3UP4P2O2n2001000000120000000b7b8b;PGPCEEO4b3W@W?W>WAWDX<3XB3XF@WCWEo"). Qed.
End VP11.

Section VP12. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma stk_ok_grows : forall segs mem mem' sp K,
  stk_ok segs mem sp K -> mem_grows mem mem' -> stk_ok segs mem' sp K.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP12"] "h02H1h12H2h22Hgh32Hsh41Kh51ah63memh74mem'h81nh94segsh:2spp;1p;4p;2p;7g005Lj1<Tg002Gj10Tg002lj12Tg003Jj13Tg00eMj1;Tg02M]j45Tg02UAj2:Tg011_j21Tg02P;j27Tg012fj24Tg015Lj16Tg012Ij28Tg02V>j79Tg01ON#<g00PG#0#0#0R0#0#0#0#2R1#3R2%20#3#;[R0g00Plf4R3f3R4f1R5f0R6C51:34g00MWf5R7,11/731115'4f2R8,11%65'8f6R9,11'4f:P8f9f8P4P3P7P4P8P5P6O4F9W1W0W8X52P9P3P4P8C5eW2W3W4X:2X70W6W9o"). Qed.
End VP12.

Section VP13. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma stk_ok_mem_denot : forall segs E mem log sp K,
  stk_ok segs mem sp K -> stk_ok segs (mem_denot E mem log) sp K.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP13"] "h01Eh11Kh23logh33memh44segsh52spp;1p;4p;3p;7g005Lj13Tg002Gj10Tg002lj12Tg003Jj11Tg00eMj18Tg02M]j47Tg00eoj36Tg02W?j34Tg02XWj75Tg01ON#3g00N6g00PG#0#0#0R0#0#0#0#2#1R1%20#1#8[g00l_#3g00Plf5R0f3R2f1R3f0R4C7f6f4R5A6052f2P3P4A4052F5UW1X51W2W3W0W4o"). Qed.
End VP13.

(* [comment removed for export] *)
Section VP14. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma stk_ok_init : forall segs ph sp argv envp uid hw rnd,
  stk_ok segs (wrap_mem ph sp argv envp uid hw rnd) sp stack_max_size.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP14"] "h02H1h12H2h21ah34argvh44envph52hwh61nh72phh83rndh94segsh:2sph;3uidp;1p;2p;<p;7p;4g005Lj12Tg002Gj10Tg002lj14Tg003Jj13Tg011_j21Tg02P;j2;Tg012fj25Tg015Lj1:Tg012Ij29Tg02Y`l<7Tg02Zhj76Tg02M]j48Tg01ON#2g02[eg00PG#0#0#0R0#0#0#0#4R1#3R2%40#3#2#2R0g02\eg00MWf7R3,11g02]eR4';f1R5,11'5f2R6,11%:5'9f8R7,11'5f;f:f9P7P3f3R7P6f6R1f5R8f4R9P5f0R:M<7W1W0W6X22P3P1P8P9P7P6P5P:F6P8P4C8eW8X52X;2X40W3W:W7W9o"). Qed.
End VP14.

Section VP15. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kwr_of_stk_ok : forall segs E mem (e : expr) (sp : word) K,
  edenot E e = sp -> stk_ok segs mem sp K -> (0 <= K <= bv_unsigned sp)%Z ->
  kentry_ok segs E mem (KWr (SA e (- K)) K).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP15"] "h04__x1h14__x2h24__x3h31Hh41dh51mh62H0h77__arithh84__ffh96__sat0h:6__sat1h;8__varmaph<5__with=4__x4h>4cstrh?2Hah@4__p1hA1zhB1EhC2HKhD2HdhE2HehF2HmhG2HshH1KhI1bhJ1ehK3memhL4segshM2spp;1p;2p;3p;4p;6p;7p;8g005Lj1WTg002Gj1>Tg002lj1UTg003Jj1QTg00eMj1zTg0071j2HTg0052j3RTg02M]j4gTg011_j21Tg02N`j1:Tg012Ij20Tg00mjj1ZTg00nHj2xTg00nej22Tg015Lj1BTg012fj27Tg008:j2FTg01Khj4ETg00>YR0j29Tg02O=j1bTg02PXj2aTg02Q@j3`Tg014Sj1@Tg021ej2=Tg023`j2KTg00a\j1_Tg00b<j3NTg024Lj2ITg024jj1^Tg025Hj4GTg025fj1]Tg026Dj1\Tg026oj2DTg02B2j2[Tg02Rjj3yTg029ij1wTg02Qdj2uTg02Dgj3CTg02:Kj2tTg008`j2sTg02:mj2rTg02;Yj3qTg02<8j4oTg02P;j2LTg02AMj1nTg00ZTj1mTg02RGj3lTg02BUj6kTg02T1j2jTg000Kj6MTg00oZj4iTg02^bj2TTg00Slj1XTg00U5j1STg010Rj3hTg01C@j2fTg01J]j2eTg01:Ej4pTg0237j3dTg027Rj4YTg028=j7VTg02SMj7cTg02C9j8vTg00dSR1f0R2'7p=3f2R3f1R4/72'9p=J1034/72p=51942,93p=A1714/92p=8g00LWR5g00M7R67R2p=?g00PlR7?d42p=;P7P4g02M6P2CYp=PP4g02FNR8g02FmR9P9g02GMR:P2g02GmR;FVp=OP3P8P9P9P:P7P4g02LOP2CYP;FVp=4P3P8P9P9P:P4P2Fcp=<f3R;P8P9P9P:P3P4P2Gvp=6g01ON#Wg00N6g00PGR<#>R=#>R>#>R?#>#>#>R@#URA#QRB%U?#Q#z[g00O>f4R?/H3=RB4f6RCP?P3P4Cg%33RD11A;7J3PBP?11A2%:?RE'0RF%Z=RG%Z@R@'xRH,2F%3?RIA5F?H3A'8g00MWRF%34RJ%B4,03RKf7RL'7RMf=RNf;RO11A?RPf8RQ#:RR'0/0;,FAP3CE#?[[]5^47'9XIB%b?12PH,8Pf5RP,1A/0ERE12EHA5E?H7AI'8PNPOf9RE,1ARS/0R/0;RR,FARTP3CE#?\M\J^5F^471aG@RU121G%3@121H[[RV%3GRWg0173RXA`G@4UW?R@%3H\X^?WRWP011ALRX#312XH11AQ%:LRX'0RY12YH%3LA5YLH3A'8P3%3Sf:RS,1ARY/2Hg02ISRZg017OR[#@R\#@R]#@R^,=7R_1=7]1=7[R[';R]';g02J?R`'K%_ZRa3N%WZRbP71I73RcP4%^7RdCG%]7Re%\7Rf1D7<Rg1[7G=y7ARG'P,OfRh%w9RiPf1[71Rj1D7=R=54fRkA4f=gRl5<fPi1u7=9C7gRm94fj1PmG,OfAC7m==4fG9<fk5<f5<fC6C61tf:RkP2P31s561r23#?dAq714CoR1b8b;b<X07X17122HAJD34%:;R6,03R5125H%3;RnA55;H3A'8[[^07^17P2POf<R5,1ARoP4PQO4b7W6W3P4P2O2n2001000000121000000b9b:PCPTP3P7PR1LYE/72XA7%n3Rp%B3#3RqPUPVP@PWP0%3oRr12oHRo11ANRs/L5%:5,0s/0LRt'7PLf>,1A#3Ruf?,1A/2HRvPaPbP7PcP41I7;RcCGPePf%m<,D7R<94fjRwPiAl7g=AC7m<Rm54fC6PkP1b8b;b<X07X17X271L43%:3,04/0;Rx'7\D^07^17^27P2POf@RDfA,1ARyPEO4b7W6W3P4P2O2n2001000000120000000b9b:b>11ATRTPpPqPUPVP@PWP0PrPo12tH,8tPLp-0Rz%@^R^#@,=71=7^/;]';/K`1=7\/;[,;_/K`=NZa5NZPbP7P71I7?P3PdCGP4PcCGRcPePf1D7>R>94fjPiPfAC7<>=4f=R=PiPfPwPiPfPhPiPfPfP8P9P9P:PCEk=<flPiA4fjm1PmG,Of5<fC6C6C6C6C6PkP1b8b;b<X07X17X27X=7W@A5;?312;HAJQP?%:C,0P/0LRG12GH'8[[\I[\n^07^17^27^=7^@zP2%3D%BSRzPOPDPyPLPQPEP4PNO:b7X6vX3uP4P2O2n2001000000121000000b9b:b>,jRRNEMP7PR%B;=52YXA7PpPqPUPVP@PWP0PrPo%BC=5tsPLPaPbPcPePfP=PiAC7m>=4fgC6PkP1b8b;b<X07X17X27X=7A53;4A5x?4[^07^17^27^=7P2PzPOPDPyPQO5b7X6vX3uP4P2O2n2001000000120000000b9b:b>PTPNEMO4XFMXDJX5FX47Cib31HLPP3EM1TP6R6#X,HL,1A%S6'0RP12PHA5P;H7An'817KCRKP5PS1TEXRX#X,HO,1A%SX'0/0;,FAP3CE#?[\J^5F^47'9eAhL6;P5PS1fOX/0;,FAP3CE#?\K\J^5F^47'9ePQPLPC1e6;CpeWCWGWEXH7XMBWJWKWBWLo"). Qed.
End VP15.

(* [comment removed for export] *)
Section VP16. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kword_intro : forall segs E mem (e : expr) (a : word) off w (v : expr) (x : word),
  edenot E e = a -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + Z.of_nat w <= 2 ^ 64)%Z ->
  rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = Some (word_to_le_bytes w x) ->
  kentry_ok segs E mem (KWord (SA e off) w v).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP16"] "h02Hah13Hw0h24__x1h34__x2h44__x3h51bh61Eh72H1h82H2h92Heh:2Hrh;2Hvh<2Hwh=3Hw1h>7__arithh?4__ffh@6__sat3hA6__sat4hB8__varmaphC5__withD1ahE4cstrhF1ehG3memhH3offhI4segshJ1vhK1whL1xp;1p;2p;3p;4p;6p;<p;7p;8g005Lj1ITg002Gj1:Tg002lj1NTg003Jj1LTg00eMj1UTg0071j2;Tg0052j34Tg014Sj16Tg0152R0j2ATg011_j27Tg012Ij20Tg015LR1j1BTg00mjj1DTg00nHj2qTg012fR2j22Tg008:j2>Tg01?Sj49Tg00hIj2?Tg01DOj2=Tg00nej28Tg00>Yj25Tg008`j2<Tg02@fj4OTg02AMj1_Tg02PXj2^Tg02Q@j3]Tg021ej2FTg0237j3MTg023`j2\Tg00a\j1[Tg00b<j3ZTg024Lj2KTg025Hj4YTg025fj1XTg026Dj1WTg02B2j2ETg00ZTj1VTg026oj2JTg029ij1pTg02Dgj3TTg02Rjj3oTg027Rj4STg02:Kj2mTg02:mj2lTg02;Yj3kTg02<8j4gTg00oZj4RTg000Kj6QTg02^bj2fTg00Slj1eTg00U5j1dTg010Rj3cTg00XAj2bTg01>Hj3hTg01:Ej4aTg02DBl<iTg028=j7jTg02SMj7`Tg02C9j8nTg00dSR3f0R4'2p=1f2R5f1R6/54'5p=3g00MWR7g00PlR8P0P1P2g02_lf5R2f4R1f3R0P5P6P4M<ip=PP8P6g02LOP4CSp=CP6g02FNR9g02FmR:P:g02GMR;P4g02GmFjp=@P5P9P:P:P;P6P4F`p=GP0P9P:P:P;P5P6P4Gnp=Hg01ON#Ig00N6g00PGR9#:R<#:#:R=#:#:#:R>#NR?#LR@%N=#LRA#U[g00O>RBf7RC/;2=4@1f8RD/;5=4@6g017ORE#6RF/A1%6FRG#6RH#6#6#6#6#6RI,A217?D/0C#1f9RJ,7?/0D%BC'0%D<RK%D>R>'qRL'2%IARA#URMf>RNf<ROf:RP,7?/0J,>?PDC9f6RQ,?D,=A34P@f;RR1APIRS17?4/0RRT#118TL%BPRU#1RV10TU/2L'533f@RWPN1>?TPPC9f?RT/;J,?P,=A54M33X5@P@PC17?O/0RRX#118XL10XU/2L,5V33PWPN1>?XPPC91?P4,=A54M53SX5@1AJIRS17?R/0PRX#118XL%BJRV#1RY10XV/2L'533RZPTf=R[1>?XPJC91?JC,=A54MRX'5P0PZPXPS%D=R=,2VRXPJPV1<8VPIP=1<8=EPP0COPX1AFP%D9RX/2UR=PFPX1<8XPPPU1<8UEPP2COP=%_R%BR#11^K>183K%1>183L[[%1KRRg0173R=A]K>6UW0%1L\=^0Rg02ISRR1F8H1F8G1F8E5M85M8g02J?'\%[R3Z%IRP81K85P61K80CY%X8%W8RR1E8X%V9,J8RE'C,@R%p:R:PR1J891J8<5T8R<=T8E1E8K=o8?RK'C,@RR9P:PR1E83RG/C<,@RRHP:P8P<g02M6PKCS,@R1CGE,@R=GR95GR9GRHCHCHCH1mR;P4P5g00LWRRg00M7R;'<1l45=4R;dAk836Cgb?bBbCX28X38X4812X51065/00/2L1050#11001R0#1180L%121002/2L'533[[[^28^38^48P4%BTPWfA,7?P1PCPDO6b>b@bAbEb1b1P4CRCR1;NDR4P2EQ1;NOPQEQ1fOPRP#e,;N,7?%dP'0RO#118OL10OV/2L,5Y33PTP[1>?OPJC91?J4,=ARA54M53SeAcNPVPTP[1bNPPJC9=4MA53SePTPNP[AhPJDCaeW:W8W7W<W=W;W9XL@XJBXK7XH8XD@WFWGW6WIo"). Qed.
End VP16.

Section VP17. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma krange_intro : forall segs E mem (e : expr) lo hi,
  (lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E mem (KRange e lo hi).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP17"] "h04__x1h14__x2h24__x3h31Eh47__arithh54__ffh68__varmaph75__with81eh92hih:2loh;3memh<4segsp;1p;2p;4p;7p;8p;3g005Lj1;Tg002Gj10Tg002lj16Tg003Jj18Tg00eMj1MTg0071j25Tg011_j27Tg012fj21Tg00>Yj22Tg00a\j1>Tg024Lj24Tg025Hj4=Tg025fj1<Tg026Dj1LTg026oj23Tg027Rj4:Tg00ZTj1KTg02SMj7JTg029ij1DTg02C9j8CTg02:Kj2BTg008`j2ATg02:mj2@Tg0052j3ETg02;Yj3?Tg02<8j4FTg01IRj3GTg01:Ej4HTg028=j7ITf1R0g02FNR1g02FmR2P2g02GMR3f0R4g02GmFIp=9g01ON#;g00N6g00PGR5#0R6#0#0R7#0#0#0#6R8#8%67#8#M[g00O>g00PlR7f4R9f2R:'5,78R;,1011;4'2g02ISR;#>%;;P7147:P0f3R;,47C=%<7%L7R<P1P2P2P3P<P1P2P2P3P71375g02LOR11376R6C:,9<P7P6P1%K5,37C:,9<FJR5%D2P5GC1B<3P4P:g00LWR<g00M7R3'A1@4:=E<3dg00dS=?70CFb5b6b7X07X17X271140110:R3'211:;,23[^07^17^27P4P:f6R4/59,78P;P0O4b4P4f5P9AG;:0CHeUX97W:W8W;W3W<o"). Qed.
End VP17.

Section VP18. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kalign_intro : forall segs E mem (e : expr) m,
  (0 < m)%Z -> (bv_unsigned (edenot E e) mod m = 0)%Z -> kentry_ok segs E mem (KAlign e m).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP18"] "h01Eh11eh21mh33memh44segsp;1p;2p;3p;4g005Lj1<Tg002Gj10Tg002lj12Tg003Jj16Tg00eMj1;Tg00nej27Tg0071j23Tg011_j24Tg01I2j25Tg0052j31Tg00oZj48Tg01Ggj29Tg01:Ej4:Tg01ON#<g00N6g00PG#0#0#0R0#0#0#0#2R1#6%20#6#;[g00O>g00PlR0g00dSR2f0R3'7f4R4f2R5'3,41f1R6'5=1021725f5R7f3R8'3,41/55=102P6P3C8f6P7P41985C:eUUW2W1W3W0W4o"). Qed.
End VP18.

Section VP19. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kimg_intro : forall segs E mem lo hi,
  (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  (forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
  kentry_ok segs E mem (KImg lo hi).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP19"] "h01ih11Eh22hih32loh43memh54segsh61xp;1p;2p;3p;4g005Lj1?Tg002Gj11Tg002lj14Tg003Jj13Tg00eMj1>Tg012fj20Tg00mjj17Tg00nHj2;Tg00nej26Tg00>Yj22Tg008:j2:Tg029ij19Tg0052j35Tg00oZj48Tg01F\j2=Tg01:Ej4<Tg01ON#?g00N6g00PG#1R0#1#1R1#1#1#1R2#4R3#3%41#3R1#>R4]6g00PlR5g00dSR6f1R7'0%70%72';R2,07f4R0f0R8'0f3R9,68'2f6R:1:37R3O1%91R1554[^0510601092R2f5R6/081680'2f7R;P3O1=541[^05R1'2f2P2P1P7P8C8C8P;P:P61=09C<eUUUX25W3W4W1W5o"). Qed.
End VP19.

Section VP20. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kzero_intro : forall segs E mem (e : expr) (a : word) off (n : expr) len,
  edenot E e = a -> bv_unsigned (edenot E n) = len ->
  (0 <= bv_unsigned a + off)%Z -> (0 < len)%Z -> (bv_unsigned a + off + len <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < len)%Z -> mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (Z_to_bv 8 0)) ->
  kentry_ok segs E mem (KZero (SA e off) n).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP20"] "h01ih12Hah24__x1h34__x2h44__x3h51Eh62H1h72H2h82H3h92Heh:2Hnh;2Hzh<7__arithh=4__ffh>6__sat4h?6__sat5h@8__varmaphA5__withB1ahC1bhD1ehE3lenhF3memhG1nhH3offhI4segshJ1xhK1zp;1p;2p;3p;4p;6p;7p;8g005Lj1QTg002Gj19Tg002lj1ITg003Jj1GTg00eMj1lTg0071j27Tg0052j35Tg011_j2:Tg00nej21Tg012Ij20Tg00mjj1JTg00nHj2kTg012fj26Tg00>Yj22Tg008:j28Tg01DOj2aTg02PXj2\Tg02Q@j3[Tg014Sj1@Tg021ej2?Tg0237j3KTg023`j2ZTg00a\j1YTg00b<j3XTg024Lj2HTg025Hj4WTg025fj1VTg026Dj1UTg026oj2BTg02Dgj3FTg00ZTj1TTg02B2j2ETg02Rjj3STg029ij1RTg027Rj4DTg02:Kj2jTg008`j2iTg02:mj2hTg02;Yj3fTg02<8j4eTg00oZj4bTg000Kj6NTg02^bj2LTg00Slj1MTg00U5j1PTg01B2j2OTg010Rj3`Tg01C@j2_Tg01@gj2cTg01:Ej4dTg028=j7^Tg02SMj7]Tg02C9j8gTf2R0f1R1':f0R2'0p=4g00dSR3/62p=31212,20p=<1631/22p==g00PlR4P1g02LOP2CDp=CP1g02FNR5g02FmR6P6g02GMR7P2g02GmF^p=;P0P5P6P6P7P1P2F]p=Af3R8P5P6P6P7P0P1P2Ggp=>g01ON#Qg00N6g00PGR5#9R9#9#9R:#9#9#9R;#IR<#GR=%I:R:#GR>#lR?]Jg00O>R@f6RAf4RB'7=5=8f7RC/70,:<=541f5RD=4<B#31138REA4<CA/0B%J9RF%J;R;'kRG'6%32RH112A'2f<RIf:RJf9RK54<RL/01,8<O118:3,a>R>55?[^04P=PKA4<2KR:11:Gf=RMf8RN'7,:<RO#310:O/6G3<'=f>R:/7K,:<,12,2HP:f;RP94<0/01,8<O1=5?>[^04'2XC=P4PA11LG10L2/6G7<H,=L1121,2HP:1:<IRL/0P/01,8<O1=5?>[^04'2XK4A4<KNRQ11QG%3A10QA/6G3<'=112C,2HPMA4<PJ/01,8<O1=5?>[^041\F;113F%3;113G[[%3FRQg0173RRA[F;1UW1%3G\R^1Qg02ISRQg017ORR#@#@R;#@,?41?4;1?4R5K45K4g02J?'Z%YQ3X%QQP41H40P11H48CW%V4%U4RQ1B451B495F4R9%T5,B4R55F41E4F=S4<RF'C,;QRR%R6R6PQP41E43R;g02M6RSP5CD,;QP6PQ1C;9,;QRTP6P4P9PSPFCD,;Q1C;5,;Q=AQR5AQ9AQTC>C>C>1jQ7P2P0g00LWRQg00M7R7'i1h20=5Q7dAf431Ceb=b@bAX24X34X441021/00/6G1008#3108BR8118G%3D108D/6G3<'=[\E[^24^34^44P2PKPPPLPBPDPAO6b<b>b?P2Cb17IC,:<RAPBEN17IJPDEN1LJNRD#M,7I%PD54<RB11BG%3A10BA/6G3<'=112O,2HPM1LIJRJ#M,7:%PJ54</01,8<O1=5?>[^04'2e1OIC9`ID1OMN,12,2HPM1_:J/01,8<O1=5?>[^04'2ePMPIPP1cDCCdeW;W8W7W6W:W9XE4XG@XH4XB=WDWFW5WIo"). Qed.
End VP20.

Section VP21. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma kblob_intro : forall segs E mem (e : expr) (a : word) off (n : expr) k bs,
  edenot E e = a -> eb E k = bs -> bv_unsigned (edenot E n) = Z.of_nat (length bs) ->
  (0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off < 2 ^ 64)%Z ->
  (bv_unsigned a + off + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (forall i, (0 <= i < Z.of_nat (length bs))%Z ->
     mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  kentry_ok segs E mem (KBlob (SA e off) n k).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP21"] "h01ih12Hah24__x1h34__x2h44__x3h51Eh62H1h73H1'h82H2h92Hbh:2Heh;2Hnh<2Hzh=7__arithh>4__ffh?6__sat3h@6__sat4hA8__varmaphB5__withC1ahD1bhE2bshF4cstrhG1ehH1khI1lhJ3memhK1nhL3offhM4segshN1xhO1zp;1p;2p;3p;4p;6p;7p;8g005Lj1ITg002Gj1<Tg002lj1MTg003Jj1KTg00eMj1pTg0071j29Tg0052j35Tg005lj2?Tg011_j2=Tg00mjj1XTg00nHj2mTg00nej20Tg01Nnj2RTg015Lj1PTg00>Yj21Tg012Ij22Tg008:j2:Tg01F<j1aTg00d7j4ATg01DOj2@Tg02AMj1`Tg02PXj2_Tg02Q@j3^Tg00a\j1]Tg024Lj2LTg025Hj4\Tg025fj1[Tg026Dj1ZTg02B2j2JTg00ZTj1YTg026oj2DTg029ij1oTg02Dgj3WTg02Rjj3nTg027Rj4VTg02:Kj2lTg008`j2UTg02:mj2kTg02;Yj3hTg02<8j4gTg00oZj4TTg000Kj6FTg02^bj2NTg00Slj1OTg00U5j1QTg01B2j2STg010Rj3fTg01C@j2eTg01E1j3dTg01:Ej4iTg012fj2ETg028=j7cTg02SMj7jTg02C9j8bTf1R0f0R1'R#Pp=8g00PlR2?501p=;f2R3/=0/21p=6g00dSR4/E1p=31230/E1p=71101,13p=41E40/11p=>P2P0g02LOP1CVp=HP0g02FNR5g02FmR6P6g02GMR7P1g02GmFcp=CP3P5P6P6P7P0P1Fjp=Gf3R8P5P6P6P7P3P0P1Gbp=Bg01ON#Ig00N6g00PGR5#<R9#<#<R:#<#<#<R;#MR<#KR=%M:R:#KR>#pR?]Ng00O>R@g00MW%I>RAf7RBf5RC'9f4RD55=f8RE/?3=5A0f9RF/9D,=<18>3';f6RG96<B#3A6<EB%X9RH%X;R;'mRI'0A6<FE18>C;7I%31RJ1R>BRK#PRL,01'1f>RMf<RNf;RO56<RP/20,:<O1P>%a0RQPE1::4R:CA,@>55?[^02P=POA6<1ORR10RIf?RSf:RT'9,=<RU#3A7RUI34'>1?SF,8>RR/;Uf@RV/9O,=<,01,1JPVf=RW96<3/20,:<O1P>PQfA/?OP:CA,@>RX55?[^0234XD=P2PL%3PRY10PIRZA7P1I,1J341;R11010,1JPVA6<MW/20,:<O1RR=5?X[^0234XO2PAPB18>ERXA7PXI'>94YZ18>1/;X18>F,01,1JP>PQP3P:CA,@>95?R[^0234XIAA6<OTRA10AI%3LRRA7ALI34'>1;LLRA101X,1JPSA6<WN/20,:<O1P>PQPFP:CA,@>55?[^02RX'1%`KPR1_H;104H%3;104I[[%3HRRg0173RKA^H;0UW1%3I\K^1Rg02ISRR#]%IRP21L23P01L28C\%[2%Z2RR1J24RK%Y5,D2R;'H,CRRZ%o6R6PR1D251D295W2R9=W2;1J2H=n2<RH'H,CRR;P6PRP2P9g02M6PHCV,CRRHP6PR1HK9,CRR9P6AGRZ;9GRH9GR9CBCBCBCB1lR7P1P3g00LWRRg00M7R7'U1k13=5R7dAh240Cgb>bAbBX22X32X42%331203?78I1238/0I128D#312DCR3103I%3GA73GI34'>[[[[^22^32^42P118>OPM1=<SP8PCPGPBO7b=b?b@bFPAPX1U2LP1CTCT1?MERLPCEF19MF,=<RCPDEF19MNPGEF1NNTRG#O,9M%QG56<RD10DI%3CA7DCI34'>18>LRL/;C101U,1JPS1NMNRN#O,9V%QN56</20,:<O1P>PQ1?VTP:CA,@>R>55?[^0234e1SMFR:9fMG1;L:1SST,01,1JPS1eVN/20,:<O1=5?>[^0234ePSPMPWAdGFECieW<W8W7W6W;W9W:WEWHXK@XL2XC=WGWJW5WMo"). Qed.
End VP21.

(* [comment removed for export] *)
Section VP22. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma wrap_mem_none_low : forall ph sp argv envp uid hw rnd (i : Z),
  (0 <= i)%Z -> (i < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem ph sp argv envp uid hw rnd (Z_to_bv 64 i) = None.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP22"] "p'0h01Hh14__x1h24__x2h32H1h47__arithh54__ffh66__sat1h76__sat2h88__varmaph95__with:2Hah;4__x3h<1bi001bh=1xi011xh>1yh?2H0h@2HihA3HsphB2HuhC4argvhD4envphE2hwhF1ihG2phhH3rndhI2sphJ3uidhK1zp;1p;2p;3p;4p;7p;6p;8g002Gj16Tg002lj1WTg003Jj1KTg005Lj1CTg011_j21Tg02P;j23Tg00nej20Tg02O=j1^Tg00mjj1>Tg00nHj2\Tg00>YR0j2DTg02PXj2YTg02Q@j3qTg014Sj1ETg021ej2ATg0237j3STg023`j2gTg00a\j1fTg00b<j3dTg024Lj2UTg024jj1aTg025Hj4LTg025fj1`Tg026Dj1_Tg026oj2@Tg02B2j2;Tg02Rjj3]Tg029ij1JTg02`Nj3ITg02RGj3HTg027Rj4MTg02SMj7[Tg02:Kj2ZTg008`j2FTg02:mj2XTg0052j35Tg02;Yj3pTg02<8j4oTg02a1j2VTg02T1j2nTg008:j2=Tg00eMR1j1mTg02aNj24Tg02akj7?Tg01Nnj2TTg015Lj1RTg02bij28Tg01F<j1NTg02cFj3QTg01DOj2OTg00=Xj2<Tg02cdj2eTg02dDj4PTg00ZTj1cTg01@Kj6GTg000Kj6hTg02d`j3bTg02Zhj8iTg012fj2jTg028=j7kTg02C9j8lTg00dSR2f0R3'jp=2g00PlR4f1R5g02M6P3CMp=9P5g02FNR6g02FmR7P7g02GMR8P3g02GmFkp=7f3R9P6P7P7P8f2R:P5P3Glp=:g00LWR;g01o6R<753p=Bg02[eg00PGR=#6R>#6#6R?#6#6#6R@#WRA#KRB%W?RC#KRD#C#CREg02\e%23f7RF,1Ag02]eRG'3,05f8RH#^11AHRI#2%>>RJ%>@RK'\RL,0I'D1YJKRI102J%2K102L[[RM%2JRNg0173ROAqJK5UW:RK%2L\O^:NRNP0f;RO,1ARP#210PLf6RQ#210QL'DP:f=RR,1ARS#2RTf>,1ARU/0LRVg02ISRWg017ORX#E#ERY#E,A41A4Y1A4X5S45S4g02J?'g%fWRX3d%CWRWP41U4:RYP5%a4CLRZ%`4R[%_4R\1@4>R>1;4J=]4ARJ'9,7\%J7R]P\1@4=R^%>?R?,;4%6@#6#6#6#>R@,;4R_5I4=I4_9H4>'9,7\R_P]P\P41;42g02LOP^CM,7\R`P]P\P6P7P7P8P`19^J,7\F[C:C:C:1Z\8R8P3P:g00M7RJ,F;1X3:=5;JdAp425CoRJb5b8b9X14X24105L1V?@/V@R@,3:,05%2:%29109L'D[[[^14^24P3f@,1AR?f:R`P5PHf9R7O5b4W3W0P5P3O2n2001000000121000000b6b7,n91=A9,1A=549P4f4R6%mDRaP1PDPaP;Pa14P3P;Pa133PRbf<RcPOP`P7PHPFPQF?Rd,TD#R'8%Nb9QDd%JDRdn0100000020000Pdn01000000200001OD3RbP;Pa13PGRe/43183P'<1=C2,ODRCPdn0100000020000n10110100021010000;5dXK4P;11A`R2/46RfP<P01453#B105:Rg[103514:5#B[Rh149:#B\g1e53P3n2001000000120000000X>4X=4RiPh^>4^=4RhP3PPf5RjPIPMPKPNP0PT10SL10HUP6f?,1ART#210?LPXPWPZP[P\P_P]19^>,7\C:P8PJb5b8b9X14X24135@,03Pg[^14^24P3fB,1APcP`O3b4W3W0P5P3O2n2001000000121000000b6b7O3b0CPA5;<fP;P<P1PDPaP;PaP3P;Pa11AcRf,3QRgPRPcPOP`P7PHPFF?Rc,TD#R'8%Ng9QDcPdn0100000020000Pdn0100000020000PbP;Pa13fGRc/4QRg18Qf'<PCPdn0100000020000n10110100021010000=5adX<;P;14ejReP<PiPhP3PcPQPIPMPKPNP0%2UPV13TG,07Pj%2?fA,1A/0LPXPWP4PYP51U49CLP[P\%c=,@49H4>,9^,7\R\P]P\C:P8PJb5b8b9X14X24X;4135:,0313:9,05[^14^24^;4P3PGfC,1APRPOO4b4W3W0P5P3O2n2001000000120000000b6b7O3b0CPA5;<eP;P<P;Pa18FS,<3PCPdn0100000020000=5adX<;1FadPgP3EGb014PjP3EGb01=A6RP,1ARgP3EhP1PDPaPOP`P7PHPFPQPjF?=b`PPbP;Pa132G/4g18g2'<PCPdn0100000020000n10110100021010000=5adebBbAP7PHPFPQPjP6P91=A:Gi=5adeW@W?XF4WHXEBXJBXDEWCWIWGo"). Qed.
End VP22.

(* [comment removed for export] *)
Section VP23. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ext_val_zx_id : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> ext_val false 0 n v = v.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP23"] "h02Hah11Hh24__x1h34__x2h41zh52H0h62Hvh77__arithh84__ffh96__sat0h:6__sat1h;6__sat2h<6__sat3h=8__varmaph>5__with?4cstrh@1nhA1vp;1p;2p;3p;4p;7p;6p;8g002Gj16Tg002lj1]Tg003Jj1NTg011_j24Tg00mjj17Tg015Lj12Tg02a1j23Tg00nHj25Tg00nej21Tg02O=j1GTg00>YR0j29Tg01I2j2=Tg008:j2BTg0052j38Tg02eaj2VTg02AMj1UTg02PXj2@Tg02Q@j3>Tg00a\j1TTg005Lj1STg024Lj2QTg024jj1MTg025Hj4LTg025fj1KTg026Dj1ITg02B2j2HTg026oj2:Tg027Rj4;Tg029ij1JTg02SMj7FTg02:Kj2ETg008`j2DTg02:mj2OTg02;Yj3PTg02<8j4CTg02fSj3RTg000Kj6?Tg02g6j2\Tg02gSj1[Tg00Fej4ZTg012fj2WTg028=j7XTg02C9j8YTg00dSR1f0R2'Wp=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFXp=<f3R7P4P5P5P6f2R8P3P2GYp=Ag00MWg00PGR9#6R:#6#6R;#6#6#6R<#]R=#NR>14=2%7:R?%7;R;%23'3'5'1%G314=3R@#0%7<R<,5?RA,1@'9g00PlR@14=8RBf4#2,3;,5?,=2,B==8>7X4@P@PB1B=2=8>7X4@1V=8%27RC,3;,5?RD,=B%U7%0C1@?<111?RC%0<111A[[%0?REg0173RFA>?<3UW0%0A\F^0Ef6#2,3;,@?f7R<#2,3;#0f8RG#2,3;,5?,11[\Cf9RC#2,3;RH=>?3VFX0E15?HRH#0\F^0EP014=<R<#011<A14=GRG#011GH'9f514=C#0f:,4=/1Ag02ISRA#T%SAP@1Q@8P3%M@CL%K@%I@RAP@1H@1g02LO1:@9RCC;,<ARG%J5RHPAP@PCg02M61:@:C;,<AR:PHPAP4P5P5P6PGP:FFCACA1EA6P2P8g00LWRAg00M7R6'D1O28=8A6dAP@13CCb8b=b>X2@X3@%021138%081187'9[[^2@^3@P2f=#2,3;,5?f<,4=P8f;O4b7W5W1P3P2O2n2001000000121000000b9b:b;b<b?9RBDE?%79,\B%[BE?b1g01o6g017OP8P3CZ=8>3eW6WAW@o"). Qed.
End VP23.

Section VP24. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma ext_val_sx_id : forall n (v : word),
  (1 <= n)%nat -> (bv_unsigned v < 2 ^ (8 * Z.of_nat n - 1))%Z -> ext_val true 0 n v = v.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP24"] "h02Hah14__x1h22H0h31Hh41zh53Hn0h67__arithh74__ffh86__sat0h96__sat1h:6__sat2h;6__sat3h<8__varmaph=5__with>4cstrh?4__x2h@6__sat4hA6__sat5hB4__x3hC4__x4hD1xhE2HnhF2HphG2HvhH1nhI1vhJ1yp%0p&0p;1p;2p;4p;3p;8p;6p;<p;7p;Bg002Gj1CTg002lj1jTg003Jk100Tg014Sj1JTg0152R0j2VTg011_j27Tg00mjj1NTg02P;j21Tg00nHj22k104Tg00nej26Tg02O=j1kTg00>YR1j2LTg015LR2j1<Tg02a1R3j23Tg02h4k10;Tg008`j2^Tg012fR4j2ETg02@fj4[Tg02AMj1ZTg02PXj2BTg02Q@j3GTg012Ij28Tg00a\j1qTg005Lj1pTg024Lj2UTg025fj1nTg026Dj1lTg02B2j2MTg026oj2PTg02`Nj3QTg02RGj3cTg02Dgj3bTg02:Kk20CTg02:mk20BTg0052j3Kk101Tg02;Yk30ATg02<8k40@Tg02hRk80>Tg02hok20=Tg021ej2FTg02iXk30<Tg023`j2TTg00b<j3STg029ik10:Tg02jAk303Tg01@Kj6RTg02jek202Tg000Kj6ITg02kGR5j1gTg02kgR6j2fTg01I2j2@Tg02lDj2WTg02lkR7j1]Tg02mIj1~Tg02DBl<eTg02mgj4zTg02g6j2OTg024jj1xTg025Hj4YTg02eaj2wTg020fj1vTg021Dj2yTg022Nj3uTg02nRj2XTg00ZTj1tTg02fSj3iTg01icj1sTg02o>j6rTg02obk305Tg02gSk106Tg00Fek407Tg027Rj4`Tg028=k708Tg0237k309Tg02C9j8aTg008:j2oTg02C]l<dTg030ClBmTg02SMk70?Tf1R8f0R9#<'3p==g00dSR:/E9p=0g00PlR;?K89p=51^;9p=>g00MWR<P;P0P2P4g02_lf5R4f4R0f3R=f2R>P8P9M<ep=\16:9p=9P;P8g02KKP9C`p=HP8g02FNR?g02FmR@P@g02GMRAP9g02GmK08p=4B09;89p=;P;P8g02LOP9C`p=?P=P?P@P@PAP>P8P9Gap=_1o>8=K=9p=:P<g01oVRBP;P;P5P2P7P=g030iP>P8P9M<dp=}PBPBPBP;P;P;P6P7P7P7P3g031FP4P0P=P>P8P9MBmp=|PBP;P;P;P7P7P4P0P=P>P8P9M<dp={P;P8g02M6P9C`p=Af6R7P?P@P@PAP4P0P=P?P@P@PAP>P8P9GaGap=DP>P?P@P@PAP8P9K0?p=hg00PGR3#CR6#CS00#CR2#C#C#CR5#jRC$00RDg017ORE#JRF/V817C8%N6RG%N2RH/=>%N3RI'1'2'6%k>17C>RJ#0%N5R5,2GRK,6J'LP;%<0RJ,3HRL/1IRM,2GRN,3GRO%<4RP,3HRQ,2GRR,59X4;RSP;&0;MRT,2GPSP;P;&04GRSPSPTPLP;\;/^S1VF01EIJRSPFPI%>IRTP0PJ%>JE\P>C[RJPS%Z4RU%0PRV1BG5RW%9GRX%05%9K[[RY%0GRZg0173R[AGG58UW0R5%0K\[^0ZR\f8,=H/1I,BGR]f9R^,=H/1IR_#0f:R`,=H/1IRa,2G#9[\XRbf;Rc,=HRd/1IRe=GG8V[X0ZRf12GeRg#0\[^0ZRhP117C^Ri#0Rj16iKRi18eI/5dP717Cc#0Rcf<Rk,7CRl/6KRmg02ISRn#qRo%pnRp1U;8Rq%n;Rr%l;Rs1M;HS011P;3Rt5Q;Ru1M;IRv5c;Rw=b;v/Hu'420CsARxP9P>g00LWRyg00M7Rz'^20B9>=KyzdB0A;:8H0@Ryb7b<b=X1;13H9R{/1I/8I/5{^1;P9f?R|#<R}O1b6W2W3P8P9O2n2001000000120000000b8b9b:b;b>b5L0>POPJPSPUPVPWPYP5P\P]PbPfPhP1PjPi%0eReP720=;H1F;FRi60<;1F;ERj';g02J?Rh'T=SnoPpPqPrPs1?vt,4s&0:@Rf1M;:Rb/?w,4sC_PxPyb7b<b=X1;1EI913H8/1I#0[^1;P9P}P`O2b6X2mX3cP8P9O2n2001000000120000000b8b9b:b;b>b5:03GMER13NGRM202NGEI12GL,5MP;17C0RMPDPC%j2R2%g7'fRL%<7RN,3HRc,2GS02,@9'WP4C:X4;P;PMPDPC1WL9P4C:X4;%g4Rw,f2R]#]RV,5QRU15QQP;P;&01;RSP9XD;RJPS1589#~XJ;XD;PQPQ%>QPVPQPJPJ%]9#>XDBP]PQP2PH%>HPwPPPJP4PP%>PRJC}E|E{M<e1VF41EIPS03PFPIPTP4PPPJE\P=C[S04Q03%Z7S05%0NS06PWPYP5P\1BG_S07%0a%9g[\XS081=HkRg/1IR_=GG8V[X0ZS0912G_R_#0\[^0ZS0:1BGdS0;%0gf=Rd,=HRJ,2G#9[\XS0<f>RP,=HRw=GG8V[X0ZS0=12GwR2#0\[^0ZS0>P1%0lS0?Pm15wwP^17CPRw#0S0@17C|Rl/6KS0APoPpPqPr1Huu,4sPxPyb7b<b=X1;15{{^1;P9fBR{#<RuO1b6W2W3P8P9O2n2001000000120000000b8b9b:b;b@bAb>b5CzPUP;PcPDPC17C7RU12G9Rq/OGRQ'8/@q/1QP7C:X4;P;11cI,2GRc/3GRQPDPC1O9GRq,8U/@9/1qP7C:X4;P;PcPDPC18U9f7Rq#<RB,3H/1I,2GRV/3G'@/19P7C:X4;P;17C4RS/8cROPDPC119VP7C:X4;1VF71EINR~PFPIPTP7PN%>NE\P0C[S0BP~%ZqS0C%0BS0DPWPYP5P\1BGaS0E%9_\e\XS0F11JIRe=GG8V[X0ZS0G12Ge#0\[^0ZS0H1BGgS0I%0J%92[\XRJ13H}R}=GG8V[X0ZRg12G}#0\[^0ZRZP117CdR[#0Re16[KR_11}I,2GR},8wRa/1},5wP`%0lRlf@S0J,7C/6KRKPoPpP;1U;>P8%x;RwCYPr1P;6R69b;tRB=c;6,Ht,4sPxPyb7b<b=X1;X?;1898/18,59^1;^?;P9fC#<S0K,3HRN/1I,2GS0L17C{S0MO2b6W2W3P8P9O2n2001000000120000000b8b9b:b;b@bAb>b511Oc,5SP;PUPDPCP9PqC:X4;1wC718UV/1VP9ERb21@OQQ0BP~Q0CQ0DPWPYP5P\Q0EQ0FQ0GQ0HQ0IPJPgPZP1PeP_%0a13}G,6a'LP`%JFRF#JRa#JR}#J,F;RV%v3,y;1F;aRa5u;';RU1;ai,;j/Th'X1;jV/Th,XV=SnoRV5SnPpP;P;1U;0P>PwCYP81U;=CYS0NPrPsPs1M;GRa,Ab,4sS0OPfPsQ01Q00,P;Rq5Q;,?b,4sS01Pf%t3,P;R3,Ab,4sFDPfPs1?vq,4sS00PfPsAQ;6aRq/H3,4sPfPs1?bt,4sRvPfPs1At6,4sRSPf1?bB,4s1ABq,4s5hsC_FDFDPxPyb7b<b=X1;X?;XB;XC;13H0#0Rq%90[\X1EI0RB13=G/50%0=R{16041847RT#0137G,6T'L[[[[[^1;^?;^B;^C;P9Q0K12GNQ0LQ0MP7PkPPP>Q0JO9b6X2KX3lP8P9O2n2001000000121000000b8b9b:b;b@bAb>b59iOQEI1OQGQ0BP~Q0CQ0DPWPYP5P\Q0EQ0FQ0GQ0HQ0IPJPgPZP1PeP_AK;G:R:#sP`PoPpPwPrPsP?P@P@PA1Hab,4sErPxPyb7b<b=g02L2\:P9b6X2KX3lP8P9O2n2001000000120000000b8b9b:b;b@bAb>b5:05cGEIQ02P8ER%]LP9ERb2PDPC1W]MP0C:e1@MRQ04Q03Q05Q06PWPYP5P\Q07Q08Q09Q0:Q0;Q0<Q0=Q0>P1Q0?Pm16[2,LeP^Q0@Q0A1F;}1F;F/;i';,;j/Th,XU=SnVPpQ0NPrPsPsQ0OPfPsQ01Pf1Ab6,4sFDPfPsQ00PfPsAQ;3a/H6,4sPfPsPvPfPs1At3,4sPfAhsvSC_FDFDPxPyb7b<b=X1;X?;XB;XC;%9=\q\X130G/5=1607%041647'L[\{[\B[^1;^?;^B;^C;P9Pu13HuRu/1I,2G12GufA,7CP7PkPdP>P|O9b6W2W3P8P9O2n2001000000121000000b8b9b:b;b@bAb>b59iMREI1OMI&06MEIbFb3PzPEP=P>H07=KD>eWGWEWIXH<o"). Qed.
End VP24.

Section VP25. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_eq_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_EQ v (Z_to_bv 64 z) = Z.eqb (bv_unsigned v) z.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP25"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1VTg003Jj1DTg00mjj1<Tg00nHj2MTg00nej21Tg00>YR0j26Tg011_j25Tg01mTj24Tg0052j33Tg008`j2;Tg008:j2=Tg02PXj2UTg02Q@j3TTg00a\j1STg005Lj1LTg024Lj2KTg025fj1HTg026Dj1FTg026oj2ETg02B2j28Tg02Rjj3CTg027Rj47Tg029ij1BTg02SMj7GTg02:Kj2ATg02:mj2ITg02;Yj3JTg02<8j4@Tg02T1j2?Tg000Kj6NTg00_hj3>Tg031gj3OTg012fj2PTg028=j7QTg02C9j8RTg00dSR1f0R2'Pp=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFQp=9f3R7P4P5P5P6f2R8P3P2GRp=:g00PGR9#2R:#2#2#2#2#2R;#VR<#Dg00PlR=%02%<:R:%<;R;'MR>,12R?'6P=P3g00LWR@15<7RA/4214A833X2=15<8/43RA,;@1=<3RB,5<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'6P8f5#0f6/1>g02ISR7#S%L71K=3%H=%F=R7P=1E=9R9g02M618=:=C=<C7,97R:%B5R0P7P=18=1g02LOP9C7,97R9P0P7P4P5P5P6P9P:FGC:C:1A76P2P8g00M7R7,;@1I28=3@7dAJ=13C@b7b:b;X1=%03%08118>'6[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,?3ENA><8B=3@Aeg032V?O8B=3@AeW5W2W<o"). Qed.
End VP25.

Section VP26. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_ne_lit : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_NE v (Z_to_bv 64 z) = negb (Z.eqb (bv_unsigned v) z).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP26"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1WTg003Jj1ETg00mjj1=Tg00nHj2OTg00nej21Tg00>YR0j27Tg011_j26Tg01mTj25Tg033Hj13Tg0052j34Tg008`j2<Tg008:j2VTg02PXj2UTg02Q@j3TTg00a\j1NTg005Lj1LTg024Lj2KTg025fj1ITg026Dj1HTg026oj2FTg02B2j29Tg02Rjj3DTg027Rj48Tg029ij1CTg02SMj7GTg02:Kj2BTg02:mj2JTg02;Yj3ATg02<8j4@Tg02T1j2MTg000Kj6?Tg00_hj3PTg031gj3QTg012fj2>Tg028=j7RTg02C9j8STg00dSR1f0R2'>p=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFRp=:f3R7P4P5P5P6f2R8P3P2GSp=;g00PGR9#2R:#2#2#2#2#2R;#WR<#Eg00PlR=%02%=:R:%=;R;'OR>,12R?'7P=P3g00LWR@16<7RA/52#315A8#334X2=16<8/53#3RA,<@1V<3RB,6<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'7P8f5#0f6/1>g02ISR7#N%L71K=3%I=%H=R7P=1F=9R9g02M619=:=D=<C8,:7R:%C5R0P7P=19=1g02LOP9C8,:7R9P0P7P4P5P5P6P9P:FGC;C;1B76P2P8g00M7R7,<@1J28=4@7dAA=13C@b7b:b;X1=%03%08118>'7[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,M3E?AP<8B#3=4@Aeg033f?Q8B=4@AeW5W2W<o"). Qed.
End VP26.

Section VP27. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_ltu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU v (Z_to_bv 64 z) = Z.ltb (bv_unsigned v) z.
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP27"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1VTg003Jj1DTg00mjj1<Tg00nHj2MTg00nej21Tg00>YR0j26Tg011_j25Tg02bij24Tg0052j33Tg008`j2;Tg008:j2=Tg02PXj2UTg02Q@j3TTg00a\j1STg005Lj1LTg024Lj2KTg025fj1HTg026Dj1FTg026oj2ETg02B2j28Tg02Rjj3CTg027Rj47Tg029ij1BTg02SMj7GTg02:Kj2ATg02:mj2ITg02;Yj3JTg02<8j4@Tg02T1j2?Tg000Kj6NTg034Xj3>Tg031gj3OTg012fj2PTg028=j7QTg02C9j8RTg00dSR1f0R2'Pp=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFQp=9f3R7P4P5P5P6f2R8P3P2GRp=:g00PGR9#2R:#2#2#2#2#2R;#VR<#Dg00PlR=%02%<:R:%<;R;'MR>,12R?'6P=P3g00LWR@15<7RA/4214A833X2=15<8/43RA,;@1=<3RB,5<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'6P8f5#0f6/1>g02ISR7#S%L71K=3%H=%F=R7P=1E=9R9g02M618=:=C=<C7,97R:%B5R0P7P=18=1g02LOP9C7,97R9P0P7P4P5P5P6P9P:FGC:C:1A76P2P8g00M7R7,;@1I28=3@7dAJ=13C@b7b:b;X1=%03%08118>'6[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,?3ENA><8B=3@Aeg035E?O8B=3@AeW5W2W<o"). Qed.
End VP27.

Section VP28. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_ltu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_LTU (Z_to_bv 64 z) v = Z.ltb z (bv_unsigned v).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP28"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1VTg003Jj1DTg00mjj1<Tg00nHj2MTg00nej21Tg00>YR0j26Tg011_j25Tg02bij24Tg0052j33Tg008`j2;Tg008:j2=Tg02PXj2UTg02Q@j3TTg00a\j1STg005Lj1LTg024Lj2KTg025fj1HTg026Dj1FTg026oj2ETg02B2j28Tg02Rjj3CTg027Rj47Tg029ij1BTg02SMj7GTg02:Kj2ATg02:mj2ITg02;Yj3JTg02<8j4@Tg02T1j2?Tg000Kj6NTg034Xj3>Tg031gj3OTg012fj2PTg028=j7QTg02C9j8RTg00dSR1f0R2'Pp=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFQp=9f3R7P4P5P5P6f2R8P3P2GRp=:g00PGR9#2R:#2#2#2#2#2R;#VR<#Dg00PlR=%02%<:R:%<;R;'MR>,12R?'6P=P3g00LWR@15<7RA,42148A33X2=15<8,43RA,;@1=<3RB,5<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'6P8f5#0f6/1>g02ISR7#S%L71K=3%H=%F=R7P=1E=9R9g02M618=:=C=<C7,97R:%B5R0P7P=18=1g02LOP9C7,97R9P0P7P4P5P5P6P9P:FGC:C:1A76P2P8g00M7R7,;@1I28=3@7dAJ=13C@b7b:b;X1=%03%08118>'6[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,?3ENA><B8=3@Aeg035E?OB8=3@AeW5W2W<o"). Qed.
End VP28.

Section VP29. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_geu_lit_r : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU v (Z_to_bv 64 z) = negb (Z.ltb (bv_unsigned v) z).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP29"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1WTg003Jj1ETg00mjj1=Tg00nHj2OTg00nej21Tg00>YR0j27Tg011_j26Tg02bij25Tg033Hj13Tg0052j34Tg008`j2<Tg008:j2VTg02PXj2UTg02Q@j3TTg00a\j1NTg005Lj1LTg024Lj2KTg025fj1ITg026Dj1HTg026oj2FTg02B2j29Tg02Rjj3DTg027Rj48Tg029ij1CTg02SMj7GTg02:Kj2BTg02:mj2JTg02;Yj3ATg02<8j4@Tg02T1j2MTg000Kj6?Tg034Xj3PTg031gj3QTg012fj2>Tg028=j7RTg02C9j8STg00dSR1f0R2'>p=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFRp=:f3R7P4P5P5P6f2R8P3P2GSp=;g00PGR9#2R:#2#2#2#2#2R;#WR<#Eg00PlR=%02%=:R:%=;R;'OR>,12R?'7P=P3g00LWR@16<7RA/52#315A8#334X2=16<8/53#3RA,<@1V<3RB,6<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'7P8f5#0f6/1>g02ISR7#N%L71K=3%I=%H=R7P=1F=9R9g02M619=:=D=<C8,:7R:%C5R0P7P=19=1g02LOP9C8,:7R9P0P7P4P5P5P6P9P:FGC;C;1B76P2P8g00M7R7,<@1J28=4@7dAA=13C@b7b:b;X1=%03%08118>'7[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,M3E?AP<8B#3=4@Aeg0367?Q8B=4@AeW5W2W<o"). Qed.
End VP29.

Section VP30. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma branch_geu_lit_l : forall (v : word) z,
  (0 <= z < 2 ^ 64)%Z ->
  branch_taken BC_GEU (Z_to_bv 64 z) v = negb (Z.ltb z (bv_unsigned v)).
Proof.
ltac2:(KReplay.run1 (kr_t_SymRun ()) ["VP30"] "h02Hah14__x1h21zh31Hh42H0h52Hzh67__arithh74__ffh86__sat0h96__sat1h:8__varmaph;5__with<1vp;1p;2p;3p;4p;7p;6p;8g002Gj12Tg002lj1WTg003Jj1ETg00mjj1=Tg00nHj2OTg00nej21Tg00>YR0j27Tg011_j26Tg02bij25Tg033Hj13Tg0052j34Tg008`j2<Tg008:j2VTg02PXj2UTg02Q@j3TTg00a\j1NTg005Lj1LTg024Lj2KTg025fj1ITg026Dj1HTg026oj2FTg02B2j29Tg02Rjj3DTg027Rj48Tg029ij1CTg02SMj7GTg02:Kj2BTg02:mj2JTg02;Yj3ATg02<8j4@Tg02T1j2MTg000Kj6?Tg034Xj3PTg031gj3QTg012fj2>Tg028=j7RTg02C9j8STg00dSR1f0R2'>p=0f1R3g02FNR4g02FmR5P5g02GMR6P2g02GmFRp=:f3R7P4P5P5P6f2R8P3P2GSp=;g00PGR9#2R:#2#2#2#2#2R;#WR<#Eg00PlR=%02%=:R:%=;R;'OR>,12R?'7P=P3g00LWR@16<7RA,52#3158A#334X2=16<8,53#3RA,<@1V<3RB,6<1U:;111:%0;111>[[%0:RCg0173RDAT:;3UW0%0>\D^0CP0%07117>f4R7#0117>'7P8f5#0f6/1>g02ISR7#N%L71K=3%I=%H=R7P=1F=9R9g02M619=:=D=<C8,:7R:%C5R0P7P=19=1g02LOP9C8,:7R9P0P7P4P5P5P6P9P:FGC;C;1B76P2P8g00M7R7,<@1J28=4@7dAA=13C@b7b:b;X1=%03%08118>'7[\?^1=P2f8P3P8O3b6W4W3P3P2O2n2001000000121000000b8b9,M3E?AP<B8#3=4@Aeg0367?QB8=4@AeW5W2W<o"). Qed.
End VP30.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

(* [comment removed for export] *)
Ltac ground_mod :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with
      | context [bv_unsigned _] => fail
      | _ => lazymatch b with
             | context [bv_unsigned _] => fail
             | _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
             end
      end
  end.

Ltac sc_unfold :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev eb vals_ev nth];
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

(* [comment removed for export] *)
Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

(* [comment removed for export] *)
Ltac sc_store :=
  match goal with
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
      apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
      apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
  end.

Ltac sc_auto extra :=
  sc_unfold;
  first [ lia
        | sc_store
        | extra
        | match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
        | idtac ].

(* [comment removed for export] *)
Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok _ _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.
