(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_HNextPrimeU1 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c69OSSVerify5KrLib7LibHash<HNextPrimeU1CU1_code_8c1bc_8c7787W_8c274C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr04K47Corelib4Init9Datatypes4prod01C35stdpp9decidable;prod_eq_decI4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decC59OSSVerify5KrLib=SymExec3Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib8SymExec33SX26kentry06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry05C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03K59OSSVerify5KrLib8SymExec33SX25saddr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX24expr01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry07C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib8SymExec33SX22evC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib:Eseed_regZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib7LibHash4HLib:krange_varC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib7LibHash4HLib:kalign_varC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC59OSSVerify5KrLib7LibHash4HLib9kwr_stackC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib8kimg_absC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib=SymExec3Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I59OSSVerify5KrLib8SymExec33SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU15RO_LOC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU15RO_HIC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib7LibHash<HNextPrimeU15kn_npC1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib7LibHash<HNextPrimeU17np_cert00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib7CatExec6wbytesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init7Decimal4uint02K47Corelib4Init7Decimal4uint04K47Corelib4Init6Number4uint01C47Corelib4Init3Nat;of_num_uintK59OSSVerify5KrLib8SymExec33SX27scripts01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU15sr_npC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX29sym_state01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX28sym_execC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib9kept_symsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25s_logC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib8SymExec33SX26sentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib<regs_ok_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC59OSSVerify5KrLib8SymExec33SX26edenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib<regs_ok_knowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SymRun39run_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec3Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C46Stdlib5Lists4List2InC59OSSVerify5KrLib7LibHash4HLib<kept_of_symsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX26adenotC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7LibHash4HLib8v_addi_ZC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib8SymExec33SX26a_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25a_offC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions4BvWfC45stdpp9bitvector;definitions9bv_signedC49OSSVerify5KrLib7SeqExec6v_jalrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib7SeqExec<step_jalr_x0C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib6CatSim6msteps01C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib6CatSim6msteps02C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6CatSim<msteps_transC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HLib7reg_litC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I49OSSVerify5KrLib6CatSim6msteps00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7LibHash<HNextPrimeU12NPC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I59OSSVerify5KrLib8SymExec33SX29sym_state00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX27scripts00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX28sidecond00C1?~~~~~~~~~~~~~~~K47Corelib4Init7Decimal4uint01c59OSSVerify5KrLib7LibHash<HNextPrimeU16NP_RETC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX24expr00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec33SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib8SymExec33SX25sr_idC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00c59OSSVerify5KrLib7LibHash<HNextPrimeU17np_knowC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00c69OSSVerify5KrLib7LibHash<HNextPrimeU1CU1_code_8c1bc_8c7787F_8c274C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02c69OSSVerify5KrLib7LibHash<HNextPrimeU1CU1_code_8c1bc_8c7787D_8c274C1?~~~~~~~~~~~~~~~k59OSSVerify5KrLib7LibHash<HNextPrimeU17np_cert01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N01C49OSSVerify5KrLib6LibEff8ro_clearC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface9in_rangesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface5ly_rwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface8ly_relroC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalC49OSSVerify5KrLib8LibIface6ly_imgC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6LibEff7ro_addrC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6LibEff;ro_clear_atC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep6np_argC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5Hoare6ret_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface:stack_roomC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1;ro_clear_S1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep9bseq_nextC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU16np_oneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts?next_prime_stmtC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash4HRep4BSEQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash6HStmts9BSEQ_LASTC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201c59OSSVerify5KrLib7LibHash<HNextPrimeU15npc_2C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU15npc_5C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU16npc_11C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU16npc_23C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU16npc_47C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU16npc_97C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU17npc_197C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU17npc_397C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU17npc_797C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU18npc_1597C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU18npc_3203C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU18npc_6421C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU19npc_12853C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU19npc_25717C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU19npc_51437C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1:npc_102877C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1:npc_205759C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1:npc_411527C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1:npc_823117C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1;npc_1646237C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1;npc_3292489C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1;npc_6584983C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibHash<HNextPrimeU1<npc_13169977C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibHash9HConstsU12hcC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_8c1bc_8c778.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8c274 : bv 32 := 0x00008067.
Lemma F_8c274 : fetch_word Ubsan.M.loaded_segments (0x8c2b4 : word) = Some W_8c274.
Proof. vm_refl. Qed.
Lemma D_8c274 : decode_any W_8c274 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_8c1bc_8c778.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HStmts HConstsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNextPrimeU1.U1_code_8c1bc_8c778.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.
Definition NP : Z := 0x8c1fc.
Definition NP_RET : Z := 0x8c2b4.

Definition RO_LO : Z := 0x10000.
Definition RO_HI : Z := 0xe8000.

Definition kn_np : list kentry :=
  [ KRange (EVar 2) (2 ^ 24) (2 ^ 47)
  ; KAlign (EVar 2) 16
  ; KWr (SA (EVar 2) (-16)) (ELit 16)
  ; KImg RO_LO RO_HI ].

Definition sr_np (n : Z) : list expr := sr_upd sr_id (ridx 10%bv) (ELit n).

Record np_cert (n r : Z) : Prop := NPC {
  npc_ss  : sym_state;
  npc_scr : scripts;
  npc_run : sym_exec SEGS 200000 true [NP_RET] (SCR [] [] []) (SS NP (sr_np n) [] kn_np 40) [] = (npc_ss, [], npc_scr);
  npc_a0  : sr_get (s_regs npc_ss) 10%bv = ELit r;
  npc_pc  : s_pc npc_ss = NP_RET;
  npc_cs  : kept_syms (s_regs npc_ss) = true;
  npc_log : s_log npc_ss = [SE (SA (EVar 2) (-8)) 8 (EVar 1)]
}.

Section NP.
  Context {fx : FPState}.
  Variables (R : bvmap 5 word) (M : mem) (sp : Z) (ret : word).
  Hypothesis Hra : getr R 1%bv = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 sp.
  Hypothesis Hsp16 : sp mod 16 = 0.
  Hypothesis Hsplo : 2 ^ 24 <= sp.
  Hypothesis Hsphi : sp <= 2 ^ 47.
  Hypothesis Hroom : stack_room SEGS M sp 16.
  Hypothesis Hro : forall i, RO_LO <= i < RO_HI -> M (Z_to_bv 64 i) = None.

  Let E := Eseed R [].

  Lemma np_know : know_ok SEGS E M kn_np.
Proof using R M sp Hsp Hsp16 Hsplo Hsphi Hroom Hro.
ltac2:(KReplay.run1 (kr_t_HNextPrimeU1 ()) ["NP"] "h04__x1h17__arithh24__ffh38__varmaph45__with52Hah67__sat17h77__sat18h87__sat19h97__sat20h:7__sat21h;7__sat22h<7__sat23h=1Hh>6__sat0h?6__sat1h@1bp;3p;1p;2p;4p;6p;:p;<p;8p;7g00C;j3pTg0000j11Tg000Uj1<Tg00D<j1TTg002]j17Tg0028j15Tg00E4j2ATg00EQj3XTg00FKj2VTg00GEj1STg00Gcj2LTg00H\j1KTg00ITj2oTg00JNj2mTg00KHj1BTg00Khj3ETg0013j1ITg00LHj2_Tg003;j3^Tg00M<j2JTg00Mnj3[Tg00Njj4ZTg005Bj3@Tg00OFj2YTg00Olj6WTg00PHj2?Tg00Q0j24Tg00QLj3>Tg00R0j2UTg00Raj2RTg00SAj1QTg00Saj2MTg00T?j1NTg00T]j1OTg00UHj2PTg00Ukj29Tg00VNj3CTg00W1j1nTg00WSj4GTg00X>j2lTg0079j2HTg00X`j2hTg00YLj3gTg00Ykj4aTg00Z]j22Tg00[9j2DTg00[Tl:`Tg00\Pj1bTg00\nl:cTg00]jj1dTg00^Gl<eTg00_Bj8]Tg00`<j2fTg00`]j6=Tg00a>j4\Tg00b=j7iTg00baj7jTg00cEj8kTf0R0#1#1p=:g00ASR1/20p=0g00A5R2f1R3g00ciP0CGp=6P3g00dPR4g00doR5P5g00eOR6P0g00eoFip=3f2R7P4P5P5P6P3P0Fjp=Ff3P4P5P5P6P7P3P0Gkp=8%10#1#1#1p=;g00fOR4g009>R8p,1ER9p,1MR:3pR;g008YR<#1R=#<R>#TR?%7=R@%5<RA#1#:RB#7RC'ARD%5=RE#5#5#5RF#7RG,A@RH3X%1=#:R=#7RI,V?RJ%S=RK,L?%KI'oR?g00gIRLg00hHRM'mRN%B4RO5E4RP5E4RQ5E4P8P9P:P>p,2spRRPDPH%:=R=#<RS#IRT1_9>RUp,1RRV%<EREg00:]7^@RW'JRX%BTPW%IEeRE5[VCZ1JVE=@TUPTPX1YSR9@T0X@Tp,3HspPUP0EWb=RU1?@GRT141@RX%0G141H[[RE%0@RVg00iGRWA>@G3UW5RG%0H\W^5VRY1URIRZ%0R%0IR[1RRI#0[[R\%7=R],?@R^%0]1A@]R_,41[\XR`A>@]3VWX5VR]%0_\W^5VRa1?@CRb%0C141D[\XRXA>@C3VWX5VRC%0D\W^5VRVg00icRW#BRc%QWRW1M23Rd%N2Re%O2Rf1P2<R<192@R@%<F5C2'6,3fRF%n5R5Pf%<B9C2@/6<,3fRBP51921Rg/6<,3fP2P<g00jORhAC2@SR@CG,3fRS5FfC8C81lf6R6P0P7g00<NRig00<nRj'H1h07=@ijdAg213CaRjb2b3b4X02120HRi12D3Rk%07147_'D[[^02P0PRp,5HsphiRlp,5HsploRmO3Rnb1b6b7b8b9b:b;b<RoPTPEPGPYPZP\PbPXPCPVPcPWPdPePfPFP5PfPBP5AFfBFC8C8P6Pjb2b3b4X0212D7127H'D\k\i^02Pnb1b6b7b8b9b:M:`P4P;PJPQP8P9P:P>PRPIPUPoPcPW%b2RoPeP2PgPh192IRhCG,3fP6Pjb2b3b4141IP0b1p,5Hsp16M:cP4P;P?PPP8P9P:P>PRPIPKPU%dI,H2PTPEPGPYPZP\PbPXPCPVPcPWPdPePfPBP516gh,3f16h<,3f5FfC8P6Pjb2b3b4X0212D012I3,D[[^02P0PRPmO2b1b6b7b8b9b:PTPEPGPYPZP\P^P`P]PaPbPXPCPVPcPWPdPePfPFP5PSC8P6Pjb2b3b4X02143_\i^02P0PRPlO2b1b6b7b8b9b:b;b<p,5HroomM<eP4P;PNPOP8P9P:PLPMPcPWPoPe%:=#;#;#7R=,92,6g,3fP6Pjb2b3b4%0=P0b1121LeP^P`P]PaPcPWPoPe%5A#1#5#1#:#;#;#;#7RA,92/6@,3fP6Pjb2b3b412A_P0b1b>b?12M_ep,3HroG]1f4;E=E=E=E=P8P9P:g00k6C\eo"). Qed.

  Lemma np_one : forall n r,
    getr R 10%bv = Z_to_bv 64 n -> np_cert n r ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 NP) M (seg_rom SEGS))
                  (@mkst fx R' ret (wbytes M (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r.
Proof using fx R M sp ret Hra Hret Hsp Hsp16 Hsplo Hsphi Hroom Hro.
ltac2:(KReplay.run1 (kr_t_HNextPrimeU1 ()) ["NP"] "p'0h01Hh12Hah21bi001bh32R'h43Hmsh51nh61Rh74__x1h82b1h92b2h:1eh;2H0h<2HRh=3HR1h>3Ha0h?3Hexh@3HkshA3HlfhB4HloghC3HpchD2HrhE4Hra1hF2R1hG7__arithhH4__ffhI7__sat17hJ7__sat18hK7__sat19hL7__sat20hM7__sat21hN7__sat22hO7__sat23hP8__varmaphQ5__withR1lhS1rhT3rethU4scr'hV3ss'hW1zi011zi028bv_is_wfi03;bv_unsignedi046npc_a0i056npc_csi067npc_logi076npc_pci087npc_runi097npc_scri0:6npc_ssi0;1xp&0p;1p;2p;3p;5p;7p;4p;6p;8p;Dp;>g0000j11Tg000Uj1ATg0013R0j1BTg0028j12Tg00M<j2<Tg00OFj23Tg005Bj30Tg00l5R1k20;Tg00m8k203Tg00mdj1~Tg002]j1=Tg00nYk20YTg00o6j1?Tg00oUj2aTg010]j3PTg011Pj2mTg012JR2j2LTg00SAj1ZTg00=Nj2jTg012dj1JTg013Bk10@Tg013`k10:Tg014=k109Tg00KHj1CTg00Khj3dTg014\k301Tg015Wj1TTg016Vj5}Tg017Sj7{Tg00?Kj4lTg018Mj17Tg019Ej2wTg00H\j1oTg01:=j18Tg01;3j1sTg01;nj16Tg00D<j1qTg00GEk10XTg00Gck20WTg01<ek30VTg01=_k20UTg003;j3ITg00Olj6:Tg01>]k20STg01?<k10RTg01?Uj2_Tg01@Mk80OTg01AKj3HTg01BJk30NTg00`<k20MTg01CJmD0LTg01D@j2DTg01E@j39Tg00[9R3j2ETg0079j2GTg01FAk30FTg01F[k30ETg01G2k80Dj6tTg01H0j54Tg01Hbk20ATg00LHj2hTg00Mnj3cTg00Njj4RTg01IZj2YTg01JNk20?Tg00PHj2STg00Q0j2KTg00E4j2XTg00QLj3UTg00R0k208Tg00Rak207Tg00Sak206Tg00T?k105Tg00T]k104Tg00UHk202Tg00Ukj2eTg00VNj3WTg00W1j1fTg00WSj4gTg00bak700Tg00X>j2|Tg00X`k20<Tg00YLk30=Tg00Ykk40>Tg00Z]j2`Tg01Jkk30BTg01Kej6]Tg01LCj1zTg01M;k10CTg01N2j2FTg01N\j3xTg01O@k20GTg01Ock20HTg01PKj2nTg001Vk10ITg01Q>l>vTg01R7k20JTg01Rkk70KTg01S_j6uTg01TWk70PTg01UPj4pTg01Ukk40QTg01VEj3QTg01W9j2bTg00b=j7rTg00cEk80TTf1R4f0R5#=g00:]R63Ip=Mf5R7f4R8f3R9f2R:'3P4P5D4p=yg009>R;P8P9P:P4P5D47Q7p=^1E45,E:p=>f6R<P7P8139:P4P5D45Q;p=@f7R=P<P7P8A99:4P5D45Q;p=\AI456p=O%=:=I96=084/b5p=;A0<78A09:4/b5'bp=[AQ;45p=kg00ASR>/`5p=5g00A5R?P4g00ciP5Cgp=VP4g00dPR@g00doRAPAg00eORBP5g00eoFrp=NP9P@PAPAPBP:P4P5L0Tp=ig008YRC#1RD#1RE#1RF#1RG#1#1RH#ARI#BRJp,1RRK%2DRL#ARM%1LRN'MRO'<RP13I43020;:4P1P9P:203MJR1p,2fxRQPKPIg01WSRRp,1MRS%~;RTEyRUPQP5p,3retRVp,2spRW%=FRX+0Y,3IRYg01XO#?#?#?#?#?#?#?#?RZ/aV5PSR[PTE^R\1mK5R]1<5OR^13I850J3>X31'LP5g01XnR_g01YkR`g01ZfRa#ZRb,j_Rc/j`P;g01[b#J#J#J#J#J$0@$0:$09Rdg00<nReg01\@Rf%C?5d?Rgg00<NRh#CRig01]@Rj#C<01iRiPRf<Rk#Tg01^8Rl#CRmg00k6Rn%1NRo#1#ARpD}%CaRqF{PcP`P_PbP4PqClP5Cl30%7:/wO%ok50j%89=0?f%78#s=0he%ZlRj%67%ADRb#q&0XFRF+0WR_%ACR`#qRc80VZ=dlmRm30p,1ERlg01_2PKPOfARr#oRs%CJRt-0UK%BMRuAIM>6Rv70ORwPuPOP0PMp-0R0P5P?P0P4g01_iR0g00iGRxP0n011010003001000010000n101100000120103102X:uP6PvP5E:P020S05b;W0&0Rwef?Rw1_ls90JPeL0O%Tr=HlKRPePPPQP;PdPgPiPRfBRR#TPnPpP=PqP<PlPSPTPKP7P5g01`FB0N;Sl-0MaND0Lf8Ra#7=Hl5%6aRq,DlPUPQP5PI%8aA9lSqPTF@3>X61,L1P2P1f9R2#7=Hl5%62Rq,DlPUPQP5PI%82A9lSqPTF@3>X61fDRq,3I90J^9>\]X31,L1P5f;Rp#7=Hl5%6pRn,DlPUPQP5PI%8pA9lSnPTF@3>P3%7k=Hl4%6kRn,DlPUPQP4PI%8kA9lSnPTF@'EfH,3I90J^9>\]X31,L1P5f>Rn#7=Hl9%6wRi,DlPUPQP8PI%8wA9lSiPTF@'EP3f@Ri#6Rg,DlPUPQP7PI%8iA9lSgPTF@fL,3I90J^9>\]X31,L1P5%6R,DlPUPQPaPIfCRg#8%6g99lSPTF@P?%8qPUPQf:RgPIP5fE#6Rd99lSPTF@XW?P5PfPiE:PUPQP213IfRfPlPS%6qPTG\PjPdPUPQPpPfPlPSP5PTG\XRjP5PmPwE:PUPQPgPfPlPSPmPTG\PJ1MMCRm,<KRg1<km=0J5XTJPKPtfF#7PpP=PrPmA0ummPu%=DRD,OMRrPmPu%2CR=,MMPmPuPMPEPmPu1OMXPmPu%2ERE,MMPmPuPM%1EPmPuPM%2EPmPuPMPoPmPuPM%2NPmPuPM%2LRL#1PmPuPM%2LRLPmPu%1=R=#1RN#1Ro#=RE,OMPmPu%2N,MMPmPuPM%2=R=#1PmPuPM%2=PmP0D;D;F[D;D;D;D;D;D;F[D;F[1Gum40Fg01aG:0EumeL0DPVp,3HraR0E:1<pm=0JVP1fR,3I90J^9>\]X31PkPQPkPVP[PTD4R],kU1mKkR\1<kOfQR^,3I50JRp'EP;PUPQPkPf20Al_RU1_lcRc,aZR=5PSPTD4P]P4PJ1hlbRb1<KrR]PrPueRr9cKtCR1<Kr=0JbPJP]1Y5F90JYX2JRrPJ13IWRMPrPJ20?WF,3IRrA0JY5X2J1GJr1YMF%2LRL#=RM,SD1K>DRr%5M1XDMRX,K>[[%5DRjAUDM4VxW1%5X\x^1j%=GRG-08W%5W%5G207WG#5[[%=HRH,SD%5H1XDHRG,K>[\rAUDH4VxX1j%5G\x^1j1SDE%5E1XDERH,K>[\rAUDE4VxX1j%5H\x^1jg00icRj#C%Zj206?4&05?&04?Rj202?CRx1e?DRD%AL5W?'V,Nj%fARLPj%Ao9W?D/Vx,NjPLPjP@PAPAPB1e?>/Vx,NjP?Pxg00jOAW?DICg,NjK00CiCi1|jBP5P:1Ghe20<5:=0hedB0=?>4H0>bHbPbQX7?1`5X1`H4%5:1K:G'E[[^7?P5PWp,5Hsphip,5HsploO3bGbIbJbKbLbMbNbO:0BWFE]P]p,3HspE]PbP5E:b0%z_,_l&0C_'Y90JYeA0JYUR_eP_PJPYPQPnPfAPS5=PTD4PQPnPVP[PTE^X2JPJ1hl`R`PgPmPueRu9cKtCR1<Ku=0J`PJPgA0JV5X2JPJPgPVP0CRP`P5E:b0A0JVcR`eP`PJPVPQPwPf1aZ59PSYPTD4PQPwPVP[PTD4RY'kX2Jg01bERS%B5RZ%B4R`P3%B:?0451F9:1F9450?R3[1F:41F:550?%B9?0:4[R0%B8?09:\3Ax:45P5n2001000000120000000W9W8W5P0^9`^8Z^5SP5PI%1C#1#1#2#2#1#1#1#1#2#1#2#1#2#2#1#2#1#1#=RC,OIRSPf1G?C1FIS1FIf50?dO4b0P620GICd9IIC=0JfPJPSPQPiP5P[PTD4PQPiPVP[PTE^X2JRiP;PQPwPSP[PTD4PQPw%ANRNAIN>6RN+0H,nVP[PTD4PY&0IJ%fJ'GPQP;PwPSP[PTg00;9PmPNPVg01bcg01d8,Ghg01dXP9M>vPJPVPi20J;Y1nV>p,4HretE]K0KPfP5E:b0PcP5E:b0PUP5E:b0EuP\PpPKPtfG#7RtPkPaPREtPlPtPkPOP^PaPqK0PCpCpH0QbEb4b4W4WAP4P5O2n2001000000121000000W0W=P4P5O2n2001000000121000000W0XF1P4P5O2n200100000012110;000b:b<WBW@WCWDW?WUWVP<P7P8P9P:P4P5O7n200100000017110:109108104107105106W0W>XS?X5?o"). Qed.
End NP.

Ltac npc :=
  lazymatch goal with |- np_cert ?n ?r =>
    let res := eval vm_compute in
      (sym_exec SEGS 200000 true [NP_RET] (SCR [] [] []) (SS NP (sr_np n) [] kn_np 40) []) in
    lazymatch res with (?ss, ?scs, ?scr) =>
      apply (NPC n r ss scr);
      [ vm_cast_no_check (@eq_refl _ (ss, scs, scr)) | reflexivity | reflexivity | reflexivity | reflexivity ]
    end
  end.
Lemma npc_2        : np_cert 5 5.
Proof.
  npc.
Qed.
Lemma npc_5        : np_cert 11 11.
Proof.
  npc.
Qed.
Lemma npc_11       : np_cert 23 23.
Proof.
  npc.
Qed.
Lemma npc_23       : np_cert 47 47.
Proof.
  npc.
Qed.
Lemma npc_47       : np_cert 95 97.
Proof.
  npc.
Qed.
Lemma npc_97       : np_cert 195 197.
Proof.
  npc.
Qed.
Lemma npc_197      : np_cert 395 397.
Proof.
  npc.
Qed.
Lemma npc_397      : np_cert 795 797.
Proof.
  npc.
Qed.
Lemma npc_797      : np_cert 1595 1597.
Proof.
  npc.
Qed.
Lemma npc_1597     : np_cert 3195 3203.
Proof.
  npc.
Qed.
Lemma npc_3203     : np_cert 6407 6421.
Proof.
  npc.
Qed.
Lemma npc_6421     : np_cert 12843 12853.
Proof.
  npc.
Qed.
Lemma npc_12853    : np_cert 25707 25717.
Proof.
  npc.
Qed.
Lemma npc_25717    : np_cert 51435 51437.
Proof.
  npc.
Qed.
Lemma npc_51437    : np_cert 102875 102877.
Proof.
  npc.
Qed.
Lemma npc_102877   : np_cert 205755 205759.
Proof.
  npc.
Qed.
Lemma npc_205759   : np_cert 411519 411527.
Proof.
  npc.
Qed.
Lemma npc_411527   : np_cert 823055 823117.
Proof.
  npc.
Qed.
Lemma npc_823117   : np_cert 1646235 1646237.
Proof.
  npc.
Qed.
Lemma npc_1646237  : np_cert 3292475 3292489.
Proof.
  npc.
Qed.
Lemma npc_3292489  : np_cert 6584979 6584983.
Proof.
  npc.
Qed.
Lemma npc_6584983  : np_cert 13169967 13169977.
Proof.
  npc.
Qed.
Lemma npc_13169977 : np_cert 26339955 26339969.
Proof.
  npc.
Qed.

Section S1.
  Variable L : Layout.
  Hypothesis HLimg   : ly_img L = [(0x10000, 0x124000)].
  Hypothesis HLrw    : ly_rw L = [(0xef000, 0x124000)].
  Hypothesis HLrelro : ly_relro L = [(0xe8000, 0xef000)].

  Lemma ro_clear_S1 : forall M, ro_clear L M -> forall i, RO_LO <= i < RO_HI -> M (Z_to_bv 64 i) = None.
Proof using L HLimg HLrw HLrelro.
ltac2:(KReplay.run1 (kr_t_HNextPrimeU1 ()) ["S1"] "p'0h01Hh12hih22Hrh32loh44__x1h57__arithh64__ffh74__p1h84__p2h94__p3h:8__varmaph;5__with<1lh=1Eh>2Hah?3Hinh@1ehA2HRhB2HihC1MhD6__sat0hE6__sat1hF1ii001pi011xi021zp;2p;1p;3p;4p;6p;7p;8g01gNj2nTg0000j16Tg002]j1ATg00PHj2hTg00Q0j29Tg00Z]j2>Tg00E4j2\Tg00QLj3YTg00KHj1NTg00SAj1MTg00Saj2STg00T?j1mTg00T]j1lTg00Ukj2@Tg00UHj2fTg0028j1;Tg00W1j1^Tg000Uj1]Tg00VNj3[Tg00X>j2ZTg0079j2OTg00X`j2XTg005Bj3<Tg00YLj3WTg00Ykj4VTg00=NR0j2UTg00Khj3HTg01hBj2:Tg01i9j1RTg01?<j18Tg01ilj1TTg00[9R1j20Tg01F[j31Tg01FAj3kTg01UPj4LTg01Ukj4QTg01jbj6GTg00Olj7ETg01Kej6JTg01k?j1eTg01l3j2cTg01lfj6bTg00WSj4PTg00b=j7dTg00baj7aTg00cEj8`Tg00?Kj4iTg012JR2j2_Tg01m]j6jTf3R3f2R4'>f1R5f0R6'9'0p=2%66#6#6#6p=4%66#6p=Dg00A5R7P5g00ciP6CPp=FP5g00dPR8g00doR9P9g00eOR:P6g00eoFdp==P7P5g00jOP6CPp=IP4P8P9P9P:P5P6Fap=?P3P8P9P9P:P4P5P6G`p=CP7P7P5P6Cip=31_76p=5A<756p=71>45/06p=BP5P8P9P9P:P6Ejp=K1956,04p=gg01nAp,1LR8/n6g00gIP6P6g00hHC2P8P3P5P4g008YR;#6R<#AR=%6<#4R<#AR>'hg00ASR?/9=1>?>1\=>R@,9?[[1>?=RAg00iGRBAY=>5UW>1>?@\B^>Ag00icRA#NRB%MARA1S75R>%m7RC%l7RD%D<#4#4#ARE,@71f7;RF'F,=DRG%;;#;#6#;RH#6#D#4#4#4#ARI,@7RJ,IF,=DRK5?DRL%^9R91@7?/FF,=D1@7=%]<5[7,IF,=D5?DCC1ZD:R:P6P4g00<NR<g00<nR='O1X64=<<=dAW7?5CVR=b6b:b;X47PEP6P6PIC2R<P?P5P5P@C2[^47P6f4R@P3O2b5bDbE1U77R?#MRM%D;#;#D#;#D#4#4#4#AR;,3ERN%N?RO5H?RP1:64RQ%R8RR/:4#8%T8RS/:4#8RT'0'0X<MPM%;H#;#;#4#4#4#ARH/3;RU=H?ORV1:P4RW%8QRQ/0T'0X<MPM13IHRT=H?ORX1:V4#8/0Q,0WX<M1356RM=1?PP5P3P3P6C2RW'0X17#5X37RQ#5A1?MVRY/0WX17#5X37#5RZ#8R[A1?MXRM/0WX17#5X37#5RW#8R\'0P7PQPEP713E6=1?PPEP4P4P6C2'0X17P;A1?NPPEP5P5P;C2RQA<?NNA1?NO1O?N3kPBPAP>PCPDPLP91@7;,IF,=D9?DGCCP:P=b6b:b;X47PQ\<^47P6P4P5O2b5CLCQCQP[P\P2P7P5P@P@P6C2R<,0YX17#5X37g01_iRQP6P5f6RGPGP6C2RL,0YX17#5P2P71346RY=1?VP4f7R4P4P6C2RN'0X17PQP613@6R]=1?VP@f9R^P^P6C2R_'0P1f5R`/35Ra=1?VP`f:RbPbP5C2RcPQP61343Rd=1?Vf8Ref=RfPfP@C2Rgg01W9Rh13^`R^9<?UA1?^ORiPQP513bGRG9<?UP?P7P0P7P7P7P6P6n2001100000120102102X@?RjPUf;Rk/34RlP6EG17;4P?P7P0P7P7P7P6P5n2001100000120102102X@?R0PUf<RU/3eReP5EG17HURm17HfP7PHP6fDRnPnPkC2Rn17;UPQ[]2X37fCRo19obRb5BH17;kP7P;fFRp19p6Rq5BHPQ]2X17PHfERrPrP;C2p-0RsPBPAP>PCPD1@7H/FF,=D1KD3Rt5?DP9PD1KD@=?DKP91KD`CCRKCCP:P=b6b:b;X47X7sX8sW9ABH65Ag35IP`[R3[^47^7s^8s^9sP6PQfGR@,>ERE19@;P@P5PpO6b5W2PUP6P5FEW0W2f>R;P6P`FEW0P6O1b0P6O1b0W=P6O1A1?GOPQPQP6n010000000W0P6O1ROn200100000021100010000W2W?P5P6O2n2001000000121000000W0X17P5P6O2n2001000000121101000W0X37P5P6O2n2001000000121101000X0ZP[eP2P710M<X17#5X37PQP610MLX17#5P2P7A1?YX/0NX17PQP6A1?]X/0_P1A1?aXPcPQP6A1?dXPhA<?T^PiPQP5A<?TGP?P7PjPTPlP6EG17H4P?P7P0PTPeP5EG17IU17IfP7PIPQ\m^2nX37ABIob17HkP7PHABIpqPQ]2X17PIPrPrPHC2PBPAP>PCPD1FJF,=D=?DtP9PKCCP:P=b6b:b;X47X7sX8sX9sABI65P3[^47^7s^8s^9sP6PQPE19@HP@P5PpO6b5W2PUP6P5FEW0W2P;P6P`FEW0P6O1b0P6O1b0W=P6O1POn200100000021100010000X2gW?P5P6O2n2001000000121000000W0X17P5P6O2n2001000000121101000W0X37P5P6O2n2001000000121101000X0WP\eCLCL1:P51:V5#81:X5#8'0'0ePSp,7HLrelroEJPRp,4HLrwEJ%e8p,5HLimgEJ1c85eEbWBXF7WAWCo"). Qed.

Theorem next_prime_spec : next_prime_stmt SEGS L hc.
Proof using L HLimg HLrw HLrelro.
ltac2:(KReplay.run1 (kr_t_HNextPrimeU1 ()) ["S1"] "h02R'h13Ha0h23Hn0h33Hnlh43Hinh52bch61Hh72Hah84__p1h97__arithh:4__ffh;7__sat17h<7__sat18h=7__sat19h>7__sat20h?7__sat21h@8__varmaphA5__withB3HrahC4HrethD3HrohE4HroLhF5HroomhG3HsphH5Hsp16hI5HsphihJ5HsplohK1MhL1RhM2fxhN1ihO3rethP2spp%0p&0p;1p;2p;3p;4p;6p;9p;Ap;5p;7p;8g0000j1BTg0028j1ATg000Uj1TTg0013j1jTg00m8k204Tg01F[j3bTg005Bj3CTg01?<j1MTg002]j1ETg003;j3QTg01o2j16Tg01ojk106Tg00Raj2VTg00E4j2cTg00Z]j2PTg020[j4xTg01gNj2uTg021Sj2qTg00Q0j2OTg00[9j2LTg001Vj1nTg00OFj2KTg00W1j1]Tg00KHj1[Tg00mdj1kTg00o6j1ITg00M<j2YTg012Jj20Tg011Pj2WTg00PHj2gTg00QLj3fTg00R0j2eTg00SAk102Tg00\Pk101Tg00T?j1~Tg00T]j1zTg00Ukj2aTg00WSj4ZTg01m]j6yTg00X>j2wTg0079j2vTg00X`j2tTg00YLj3sTg00Ykj4rTg01>]j2^Tg00Oll9iTg022Xj1;Tg023SlA@Tg024Sj3pTg00Khj3oTg00nYj2{Tg00oUj2|Tg010]j3}Tg01H0j5UTg01VEj3dTg00b=j7mTg025Vk600Tg00cEj8lTf0R0#B#Bp=Hg00A5R1g00ASR27C0#Mp=9f4R3f3R4f2R5'Yf1R6/K03Cp=71Y56=C40p=8AC102p>03%A0#Ep=DAC120p=S%B0#A#Ep=G%A0#Bp=J%B0#Ap=R%A0#Ap=NAo160p=>Ab160p=41{60,K5p=1f7R7f6R8f5R91|569}34P0DUp=21W93%;0,K69C45'Lp=:g009>R:P8P9P3P4P5DU;d6/L0p=3AC160#Mp=?%;0,K69C45p=X1W56/L0p=<P9P3P4P5P6DU=d:0p>051L60,L5p=h1P20p=FP6g00dPS00g00doR;P;g00eOR<P0g00eoFmp=`P6Q00P;P;P<P0J00p=\P4Q00P;P;P<P5P6P0Glp=_AC160p=5P1P7P8P9P3P4P5P6P0M9ip==g026:g008YR8#BR=#AR>#TR?%H=R@#BRA#H#TRB#jRC+04RDg01nAg02719b15%94g027g9C13#MPCP7%B>#Eg00:]R45Q?REPB%69D7PCf8S01%E8=Q?4P3C8&069PCf:S02%E=R==Q?4PBP7D7Q01%EARA'V$03%A8#HR8#BR4#ER?,c=R9f9S03'PQ02%A>RF#ARG#DRH,c=RI'PP:f=RJf;RKPACxp,1LS04f>RL'uf?RM/q0g00gI/P0g00hH,O0'L%T@#jRN#nfARO1KB6O1%]N3C[^N1g01W9RN%SM%E>R>%EFRF%EGRG%G4RP%A4R4#GRQ%A4R4#GRR%A4R4#GRS%J4#DR4%J8#HR8#B#R#DRT%A8R8#B#J#DRU%A8R8#B#J#DRV%A8R8#RRW#GRX%AWRW#GRY%AWRW#GRZ%NW#DRW%J8R8#B#H#N#DR[%J8R8#B#NR\#GR]%J\#DR\%J8R8#RR^#BR_#GR`%N_#DR_%N^#H#DR^%A8#H#H#H#DR8%[1S05'>S06'>S07'>S08'>S09'>S0:'>S0;'>S0<'>S0='>S0>'>S0?'>S0@'>Ra'>Rb'>Rc'>Rd'>Re'>Rf'>Rg'>Rh,>HRi'>Rj'>Rk'>Rl,>=S0A,4MfDRmfCRng01WS,KBRofBRp%k:RqPmP0PMPpf@Rr%E@R@51Bg01XO#I#I#I#I#I#I#I#IRsPMPqG2PnP0PC1Y0ERtPBPOE:F3X0D,0Df<S0B%SrP1P2%90Ru1?68RvPCfFRwPE%65,KBRxC8fIRyfHRzPofGR{PqPyP0PmP{fER|=1B@PsPmPqG2PCPtPBP3CXR39<z0F3X0D,0D]1]3]2X51AC122S0C#M%S8#MPCP|PEPB%62D7PzP{PoPwPqPzP0PnPwA1Bm@PsPnPqG2J05S0D1W{0S0EPCPtPBP2CX3hX0D,0D1g=HS0F1O2=S0G%FH1O2I[[S0H%F=R}g00iGR~Af=H6UW7S0I%FI\~^7}S0J1e|A%F|%FARI1V{A#F[[1g=?S0KQ0G%F?1O29[[S0GAf=?6V~X7}S0L%F9\~^7}S0Mp-0R}g00icR~#[S0N&02~S0O&011S0P%~1S0Q%z1R~P11a12R9g028dS0RP9CZ,`~,\~%];S0SP~Q00P;P;P<P5EyS00C_1w~<R<P0P5g00<NR;g00<nR9'v1t05=C;9dAs126CrR2b:b@bAW8Q0Cg01_iR9[P6[^8}P0P9Q01O2b9b;b<b=b>b?'^W1W3W2POP0PJQ0BPKM9iW6P0O1Q0A,4rPN15=O14OlPwP|PoPmPqPwP0POPmA1Bp@PsPOPqG2P|P0PCPtPBPnE:F3X0D,0DP015=pP=PCPzPEPxC8fKR;fJR5PoPyPqP;P0PwPyA1B{@PsPwPqG2A<503F3X0D,0D]1^3v^2uX51%9=1?=8PCP{PEPB%6=R?D7PyPzP{P|PmPMPLPJQ0BPKQ02Q03P7P?%;=P0g029KMA@W1W3W2PnP0PMPLPJG=W6P0O114plPN15>n14nkQ0DQ0EPCPtPBP|CX3hX0D,0DP015>mP>PCP5PEPxC8fMRlfLR=PoP;PqPlP0PzP;A1By@PsPzPqG2A<=03F3X0D,0D]1^3v^2uX51%9>1?>8PCPyPEPB%6>R?D7P;P5PyP{PwPOPrPMPLPJQ0BPKQ03P?%;>P0g02:JMA@W1W3W2P|P0POPrPMG=W6P0O114mkPN15F|14|jP5PyPoPzPqP5P0P|PzA1Bw@PsP|PqG2PyP0PCPtPBP{E:F3X0D,0DP015FwPFPCP=PEPxC8fORkfNR>PoPlPqPkP0P5PlA1B;@PsP5PqG2A<>03F3X0D,0D]1^3v^2uX51%9F1?F8PCP;PEPB%6FR?D7PlP=P;PyPzPnPpPOPrPMPLPJPKP?%;FP0g02;IMA@W1W3W2P{P0PnPpPOG=W6P0O114wjPN15G{14{iP=P;PoP5PqP=P0P{P5A1Bz@PsP{PqG2P;P0PCPtPBPyE:F3X0D,0DP015GzPGPCP>PEPxC8fQRjfPRFPoPkPqPjP0P=PkA1Bl@PsP=PqG2A<F03F3X0D,0D]1^3v^2uX51%9G1?G8PCPlPEPB%6GR?D7PkP>PlP;P5P|PmPnPpPOPrPMPJP?%;GP0g02<IMA@W1W3W2PyP0P|PmPnG=W6P0O114ziPN15Hy14yhP>PlPoP=PqP>P0PyP=A1B5@PsPyPqG2PlP0PCPtPBP;E:F3X0D,0DP015H5PHPCPFPEPxC8fSRifRRGPoPjPqPiP0P>PjA1Bk@PsP>PqG2A<G03F3X0D,0D]1^3v^2uX51%9H1?H8PCPkPEPB%6HR?D7PjPFPkPlP=P{PwP|PmPnPpPOPMP?%;HP0g02=IMA@W1W3W2P;P0P{PwP|G=W6P0O1145hPN15P;14;gPFPkPoP>PqPFP0P;P>A1B=@PsP;PqG2PkP0PCPtPBPlE:F3X0D,0DP015P=PPPCPGPEPxC8fURhfTRHPoPiPqPhP0PFPiA1Bj@PsPFPqG2A<H03F3X0D,0D]1^3v^2uX51%9P1?P8PCPjPEPB%6PR?D7PiPGPjPkP>PyPzP{PwP|PmPnPOP?%;PP0g02>IMA@W1W3W2PlP0PyPzP{G=W6P0O114=gPN15Ql14lfPGPjPoPFPqPGP0PlPFA1B>@PsPlPqG2PjP0PCPtPBPkE:F3X0D,0DP015Q>PQPCPHPEPxC8fWRgfVRPPoPhPqPgP0PGPhA1Bi@PsPGPqG2A<P03F3X0D,0D]1^3v^2uX51%9Q1?Q8PCPiPEPB%6QR?D7PhPHPiPjPFP;P5PyPzP{PwP|PnP?%;QP0g02?IMA@W1W3W2PkP0P;P5PyG=W6P0O114>fPN15Rk14kePHPiPoPGPqPHP0PkPGA1BF@PsPkPqG2PiP0PCPtPBPjE:F3X0D,0DP015RFPRPCPPPEPxC8fYRffXRQPoPgPqPfP0PHPgA1Bh@PsPHPqG2A<Q03F3X0D,0D]1^3v^2uX51%9R1?R8PCPhPEPB%6RR?D7PgPPPhPiPGPlP=P;P5PyPzP{P|P?%;RP0g02@JMA@W1W3W2PjP0PlP=P;G=W6P0O114FePN15Sj14jdPPPhPoPHPqPPP0PjPHA1BG@PsPjPqG2PhP0PCPtPBPiE:F3X0D,0DP015SGPSPCPQPEPxC8f[RefZRRPoPfPqPeP0PPPfA1Bg@PsPPPqG2A<R03F3X0D,0D]1^3v^2uX51%9S1?S8PCPgPEPB%6SR?D7PfPQPgPhPHPkP>PlP=P;P5PyP{P?%;SP0g02AKMA@W1W3W2PiP0PkP>PlG=W6P0O114GdPN154i14icPQPgPoPPPqPQP0PiPPA1BH@PsPiPqG2PgP0PCPtPBPhE:F3X0D,0DP0154HP4PCPRPEPxC8f]Rdf\RSPoPePqPdP0PQPeA1Bf@PsPQPqG2A<S03F3X0D,0D]1^3v^2uX51%941?48PCPfPEPB%64R?D7PePRPfPgPPPjPFPkP>PlP=P;PyP?%;4P0g02BLMA@W1W3W2PhP0PjPFPkG=W6P0O114HcPN15Th14hbPRPfPoPQPqPRP0PhPQA1BP@PsPhPqG2PfP0PCPtPBPgE:F3X0D,0DP015TPPTPCPSPEPxC8f_Rcf^R4PoPdPqPcP0PRPdA1Be@PsPRPqG2A<403F3X0D,0D]1^3v^2uX51%9T1?T8PCPePEPB%6TR?D7PdPSPePfPQPiPGPjPFPkP>PlP;P?%;TP0g02CNMA@W1W3W2PgP0PiPGPjG=W6P0O114PbPN15Ug14gaPSPePoPRPqPSP0PgPRA1BQ@PsPgPqG2PeP0PCPtPBPfE:F3X0D,0DP015UQPUPCP4PEPxC8faRbf`RTPoPcPqPbP0PSPcA1Bd@PsPSPqG2A<T03F3X0D,0D]1^3v^2uX51%9U1?U8PCPdPEPB%6UR?D7PcP4PdPePRPhPHPiPGPjPFPkPlP?%;UP0g02DPMA@W1W3W2PfP0PhPHPiG=W6P0O114QaPN15VfQ0@,4fP4PdPoPSPqP4P0PfPSA1BR@PsPfPqG2PdP0PCPtPBPeE:F3X0D,0DP015VRPVPCPTPEPxC8fcRafbRUPoPbPqPaP0P4PbA1Bc@PsP4PqG2A<U03F3X0D,0D]1^3v^2uX51%9V1?V8PCPcPEPB%6VR?D7PbPTPcPdPSPgPPPhPHPiPGPjPkP?%;VP0g02ERMA@W1W3W2PeP0PgPPPhG=W6P0O1Q0@,4RPN15XeQ0?,4ePTPcPoP4PqPTP0PeP4A1BS@PsPePqG2PcP0PCPtPBPdE:F3X0D,0DP015XSPXPCPUPEPxC8feRVfdR?PoPaPqPVP0PTPaA1Bb@PsPTPqG2A<?03F3X0D,0D]1^3v^2uX51%9X1?X8PCPbPEPB%6XRkD7PaPUPbPcP4PfPQPgPPPhPHPiPjPk%;XP0g02FUMA@W1W3W2PdP0PfPQPgG=W6P0O1Q0?,4SPN15YdQ0>,4dPUPbPoPTPqPUP0PdPTA1B4@PsPdPqG2PbP0PCPtPBPcE:F3X0D,0DP015Y4PYPCP?PEPxC8fgRXffRkPoPVPqPXP0PUPVA1Ba@PsPUPqG2A<k03F3X0D,0D]1^3v^2uX51%9Y1?Y8PCPaPEPB%6YRjD7PVP?PaPbPTPePRPfPQPgPPPhPiPj%;YP0g02GXMA@W1W3W2PcP0PePRPfG=W6P0O1Q0>,44PN15ZcQ0=,4cP?PaPoPUPqP?P0PcPUA1BT@PsPcPqG2PaP0PCPtPBPbE:F3X0D,0DP015ZTPZPCPkPEPxC8fiRYfhRjPoPXPqPYP0P?PXA1BV@PsP?PqG2A<j03F3X0D,0D]1^3v^2uX51%9Z1?Z8PCPVPEPB%6ZRiD7PXPkPVPaPUPdPSPePRPfPQPgPhPi%;ZP0g02H[MA@W1W3W2PbP0PdPSPeG=W6P0O1Q0=,4TPN15WbQ0<,4bPkPVPoP?PqPkP0PbP?A1BU@PsPbPqG2PVP0PCPtPBPaE:F3X0D,0DP015WUPWPCPjPEPxC8fkRZfjRiPoPYPqPZP0PkPYA1BX@PsPkPqG2A<i03F3X0D,0D]1^3v^2uX51%9W1?W8PCPXPEPB%6WRhD7PYPjPXPVP?PcP4PdPSPePRPfPgPh%;WP0g02I_MA@W1W3W2PaP0PcP4PdG=W6P0O1Q0<,4UPN15[aQ0;,4aPjPXPoPkPqPjP0PaPkA1B?@PsPaPqG2PXP0PCPtPBPVE:F3X0D,0DP015[?P[PCPiPEPxC8fmRWflRhPoPZPqPWP0PjPZA1BY@PsPjPqG2A<h03F3X0D,0D]1^3v^2uX51%9[1?[8PCPYPEPB%6[RgD7PZPiPYPXPkPbPTPcP4PdPSPePfPg%;[P0g02JcMA@W1W3W2PVP0PbPTPcG=W6P0O1Q0;,4?PN15]VQ0:,4VPiPYPoPjPqPiP0PVPjA1Bk@PsPVPqG2PYP0PCPtPBPXE:F3X0D,0DP015]kP]PCPhPEPxC8foR[fnRgPoPWPqP[P0PiPWA1BZ@PsPiPqG2A<g03F3X0D,0D]1^3v^2uX51%9]1?]8PCPZPEPB%6]RfD7PWPhPZPYPjPaPUPbPTPcP4PdPePf%;]P0g02KgMA@W1W3W2PXP0PaPUPbG=W6P0O1Q0:,4kPN15\XQ09,4XPhPZPoPiPqPhP0PXPiA1Bj@PsPXPqG2PZP0PCPtPBPYE:F3X0D,0DP015\jP\PCPgPEPxC8fqR]fpRfPoP[PqP]P0PhP[A1BW@PsPhPqG2A<f03F3X0D,0D]1^3v^2uX51%9\1?\8PCPWPEPB%6\ReD7P[PgPWPZPiPVP?PaPUPbPTPcPdPe%;\P0g02LkMA@W1W3W2PYP0PVP?PaG=W6P0O1Q09,4jPN15`YQ08,4YPgPWPoPhPqPgP0PYPhA1Bi@PsPYPqG2PWP0PCPtPBPZE:F3X0D,0DP015`iP`PCPfPEPxC8fsR\frRePoP]PqP\P0PgP]A1B[@PsPgPqG2A<e03F3X0D,0D]1^3v^2uX51%9`1?`8PCP[PEPB%6`RdD7P]PfP[PWPhPXPkPVP?PaPUPbPcPd%;`P0g02N0MA@W1W3W2PZP0PXPkPVG=W6P0O1Q08,4iPN15_ZQ07,4ZPfP[PoPgPqPfP0PZPgA1Bh@PsPZPqG2P[P0PCPtPBPWE:F3X0D,0DP015_hP_PCPePEPxC8fuR`ftRdPoP\PqP`P0PfP\A1B]@PsPfPqG2A<d03F3X0D,0D]1^3v^2uX51%9_1?_8PCP]PEPB%6_RcD7P\PeP]P[PgPYPjPXPkPVP?PaPbPc%;_P0g02O5MA@W1W3W2PWP0PYPjPXG=W6P0O1Q07,4hPN15^WQ06,4WPeP]PoPfPqPeP0PWPfA1Bg@PsPWPqG2P]P0PCPtPBP[E:F3X0D,0DP015^gP^PCPdPEPxC8fwR_fvRcPoP`PqP_P0PeP`A1B\@PsPePqG2A<c03F3X0D,0D]1^3v^2uX51%9^1?^8PCP\PEPB%6^RbD7P`PdP\P]PfPZPiPYPjPXPkPVPaPb%;^P0g02P:MA@W1W3W2P[P0PZPiPYG=W6P0O1Q06,4gPN158[Q05,4[PdP\PoPePqPdP0P[PeA1Bf@PsP[PqG2P\P0PCPtPBP]E:F3X0D,0DP0158fP8PCPcPEPxC8fyRxfxR[PoP_PqPxP0PdP_A1B`@PsPdPqG2A<[03F3X0D,0D]1^3v^2uX51%981588Ru#MPCP`PEPB%68D7P[P_PoPcPqP[P0P\PcA1Bd@PsP\PqG2P_P0PCPtPBP8E:F3X0D,0DQ0FQ0HQ0IQ0J1e`A%F`1V_A#F\I[Q0KQ0GQ0LQ0MQ0NQ0OQ0PQ0QP~P11a18R8Q0RP8CZ,`~,\~Q0SQ00C_P<P2b:b@bAX8}P9\uP6[^8}P0P9P7O2b9b;b<b=b>b?'^W1W3W2P]P0PWPhPZG=W6P0O1Q05,4fP9PcP`PoPdPqPcP0P]PdA1Be@PsP]PqG2P`P0PCPtPBP\E:F3X0D,0DP0n010000000W4P0O1n200100000021100010000W4P0O1n200100000021100011000W4P0O1n200100000021100011000W4P0O1n200100000021100011000W4P0O1n200100000021100011000W4P0O1n200100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000W4P0O1n201100000021100011000bDWEWFWIWJWHWGWCWBW1W3W2W4XOCXP1X51WKWLWMQ04g02Q@5p:eo"). Qed.
End S1.
