(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_PrsStmt () := "K47Corelib4Init9Datatypes3nat02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes3nat00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt9PM_FRAMESK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z7compareI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z=pow_le_mono_rC56Stdlib6ZArith6BinInt1Z3powc6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7po_costI47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z7le_reflC46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt7umap_shI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z;div_le_monoC56Stdlib6ZArith6BinInt1Z3divC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addc6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt8po_smallc6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt6po_cntc6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_PrsStmt8po_largeK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition APO_ENTRY : Z := 0xea7bc.
Definition AWO_ENTRY : Z := 0xea7c4.
Definition APM_ENTRY : Z := 0xeeefc.
Definition ASN_ENTRY : Z := 0xf93d0.

Definition AWO_PM_RA : Z := 0xec0d0.

Definition WO_FCLASS : Z := 3.   Definition WO_FSIZE : Z := 480.
Definition WO_CTX_OFF : Z := 32.  Definition WO_PARSER_OFF : Z := 128.
Definition PM_FCLASS : Z := 8.   Definition PM_FSIZE : Z := 15616.

Definition PO_FRAMES : nat := 10.

Definition PM_FRAMES : nat := 9.
Lemma PO_PM_FRAMES : PO_FRAMES = S PM_FRAMES.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PrsStmt ()) [] "p;1p;2g0000j11Tg000Oj20Tg000ig001H#1'0o"). Qed.

Definition APM_STACK : Z := 32768.
Definition APO_STACK : Z := 512 + APM_STACK.

Definition cc_gen (len mid : Z) : list byte :=
  shadow_of mid ++ poison_bytes (Z.to_nat (nsh len - nsh mid)) 0xfc.

Definition fsin (LF : list fframe) (O n : Z) : Prop :=
  exists f, In f LF /\ ff_addr f <= O /\ O + n <= ff_addr f + fsz (ff_class f).

Definition parser_repA (LB : list block) (m : mem) (p : Z) (c : parserC) : Prop :=
  @parser_rep AC_A ASEGS LY_A MI_A (lbl LB) m p c.
Definition state_vstride (c : stateC) : Prop :=
  (t3a (st_v1 c) <> 0 -> (t3b (st_v1 c) - t3a (st_v1 c)) mod 20 = 0) /\
  (t3a (st_v2 c) <> 0 -> (t3b (st_v2 c) - t3a (st_v2 c)) mod 4 = 0) /\
  (t3a (st_v3 c) <> 0 -> (t3b (st_v3 c) - t3a (st_v3 c)) mod 4 = 0).
Definition state_repA (LB : list block) (m : mem) (st : Z) (c : stateC) : Prop :=
  @state_rep AC_A ASEGS LY_A MI_A (lbl LB) m st c /\ state_vstride c.
Lemma vstride_of_vsteps : forall c, st_vsteps c -> state_vstride c.
Proof.
  intros c ((n1 & _ & E1) & (n2 & _ & E2) & (n3 & _ & E3)). unfold state_vstride. rewrite E1, E2, E3.
  split; [|split]; intros _;
    [replace (t3a (st_v1 c) + 20 * n1 - t3a (st_v1 c)) with (n1 * 20) by lia
    |replace (t3a (st_v2 c) + 4 * n2 - t3a (st_v2 c)) with (n2 * 4) by lia
    |replace (t3a (st_v3 c) + 4 * n3 - t3a (st_v3 c)) with (n3 * 4) by lia]; apply Z_mod_mult.
Qed.

Section Sh.
  Context {HCEIL : HeapCeil}.

  Definition umap_sh {V : Type} (m : mem) (ns : Z) (t : Z * Z * list (Z * (Z * V))) : Prop :=
    (t3b t <> 0 -> addressable m (t3a t) (8 * t3b t))
    /\ (forall p k v, In (p, (k, v)) (t3c t) -> addressable m p ns).

  Definition vec_sh (m : mem) (v : Z * Z * Z) : Prop :=
    t3a v <> 0 -> SHAD m (t3a v) (cc_gen (t3c v - t3a v) (t3b v - t3a v)).

  Definition state_sh (m : mem) (c : stateC) : Prop :=
    umap_sh m 24 (st_m1 c) /\ umap_sh m 32 (st_m2 c) /\ umap_sh m 24 (st_m3 c)
    /\ vec_sh m (st_v1 c) /\ vec_sh m (st_v2 c) /\ vec_sh m (st_v3 c).

  Definition parser_sh (m : mem) (p : Z) (c : parserC) : Prop :=
    addressable m p PARSER_SIZE /\ addressable m (pc_cons c) 48 /\ state_sh m (pc_state c).

  Definition words_okA (LB0 : list block) (m : mem) (words n : Z) : Prop :=
    exists (pw : bptr) (k : Z), In (pw, words, k) LB0 /\ 0 <= 4 * n <= k
    /\ 0 < words /\ words mod 16 = 0 /\ words + k <= 2 ^ 47
    /\ mdef m words (4 * n)
    /\ SHAD m words (cc_gen k (4 * n)).
End Sh.

Definition po_small (n : Z) : Z := 36 * n + 2 ^ 20.
Definition po_cnt (n : Z) : Z := n / 2 + n / 3 + n / 2 + 64.
Definition po_large (n : Z) : Z := 16.

Definition po_cost (n : Z) : Z := 2 ^ 34.
Lemma po_cost_lo : forall n, 2 ^ 30 <= po_cost n.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PrsStmt ()) [] "p'0h01Hh12H0h21eh31ni001cp;1p;2p;3p;6p;5g002Jj10Tg002oj12Tg003Mj11Tg000Oj24Tg0042j2;Tg004Sj3:Tg004mj69Tg005Ij25Tg005hj23Tg006Dj56Tg006kj27Tg007Hj18Tg008Hg008fR0#0R1#2R2%10#1#1#0#2R0%01#0#1#0#2R1g009KR3g00:1'41;01R4g00:WR55:3P3P4P3p-0f0R4g00;=R6g00;ZP6n011000003000000X23g00<6P5P4E9P61564b1W01301eD61720%84'3eW3o"). Qed.
Lemma po_cost_hi : forall n, po_cost n <= 2 ^ 34.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PrsStmt ()) [] "h01np;1p;2g002Jj10Tg002oj11Tg003Mj13Tg006kj22Tg00<Rj16Tg007Hj15Tg005hj24Tg008Hg008f#0R0#1%00#0#3#0#1'2R0#6f0#5/40eW0o"). Qed.

Lemma po_mono : forall n n', 0 <= n <= n' ->
  po_small n <= po_small n' /\ po_cnt n <= po_cnt n' /\ po_large n <= po_large n' /\ po_cost n <= po_cost n'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_PrsStmt ()) [] "h07__arithh12Hah24__ffh38__varmaph45__with54__x1h64__x2h74__p1h86__sat1h94__x3h:4__x4h;4__x5h<4__x6h=1Hh>2H0h?2Hnh@6__sat0hA6__sat2hB6__sat3hC6__sat4hD6__sat5hE6__sat6hF6__sat7hG6__sat8hH1nhI2n'p;2p;1p;4p;3p;6p;5p;7p;8p-1R0p100=3p4p710R1p8P0p100=Jp4p710p8P0p100=fp4p710p8p100>Gp4p710P1p8g005hj21Tg00?Gj24Tg002Jj13Tg002oj18Tg00?bj1aTg00@Bj1]Tg00@bj1\Tg00A@j1ZTg00A^j1XTg00BIj2:Tg00Blj4ETg00CWj2hTg000Oj2fTg00D9j2eTg004Sj3`Tg00Dej3_Tg00EDj4^Tg00F6j2>Tg00FRj2@Tg00G0j4ATg00GNj6[Tg00H2j29Tg00HUj1YTg00I7j5JTg00I\j22Tg003Mj1?Tg00J9j2;Tg00Jjj2ITg006kj2HTg00KRj3GTg0000j1BTg00L6j2CTg00L_j2WTg00MHj3VTg00N1j3DTg00NZj2UTg00OFj2gTg00P2j3TTg00PRj3RTg00Q5j1KTg00QSj3LTg00R6j2QTg00RSj26Tg00S0j1PTg00T1j1OTg00U0j1NTg007Hj1STg00V1j7MTg00VUj7bTg00W9j8cTg00W]j3dTg00X@R1f0R0'1p=0f1R2g00X^R3g00Y=R4P4g00Y]R5P0g00Z=R6FMp=Ff2R7P3P4P4P5g008HR8P2g00Z]P0CEP6FMp=7P7P3P4P4P5P2P0Fbp=<f3R6P3P4P4P5P7P2P0Gcp==Ad820p=5%021120'4P7P2g008fR9#3R:#8R;g00[DR<#aR=%]<R>%\8R?%Z8R@%X8RAP81:81RBg00\0RC1:8;RDCE'F1hA5REP0P7g00\WRFg00]7RG'f1e07=`FGdA_812C^RGb2b3b41>1;RFP0b0p-0RHP=P>P81@87P2P?CAP@PAPAP3P4P4P5f4R5E[1989R3198:RI57ARJ5<A%Y4R4PJC=PEPGb2b3b4X58X68W7RK1102,471127[^58^68^7HRHP0%06P7P6P2O4b0DJ127;122;'1P6P7%?9R9#8RLP=P>P?P@P8PBPC1:8LCE,FAPEPGb2b3b41>1LP0b01;7;%07RC%0;RM125;#0[[1;5;%05f6RN/2;#0\M[PKPHP0%0NRHf5RKPNP5O4b0b@b8DJ126L127L'1%3:RO#3RP#?#3RQ#8RR,I;%0R1H;RRS,>1[\Fg00;ZRTAG;R2UX1M%0S\T^1M1;KL%0K%0LRRf7RU/2L#0[[1;N;f8RV/2;#0\M\H1;VL%0Vf:RH/2L#0\R[f9RR/;;%0Rf;RW/2;#0\M[%?:R:#3#3RX#8RY,I;%0Y1H;YRZ,>1[\FAG;Y2VTX1M%0Z\T^1Mg00]WRM#B#BRT#BRY#B,C81W8;1C8Y5V81C8MRM5D85D8g00^6RY'U1C8T9D8M/UY,gM=T<=5T<P>P8P81@85P71@8NCAP2P81@8KP6P?CACAP@PA198OR@%39,98R?57AP4PA1989R9198:R:57AP4PAA7AB3=<AJP4%?O#3#3#8RO,:8R4=R83%KX9L8DRX'5AR84I/5X57A159@/59%3PRP#3#3#8R9,:8R@'515:?/5:/5@57A%8PRP,:8R@=7A@%KQ9L8DRD=7AD5<A5<A5<AC=C=C=PEPGb2b3b4X58X68X98X:8X;8X<8116KRG1176,4C1QO6/6Z1QO5/6Z'116KN/6K/6916UV/6U/69'111PP11SS'4'4'4[\G[^58^68^98^:8^;8^<8P0f<R0/2L120;f=RG/2L12G;P0PGPRPHPWO9b0b8bAbBbCbDbEbFbGb>b=%P7%P2'1%O7%O2'1%N7%N2'1%S7%S2'1'4'4'4eW?XI8XH8o"). Qed.

Definition PM_DTOR_RAS : list Z :=
  [0xf0e44; 0xf0c60; 0xf16e4; 0xf1d0c; 0xf20c4; 0xf2324; 0xf255c; 0xf2884; 0xf2b28; 0xf2d00; 0xf2ef4; 0xf30dc;
   0xf3318; 0xf34e0; 0xf37e4; 0xf39d0; 0xf42fc; 0xf3c58; 0xf3f54; 0xf4098; 0xf4780; 0xf4a6c; 0xf4cc8].
Definition PM_EXH_RAS : list Z := [0xf12d8; 0xf2dec; 0xf19d4].
Definition PM_PF : list (Z * list Z) :=
  map (fun r => (APC0_FREE, [0xfd148; r])) PM_DTOR_RAS ++ map (fun r => (APC0_FREE, [0xfd148; 0xf8f14; r])) PM_EXH_RAS
  ++ [(APC0_FREE, [0xf5618]);
      (APC0_FREE, [0xf4188]);

      (APC0_FREE, [0xfd148; 0xf99ec; 0xf2738]); (APC0_FREE, [0xfd148; 0xf9d14; 0xf2738]);
      (APC0_FREE, [0xfd148; 0xf99ec; 0xf3b10]); (APC0_FREE, [0xfd148; 0xf9d14; 0xf3b10])].

Definition PO_PF : list (Z * list Z) :=
  [(APC0_FREE, [0xeb480]); (APC0_FREE, [0xec22c]); (APC0_FREE, [0xec2b0]);
   (APC0_FREE, [0xfd148; 0xeb704]); (APC0_FREE, [0xfd148; 0xeb99c]); (APC0_FREE, [0xfd148; 0xebce0]);
   (APC0_FREE, [0xfd148; 0xebfb4])] ++ pf_shift AWO_PM_RA PM_PF.

Definition ST_MVA_DEL_RAS : list Z := [0xed8d0; 0xed9ac; 0xed020; 0xed100; 0xedca8; 0xedd84; 0xee10c; 0xee2bc; 0xee46c].
Definition ST_DTOR_DEL_RAS : list Z := [0xed60c; 0xed61c; 0xed62c; 0xed66c; 0xed6b4; 0xed6f4; 0xed73c; 0xed77c; 0xed7c4].

Definition PM_DEL_RAS : list Z := [0x1200e8; 0xfad2c; 0xfc020; 0xf8900; 0xf8b70; 0xfb5bc; 0x100228; 0xfc600].

Definition RESV_DEL_RAS : list Z := [0xec5f0; 0xec748; 0xec89c].

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Variable LINV : mem -> Prop.

  Definition pm_tr_ok : Prop := Forall (fun r => trace_ok (as_TR H) APC0_FREE [r]) PM_DEL_RAS.

  Definition po_tr_ok : Prop :=
    pm_tr_ok /\ Forall (fun r => trace_ok (as_TR H) APC0_FREE [r]) (ST_MVA_DEL_RAS ++ ST_DTOR_DEL_RAS ++ RESV_DEL_RAS).

  Definition ctx_okA (LB0 : list block) (m : mem) (ctx env : Z) : Prop :=
    exists (pc : bptr) j1 j2, In (pc, ctx, 64) LB0
    /\ rw_cells asegs m ctx [C4 (wz env); CB 44 j1; C8 (wz 0); CB 8 j2]
    /\ addressable m ctx 64 /\ 0 <= env < 19.

  Definition po_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (n lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block)
                    (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' LB
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m'

      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ LINV m'
      /\ as_AL H s' >= as_AL H s - po_cost n.

  Definition po_stmt_at (entry : Z) (needs_a7 : bool) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (ctx env words n lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 entry) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 ctx -> a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 words -> a3 = Z_to_bv 64 n ->
      a4 = Z_to_bv 64 0 -> a5 = Z_to_bv 64 0 -> a6 = Z_to_bv 64 0 -> (needs_a7 = true -> a7 = Z_to_bv 64 0) ->

      ctx_okA LB m ctx env ->
      0 <= n < 2 ^ 24 -> (words = 0 /\ n = 0) \/ words_okA LB m words n ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_small LB + po_small n <= RT_SMALL_MAX -> Z.of_nat (length LB) + po_cnt n <= RT_CNT_MAX ->
      nlarge LB + po_large n <= RT_LARGE_MAX ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - APO_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      LINV m ->

      ACONST m ->
      as_RFS H LF m -> (length LF + PO_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) PO_PF (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      po_tr_ok ->
      po_cost n <= as_AL H s ->
      as_SR H (po_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF n lo B shi m mo) (mkCfg msF mo).

  Definition binary_parse_stmtA : Prop := po_stmt_at APO_ENTRY false.
  Definition parse_with_options_stmtA : Prop := po_stmt_at AWO_ENTRY true.

  Definition state_own (LB LB0 LBs : list block) (c : stateC) : Prop :=
    Permutation LB (LB0 ++ LBs) /\ Permutation (lbl LBs) (state_blocks c).

  Definition pm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (p : Z) (c : parserC) (lo B shi : Z) (m : mem) (mo : Model)
      : config -> Prop :=
    fun cf => exists t0 t1 t2 (r : Z) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' LBs' : list block)
                     (c' : parserC) (XS : list (Z * Z)) (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ state_own LB' LB0 LBs' (pc_state c') /\ lb_own LBs' m'

      /\ parser_repA LB' m' p c' /\ parser_sh m' p c'
      /\ pc_cons c' = pc_cons c /\ pc_user c' = pc_user c
      /\ st_words (pc_state c') = st_words (pc_state c) /\ st_nwords (pc_state c') = st_nwords (pc_state c)

      /\ lb_small LBs' + 2 ^ 12 <= po_small (st_nwords (pc_state c))
      /\ Z.of_nat (length LBs') + 8 <= po_cnt (st_nwords (pc_state c))
      /\ nlarge LBs' + 3 <= po_large (st_nwords (pc_state c))
      /\ st_vsteps (pc_state c')
      /\ (forall q k, In (q, k) (state_blocks (pc_state c')) -> k <= 2 ^ 40)
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB0 (bv_unsigned sp) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (p, p + PARSER_SIZE) :: XS) m m'

      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi /\ LINV m'
      /\ as_AL H s' >= as_AL H s - po_cost (st_nwords (pc_state c)).

  Definition parse_module_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBs : list block) (LF : list fframe) (CH : list (Z * Z)) (p : Z) (c : parserC)
           (lo B shi : Z) (errv : word),
      let words := st_words (pc_state c) in let n := st_nwords (pc_state c) in
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 APM_ENTRY) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 p ->

      parser_repA LB m p c -> parser_sh m p c -> fsin LF p PARSER_SIZE -> fsin LF (pc_cons c) 48 -> pc_cons c mod 16 = 0 ->
      wr_at asegs m (pc_cons c) 48 ->
      fresh_state (pc_state c) words n ->
      0 <= n < 2 ^ 24 -> (words = 0 /\ n = 0) \/ words_okA LB0 m words n ->
      state_own LB LB0 LBs (pc_state c) -> lb_own LBs m ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_small LB0 + po_small n <= RT_SMALL_MAX -> Z.of_nat (length LB0) + po_cnt n <= RT_CNT_MAX ->
      nlarge LB0 + po_large n <= RT_LARGE_MAX ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - APM_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      LINV m ->

      ACONST m ->
      as_RFS H LF m -> (length LF + PM_FRAMES <= AFS_MAXLIVE_BP)%nat ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) PM_PF (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pm_tr_ok ->
      po_cost n <= as_AL H s ->
      as_SR H (pm_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB0 LF p c lo B shi m mo) (mkCfg msF mo).
End Stmts.
