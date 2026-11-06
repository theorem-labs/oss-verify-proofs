(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac Arr Bytes ITree.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Startup_glue () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I69OSSVerify5KrLib2K53Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4implC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53Lib4Exec3evtC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5ITree5itree01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec7evt_cutC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5ITree5itree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree4nretC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib4Exec8evt_monoC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C69OSSVerify5KrLib2K53Lib5ITree4respC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K52PG<Startup_glue=impl_post_evtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5ITree5epostC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2K53Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib2K53Lib5ITree3Exc3exc02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes3appC69OSSVerify5KrLib2K53Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3iffC69OSSVerify5KrLib2K53Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsIreflexive_reflexive_proxyC47Corelib7Classes>Morphisms_Prop@and_iff_morphismC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC69OSSVerify5KrLib2K53Lib5Cells<cells_wf_appC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addC47Corelib7Classes9Morphisms:respectfulC47Corelib7Classes9MorphismsNReflexive_partial_app_morphismC69OSSVerify5KrLib2K53Lib3Mem<bytes_at_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Logic6eq_indK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphK47Corelib7Numbers7BinNums8positive01C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC47Corelib4Init5Logic8eq_ind_rC46Stdlib6ZArith:ZArith_dec8Z_lt_decC47Corelib4Init5Logic3notI47Corelib4Init6Specif7sumbool00K46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib2K53Lib5Cells>cells_size_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Cells?cells_bytes_appC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib7Classes9MorphismsFreflexive_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C47Corelib7Classes?RelationClasses>iff_TransitiveI47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C47Corelib7Classes?RelationClasses=iff_ReflexiveC46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53Lib3Mem3le8C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes6option01I47Corelib4Init5Peano2le00C69OSSVerify5KrLib2K53Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC69OSSVerify5KrLib2K53Lib3Mem@bytes_at_ov_readC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib2K53Lib3Arr4u64sC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorC69OSSVerify5KrLib2K53Lib3Arr:u64s_splitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C47Corelib4Init3Nat3mulC56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions7Z_to_bvK46Stdlib9micromega7EnvRing5PExpr05C35stdpp7tactics<f_equal_helpc69OSSVerify5KrLib2K52PG<Startup_glue6rd_u64C1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mul".
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q Q' ms,
  impl segs atn t Q' ms -> (forall r ms', Q' r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_glue ()) [] "h03rsph11Qh22Q'h32msh43ms1h53ms'h61rh71Hh82H0h92HQh:1th;1xh<3Hath=2Hkh>2IHh?1Rh@3atnhA1khB1nhC4nodehD4segsp;1p;2p;7p;3p;6p;4p-1R0p10000p4p710p9P0p1000SR1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p10011p4p710p9p200R0g001iR1p4p710p8p202R2g002bR3p4p7210p8P2g003]R4p4p741110p8g004Sj1;TP1j23TP4j70Tg0053j35Tg005gj36Tg006`j6:Tg007Xj44Tg008Qj21Tg009GR4j22Tg009bj48Tg00:=j67TP3j69Tg00;6#;f1R3g00<5R1p-0[R5[f3R6f0R7'3f4R8P31383f2R9P5];R:P5\6R;f8R<f7R=f6R>f5R?P6P3P7F0P8P3P7O2R@f;RAP>P9O1RB;53[^51^6>RCf:RDf9REP<P=P?P8P9F0[[^31]2]1W:P<P=P>P?A6<?6P3P7F0PEP6P?O1P8P?O1P9P3P8P>P7O2P9P=P3P7O3W8X51E:PDPEP<P=A6D=?P8P9F0eX9CW7X31X2;X1:X63g00=<R:13>6[P5^;8R;P5\?R5PDPEP<P=P8P6O1P3P7F0f=RC?5B3\@^51^6<R@f<RBPAPDPEP>P?O1P8P9F0[[^31]2]1\:PDPEP<P=PDP=P?P8C4P3P7F0PAPAP<P7O2RFf>RGPCPBPAP<P7O1RHP?1137RIF0^0:'2X41PGPCPBPAPHP>PIF0^0:,2FX41P9P3PBPEP7O2f?RFPGPCPBPEP7O1RHP>PIF0^0:'2X41P7O1P4PBPEP3O2PFPGPCPBPHP>1197F0^0:PCPDP9O2f@RHPFPGPCPDP7O1P<1167F0^0:'2P7PGPAP6O2fBR6fARGPHPFPBP7O1PE11?7F0^0:PHPCP?O2fCP6PGPHPCP7O1PA11>7RCF0^0:P3PBP7PAPDPCP3P7O1P=O6X0:C8W=W<P3P7O2n2001000000120000000W8X41E7PBPAPDPEPBPEP=P>C4P8P9F0eX9@W7X31X25X1;W>WAXB8P7E9W:X?2W@WDXC0o"). Qed.

Lemma impl_epost_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {A} (t : itree node (exc A)) Q Q' ms,
  impl segs atn t (epost Q') ms -> (forall a ms', Q' a ms' -> evt segs (Q a) ms') -> impl segs atn t (epost Q) ms.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_glue ()) [] "p'0h03ms'h12Hph21ai001ah31Ah41Hh52HQh61Qh72Q'h83atnh92msh:4nodeh;1rh<4segsh=1th>1xi011ep;1p;2p;7p;3p;4p;:p200R0g00>2R1p4p710p8P0g001iR2p4p710p8p202R3P1p4p741110p8P3g003]R4p4p741110p8P3g00?7R5p4p710p8g004Sj1;Tg00?nR6j14TP2j29TP5j23j41j32TP4j7:Tg0053j30Tg00@ij16Tg00Adj48Tg00B]j25TP1l:7Tg00;6#;f1R1g00<5R4p-0[R5[f3R2f0R7#4'9P5^>1f2R8P5[f7R5f6R9f5R:f4R;#4P213;1P7F:P;P1P7O2f:R<P9P8O1;01[^04^2:f9R=f8R>P5%49R?P:139;1392P8P1P6P5P=P9P1P7C1f<A2<>8;01[^04P7P>P:%6>P7C1f;R9%6=92=5R6P1g00CXC8A0961eW1X04P<P515<1P7C1P:P8P1P7O3f=1598929=;01eW1X04X2>P7O1n10110100020010100X;?M:7W5W4X94W7W6W=X33W8W<X:0o"). Qed.

(* [comment removed for export] *)
Ltac astep := lstep; try (first [if_true | if_false]).
(* [comment removed for export] *)
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
Tactic Notation "icallk" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  eapply impl_epost_evt; [ eapply SPEC | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac amo_decide :=
  repeat match goal with
  | |- context [amo_aligned ?wd ?a] =>
      let b := eval vm_compute in (amo_aligned wd a) in
      (* [comment removed for export] *)
      replace (amo_aligned wd a) with b by (vm_compute; reflexivity); cbv beta iota delta [negb]
  | |- context [Z.eqb (bv_unsigned ?x) (bv_unsigned ?y)] =>
      let b := eval vm_compute in (Z.eqb (bv_unsigned x) (bv_unsigned y)) in
      replace (Z.eqb (bv_unsigned x) (bv_unsigned y)) with b by (vm_compute; reflexivity); cbv iota
  end.

Ltac amo_step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; amo_decide; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition td_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 32 (repeat (Z_to_bv 8 0) 32);
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition rtd_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale canary dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 24 (repeat (Z_to_bv 8 0) 24); C8 canary;
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition libc_cells (can_do : byte) (auxv tls_size tls_align page_size : word) : list cell :=
  [C1 can_do; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 auxv;
   C8 z64; C8 tls_size; C8 tls_align; C8 z64; C8 page_size; CB 48 (repeat (Z_to_bv 8 0) 48)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_glue ()) [] "p'0h06__sat4h14__x1h24__x2h34__x3h41ih51Hh62L0h77__arithh86__sat3h94cstrh:5cstr0h;5cstr1h<4__ffh=8__varmaph>5__with?3HN0h@1ni001nhA1xhB4__p1hC2B2hD2HihE3Hi0hF1yhG2B1hH2HahI2L1hJ2W1hK2W2hL4__x4hM1li011lhN5lemmahO1mhP1zhQ1AhR1BhS2HAhT3HA1hU3HA2hV2HNhW3HN1hX3HN2hY2HWhZ3HW1h[3HW2h\2WRh]3cs1h^3cs2h_1si021sh`4segsp%0p%1p&0p;1p;3p;2p;4p;6p;;p;5p;9p;<p;Bp;7p;8g004Sj1qTg00D4j1UTg00DYk10:Tg00E7k104Tg00EZk10iTg00F<j3sTg00FYj16Tg009GR0j22Tg00GSR1j2^Tg00Glj14Tg00Hij47Tg00Iaj13Tg00J]k30hTg00KSR2j6|Tg00LER3j11Tg00LeR4j20Tg00MBj48Tg00N7k20YTg00Nck20WTg00Oaj2GTg00P8k40MTg00P_m;0KTg00QZk50JTg00RVk206Tg00SZj2@Tg00T:j6zTg00TVk10BTg00U4k20^Tg00UQk10?Tg009bj4MTg00V3R5j2ATg00VOk10=j3KTg00Vik20\Tg00WLk30[Tg00Wij4DTg00XPk10<Tg00Xnk40ZTg00YQj1;Tg00Z6k20XTg00Z^R6j2=Tg00[:k30VTg00[^k20UTg00\?j2PTg00\Yk10TTg00]9j2mTg00]Wk10STg00^5k10QTg00^`k207Tg00_Cj2aTg00_fk20PTg00`Hk20OTg00a4k30NTg00aSk40LTg00bEj1jTg00bdj2[Tg00cMj2iTg00d9j3dTg00dYk10ITg00e7k30HTg00eZj3fTg00f@j6gTg00fik102Tg00gNj4yTg00h9j1xTg00hkj3nTg00ihj6wTg00jFk20ETg00jjj1XTg00kCS00k20DTg00kck309Tg00lFj2oTg00lck60CTg00mGk20gTg00nGk20fTg00oHk401Tg010Ak40eTg0114m90dTg011nm<00Tg012SmB0ATg0139m<0`Tg013^j4}Tg014Ik70@Tg014mj8~Tg015Qk30_Tg016:k40aTg016Xk30bTg017;k70cTg017_k60]Tf3R7f2R8f1R9f0R:#1C8p=lp-0R;P1P9P:H0ep=vf5R<f4R='2P7P8P9P:C8'2p>0>P=P7P8P9C7,2</2:p=BP;P1g018CP<P=P7P8P9P:N90dp>0;P7P8P9P:C8,2=p>0Rf6R>P<P=1@89#1,07P:C7'2p=FP=P7P81G9:#1C8p=C12<=P7P8P9%1:C8'2p>031278/29/2:p=J1289/2:p=c1@9:#1p=eP=P71089P:C7p=\g0194R??K9:p=I%1:,09p=bg019SR@/A:p=51G9:#1p=N1089/A:p=<1=9:,28p=:1089#x9n=7=K<:#Xp=>P7P8P9P:C7,2=p={%69/2:p=tg01:1RA?K9:p=?1PA:p=9P?PAP:P3P9P8P7P=P<P>f7RBf8RCN<00p=VP?P?P?PAPAPAg01:OP3P3P3P4g01:oP<P=P7P8P9P:NB0Ap=RP?PAPAPAP3P3P<P=P7P8P9P:N<0`p=QPAPAPAPAPAPAP4P:P9P8P4P7P=P<P>PBPCf9R4NB0Ap=rPAPAP5PBP5P>P<P=P7P8P9P:N<00p=p%4:,@9p=TP8g01;RS01g01<1R5P5g01<QR3PAP9g01=1P:C}g01=XRDK0@p=EP7Q01P5P5P3P8P9P:G~p=]B0_A9:p=SPAP8P9P:H0ap=YB0bA9:p=LP>Q01P5P5P3P<P=P7Q01P5P5P3P8P9P:G~G~p=W%3:#1p=`PAPAP6PBP6P>P<P=P7P8P9P:N<00p=uPAP9g01>8P:C}p=ZP9Q01P5P5P3P:PDK0@p=HP8Q01P5P5P3P9P:K0cp=OP>P<P=P7P8P9P:CMCMp=_%x99n78=K=:#Xp>0GPAP9g01>_P:C}p=hAK89:#Xp>051@9:#1,08p>0FP=P7P8P9C7,2<,2>/2:p=kP9Q01P5P5P3P:J0]p>08g00;6#qg01?FRD#US02#UR6#URE#U#U#URF$0:RG$04&0:E$04RE$0iRH[g01?kRI#qS03Q03AsI9:S04#6%69RJ%6:RK'2RL'^AsI89RI#6RMP<P=P7%4IC7RN'2ROP<P=P7%3IClRI'2%68S05/2JRP/2NRQ/2IPOPQPMPPP:PNPNg01@c:0h;1RM/vNE|PIPI1vMIE|Q05P<P=P7%48S06C7RNP<P=P7%38S07#1RQJ0>S08PJP<P=107QRO%49RRP<P=PO%39RO#1RSC8EBS09'2RTPT20Y;TRUJ0;WN20W9:%qERV%4:RW9sERRXPPP<P=P7P:PIEB/^TXMVP?%3:RV,GORIP<P=P7Q06=sERC7RY,2PRZP<P=P7%1:S0:I0R/^TX@?P=P7P8PXC7P=P7P8PRC7RXP=P7P8PEPRPWFFR['^P<P=P7Q07PODCRO,2ZPNP<P=P7PEQ06PRFFRN,2PR\/2OR]PZP\P;P;^R;P1P;P;P1P1H0MP0P2PP1vMPPYPNP:N;0KPOPO1vMOE|PTPTPUJ0;WNP=P7P8PRPWI0JPLP[P=P7P8PIJ03S0;PT[PJPXP=P7P8PSC8PKP=P7108SS0<PWP=P7Q0<PVClEBCJS0=P][Q0;P0P\PO%67S0>P>P<P=%47S0?C7S0@P>P<P=%37S0A#1ROC8Q05P>P<10=OROQ06P>P<POPQC8EBCJP:%6=S0BQ0>PBP>P<%4=RQC7S0CPBP>P<PEPQQ0?FF3cP0%6<S0DQ0B'2PCPBP>%4<S0EC7S0FPCPBP>PEQ0EPQFFP4PCPB%3>S0G%3<S0HDC%6BRQf:ROP4PC%4BS0IC7S0J'2S0KPOP4PC%3BS0L#1R\C8%6>R]POP410C\R\%4>S0MPOP4P\Q0G#1S0NC8EB3c[P:12Q]S0OP0%6CS0PPQf<RQf;R]PO%44S0QC7PQP]POPEQ0Q%4CS0RFFf=R\PQP]%3OS0S%34S0TDC%6]S0Uf>RVP\PQ%4]S0VC7S0WPVP\PQ%3]S0X#1RWC8%6OS0YPVP\10QWRW%4OS0ZPVP\PWQ0S#1S0[C8EBCJ[[P:Q0YQ0Yf?RWPVP\%4QRSC7PWPVP\PEPSQ0VFFP0f@RKPWPV%4\S0\C7PKPWPVQ0\,eEPSD\fARSPKPW%3VS0]%3\S0^DC%6WS0_fBRXPSPK%4WS0`C7S0aPXPSPK%3WS0b#1RJC8%6VS0cPXPS10KJRJ%4VS0dPXPSPJQ0]#1S0eC8EBCJ[P:Q0afCRJPXPS%4K,eEQ0`D\fDRTPJPX%3SS0f%3KS0gDC206XB%4XS0h,@E%3XS0i'IP?%4JS0j,@ES0kfGRIfFR[fERLQ0:Q0jD\X@?P8%3JS0lP:EzP[PLQ0l,bTS0mQ0hC7P0%5L%3TRRQ0l'NQ02$0BRU&0BFRF+0^RM5<L%5:RN%3LRY/NR7::PHfIRPfHR2PIP9&0?ER1E>S0n[^4A'2%6LS0oP2PIP[%4LS0pD{P2PIP[%1YS0qC8%6TP2PIQ0q,0[RY%4TP2PIPYPRClEBS0r3cP8%5I%3IRR%3[S0s'NS0t=<2M%32RY/NRRR9:N:PHfLRZfKR^fJR_P9P1E>[^4A'2P0A<PRM%3PRR/NY9:N:PHfMR`PZP^P9P1E>[^4APZP^P_%4PC7,tPPZP^P_%1RS0uC8%62S0vPZP^Q0u,0_Ra%42C7S0wPZP^Pa%1YS0xJ0>3cP:%3_S0y/NR=<^M%3ZRR%3^S0z'N9:N:PHfPRYfORafNRbP9P1E>[^4A%6ZRcPaPbP`%4ZRdC7Re'2RfPaPbP`%1RRgC8Rh'2%6^S0{PaPb10`gRi%4^S0|C7S0}'2S0~PaPbPiQ0z#1S10C8S11'2PfPhPcPePSPQCM%5`1AiMRe%3`Rc#1Rh9:N:S12PHfQRfPYPaP9P1E>[^4ARj'21@EdRd/IR%1dRk/?gS13&0=?S14&0=AS15%19Q0:'?1I9:20\9:40[XF?XA?S16PdPk%9kPRPg%9gRkM9VP4CDS17Q131GcRRd#1Rl,0bRm/AM10hgRn=<bMS18P:XAARo1A9:$0<XFAXAAS19PmPoPnO1Rm,0bPoPoPoPAPAg01AS109:H0Z#9XOAX@AS1:PbPb%9bPlPmPoPoQ0:#9XA?S1;PdPnPcPh%9hS1<PRPgPkEREQM:rPMPM%9MS1=1?MMeS1>GpP8CDS1?Q18%;cS1@%5hS1A%3aRk#;RR%1kRn#5Rd1TEYRm#;S1B%1m#5S1C20XUFRm1=@URl%5F1=@M[Rp[Rq%5URrg01B7RsB0VUF9UWHRF%5M\s^HrRrP9g01BS20U@U'PPleO1RlPpg01C9Rs$0TRt%qsRu1mA9&0SARv&0QARw207A@Rx1aADRy5EwS1D&0?5RzQ1DC]20Pw3R{P:P8g01CeR|g01DER}'P20O:8=K|}dB0NA@9H0LR@b<b=b>X1AS1E%59R}\N^1AS1FP:fVR|PVO2b7b0b8b0b;b:b9b?b6PePjQ17Q13Q1?Q18Q1@Q1APRPdQ1BQ1CPmPqPFPrPlPpg01DeRj#jRe#jS1G,[AS1H1[Ae1[AjS1I'SS1J'SS1Kg01EDS1L'i=dstPu1mA7S1M&0IAS1N7Y8Q1N7Y9PvPw1aA6R69EwxPzPwQ02,aARj/L6,Ly207AU>0HAGRG5EwPz1LyjS1O=EwGFWP{P@b<b=b>X1AX2AX3A%58RU1087R6=<9MS1P1A6M[[^1A^2A^3AP:fTS1Q#`S1RfUR6#`S1SP|P>PBO5b7b0b8b0b;b:b9b?b6Q12P8P9%3bRe/GcS1T#1S1U,=9S1V,2}%1eR~/0hS1W,=9S1X,2}P}Q1VP}Q1X1P;}9f}}Po1=9:$0<XFAXAAS1XP9P9%99Q1UQ1WPoPoQ1;Q1TQ1WPeP~%9~S1WPcPhQ1<EREQGuEg%4bS1<,@ES1T/IeQ1T#1Rc/?~S1UQ14Q15Q16Q1TPc%9cPeP~Q1WM9VP]CDS1TQ1U1GkeS1V#1S1Y,0YRc/AM10n~S1Z=<YMS1[PoQ19PcPoQ1ZO1Rc,0YPoPoPoQ1:PYPY%9YQ1YPcPoPoQ1;Q1VQ1ZPkPn%9nS1VPeP~Q1WEREQS1WM:rPMPMQ1>GpP=CDS1\Q1[PRPd%3fRe#;S1]%1eS1^#5S1_fRRe#4S1`,@ERc#;S1a%1c#5S1bPmPqPFPrPlPpQ1G#jS1G,[AS1cQ1J'SQ1L'i=dstPu1mA8S1JQ1M7Y9S1MPvPw&02D,aARD9EwxS1dPzPwQ1D1Zyj,HwS1e5OwS1fPzQ1D1LjDS1g,Zy,HwS1h5OwFWP{P@b<b=b>X1AX2AX3A1=98S1i,2}107=S1j9:U8[\U^1A^2A^3AP:%3|S1k#1S1lfWS1m#3R}#1RcPOP>P4O5b7b0b8b0b;b:b9b?b6CyO2WDX4ACMF_Q0~Q11Q0{Q0}PKPCCM%5iQ10=<iMS10A:N:gS11PHPfPY10a~S0~/09S12P1I0G[^4ARi'2Q17Q13Q1?Q18Q1@Q1APRPdQ1BQ1CPmPqPFPrPlPpQ1cQ1K'SQ1L'i=dstPuQ1MPvPwQ1dPzPw1hDj,HwPzPwQ1DPzQ1O9EwxS1dC]FWP{P@b<b=b>X1AX2AX3A1?78Q1j#5S1K\U[\U^1A^2A^3AP:%46,eEQ1SP|P=PCPVO6b7b0b8b0b;b:b9b?b6Q10PiQ17Q13Q1?Q18Q1@Q1APRPdQ1BQ1CPmPqPFPrPlPpPtPuQ1MPvPwQ1g,LyS1g=EwGS1CPzQ1O/LDRi=EwGS1BC]P{P@b<b=b>X1AX2AX3A1098S1A,0:RG/AMQ1A?<7M[^1A^2A^3AP:Q1RQ1SP|PBO4b7b0b8b0b;b:b9b?b6Q11Q1TQ1UQ1\Q1[PRPdQ1]Q1_Q1aQ1bPmPqPFPrPlPpPtPuQ1MPvQ1g/hi,HwP{P@b<b=b>X1AX2AX3A10:9S1g/08S1b,?G^1A^2A^3AP:POPcfXRGO3b7b0b8b0b;b:b9b?b610~9,0aQ12'?PA10n8Ri,0YfSRd%x:S127ne>05H1XPAP7Pi%5iRRQ1Y,=iS1a'2Q1Z,=iS1_,2RPRQ1aPRQ1_1P;R9fRRPoQ1XPiPi%9iQ1YQ1ZQ1WGuEg%4aS1W,@ERi/Ik%1iS1Z/?nRRQ14Q15Q16PiQ1ZQ1Z#9PkPnQ1VM9VPQCDPR%3YRR/GkS1_#1S1a,0fS1]/AM%1RRi/0nS1[=<fMS1\PoQ19Q1]PoQ1[O1S1],0fPoPoPoQ1:PfPf%9fQ1aQ1]PoPoQ1;Q1_Q1[PRPi%9iPkPnQ1VEREQM:rPMPMQ1>GpP<CDQ1\%;R%5i%3eRR#;%1RRk#5%4dS1\,@ES1>#;Q1>#1S1>#5PmPqPFPrPlPpQ1G#j,[AQ1cQ1HQ1I'S'S'SQ1L'i=dstPuQ1J1mA=Q1N7Y77Y9PvPwQ02$02,aARs9EwxPzPw1hsy,HwPzPwAEwxj1ZjD,Hw5OwPzQ1dQ1O1LyDS02'Z,Hw5OwC]FWP{P@b<b=b>X1AX2AX3AXLA%57Rs1?=9A:s7=Q1KQ1j107<3:[[[^1A^2A^3A^LAP:%4G,eEPcP]%3GRs#1P=PCPOO7b7b0b8b0b;b:b9b?b6CyO210Yn/08P:Ezb5WDX4AF_F_WYWVP9P:O2n2001000000121000000W5WSP9P:O2n2001000000121000000bCbIW\WCWGP9P:O2n2001000000121000000W5WKWJP9P:O2n2001000000121000000W5P9P:O2n2001000000121000000W5P9P:O2n2001000000121000000W5Q0=P0Q08Q09Q0>Q05Q0@P>P<P=PEQ0?Q06FFP>P<P=Q0AQ07DCCJP:Q0BQ0CPBP>P<%3=J03P0Q0DQ0F'2PCPBP>Q0H#1S0HC8Q0DP4PCQ0N,0BRnQ0EP4PCPnQ0HC8EBQ0OQ0JPOP4Q0I:0FCEQ0MPOP4PCQ0LQ0GDCFk[P:Q0KP0Q0PP]POP4Q0RC7PQP]POQ0T#1S0TC8%64P\PQQ0[,0]RnQ0QP\PQPnQ0TC8EBQ0UQ0YQ0WPVP\PQPEQ0VQ0ZFFPVP\PQQ0XQ0SDCCJ[[P:Q0YQ0WPWPVP\%3QClP0%5VRQQ0^#1Rn=<VMQ0e9:N:PHPXPSPKP9P1E>[^4A'2%6\PSPKQ0e,0WRWQ0\PSPKPWPnC8EBQ0_Q0cQ0aPXPSPKPEQ0`Q0dFFPXPSPKQ0bQ0]DCCJ[P:%5KQ0g#1=<SMQ0f#1RK9:N:PHPLPTPJP9P1E>[^4A'2P0A<XKMQ0i#1Rn9:N:PHP[PLPTP9P1E>[^4A%6SPLPT10JnRn%4SPLPTPnPKC8EB%6X,tJP[PLPTQ0jC7P[PLQ0k,bTQ0hP[PLPTQ0lQ0iDCFk[P:Q0m/AMQ0q9:N:Q0n[^4AQ0rP0Q0oPPP2Q0s,bIRTQ0pD{PPP2PTQ0qC8%6IRT%6[P_PPP2%4IRLC7P_PPP2PEPL%4[FFP_PPP2Q0tC8CJP:PTP^P_Q0x,0PPLD{P0Q0vQ0wP`PZQ0y,b^Q0uC8Q0{%6_RLPbP`PZQ0|C7PbP`PZPEQ0|%4_FFPbP`PZQ0zQ0yDCCJ[P:Q0}PYPa10bhPgC8P0Q0~#5Q0~?<hMA:N:~PHPdPe10fiR~P9P1E>[^4A'2%6b,taPePfPYQ1WC7PePfQ1Z,0YQ1<PePfPYQ1YC8FkP:%5~Q1^,0e?<iMQ1^9:N:PHP|P6Q1Q%3dRi#1R~'0P9P1E>[^4A'2P010dkQ1^;<MA:N:kPHQ1mP|Q1R,06RkP9P1E>[^4A%6e,tdP|P6Q1QQ1\C7P|P6Q1QQ1>'0Q1`P|P6Q1QPiPRDCFkP:A<k~MQ1S9:N:PHfZRkfYR~10GcP9P1E>[^4A206|^%4|RR,@EQ1k'IQ1m#6Ri%6|R|'2R6PkP~PGQ1m#4RdC7RePkP~PG1@EdR0#1RYPRD\RR'2Rf'2PkP~PGQ1k,G}Rb#1RhC8P6PfPiP|PZP]CMPePRP^P?P}f[R^PkP~Q0:PdD\X@?POP0P:EwF_%5G10GhR?/AMRd1Ns}9:N:RsPHf\RRP^PkP9P1E>[^4ARe'21I0}1?YcR]Q14Q15Q16P0PY%9YP}Pc%9cRYM9VP:CDR0P]%;}RZ%5cR|%3~R~#;Ri%1~R~#5Rf1TEkR6#;Rg%16#5R6PmPqPFPrPlPpQ1EQ1FP:f`R`PaO2b7b0b8b0b;b:b9b6PdPePdQ1l,0cRd,0GRe/AMPoQ19P?PePoPoPoQ1:PGPG%9GPhPdPoPoQ1;PbPdP}PcPYQ1kQ1lQ1l#9EREQM:rPMPMQ1=GpP0P]PZP|PiPfPgP6PmPqPFPrPlPpPtPuQ1MPvPwQ1BPzQ1CC]P{P@b<b=b>X1AX2AX3AQ1b/AMQ1P[^1A^2A^3AP:f^RM#3R6#1Rgf_#3Rf#1RiP`POO4b7b0b8b0b;b:b9b6Cy20E9~1=9~R~%X~+0DQ00%`k,=8Rk%XkPHPMf]RkPRP7P1E>P:%3^R^#1R~,=7R|PIP=%5=RI%3RRR/G^RZ#1R],==R0'2%1RRY/0~Rc9:I=R}PIP0PIPoPcO1R0,==1P;IAK;IIe9fIIPoQ1XP=P=%9=P]P0PoPoQ1;PZPcPRPY%9YRcP^P~%9~EREQGuEgP7CDR~P}1TEkR^%3kRZ'I%1^R0%1ZR]'?RIQ14Q15Q16P^P0%90PZP]%9]R0M9VP>CDR>PI%;ZR^%5]Rd%;fRf%5iRi1TE`Rb#;Rh%1b#5RbPmPqPFPrPlPpPtPuQ1JQ1N7Y9PvPwQ1D208w=5OwPzPwQ1ePzQ1fFWP{P@b<b=b>X1AX2AXB;12N8Q1iA:U87[[^1A^2A^B;P:fe#`RUfd#3'b,=\PUP\PCP4O5b7b0b8b0b;b:b9b6bEO2WMP:O1%X|P~P}P>PIP^PdPfPiPhPbPmPqPFPrPlPpPtPuQ1MPvQ1OB09ADj'LQ02'h,HwP{P@b<b=b>X1AX2AX3AQ1g1o89'010:8'?^1A^2A^3AP:P\PUffR\O3b7b0b8b0b;b:b9b6bE10kY1o=Y'010k='?PA10M]1o<]Rk'0faRbQ127n`>05H1XPAPBPk%5<Rk1GZRR1#1RH,=<Rh'210]YRi9:k<RfPkPhPkPoPiO1Rh,=<1P;kAK;kke9fkkPoQ1XP<P<%9<PHPhPoPoQ1;P1PiPZP]P0PRPYPcEREQGuEgP=CDPf1TEMRf/I6%1fRc/?gRYQ14Q15Q16PfPc%9cP6Pg%9gM9VPBCDPY%;6%5g%3`R`#;%1`#51TEbRb#;%1b#5PmPqPFPrPlPpPtPuQ1MPvPw208w<Q1h5OwPzPwPwQ01P5P5P3Q1eJ0CPzB09AyjRj9Ewx1ZjD,Hw5OwFWP{P@b<b=b>X1AX2AX3AXB;Q1A9:7:Q1ig01F0[1o87R@#5?:@=[[^1A^2A^3A^B;P:PQPU%`\PVPCPOO6b7b0b8b0b;b:b9b6bEO210M<P:Ezb5W@P:O1n200110200021110111100b_XDsX4ACMF_bIW[WXP9P:O2n2001000000121000000W5WUP9P:O2n2001000000121000000W5WCXKLP9P:O2n2001000000121000000W5P9P:O2n2001000000121000000W5WZWWP9P:O2n2001000000121000000W5WTP9P:O2n2001000000121000000W5WGWJP9P:O2n2001000000121000000W5P9P:O2n2001000000121000000W5P9P:O2n2001000000121000000W5CMO2Q04#320g9:EwQ04#420f9:EwO2P=P7P8Q04H01P=P7P8P9H01P=P7Q0<P:H01'2'^eW^W]XQAWOW`o"). Qed.

(* [comment removed for export] *)
Lemma rd_u64 : forall segs m A (w : word) rest a,
  bytes_at segs m A (le8 w ++ rest) -> a = wa A -> ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_glue ()) [] "h01Rh14__x1h21ah31nh41Ah51Bh61Hh71Lh87__arithh94__ffh:8__varmaph;5__with<4cstrh=1mh>1oh?4resth@4segshA1whB1zp;1p;3p;4p;2p;8p;6p;Bp;<p;7g004Sj1BTg00D4j12Tg00DYj1HTg00E7j1DTg00EZj1JTg01FMj14Tg00F<j36Tg00Hij4YTg00h9j13Tg00VOj31Tg00bEj10Tg01G@j4:Tg01HEj25Tg00SZj28Tg00Oaj2=Tg01HgR0j2;Tg00TVj1\Tg00LeR1j29Tg00LER2j1?Tg00V3R3j2<Tg00\?j27Tg00YQj1VTg00\Yj1UTg00]9j2TTg00]Wj1QTg00^5j1OTg00^`j2ETg00_Cj2NTg013^j4GTg00UQj1MTg016Xj3FTg014mj8LTg00_fj2PTg00`Hj2KTg00a4j3RTg00aSj4STg00gNj4cTg01IAj1bTg00ihj6>Tg01J;j3aTg01JZj8`Tg01KZj3@Tg01L8j3ATg01LWj1^Tg00T:j6]Tg012SlBITg011nl<[Tg014Ij7_Tg0194R4P4P4g01:1R5P5P5g01:OR6P2P2P2P1g01:oR7g01DeR8g019SR9f3R:f2R;f1R<f0R=MBIp=ZP4P4P4P5P5P5P6P2P2P2P1P7f5R7f4R1P:P;P<P=MBIp=XP4P5P0P2P3g01M8P7P1P:P;P<P=M<[p=WP<g01;RR3g01<1R2P2g01<QR0P=g01=XF_p=Cg00;6#Bg01?FR6#2#2#2R>#2#2#2#H#DR?%H>#DR@#J[%B@RAP7P1P:%4;=6@<CY%3191?<P?%37%JARBf8RCf7RDP=%08#0#0#0#0#0#0#0REC:%47RF,5A31X2?P4%41RG,8@RH18@:RI'=1=8ERJ/;=X34P4PE18@1,==,;JX341=EIR4,;J%\>R>,99RK%?IRL,9>RM'<PJPK1759PEP>175>RNCZP4PMPEP>PNPIPL175LEXEW%VI1<9Lg01C9RL#U%BL1T5<%Q5%O5RLP3P2P2P0P51E59R3g01=1RI1N56R6CG,CL%M2P51E5>R29F53PIAF526CG,CLGL1PL0P=P;g01CeRLg01DER0'71K=;=1L0dAR59<CSb9b:b;X151<9=19><,<K[^15P=18@7#?P<O2b8b<CcPH%b1E>A6@G:,8@RHAa@G:E>1;JHPCPDf6RHA6@F1RFP8PEP;P=G`PCPD%?8,9H#3PEC:A@@8F9A@E,5A51BP519D9f:R9f9RF%3=PEC:%4DR1=6@H9@@89A@E,5ARJ51BXB5P=PD%^DE]PFPC%3DPEC:%4H=6@79@@89A@E,5A51BPBPJ%4C,5A91B=X>B15A1,7BP9PF%3CPEC:P=E>b0b0b7P;P=E>W6W5X2?W?XA?X45W=W@o"). Qed.

(* [comment removed for export] *)
Lemma rd_u64s_g : forall segs mm A ws (i : nat) w a,
  bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
  ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
ltac2:(KReplay.run1 (kr_t_Startup_glue ()) [] "p'0h01Hh11Bh24posth31ah41xi001xh51mh63preh74segsh84__x1h94__x2h:3bs1h;3bs2h<1nh=1yh>1Ah?2E1h@2EuhA4HlenhB5Hlen0hC3HluhD4Hlu0hE2HnhF2_HhG7__arithhH4__ffhI8__varmaphJ5__withK4cstrhL5cstr0hM5cstr1hN1ehO1ihP1lhQ2mmhR1whS2wsp;1p;4p;3p;2p;6p;5p;<p;7p;8p;Bg004Sj1JTg00D4j1GTg00DYj1WTg00E7j1TTg00EZj1STg01MZj10Tg00Hij44Tg01NNj3fTg00TVj1_Tg00VOj38j1\Tg00bEj1;Tg01G@j4CTg01FMj17Tg01Nlj4{Tg00d9j3DTg00F<j33Tg00SZj22Tg01OfR0j2KTg00T:j6UTg00LER1j11Tg009GR2j2?Tg00QZj5^Tg01P@j2ITg00LeR3j2HTg01PWR4j2MTg00h9j1LTg01Q4j1]Tg00\?j2RTg00XPj1~Tg00Xnj4}Tg011nl<ZTg00Vij2vTg00WLj3uTg00Wij4XTg00YQj1PTg00V3j2QTg00\Yj1rTg00]9j2qTg00dYj1oTg016:j4kTg00]Wj1jTg00^5j1iTg00_Cj2VTg00^`j2hTg01QZj3lTg016Xj3gTg013^j4mTg014Ij7nTg00_fj2eTg00`Hj2dTg00a4j3pTg00aSj4cTg00gNj4tTg01R=j8bTg01RZj8wTg00ihj6xTg01HEj2aTg012SlB[Tg0139l<`Tf3R5f2R6f1R7f0R8'a38p=>%18,M7,H6#Lp=:g0194R9?878p=Ff4R:A3678785p=61I789896p=N1?78,?6p=AA8567/?8p=@%77=368p=51267=898p=E12561I78589p=<A367893:5p=OP:P51H67P8C4p==g01:1R;?878p=B1R;8p=9P9P9P9P;P;P;g01SXP1P1P1P4g01T8f5R4P:P5P6P7P8MB[p=|P9P;P;P;P1P1P4P:P5P6P7P8M<`p=zP;P;P;P;P;P;P3P8P7P6P3P5P:P4f6R3f7R<f8R=f9R>MB[p=yP9P;P8P1P7P6P5P:P4P3P<P=M<Zp=Y1M78,H6p=sg00;6#JR1g01?FR?#GR@#G#GRA#G#G#G#WRB#TRC%WA#TRD#S[RE%JCRFP3P4P:%05C4%SCAfC:5PCP6C>%_ARA=:3:98C6PCA:<A4%JDRG#SRHf:RIP>P8g01De#;#;#;#;#;#;#;#;RJCCPG%74C>X3CP3P4P:P7C{PFP=ADC3893C712C7RK/F<PG%0=RLPD%07RM%73RN%08RO53DD612DMRP?NJ<3AC@X2F,KFX6F,KFP0PFPFP>ADC<893C71FK=PG%0>RQPDPMA5D<OD6ANPJ=3AC@X2F,KFX6FPHf;RRPIA:>A<PJCCPGPNC>P8PFPRADC>893C71FKIPG%0RRKPDPMA5D>OD6ANPJI3AC@X2F,KFP0PFPFf<R0ADCI893C6AEC6RPG%00RPPD%06RN%7IRI=3DOD6PDPNPJPRC<3AC@X2FPHf?RNf>RSf=RT?:ARPJCCPGPIC>P8PFPSADC0893C:AEC:TPG%0SPD%0:RIA5D0OD6PDPIPJPTC<3AC@P2PFPNPCP4ADCT7D6AEC4SPG%0NR0PD%04ROA5DTMD6PDPOPJPSC<3APHfCRMfBRUfARV?:ANPJCCPG%7SC>P8PFPVPCP<ADCN5D6AEC=VPG%0UPDPLf@RN=5DID6PDPLPJPVC<3AP2AEC>UPG%0MR>PDPQPD%7VPODOPDPQPJPUC<C@PHfGROfFRIfERW?:AMPJCCPG%7UC>P8fDRU9ECRPG%0IRRPDPPPD%7UPLDOPDPPPJPWC<C@P2PG%0ORPPD%0TRTA5DWQD6PDPTPJPIC<PHfKRQfJRLfIRM?:AOPJCCPG%7IC>P8PG%0MRIPDP0A5DOKD6PD%0NRNPJPMC<PG%0QfORKfNRXfMRYP8C4XPGPOPD%0VPD%7MPTDORTP7EUPXPYfLRMPTC4P2P:P5P6A3D78C4P4P:P5P6C4P4P:P512D6#1P7D='?[RTP:P5P6P7C4P:P5P612D7#1P8D='?P4P:P5A3D67C4RV[P3P4P:P5C4P3P4P:12D5#1P6D='?\VP:P5P6P7P8D^P7n2001000000120000000X;GX:GX3;X5EX71PT^;G^:G^3;^5E^71P8fPR1PKPXP>A5DQ0RQP7O6P1PKPXP>C4P1PKPX12D>#1PQD='?P2fQR2P1PK%0URUC4P2P1PK12DU#1A5DMND=PHfRRHP2A:1AXPJCCPG%7YC>P8fSRGPHP2PRC4fTRRPGPH12DP#1A5DK>D=P9fH#0,2DfVRKfUR>PR%18RP%0WRW95D2D=X<9P81IJ2RXP<EUP>PRPG%1XA5D1UD=PKP>1IJHR>#1RK,HRRUP2PW%1HRW,MAR2,HRR1#LRXP8P;PC%]BRBPBP1PUPC\;/RB1B1U1B11P;P;%\;RBP8X4;R<PB1B78#~X=;X4;P1P1%91PUP1P<P<P<P;P;g01AS1H78C}#9X5;X<;PRPR%9RPKP2P<P<%9PX49P>P2PJPA%9APHPW%9WE|RWEzM:yM<Z12DIRI/F>%1IRH/B2RJ%\9R<PB%17/BP1F781v783uX=9X49RPPIPH%9HP>P2PWM9YP=CXPJ12CLRL/FG%1LRJ%1GR='BRWP<PBPPPLPJ%9JPGP=%9=M9YPSCXPW%PRg019SRW%1R'Q12CMRM#P%1M,QW%0Y,2DRD#P%1D,QWg01C9RD#r%JDP;1q;6P7%o;Ck%j;%i;RDg01;Rg01<1RYPYg01<QRYP;1V;?1h;A1V;@5l;5g;R@g01>_P@Cmg01=XFn1eDYP8P6g01CeRYg01DERD'R1d86=8YDdAp;W7CcbHbIbJX8;X9;As8A7RA/BA^8;^9;P8fX#1fZO2bGbMbLbKbBbDCtGb%LU98CXeGwb1W1WFP7P8O2n2001000000121000000b1b0b1WCW@P7P8O2n2001000000121000000W0WAP7P8O2n2001000000121000000W0W?P7P8O2n2001000000121000000W0X2FP7P8O2n2001000000121100000W0X6FP7P8O2n2001000000121100000bNP5P8ExW0WEW1X3CXRCXO9WSX>;WQW7o"). Qed.

(* [comment removed for export] *)
Ltac exact_evt H :=
  lazymatch type of H with evt _ _ ?s1 =>
    lazymatch goal with |- evt _ _ ?s2 =>
      replace s2 with s1; [exact H|];
      cbv delta [mkR]; repeat first [reflexivity | lia | progress f_equal]
    end
  end.

(* [comment removed for export] *)
Ltac ldaux AUXB i :=
  let a := cur_mem_addr in
  let RD := fresh "RD" in
  pose proof (rd_u64s_g _ _ _ _ i _ a AUXB eq_refl ltac:(addr_tac)) as RD;
  zstep; clear RD.

(* [comment removed for export] *)
Ltac join2 H1 H2 :=
  lazymatch type of H2 with rw_cells ?segs ?mm ?A2 ?cs2 =>
  lazymatch type of H1 with rw_cells _ _ ?A ?cs1 =>
    let H := fresh "J" in
    assert (H : rw_cells segs mm A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app segs mm A cs1 cs2)); split;
            [ exact H1
            | replace (A + Z.of_nat (cells_size cs1))%Z with A2 by (simpl; lia); exact H2 ]);
    clear H1 H2; cbn [app] in H; rename H into H1
  end end.

(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
