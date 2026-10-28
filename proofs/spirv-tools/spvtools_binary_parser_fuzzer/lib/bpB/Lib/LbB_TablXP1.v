(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablPT1 LbB_TablPT2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_TablXP1 () := "C47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1c6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablXP15rroleC46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalI47Corelib5Lists7ListDef6Forall00C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:Forall_appI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init9Datatypes3fstC4ARocqVerifyHarness?AgentSubmission8PropExec4getrC47Corelib4Init9Datatypes3sndC45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablXP13RPlI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2eq01K47Corelib5Lists7ListDef6Forall02K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C6ARocqVerifyHarness?AgentSubmission3bpB3Lib7LbB_RGl7kept_inC46Stdlib5Lists4List2InC47Corelib7Program6Basics4implC47Corelib7Classes9Morphisms5flip2C46Stdlib5Lists4List=Forall_forallC47Corelib7Classes9MorphismsDiff_impl_subrelationC47Corelib7Classes9MorphismsIiff_flip_impl_subrelation".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AT_EXPAND : Z := 0xfef88.
Definition XP_SM_RET : Z := 0xfeffc.
Definition XP_HDR : Z := 0xff0d0.
Definition XP_DISP : Z := 0xff0dc.
Definition XP_ONE : Z := 0xffaf8.
Definition XP_EXIT : Z := 0xffafc.
Definition XP_RET : Z := 0xffc28.

Definition XP_STACK : Z := 192 + AFS_STACK + 2 * AINTRIN_STACK + 2 * V4_STACK.

Record xgeo : Type := XG { g_SP : Z; g_S1 : Z; g_ff : Z; g_v : Z; g_b : Z; g_e : Z; g_c : Z }.
Definition g_end (g : xgeo) (e' : Z) : xgeo := XG (g_SP g) (g_S1 g) (g_ff g) (g_v g) (g_b g) e' (g_c g).

Definition xg_ok (g : xgeo) : Prop :=
  let SP := g_SP g in let S1 := g_S1 g in let ff := g_ff g in let v := g_v g in let b := g_b g in let e := g_e g in let c := g_c g in
     S1 mod 32 = 0 /\ 2 ^ 45 <= S1 /\ S1 + 160 <= SP /\ SP <= 2 ^ 47
  /\ ff mod 64 = 0 /\ 0x6f1000 <= ff /\ ff + 256 <= S1 /\ (ff + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
  /\ v mod 8 = 0 /\ 0x6e8000 <= v /\ (v + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= v) /\ v + 24 <= 2 ^ 47
  /\ (v + 24 <= S1 \/ SP <= v) /\ (v + 24 <= ff \/ ff + 256 <= v)
  /\ 0 <= b /\ b <= e /\ e <= c /\ c <= S1 /\ e mod 4 = 0 /\ (b = 0 -> c = 0)
  /\ (b <> 0 -> 16 <= b /\ b mod 8 = 0 /\ (c <= 0x7fff7000 \/ 0x10007fff8000 <= b) /\ (v + 24 <= b \/ c <= v)
                /\ (ff + 256 <= b \/ c <= ff)).

Definition rrole : Type := (bv 5 * Z)%type.
Definition RPl (l : list rrole) (R : bvmap 5 word) : Prop := Forall (fun rz : rrole => getr R (fst rz) = Z_to_bv 64 (snd rz)) l.

Definition xcommon (g : xgeo) : list rrole :=
  [(2%bv, g_S1 g); (8%bv, g_SP g); (9%bv, g_S1 g); (25%bv, sh (g_ff g)); (26%bv, g_ff g); (27%bv, 0x7fff8000)].

Lemma RPl_app : forall l1 l2 R, RPl (l1 ++ l2) R <-> RPl l1 R /\ RPl l2 R.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablXP1 ()) [] "h01Rh12l1h22l2h32rzp;1p;2p;3p;4p-1R0p10000p4p710p9P0p1000\R1p4p710p9P0P1p4p7210p9P0P1p4p73110p9P0p1001:p4p710p9g0022R0p4p70R1p10030p4p710p8P1p1003Gp4p710p8P1p1003cp4p710p8P1p1004Ap4p7210p8P1p1004^p4p710p8P1p1005?p4p710p8P1g005]R2p4p710p8P1g006:R1p4p710p8g006Yj1?Tg0079j10Tg007^j18Tg008Cj12Tg008aj13Tg009Dj2<Tg00:0j3;Tg00:Mj27Tg00;?j35Tg00;\j26Tg00<Bj34TP1j49TP2j3:Tg00<\j21Tg00=Xj2>Tg00>3j2=T%?0R2g00>L#0R1#8#2R3%01#0#0#0#0#2R1#3R4'<P0f1R5%33R3g00?1R6f0R73;'7A5367,61544X30f2R4P5C9A:045/1711471157'>'=eW0X22W1o"). Qed.
Lemma RPl_cons : forall r z l R, RPl ((r, z) :: l) R <-> getr R r = Z_to_bv 64 z /\ RPl l R.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablXP1 ()) [] "p'0h01Hh12rzh22H0h32H1h41eh51li001lh62H2h71ri011rh81Ah91Bh:1Rh;1Xh<2l0h=1xi021xh>1zp;1p;2p;3p;6p;4g0079j17Tg007^j1MTg008Cj1@Tg008aj1;Tg00?Oj2LTg006YR0j1BTg009Dj2HTg00:0j38Tg00;?j39Tg00;\j2:Tg00?oj34Tg00=XR1j26Tg00<Bj31Tg00@Oj1KTg003Gj6JTg00@oj2GTg004Aj6?Tg00ANj4<Tg005?j6>Tg00Aij2FTg00BCj6ETg00<\j2=Tg00>3j2DTg00:Mj2ATg00Bdj4CTg004^R2j3ITf3R3f2R4f1R5'Af0R631p=3P4g00?1R7P5P6CCp=0g0022R8?I56p=2f4R91A341:5631p=5g00>L#7R:#M#@R;#;R<1L<7R=#B%7:#7#7#7#7#@R:#;R>,H;P>P5A8<76R;A9<76,::R?C3X18R@A0<34=4=5RA'2RBP>P5P9P:P3D5RCP>P4P;P?C3X18RD/24RE'6[P>P6P3P:P4D5RF12@5'6R@A0<93=4=4RG,2D[P2P8PD%B8RDf6R2f5RH50<=4=9RI715P>P9f7RJP:P2D5P>PHP;P?C3X18/2HRK'6RL[P6%K8RM=1DGA0<H9=4=3RN91DMPDPMP0P8p-0P6g00CDg00C`RMn10110000020020000000X4Dg00D=PIP6EJPM1GL6b2W0P6O1W0P>PJA8<75RLA9<75,::RMC3P>f9RIP;P?C3X18/25A4834f<ROf;RP50<f:RQ54=51DA4893f=RR=0<O=4=P51DPDPDP0P8PDP6PHP6n10110000020020101100X4DA48H9f>RS=0<R=4=OP6E?A1D9OPDP8P0P8P8P6PJP5n10110000020020101100X4DA482Hf?R0=0<SRS=4=RP5E?A182Sf@RS=0<0918JP6f8R0fARR=0<S518P8fBRO=0<RA1DIRRTP>PRPLPMC3P>fCRMP;P?C3X18RL/2PP>PMfFRPP:fERUD5RVP>fDRWP;P?C3X18RX/2WRY'6]2]0[X78A1D0SP6PTPDPOP>POA0<UWRO98<7P:A9<7OD512X5P>PWfGP:PPD5P>PUP;P?C3X18/2U'6]2]0X5DP>PRA0<WMRW98<7P:A9<7WD512LMPVPYP5P6C<W6W3PQP6E>b6W2PIP6E>b2W0P6O1b0P6O1b0W3P6P4P5O3W3W2W0X<DX=8P3P4P5P6O4n200210000000020041102100000000A1D6NP>P3P2P:PHD5RHP>P9P;P?C3X18/29'6[X5DPGO1P61FDNO1b0X;BP1PCPEP>P3P;P?C3X18/2NP6P=P>P2P;P?C3X18A0<0JP2P5P6EEX9KX8HP5P6O2n2001000000120000000X0@C<1=A61=56,6F'DeW:W5X>7W7o"). Qed.

Lemma RPl_kept : forall l ks R R', RPl l R -> kept_in ks R R' -> Forall (fun rz : rrole => In (fst rz) ks) l -> RPl l R'.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablXP1 ()) [] "h02rzh11xh25lemmah31Fh41Ph53Hrzh61Kh71Rh82R'h91bh:2ksh;1lh<1yp;1p;2p;3p;7p;6g006Yj1<Tg0079j13Tg007^j1@Tg008Cj17Tg008aj1>Tg009Dj2ETg00<\j29Tg00DYj3?Tg00:0j38Tg00EUj30Tg00:Mj22Tg00;?j3:Tg00;\j2=Tg00<Bj34Tg00>3R0j25Tg00Elj2DTg00FJj7CTg00Flj36Tg00GNj3;Tg005?j6ATg004^j3BTg0022R1f1R2f0R33Bp=1%<1g00>L#3R4#@#7R5#>R6#<%34#3#3#3#3#7R4#>R7,E5R5f3R8/92f2R9=?82g00?1R:=863R;f5R<506X01/1<f4/2;A:6:3,=4R=547X01R>f6R?'1f7R@9013RA12?;=47=X01RBP2O1[^11'5p-0RCP01D32X<CX1Cg00H?12<;=47=X01RC/1@f8R09013RD12@;=47=X01P2O1RE[^11P3FCW2A61>?11C?PE\A^11RA'511B@120;=47=X01P2O1\D^11;;3W2A61C?P9O2PAA06;@X01RA/1@f9RC906;X01P2O1\D^11RD'5A06;0X01/10A013CRCf:906;X01P2O1[^11;;3W2A61A@P2O2PDP7A86:2RD,20A:6:9,=49473X97P8P2P3O212@DP<PDP9P2P3O2O2EAX5CX01b3b4O219?8eW3W6W4X85W7W:W;o"). Qed.

Record xsite : Type := XS {
  xs_pc : Z;
  xs_nx : Z;
  xs_c : v4_consts;
  xs_sra : Z;
  xs_ara : Z;
  xs_lit : Z;
  xs_src : Z;
  xs_tk : Z;
  xs_pk : Z;
  xs_fk : Z;
  xs_sv : bool;
  xs_setslots : bool;
  xs_rin : xgeo -> list rrole;
  xs_rmid : xgeo -> list rrole;
  xs_rmid' : xgeo -> list rrole;
  xs_rout : xgeo -> Z -> list rrole }.

Definition rinK (g : xgeo) : list rrole := [(18%bv, g_ff g); (19%bv, g_v g); (20%bv, g_ff g + 32)].

Definition rmidKA (g : xgeo) : list rrole :=
  [(18%bv, sh (g_v g + 16)); (19%bv, g_v g); (20%bv, g_ff g + 32); (21%bv, sh (g_v g + 8)); (22%bv, g_e g + 4); (23%bv, g_v g + 16); (24%bv, g_e g)].
Definition rmidKA' (g : xgeo) : list rrole := [(18%bv, sh (g_v g + 16)); (19%bv, g_v g); (21%bv, sh (g_v g + 8)); (23%bv, g_v g + 16)].
Definition routKA (tmp : Z) (g : xgeo) (e' : Z) : list rrole :=
  [(18%bv, sh (g_v g + 16)); (19%bv, g_v g); (21%bv, sh (g_v g + 8)); (22%bv, e'); (23%bv, g_v g + 16); (24%bv, g_ff g + tmp)].

Definition rmidKB (g : xgeo) : list rrole :=
  [(18%bv, g_ff g); (19%bv, g_v g); (20%bv, g_ff g + 32); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16); (23%bv, g_e g + 4); (24%bv, g_e g)].
Definition rmidKB' (g : xgeo) : list rrole := [(18%bv, g_ff g); (19%bv, g_v g); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16)].
Definition routKB (tmp : Z) (g : xgeo) (e' : Z) : list rrole :=
  [(18%bv, g_ff g); (19%bv, g_v g); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16); (23%bv, e'); (24%bv, g_ff g + tmp)].

Definition K1 : xsite := XS 0xff0f8 0xff6dc VOT_SLOW_CREF 0xff6b0 0xff17c 106 32 0 0 0 true true rinK rmidKA rmidKA' (routKA 144).
Definition K2 : xsite := XS 0xff1b4 0xff79c VOT_SLOW_CREF 0xff770 0xff238 53 32 0 0 0 true true rinK rmidKA rmidKA' (routKA 64).
Definition K5 : xsite := XS 0xff3b8 0xff61c VOT_SLOW_CREF 0xff5f0 0xff43c 52 32 0 0 0 true true rinK rmidKA rmidKA' (routKA 48).
Definition K3 : xsite := XS 0xff260 0xff4a0 VOT_SLOW_CREF 0xff470 0xff2e4 54 32 0 0 0 false true rinK rmidKB rmidKB' (routKB 80).
Definition K4 : xsite := XS 0xff30c 0xff560 VOT_SLOW_CREF 0xff530 0xff390 55 32 0 0 0 false true rinK rmidKB rmidKB' (routKB 112).

Definition rmidLa (tmp : Z) (g : xgeo) : list rrole := [(18%bv, g_ff g); (20%bv, g_e g + 4); (21%bv, sh (g_v g + 8)); (22%bv, g_e g); (24%bv, g_ff g + tmp)].
Definition rmidLa' (g : xgeo) : list rrole := [(18%bv, g_ff g); (21%bv, sh (g_v g + 8))].
Definition routF (g : xgeo) (e' : Z) : list rrole := [(18%bv, g_ff g)].
Definition L1 : xsite := XS 0xff6dc XP_ONE VOT_SLOW_RREF 0xffa00 0xff73c 105 144 18 0 18 true false (fun g => routKA 144 g (g_e g)) (rmidLa 144) rmidLa' routF.
Definition L2 : xsite := XS 0xff61c XP_ONE VOT_SLOW_RREF 0xff9c0 0xff67c 42 48 6 0 6 true false (fun g => routKA 48 g (g_e g)) (rmidLa 48) rmidLa' routF.
Definition L3 : xsite := XS 0xff79c XP_ONE VOT_SLOW_RREF 0xffa40 0xff7fc 45 64 8 0 8 true false (fun g => routKA 64 g (g_e g)) (rmidLa 64) rmidLa' routF.

Definition rmidLb (tmp : Z) (g : xgeo) : list rrole :=
  [(18%bv, g_ff g); (19%bv, g_v g); (20%bv, g_e g + 4); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16); (23%bv, g_e g); (24%bv, g_ff g + tmp)].
Definition rmidLb' (g : xgeo) : list rrole := [(18%bv, g_ff g); (19%bv, g_v g); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16)].
Definition routLb (tmp' : Z) (g : xgeo) (e' : Z) : list rrole :=
  [(18%bv, g_ff g); (19%bv, g_v g); (20%bv, e'); (21%bv, sh (g_v g + 16)); (22%bv, g_v g + 16); (23%bv, g_ff g + tmp')].
Definition L4 : xsite := XS 0xff4a0 0xff860 VOT_SLOW_RREF 0xff830 0xff4fc 1 80 10 0 0 false false (fun g => routKB 80 g (g_e g)) (rmidLb 80) rmidLb' (routLb 96).
Definition L6 : xsite := XS 0xff560 0xff928 VOT_SLOW_RREF 0xff8f8 0xff5bc 6 112 14 0 0 false false (fun g => routKB 112 g (g_e g)) (rmidLb 112) rmidLb' (routLb 128).

Definition rmidLc (tmp : Z) (g : xgeo) : list rrole := [(18%bv, g_ff g); (20%bv, g_e g); (22%bv, g_e g + 4); (23%bv, g_ff g + tmp)].
Definition rmidLc' (g : xgeo) : list rrole := [(18%bv, g_ff g)].
Definition L5 : xsite := XS 0xff860 XP_ONE VOT_SLOW_RREF 0xffa80 0xff8c4 47 96 12 10 12 false false (fun g => routLb 96 g (g_e g)) (rmidLc 96) rmidLc' routF.
Definition L7 : xsite := XS 0xff928 XP_ONE VOT_SLOW_RREF 0xffac4 0xff98c 42 128 16 14 16 false false (fun g => routLb 128 g (g_e g)) (rmidLc 128) rmidLc' routF.

Definition xp_chain (t : Z) : list xsite :=
  if t =? 106 then [K1; L1] else if t =? 52 then [K5; L2] else if t =? 53 then [K2; L3]
  else if t =? 54 then [K3; L4; L5] else if t =? 55 then [K4; L6; L7] else [].

Section Runs.
  Context {HCEIL : HeapCeil}.

  Definition xslotc (sv : bool) (g : xgeo) (m : mem) : Prop :=
    if sv then rw_cells asegs m (g_S1 g + 16) [C8 (Z_to_bv 64 (g_v g + 8)); C8 (Z_to_bv 64 (g_ff g))]
    else rw_cells asegs m (g_S1 g + 16) [C8 (Z_to_bv 64 (sh (g_v g + 8))); C8 (Z_to_bv 64 (g_v g + 8))].

  Definition fkw (g : xgeo) (k : Z) : list (Z * Z) := if k =? 0 then [] else [(sh (g_ff g) + k, sh (g_ff g) + k + 1)].
  Definition fkc (g : xgeo) (k v : Z) (m : mem) : Prop := k <> 0 -> rw_cells asegs m (sh (g_ff g) + k) [C1 (b8 v)].

  Definition xwa (s : xsite) (g : xgeo) : list (Z * Z) :=
    (if xs_setslots s then [(g_S1 g + 16, g_S1 g + 32)] else [(g_ff g + xs_src s, g_ff g + xs_src s + 4)])
    ++ fkw g (xs_pk s) ++ fkw g (xs_tk s).

  Definition xrun_a (s : xsite) : Prop :=
    forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (g : xgeo),
      RPl (xcommon g ++ xs_rin s g) R -> xg_ok g ->
      fldA m (g_v g) 8 (g_b g) -> fldA m (g_v g + 8) 8 (g_e g) -> fldA m (g_v g + 16) 8 (g_c g) -> gz m (g_v g) 24 ->
      wr_at asegs m (g_S1 g + 16) 16 -> (xs_setslots s = false -> xslotc (xs_sv s) g m) ->
      wr_at asegs m (sh (g_ff g)) 32 -> wr_at asegs m (g_ff g + 32) 128 ->
      exists R' M' pc',
        CatSim.msteps asegs (MS R F (Z_to_bv 64 (xs_pc s)) fc None m ro) (MS R' F (Z_to_bv 64 pc') fc None M' ro)
        /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4
        /\ munch (xwa s g) m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
        /\ (mem_inv asegs m -> mem_inv asegs M')
        /\ xslotc (xs_sv s) g M'
        /\ (xs_setslots s = false -> rw_cells asegs M' (g_ff g + xs_src s) [C4 (Z_to_bv 64 (xs_lit s))])
        /\ fkc g (xs_tk s) 4 M' /\ fkc g (xs_pk s) 0xf8 M'
        /\ (if g_e g <? g_c g
            then pc' = AANNOTATE_CC /\ getr R' 1 = Z_to_bv 64 (xs_ara s)
                 /\ getr R' 10 = Z_to_bv 64 (g_b g) /\ getr R' 11 = Z_to_bv 64 (g_c g)
                 /\ getr R' 12 = Z_to_bv 64 (g_e g) /\ getr R' 13 = Z_to_bv 64 (g_e g + 4)
                 /\ RPl (xcommon g ++ xs_rmid s g) R'
            else pc' = v4_entry (xs_c s) /\ getr R' 1 = Z_to_bv 64 (xs_sra s)
                 /\ getr R' 10 = Z_to_bv 64 (g_v g) /\ getr R' 11 = Z_to_bv 64 (g_ff g + xs_src s)
                 /\ RPl (xcommon g ++ xs_rmid' s g) R').

  Definition xrun_b (s : xsite) : Prop :=
    forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (g : xgeo) (j : Z),
      RPl (xcommon g ++ xs_rmid s g) R -> xg_ok g -> g_e g < g_c g ->
      rw_cells asegs m (g_ff g + xs_src s) [C4 (Z_to_bv 64 (xs_lit s))] ->
      LbB_Kit.shk m (g_e g) j -> (j = 0 \/ ((g_e g) mod 8 = 0 /\ 4 <= j < 8)) ->
      xslotc (xs_sv s) g m -> sh0 m (g_v g + 8) ->
      wr_at asegs m (g_e g) 4 -> wr_at asegs m (g_v g + 8) 8 -> wr_at asegs m (sh (g_ff g)) 32 ->
      exists R' M',
        CatSim.msteps asegs (MS R F (Z_to_bv 64 (xs_ara s)) fc None m ro) (MS R' F (Z_to_bv 64 (xs_nx s)) fc None M' ro)
        /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4
        /\ munch ([(g_e g, g_e g + 4); (g_v g + 8, g_v g + 16)] ++ fkw g (xs_fk s)) m M' /\ wmono asegs m M'
        /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi) /\ (mem_inv asegs m -> mem_inv asegs M')
        /\ rw_cells asegs M' (g_e g) [C4 (Z_to_bv 64 (xs_lit s))] /\ rw_cells asegs M' (g_v g + 8) [C8 (Z_to_bv 64 (g_e g + 4))]
        /\ fkc g (xs_fk s) 0xf8 M'
        /\ RPl (xcommon g ++ xs_rout s g (g_e g + 4)) R'.

  Definition xrun_c (s : xsite) : Prop :=
    forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (g : xgeo) (E : Z),
      RPl (xcommon g ++ xs_rmid' s g) R -> getr R 10 = Z_to_bv 64 E -> xg_ok g -> 0 <= E <= 2 ^ 47 -> 5 <= E -> E mod 4 = 0 ->
      xslotc (xs_sv s) g m -> sh0 m (g_v g + 8) ->
      wr_at asegs m (g_v g + 8) 8 -> wr_at asegs m (sh (g_ff g)) 32 ->
      exists R' M',
        CatSim.msteps asegs (MS R F (Z_to_bv 64 (xs_sra s)) fc None m ro) (MS R' F (Z_to_bv 64 (xs_nx s)) fc None M' ro)
        /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4
        /\ munch ([(g_v g + 8, g_v g + 16)] ++ fkw g (xs_fk s)) m M' /\ wmono asegs m M'
        /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi) /\ (mem_inv asegs m -> mem_inv asegs M')
        /\ rw_cells asegs M' (g_v g + 8) [C8 (Z_to_bv 64 E)]
        /\ fkc g (xs_fk s) 0xf8 M'
        /\ RPl (xcommon g ++ xs_rout s g E) R'.

  Definition site_runs (s : xsite) : Prop := xrun_a s /\ xrun_b s /\ xrun_c s.
End Runs.
