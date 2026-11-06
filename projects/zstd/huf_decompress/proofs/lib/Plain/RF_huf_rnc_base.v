(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg RF_huf_tbl_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rnc_base () := "C46Stdlib5Lists4List=nth_error_mapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib5Plain?RF_huf_rnc_base5c_BUFC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvc59OSSVerify5KrLib5Plain?RF_huf_rnc_base5c_bufC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib5Lists7ListDef6Forall00c59OSSVerify5KrLib5Plain?RF_huf_rnc_base6c_msv0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3addc59OSSVerify5KrLib5Plain?RF_huf_rnc_base5c_rt0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain?RF_huf_rnc_base4c_SPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib5Plain?RF_huf_rnc_base4c_loC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subc59OSSVerify5KrLib5Plain?RF_huf_rnc_base4c_NCC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib5Plain?RF_huf_rnc_base6c_MSVPC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain?RF_huf_rnc_base5c_TLPC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes3nat02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC59OSSVerify5KrLib4Spec9FseNCount4ZnthC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init5Peano2ltK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3nthC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC46Stdlib5Lists4List>nth_error_nth'C46Stdlib9micromega;ZifyClasses7rew_iffC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic5proj1K47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain?RF_huf_rnc_base8RD_STACKC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec9FseLemmas9all_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9FseLemmas@Forall_all_bytesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Record rdctx : Type := mkRD {
  c_ra : word; c_gp : word; c_tp : word;
  c_s0 : word; c_s1 : word; c_s2 : word; c_s3 : word; c_s4 : word; c_s5 : word; c_s6 : word;
  c_s7 : word; c_s8 : word; c_s9 : word; c_s10 : word; c_s11 : word;
  c_F : bvmap 5 word; c_fc : bv 32;
  c_m : fmem;                               (* [comment removed for export] *)
  c_SP : Z; c_NC : Z; c_MSVP : Z; c_TLP : Z; c_BUF : Z; c_lo : Z;
  c_rt0 : list Z; c_buf : list Z; c_msv0 : Z
}.

Definition RD_STACK : Z := 112.

Definition rd_W (C : rdctx) : list (Z * Z) :=
  [(c_NC C, c_NC C + 2 * zlen (c_rt0 C)); (c_MSVP C, c_MSVP C + 4); (c_TLP C, c_TLP C + 4); (c_SP C - RD_STACK, c_SP C)].

(* [comment removed for export] *)
Definition rd_ok (C : rdctx) : Prop :=
  8 <= zlen (c_buf C) <= 65536 /\ Forall (fun c => 0 <= c < 256) (c_buf C)
  /\ 0 <= c_msv0 C <= 255 /\ c_msv0 C + 1 <= zlen (c_rt0 C)
  /\ 0 <= c_SP C < 2^64 /\ c_lo C <= c_SP C - RD_STACK /\ 0 <= c_lo C
  /\ (0 <= c_NC C /\ c_NC C + 2 * zlen (c_rt0 C) <= 2^64) /\ (0 <= c_BUF C /\ c_BUF C + zlen (c_buf C) + 8 <= 2^64)
  /\ (0 <= c_MSVP C /\ c_MSVP C + 4 <= 2^64) /\ (0 <= c_TLP C /\ c_TLP C + 4 <= 2^64)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_lo C \/ c_SP C <= c_NC C)      (* [comment removed for export] *)
  /\ (c_MSVP C + 4 <= c_lo C \/ c_SP C <= c_MSVP C)
  /\ (c_TLP C + 4 <= c_lo C \/ c_SP C <= c_TLP C)
  /\ (c_BUF C + zlen (c_buf C) <= c_lo C \/ c_SP C <= c_BUF C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_MSVP C \/ c_MSVP C + 4 <= c_NC C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_TLP C \/ c_TLP C + 4 <= c_NC C)
  /\ (c_NC C + 2 * zlen (c_rt0 C) <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_NC C)
  /\ (c_MSVP C + 4 <= c_TLP C \/ c_TLP C + 4 <= c_MSVP C)
  /\ (c_MSVP C + 4 <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_MSVP C)
  /\ (c_TLP C + 4 <= c_BUF C \/ c_BUF C + zlen (c_buf C) <= c_TLP C).

(* [comment removed for export] *)
Definition rd_inv (C : rdctx) (m1 : fmem) (nc : list Z) (msvw tlw : word) : Prop :=
  u8arr psegs m1 (c_NC C) (u16s (map (Z_to_bv 64) nc)) /\ length nc = length (c_rt0 C)
  /\ bytes_at psegs m1 (c_BUF C) (map (Z_to_bv 8) (c_buf C))
  /\ rw_cells psegs m1 (c_MSVP C) [C4 msvw]
  /\ rw_cells psegs m1 (c_TLP C) [C4 tlw]
  /\ (exists junk8, rw_cells psegs m1 (c_SP C + -112)
        [CB 8 junk8; C8 (c_s11 C); C8 (c_s10 C); C8 (c_s9 C); C8 (c_s8 C); C8 (c_s7 C); C8 (c_s6 C); C8 (c_s5 C);
         C8 (c_s4 C); C8 (c_s3 C); C8 (c_s2 C); C8 (c_s1 C); C8 (c_s0 C); C8 (c_ra C)])
  /\ stk psegs m1 (c_lo C) (c_SP C + -112)
  /\ munch (rd_W C) (c_m C) m1 /\ wmono psegs (c_m C) m1 /\ mem_inv psegs m1.

(* [comment removed for export] *)
Definition rd_body_post (C : rdctx) (rt : list Z) (msv tl n : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (c_ra C) (Z_to_bv 64 (c_SP C)) (c_gp C) (c_tp C) t0 t1 t2 (c_s0 C) (c_s1 C) (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                 (c_s2 C) (c_s3 C) (c_s4 C) (c_s5 C) (c_s6 C) (c_s7 C) (c_s8 C) (c_s9 C) (c_s10 C) (c_s11 C) t3 t4 t5 t6)
             (c_F C) (ret_pc (c_ra C)) (c_fc C) None m' (seg_rom psegs)
    /\ munch (rd_W C) (c_m C) m'
    /\ wmono psegs (c_m C) m' /\ mem_inv psegs m'
    /\ stk psegs m' (c_lo C) (c_SP C)
    /\ u8arr psegs m' (c_NC C) (u16s (map (Z_to_bv 64) rt))
    /\ rw_cells psegs m' (c_MSVP C) [C4 (Z_to_bv 64 msv)]
    /\ rw_cells psegs m' (c_TLP C) [C4 (Z_to_bv 64 tl)].

(* [comment removed for export] *)
Definition rd_lst (C : rdctx) (pc : Z) (m1 : fmem) (x1 x12 x14 x20 x22 x23 x24 x25 x26 x27 x30 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 (c_SP C + -112)) (c_gp C) (c_tp C)
          (Z_to_bv 64 (c_BUF C + zlen (c_buf C) + -7)) (Z_to_bv 64 (c_BUF C + zlen (c_buf C) + -4)) (Z_to_bv 64 1431655765)
          (Z_to_bv 64 (c_MSVP C)) (Z_to_bv 64 (c_BUF C)) (Z_to_bv 64 32) (Z_to_bv 64 1) x12 (Z_to_bv 64 2) x14
          (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 24) (Z_to_bv 64 23)
          (Z_to_bv 64 (c_NC C)) (Z_to_bv 64 125613361) x20 (Z_to_bv 64 (c_msv0 C + 1)) x22 x23 x24 x25 x26 x27
          (Z_to_bv 64 858993459) (Z_to_bv 64 252645135) x30 (Z_to_bv 64 16843009))
     (c_F C) (Z_to_bv 64 pc) (c_fc C) None m1 (seg_rom psegs).

(* [comment removed for export] *)
Definition rd_head (C : rdctx) (s : rstate) (m1 : fmem) (x1 x25 x26 x27 : word) : machine_state :=
  rd_lst C (if r_previous0 s then 0x1b260 else 0x1b258) m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s))
         (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_charnum s))
         (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x25 x26 x27 (Z_to_bv 64 (r_nbBits s)).

(* [comment removed for export] *)
Definition rd_cnt (C : rdctx) (s : rstate) (m1 : fmem) (x1 x23 x26 x27 : word) : machine_state :=
  rd_lst C 0x1b36c m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s))
         (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) x23
         (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) (Z_to_bv 64 (r_charnum s)) x26 x27 (Z_to_bv 64 (r_nbBits s)).

(* [comment removed for export] *)
Definition rd_exit (C : rdctx) (s : rstate) (m1 : fmem) (x1 x20 x23 x24 x26 x27 x30 : word) : machine_state :=
  rd_lst C 0x1b4ec m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (c_BUF C + r_ip s)) x20 (Z_to_bv 64 (r_bitCount s)) x23 x24
         (Z_to_bv 64 (r_charnum s)) x26 x27 x30.

(* [comment removed for export] *)
Definition rd_brk_ok (C : rdctx) (s : rstate) : Prop :=
  0 <= r_remaining s < 2^31 /\ 0 <= r_bitCount s < 2^31 /\ 0 <= r_charnum s < 2^31 /\ 0 <= r_ip s /\ r_ip s + 4 <= zlen (c_buf C).

Section Base.
  Variable C : rdctx.
  Hypothesis OK : rd_ok C.

  (* [comment removed for export] *)
  Lemma buf_rd : forall m1 i, bytes_at psegs m1 (c_BUF C) (map (Z_to_bv 8) (c_buf C)) -> 0 <= i < zlen (c_buf C) ->
    ov_read_bytes psegs m1 (Z_to_bv 64 (c_BUF C + i)) 1 = Some [Z_to_bv 8 (Znth i (c_buf C))] /\ 0 <= Znth i (c_buf C) < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rnc_base ()) ["Base"] "h04__p1h14__x1h21xh32H2h47__arithh54__ffh64__p2h78__varmaph85__with94__x2h:4__x3h;4cstrh<1oh=2z2h>2FBh?1Hh@2HBhA2HihB1LhC2L0hD2_HhE3_H0hF1chG1ihH2m1hI1rp&0p;1p;4p;2p;3p;7p;5p;6p;;p;<p;8g0000R0p4p7210g000RR1p4p710p8g0010j1?Tg001Uj1XTg0023j1VTg002Vj1RTg0038k10@Tg0048k10<j25Tg004^j1sTg005^j4mTg006:j4iTg006oj2UTg007OR2j1STg007oj18Tg008Mj20Tg008iR3j21Tg009Dk30>Tg009ek10=Tg00:fj19Tg00;Kj24Tg00;hj1rTg00<hj1oTg00=gj2nTg00>DR4j22Tg00>`j1kTg00?_j2jTg00@<j1hTg00A;j2gTg00AXj1fTg00BYj1eTg00CYj1TTg00D9j1ITg00DXj4ETg00E]j2KTg00FUj1aTg00G5j3<Tg00GUj2:Tg00H7j33Tg00HQR5j1PTg00I1R6j2`Tg00IIj2@Tg00Ick10?Tg00JHj2]Tg00Jjj2DTg00KDj2FTg00Kmj3GTg00LVj2\Tg00MBj2JTg00M`k40;Tg00N>k10:Tg00N\j1zTg00OGj2LTg00Ojj4=Tg00PUj2yTg00Q8j7qTg00Q\j1pTg00R>j2tTg00R`j2uTg00SLj3vTg00Skj4wTg00T]j4xTg00UHj4WTg00Udj3YTg00VBj4ZTg00Vfj5lTP1j6[TP0j5{Tg00WIj4|Tg00X0j1}Tg00X_l;~Tg00YUk300Tg00Ylk301Tg00ZNk502Tg00Zik603Tg00[Dk404Tg00[_k205Tg00\<m<06Tg00\am<07Tg00]Fk608Tg00]jk709Tg00^Nj7dTg00_2j8cTf0R0#?#?p=Cg00_VR1/00p=Bf2R7f1R8/20'1p=Q1018/10p=71078/D0p=bf4R9f3R:'01078'D/10p=61180,17p=;20510p=Ag00`4R;g00`RR<P;P;P5P9P2P:g00a1P7P8P0N<06p=_P<P;P6P2P4g00a^f5R4P9P:P7P8P0N<07p=^A3;01p=OP8g00b@R2g00b_R6P6g00c?R<P0J08p=NP8P2P6P6P<P0g00c_K09p=>P7P2P6P6P<P8P0Fdp=HP:P2P6P6P<P7P8P0Gcp=Mg00d?R5#?R=#?R>#?R?#?#CR@#XRA#VRB%X?RC#VRD#RRE[g00ddRFP8p,1CRG$0@RHP;PD&0<CRI%sGRJCmRKCi%B8RL1U;JRM#SRN7Q8p,2OK%8?R?/0N%C@RO#C#C#C#C#8,0N'1RP%B0RQ%8ORO7Q0XF;RR>0>;JRS&0=GRT%95RU#9#9#9#9#9#9#8,0T'7%85,4T%rG,U;#SRT'0%oGRV%8=RW%8@'nR@,2V'7%kGRXg00eY,jV'0%hGRY1gWT,4YRW/0@'714HNRT/4?/0@,7H%fGR?%8>R>,4?RZ/0@'7%eGRG14G>R>/0@'7PWPXPVPYPZPXPVP?P>PXPVPGPTPXPVPHPWP?PZPYPWPGP>PYPWPHPTPYPZPGP>P?PZPHPTP?10TG9b>HD6D6D6D6D6D6D6D6D63;3;,7X3;3;RX'1R>'1P3PPP>%TDRG#RRTPFP414H9,5Ag00f\R?#IRZCE1K9JRY,5C%aDRW5<D,:G33%BY12YO3;P0P3PSPXPFf9f8R3,4H,5APZCE1K3JR3,5C=<DW,:G53T%B3123O3;P0f;R3#PRY/`MRV%A3R@/2NPYP@P0X2;R@%A0X2;RYP3P31@;3D_PMPN1@;NR[E^&0?MR\%BNR]f<R^,]1121^%A^R_=3;^'110^1%O_'1'Df=R`#AP;p-0Rag00g;Rb%IZRc#I,F;Rd1F;c1F;Z1F;?5G;R?5G;5G;g00ggRc'\AG;d?/\c%abRc5<b3<%TbRbP;1J;7P81J;:H0;&0:;R?%z;RdPdP2P6P6P<1Nd4P;1L;5R5g00hSR41L;URUC=,>d5Hdf6,NdP;P5P41y;1R4C=,>d5HdFq%p6R6PdP;P4g00i:R2PUC=,>dP;PUg00iaRU1L;=R=C=,>d5HdP6P;P5PUP=C=,>dCMCM1td<R<P0P7g00jHR=g00jhRU'@1u07=3=UdAv;18CwRUb5b7b8X1;X9;X:;X0aW6A3;07,1:%O0,19'D12:7,7:127:[[^1;^9;^:;^0a^6aP0f?R9/011219P9PNP8P7P`O7b4b=b3b;CxPVPFP`14H^RV,5AR=PZCEP;%P^RePJP1CWRf,5CRg=<DW,:G53T12fO,7fPFP`PHPKP^PgP=P3PEP;PDPIAY;JeRhCZP;%P`PJP1CW,5C,:DR`93E0X<E%R;Ri1:;fP;PDPIP0CZ=3E`X<i1:Dg,@EPhP;PJPeP1P0DlE[AYDKeP;PDPIPePJD{E[1`eM12_NR_PePYP^O1P@PYP^P^1@;^D_PMPNP[E^P0C|P_P\P]f>R],]1121]%A]R\=3;]'110]1%O\'1'D%A9P;PcPb1J;8P?PdP;P4P2P5C=,>dR51Nd:5HdP6P5CMP<PUb5b7b8X1;X0a11Q8PL[^1;^0aP0fARa/2NPaP9O3b4b=b3b;bC1@B=%}V93B=eM;~B00;0JAQL8O[^2;RL\SPS\LB01;RJP7PfP;PePJP1P0I02J03H04bBPFP^14H3,5APZCE1K3JR3,5C=<DW,:G53T%B3123O3;eXEXX>SP8P0O2n2011000000121000000X?>XDPP8P0O2n2011000000121000000bIWAW@XG;WHo"). Qed.

  Lemma buf_all_bytes : all_bytes (c_buf C).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rnc_base ()) ["Base"] "h02FBh11Hh22_Hh33_H0h41ch51rp;1p;2p;3g0010j17Tg007oj12Tg004^j1CTg006oj2:Tg007Oj1=Tg008Mj20Tg008iR0j24Tg00>Dj2;Tg009Dj3?Tg009ej1>Tg00:fj15Tg00;Kj28Tg00;hj1MTg00<hj1LTg00=gj2KTg00>`j1JTg00?_j2ITg00@<j1HTg00A;j2GTg0038j1FTg00AXj1BTg00BYj1DTg00kHj1ATg00lEj2@Tg00Jjj2<Tf0R1#7#7p=6g00_Vf1R2'0/41p=3f2R3/02/<1p=Ef4f3'01032'</41p=11421,43p=9p,2OKg00d?R3#7R4#7R5#7R6#2R7g00`4R8p,1CR9#CR:':#=R;'0%76#6R6#6R<#6#6#6#6#2,0;'4R=%2<,;1,31X48=?8:R<%>9R>%53#5#5#5#5#5#5#2,0>'3%23,8>%M9,:8#=R8'0%L9R>%24R4%26'KR6,;>'3%J9R3g00eY,I>'0%H9R?1G48,8?R4/06'3%F9R8188;R;/87/06'3%B9R7%25R5,87R@/06'3%D9R91895R5/06'3P4P3P>P?P@P3P>P7P5P3P>P9P;P3P>P8P4P7P@P?P4P9P5P?P4P8P;P?P@P9P5P7P@P8P;P710;99E58D1D1D1D1D1D1D1D1D13939,333939R3'4R5'4P0P=P5%A:R8P1P0P<P3P8P11@:2X33X0<P2P1O2n2011000000121000000X15X2=P2P1O2n2011000000121000000b5o"). Qed.
End Base.
