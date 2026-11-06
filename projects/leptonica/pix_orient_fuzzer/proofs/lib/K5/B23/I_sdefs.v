(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import R_small R_m2s I_consts I_qck I_memchrw I_memcpyw F_shfile F_shgetc RT23b_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_I_sdefs () := "C46Stdlib5Lists4List2Inc69OSSVerify5KrLib2K53B237I_sdefs9rt3_apartC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.

Definition vfscanf_entry : Z := 0x2132c4.

(* [comment removed for export] *)
Definition RT3_CELLS : list (Z * Z) :=
  [(0x225d10, 48); (0x2268a0, 8); (0x226b70, 8); (0x227c58, 8); (0x227cb0, 16); (0x227e40, 8); (0x227e90, 16);
   (0x244ab8, 8); (0x245798, 32); (0x2d65e8, 256); (0x797ed8, 8)].
Definition rt3_apart (p : Z) : Prop := forall a n, In (a, n) RT3_CELLS -> p + 4 <= a \/ a + n <= p.

(* [comment removed for export] *)
Lemma rt3_apart_facts : forall p, rt3_apart p ->
  (p + 4 <= 0x225d10 \/ 0x225d10 + 48 <= p) /\ (p + 4 <= 0x2268a0 \/ 0x2268a0 + 8 <= p) /\ (p + 4 <= 0x226b70 \/ 0x226b70 + 8 <= p)
  /\ (p + 4 <= 0x227c58 \/ 0x227c58 + 8 <= p) /\ (p + 4 <= 0x227cb0 \/ 0x227cb0 + 16 <= p) /\ (p + 4 <= 0x227e40 \/ 0x227e40 + 8 <= p)
  /\ (p + 4 <= 0x227e90 \/ 0x227e90 + 16 <= p) /\ (p + 4 <= 0x244ab8 \/ 0x244ab8 + 8 <= p) /\ (p + 4 <= 0x245798 \/ 0x245798 + 32 <= p)
  /\ (p + 4 <= 0x2d65e8 \/ 0x2d65e8 + 256 <= p) /\ (p + 4 <= 0x797ed8 \/ 0x797ed8 + 8 <= p).
Proof.
ltac2:(KReplay.run1 (kr_t_I_sdefs ()) [] "h01Hh11pp;1p;2p;3p;4p-1g0000R0p4p710p8g000Gj1YTg001Dj1ITg001bj2QTg002?j12Tg002dj15Tg003Ij2<Tg003dj2XTg004Dj30Tg004^j1WTg005>j3MTP0j38Tg005^j21Tg0068j2BTg006Rj2OTg006nj4TTg007Nj3PTg007hj3LTg008Bj4STf0R0#2#2p==%20#5#2#2p=>%50#2#5#5p=A%50#2p=@%20#2#5#2p=?%20#2#2#Ip=6f4R1f3R2'Of2R3f1R4'Q/O0'1p=:%50#5p=F%20#5p=7%20#2#2#5p=U%50#5#5#5p=D%50#2#2#2p=R%50#5#2#2p=Ng008]R5P5P4P0CTp=9f5R6?012A0340g009;R7'1'1p=Jf6R8?061A0234/10'1p=31B409P23p=CAM3409M12p=HA0340/17p=GA06121134;L0p=;AP3409L12p=EAL3409L12p=41107p=VP8P6P1P2P3P4P0CSCSp=K%Y0g009XR3#=R2#I,Q4R1%=3#>#A#@#@#?#6R6P6%@3#6R8P4D:P1%=3#>#F#7#U#>#6R9P9%22R2#IR:P4D:R;P1%=3#>#F#7#7#A#@#6R<P<P:P4D:R=P1%=3#>#D#R#A#6R>P>P:P4D:R?P1%=3#>#D#@#7#7#@#6R@P@%22R2#IRAP4D:RBP1%=3#>#D#N#R#6RCPCP:P4D:RDP1%=3#>#F#D#7#?#6REPEPAP4D:RFP1%?3#?#7#7#7#7#F#6RGPGP:P4D:RHP1%?3#?#A#N#F#6RIPI%22R2#IRJP4D:RKP1%73#@#A#?#D#7#6RLPL%62R2P4D:RMP1%53#N#A#D#7#A#6R3P3P:P4D:R4'<R1'<RN'<RO'<RP'<RQ'<RR'<RS'<RT'<P0P6P81X55RU1968R8;08PU199:R6P8PU19<:RVP8PU19>:RWP8PU19@ARXP8PU19C:RYP8PU19EARZP8PU19G:R[P8PU19IJR\P8PU19L2R]P8PU193:R^P8EJF3F3F3F3PUP8CCPUP8PUP6PUPVPUPWPUPXPUPYPUPZPUP[PUP\PUP]%WU9MU^DHDHDHDHDHR_98U8eO3P;PTP0P9P:PUP8P6A0U66R9PUPVP6PUPWP6PUPXP6PUPYP6PUPZP6PUP[P6PUP\P6PUP]P6AGU^6F3F3F3F3RTP9PTPUP6CCE;A8U6_eO3P=PSP0P<P:PUP8PVA0U6VR<A0UVVRSPUPWPVPUPXPVPUPYPVPUPZPVPUP[PVPUP\PVPUP]PVPUP^PVEJF3F3F3R='1RTP<PTPSP=1BUVDEE;A8UV_eO3P?PRP0P>P:PUP8PWA0U6WR>A0UVWRRA0UWWR?PUPXPWPUPYPWPUPZPWPUP[PWPUP\PWPUP]PWAGU^WF3F3F3R='1RS'1RTP>PTPRPSP?P=PUPWCCD4E;A8UW_eO3PBPQP0P@PAPUP8PXA0U6XR@A0UVXRQA0UWXRBA0UXXR=PUPYPXPUPZPXPUP[PXPUP\PXPUP]PXPUP^PXEJF3F3R?'1RS'1RR'1RTP@PTPQPRPBPSP=P?1BUXDED4E;A8UX_eO3PDPPP0PCP:PUP8PYA0U6YRCA0UVYRPA0UWYRDA0UXYR?A0UYYR=PUPZPYPUP[PYPUP\PYPUP]PYAGU^YF3F3RS'1RB'1RR'1RQ'1RTPCPTPPPQPDPRP?PBP=PSPUPYCCD4D4E;A8UY_eO3PFPOP0PEPAPUP8PZA0U6ZRAA0UVZREA0UWZROA0UXZRFA0UYZRSA0UZZR=PUP[PZPUP\PZPUP]PZPUP^PZEJF3RB'1R?'1RR'1RD'1RQ'1RPPAPPPEPQPOPDPFPRPSP?P=PB1BUZDED4D4E;A8UZ_eO3PHPNP0PGP:PUP8P[A0U6[RGA0UV[RNA0UW[RHA0UX[RBA0UY[R=A0UZ[R?A0U[[RSPUP\P[PUP]P[AGU^[F3RR'1RF'1RD'1RO'1RQ'1RE'1RPPGPPPNPEPHPQPBPOP=PDP?PFPSPRPUP[CCD4D4D4E;A8U[_eO3PKP1P0PIPJPUP8P\A0U6\RJA0UV\RIA0UW\R1A0UX\RKA0UY\RRA0UZ\RSA0U[\RFA0U\\R?PUP]P\PUP^P\EJRD'1R='1RO'1RB'1RQ'1RH'1RE'1RNPJPNPIPEP1PHPKPQPRPBPSPOPFP=P?PD1BU\DED4D4D4E;A8U\_eO3PMP4P0PLP2PUP8P]A0U6]R2A0UV]RLA0UW]R4A0UX]RMA0UY]RDA0UZ]R?A0U[]R=A0U\]RFA0U]]ROAGU^]RS'1RB'1RR'1RQ'1RK'1RH'1R1'1RE'1RIP2PIPLPEP4P1PMPHPDPKP?PQP=PRPFPBPOPSPUP]CCD4D4D4D4E;A8U]_eO3P0P3P:PUP8P^A0U6^R6A0UV^RVA0UW^RWA0UX^RXA0UY^RYA0UZ^RZA0U[^R[A0U\^R\A0U]^R]A0U^^R8#VR:'1R3'1R0'1RS'1RO'1RB'1RF'1RR'1R=P6P=PVPRPWPFPXPBPYPOPZPSP[P0P\P3P]P:P8P71BU^DED4D4D4D4E;A8U^_eO3FKFKFKFKFKW0X15o"). Qed.
Notation VFSCANF_DEPTH := 2960%Z (only parsing).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sf_init (s : Z) : sfst :=
  mkSF 0 0 0 0 0 string_read_entry s 0 (Z_to_bv 64 0) SF_M1 s 0 (Z_to_bv 64 0) (Z_to_bv 64 0).

Definition vfscanf_dd_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f p1 p2 d1 d2 : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (st' : sfst),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 2) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 232); (bv_unsigned sp - VFSCANF_DEPTH, bv_unsigned sp); (p1, p1 + 4); (p2, p2 + 4)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' f (sfile st')
    /\ rw_cells asegs m' p1 [C4 (Z_to_bv 64 d1)] /\ rw_cells asegs m' p2 [C4 (Z_to_bv 64 d2)].

(* [comment removed for export] *)
Definition vfscanf_dd_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (f s ap p1 p2 : Z) (tok : list Z) (extra : list byte) (d1 d2 : Z) (j1 j2 : list byte) (g : word) (lo : Z),
  a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 SSCANF_FMT -> a2 = Z_to_bv 64 ap ->
  rw_cells asegs m f (sfile (sf_init s)) -> bv_unsigned sp <= f -> f + 232 <= 2^47 ->
  rw_cells asegs m ap [C8 (Z_to_bv 64 p1); C8 (Z_to_bv 64 p2)] -> bv_unsigned sp <= ap -> ap + 16 <= 2^47 ->
  (f + 232 <= ap \/ ap + 16 <= f) ->
  In (tok, (d1, d2)) SSCANF_TOKENS -> bytes_at asegs m s (map (Z_to_bv 8) tok ++ extra) -> s mod 16 = 1 ->
  Z.of_nat (length tok) + Z.of_nat (length extra) = 7 -> 0 < s -> s + 7 <= lo ->
  chk_ok m s (Z.of_nat (length tok)) -> chk_ok m (s + Z.of_nat (length tok) - 1) 1 ->
  chk_ok m (bv_unsigned sp - 561) 1 -> chk_ok m (bv_unsigned sp - 641) 1 ->
  rw_cells asegs m p1 [CB 4 j1] -> rw_cells asegs m p2 [CB 4 j2] -> 0 < p1 -> 0 < p2 ->
  (p1 + 4 <= p2 \/ p2 + 4 <= p1) -> p1 + 4 <= lo -> p2 + 4 <= lo ->
  (s + 7 <= p1 \/ p1 + 4 <= s) -> (s + 7 <= p2 \/ p2 + 4 <= s) -> rt3_apart p1 -> rt3_apart p2 ->
  (p1 + 4 <= 0x7fff8000 \/ 0x10007fff8007 <= p1) -> (p2 + 4 <= 0x7fff8000 \/ 0x10007fff8007 <= p2) ->   (* [comment removed for export] *)
  m2s_cells m -> icells_mc m -> icells m -> ssp_cells m g ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - VFSCANF_DEPTH -> kHighShadowEnd + 8 <= lo ->
  mem_inv asegs m ->
  evt asegs (vfscanf_dd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f p1 p2 d1 d2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 vfscanf_entry) fc None m (seg_rom asegs)).
