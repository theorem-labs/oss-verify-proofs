(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import SysStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import StrFun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import R_small R_m2s I_consts I_qck I_memchrw I_memcpyw F_shfile F_shgetc RT23b_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_I_sdefs () := "C46Stdlib5Lists4List2Inc69OSSVerify5KrLib2K53A237I_sdefs9rt3_apartC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive03".
Import ListNotations.
Open Scope Z_scope.

Definition vfscanf_entry : Z := 0x1fed7c.

(* [comment removed for export] *)
Definition RT3_CELLS : list (Z * Z) :=
  [(0x2117c8, 48); (0x212358, 8); (0x212628, 8); (0x2136f8, 8); (0x213750, 16); (0x2138e0, 8); (0x213930, 16);
   (0x230338, 8); (0x231018, 32); (0x2c1e68, 256); (0x783758, 8)].
Definition rt3_apart (p : Z) : Prop := forall a n, In (a, n) RT3_CELLS -> p + 4 <= a \/ a + n <= p.

(* [comment removed for export] *)
Lemma rt3_apart_facts : forall p, rt3_apart p ->
  (p + 4 <= 0x2117c8 \/ 0x2117c8 + 48 <= p) /\ (p + 4 <= 0x212358 \/ 0x212358 + 8 <= p) /\ (p + 4 <= 0x212628 \/ 0x212628 + 8 <= p)
  /\ (p + 4 <= 0x2136f8 \/ 0x2136f8 + 8 <= p) /\ (p + 4 <= 0x213750 \/ 0x213750 + 16 <= p) /\ (p + 4 <= 0x2138e0 \/ 0x2138e0 + 8 <= p)
  /\ (p + 4 <= 0x213930 \/ 0x213930 + 16 <= p) /\ (p + 4 <= 0x230338 \/ 0x230338 + 8 <= p) /\ (p + 4 <= 0x231018 \/ 0x231018 + 32 <= p)
  /\ (p + 4 <= 0x2c1e68 \/ 0x2c1e68 + 256 <= p) /\ (p + 4 <= 0x783758 \/ 0x783758 + 8 <= p).
Proof.
ltac2:(KReplay.run1 (kr_t_I_sdefs ()) [] "h01Hh11pp;1p;2p;3p;4p-1g0000R0p4p710p8g000Gj1XTg001Dj1HTg001bj2QTg002?j12Tg002dj17Tg003Ij2<Tg003dj2WTg004Dj30Tg004^j1VTg005>j3NTP0j39Tg005^j21Tg0068j2BTg006Rj2PTg006nj4TTg007Nj3OTg007hj3LTg008Bj4STf0R0#2#2p=>%20#2#7#2p=K%70#7p=5%70#2#2#7p=D%20#2#2#Hp=6%70#2p=@f4R1f3R2'Pf2R3f1R4'Q/P0'1p=:%20#2#2#2p==%20#7#7#2p=?%70#7#2#2p=M%20#7p=A%70#2#2#2p=Rg008]R5P5P4P0CTp=8f5R6?012A0340g009;R7'1'1p=If6R8?061A0234/10'1p=41B409O23p=CAN3409N12p=GA0340/17p=FA06121134;L0p=;AO3409L12p=EAL3409L12p=31107p=UP8P6P1P2P3P4P0CSCSp=J%X0g009XR3#>R2#H,Q4R1%>3#K#K#5#5#D#6R6P6%@3#6R8P4D:P1%=3#D#>#?#@#5#6R9P9%22R2#HR:P4D:R;P1%=3#D#>#M#A#A#6R<P<P:P4D:R=P1%>3#K#?#5#A#5#5#6R>P>P:P4D:R?P1%>3#K#?#5#@#@#@#6R@P@%22R2#HRAP4D:RBP1%=3#D#M#A#M#6RCPCP:P4D:RDP1%=3#D#5#K#?#6REPEPAP4D:RFP1%>3#?#=#A#D#5#6RGPGP:P4D:RHP1%>3#A#R#R#=#5#6RIPI%22R2#HRJP4D:RKP1%?3#=#5#M#5#A#6RLPL%62R2P4D:RMP1%73#5#=#?#5#@#@#5#6R3P3P:P4D:R4'<R1'<RN'<RO'<RP'<RQ'<RR'<RS'<RT'<P0P6P81W55RU1868R8;08PU189:R6P8PU18<:RVP8PU18>:RWP8PU18@ARXP8PU18C:RYP8PU18EARZP8PU18G:R[P8PU18IJR\P8PU18L2R]P8PU183:R^P8EIF4F4F4F4PUP8CCPUP8PUP6PUPVPUPWPUPXPUPYPUPZPUP[PUP\PUP]%VU9NU^DGDGDGDGDGR_99U8eO3P;PTP0P9P:PUP8P6A0U66R9PUPVP6PUPWP6PUPXP6PUPYP6PUPZP6PUP[P6PUP\P6PUP]P6AFU^6F4F4F4F4RTP9PTPUP6CCE;A9U6_eO3P=PSP0P<P:PUP8PVA0U6VR<A0UVVRSPUPWPVPUPXPVPUPYPVPUPZPVPUP[PVPUP\PVPUP]PVPUP^PVEIF4F4F4R='1RTP<PTPSP=1BUVDEE;A9UV_eO3P?PRP0P>P:PUP8PWA0U6WR>A0UVWRRA0UWWR?PUPXPWPUPYPWPUPZPWPUP[PWPUP\PWPUP]PWAFU^WF4F4F4R='1RS'1RTP>PTPRPSP?P=PUPWCCD3E;A9UW_eO3PBPQP0P@PAPUP8PXA0U6XR@A0UVXRQA0UWXRBA0UXXR=PUPYPXPUPZPXPUP[PXPUP\PXPUP]PXPUP^PXEIF4F4R?'1RS'1RR'1RTP@PTPQPRPBPSP=P?1BUXDED3E;A9UX_eO3PDPPP0PCP:PUP8PYA0U6YRCA0UVYRPA0UWYRDA0UXYR?A0UYYR=PUPZPYPUP[PYPUP\PYPUP]PYAFU^YF4F4RS'1RB'1RR'1RQ'1RTPCPTPPPQPDPRP?PBP=PSPUPYCCD3D3E;A9UY_eO3PFPOP0PEPAPUP8PZA0U6ZRAA0UVZREA0UWZROA0UXZRFA0UYZRSA0UZZR=PUP[PZPUP\PZPUP]PZPUP^PZEIF4RB'1R?'1RR'1RD'1RQ'1RPPAPPPEPQPOPDPFPRPSP?P=PB1BUZDED3D3E;A9UZ_eO3PHPNP0PGP:PUP8P[A0U6[RGA0UV[RNA0UW[RHA0UX[RBA0UY[R=A0UZ[R?A0U[[RSPUP\P[PUP]P[AFU^[F4RR'1RF'1RD'1RO'1RQ'1RE'1RPPGPPPNPEPHPQPBPOP=PDP?PFPSPRPUP[CCD3D3D3E;A9U[_eO3PKP1P0PIPJPUP8P\A0U6\RJA0UV\RIA0UW\R1A0UX\RKA0UY\RRA0UZ\RSA0U[\RFA0U\\R?PUP]P\PUP^P\EIRD'1R='1RO'1RB'1RQ'1RH'1RE'1RNPJPNPIPEP1PHPKPQPRPBPSPOPFP=P?PD1BU\DED3D3D3E;A9U\_eO3PMP4P0PLP2PUP8P]A0U6]R2A0UV]RLA0UW]R4A0UX]RMA0UY]RDA0UZ]R?A0U[]R=A0U\]RFA0U]]ROAFU^]RS'1RB'1RR'1RQ'1RK'1RH'1R1'1RE'1RIP2PIPLPEP4P1PMPHPDPKP?PQP=PRPFPBPOPSPUP]CCD3D3D3D3E;A9U]_eO3P0P3P:PUP8P^A0U6^R6A0UV^RVA0UW^RWA0UX^RXA0UY^RYA0UZ^RZA0U[^R[A0U\^R\A0U]^R]A0U^^R8#UR:'1R3'1R0'1RS'1RO'1RB'1RF'1RR'1R=P6P=PVPRPWPFPXPBPYPOPZPSP[P0P\P3P]P:P8P71BU^DED3D3D3D3E;A9U^_eO3FJFJFJFJFJW0X15o"). Qed.
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
