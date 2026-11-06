(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvLib Jb0DrvRead Jb0DrvPiece Jb0DiagLoopK Jb0DrvStdio Jb0DrvPrintfK Jb0DrvPrintf1 Jb0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem JbtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Jb0DrvP_dpXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0DrvExitM () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvExit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DrvExitM.FPX_1.ExitM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1list"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "3Z"; "0LB"; "0LK"; "4mkCfg"; "5Model"; "5m_fs"; "6bvmap"; "0M"; "0MV"]; ["0R"; "7mrestrict"; "8credit"; "9ahid"; "9fframe"; ":stdoutPA"; ";exit_preM"; "<getr"; "<mkst"; "<seg_rom"; "=t_exit"; ">srealizes"; "?loaded_segments"; "0S"; "@le"; "@lt"]; ["0cr"; "0fx"; "0model"; "0scfg"; "0st"; "ABV"; "AZ_to_bv"; "Abv"; "0tid"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Definition XCM_CELLS : list (Z * Z * Z) :=
[(6884656, 4, 0); (6884691, 1, 0); (6884128, 8, 6884136); (6884120, 4, 1); (6884144, 8, 1136392); (6884400, 8, 618204); (6884116, 4, 0); (6884136, 8, 0); (6886088, 8, 0); (1281648, 8, 1281416); (1281556, 4, 4294967295); (1281456, 8, 0); (1281472, 8, 0); (1281424, 8, 0); (1281432, 8, 0); (1281408, 8, 1281176); (1281168, 8, 1280936); (1281076, 4, 4294967295); (1280976, 8, 6886104); (1280992, 8, 6886104); (1280944, 8, 0); (1280952, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
cells_at MV XCM_CELLS
/\ rdn ASEGS MV (Z_to_bv 64 6752792) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
/\ (forall i, 0x138ea0 <= i < 0x139380 -> MV (Z_to_bv 64 i) = None).
Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ExitM.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable IL : icpt_layout.
Variable HI : asan_iface.
Hypothesis HIok : asan_iface_ok L ar C scfg HI.
Hypothesis ICok : aicpt_ok L ar IL scfg HI.
Hypothesis ILY : as0_icpt_layout IL.
Variable sp0 : word.
Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
Hypothesis DL : drv_layoutA L ar IL sp0.
Hypothesis Hex : incl EX_CELLS (asc_cells C).
Variable M0 : word -> option byte.
#[local] Notation dinvA := (dinv ar HI sp0 M0).
#[local] Notation usp := (bv_unsigned sp0).
#[local] Notation rom := (seg_rom ASEGS).
Definition exit_preM (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
let MV := mrestrict (ahid A model) M in
dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
/\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
/\ (forall i, 65536 <= i < 1269760 -> MV (Z_to_bv 64 i) = None)
/\ exitMA tid MV.
Section SE.
Local Abbreviation SEC_T_exit_run_m := (ltac2:(TCodec.tc2 tcn__Jb0DrvExitM "S8'1'3'7%2211%411&D%611&B'Q7yR0%211'2y8%511%311p051';&=y5%2219&Fr:r9r8r7r6r5r3r1%9887654321&A&C%1297%3219'5&Nzr4%3221&O+X0%2241%8241'6&G(Q5+2(4%33N21%52I1&Q6%12Q:J%93Q:31+4%93Q417%;2Q01+V^Rf0%72Q@1%?3Q@31+:%?3Q:1=%A2Q71%<2QEQ6%D3QE21&E%11Q7'K&LvQ3(:&HvQ1r;+QRejL%H2R11r=&I%11:%8576431r<%;221&J%Q02R9QL&<%115%4231%D4CB61p0F1p0I1p0O1p0Q61p0QA1tQ0R=QK1p0R01pRBRL1pR:RM1pQLRN1pQ2R>1pR6RB1pNRD1p2S01pR2RN1pDS01pBS31")) (only parsing).
Variable LB : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 0%nat 0%nat).
Variable LK : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 1%nat 0%nat).
Variable cr : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 2%nat 0%nat).
Variable A : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 3%nat 0%nat).
Variable M : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 4%nat 0%nat).
Variable model : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 5%nat 0%nat).
Variable R : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 6%nat 0%nat).
Variable S : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 7%nat 0%nat).
Variable st : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 8%nat 0%nat).
Variable tid : ltac:(sec_ty2 constr:(SEC_T_exit_run_m) 9%nat 0%nat).
Lemma exit_run_m : ltac:(sec_stmt2 constr:(SEC_T_exit_run_m) 10%nat 0%nat).
Proof using L C IL HIok ICok ILY Hsp DL Hex LB LK cr A M model R S st tid.
intros (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
pose proof Hsp as Hsp'. destruct SOP as (SOlock & SOwpos & SOwbase & SOrpos & SOrend).
set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
assert (HSa : AS0DRVP_dpXm.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
{ cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
{ cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
{ intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable sp0 Hsp M0 MV a n W B1 B2). }
assert (SHW : forall a n, ((2147468844 <=? a) && (a + n <=? 2147469096) || (2147611092 <=? a) && (a + n <=? 2147611248)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x138ea0 <=? a) && (a + Z.of_nat n <=? 0x139380) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
G2 G4 HSr HSa CWR CDF
IMGc (WSG 1282944 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1283024 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286896 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884112 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884120 4%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6884128 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6884656 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl) (SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl)
(SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468860 1 eq_refl) (SHW 2147468860 4 eq_refl)
(SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl) (SHW 2147468864 4 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl)
(SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl)
(SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl)
(SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl)
(SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
(SHW 2147468936 4 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl)
(SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl) (SHW 2147468948 4 eq_refl)
(SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
(SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 4 eq_refl)
(SHW 2147468968 4 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl)
(SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl)
(SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl)
(SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468992 4 eq_refl) (SHW 2147468993 1 eq_refl)
(SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469004 4 eq_refl)
(SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl)
(SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl)
(SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl)
(SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl)
(SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl)
(SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl)
(SHW 2147469047 1 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl)
(SHW 2147469052 4 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl)
(SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl) (SHW 2147469064 4 eq_refl)
(SHW 2147469068 4 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl)
(SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl)
(SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469084 4 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl)
(SHW 2147469087 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl)
(SHW 2147469095 1 eq_refl) (SHW 2147611092 1 eq_refl) (SHW 2147611092 4 eq_refl) (SHW 2147611093 1 eq_refl) (SHW 2147611094 1 eq_refl) (SHW 2147611095 1 eq_refl)
(SHW 2147611096 4 eq_refl) (SHW 2147611100 4 eq_refl) (SHW 2147611104 4 eq_refl) (SHW 2147611108 4 eq_refl) (SHW 2147611112 4 eq_refl) (SHW 2147611116 4 eq_refl)
(SHW 2147611120 8 eq_refl) (SHW 2147611128 8 eq_refl) (SHW 2147611136 8 eq_refl) (SHW 2147611144 8 eq_refl) (SHW 2147611152 8 eq_refl) (SHW 2147611160 8 eq_refl)
(SHW 2147611168 8 eq_refl) (SHW 2147611176 8 eq_refl) (SHW 2147611184 8 eq_refl) (SHW 2147611192 8 eq_refl) (SHW 2147611200 8 eq_refl) (SHW 2147611208 8 eq_refl)
(SHW 2147611216 4 eq_refl) (SHW 2147611220 4 eq_refl) (SHW 2147611224 4 eq_refl) (SHW 2147611228 4 eq_refl) (SHW 2147611232 4 eq_refl) (SHW 2147611236 4 eq_refl)
(SHW 2147611240 1 eq_refl) (SHW 2147611240 4 eq_refl) (SHW 2147611241 1 eq_refl) (SHW 2147611242 1 eq_refl) (SHW 2147611243 1 eq_refl) TIDC
HTr (XCC 0%nat 6884656 4 0 eq_refl) (XCC1 1%nat 6884691 0 eq_refl eq_refl) (XCC 2%nat 6884128 8 6884136 eq_refl) (XCC 3%nat 6884120 4 1 eq_refl) (XCC 4%nat 6884144 8 1136392 eq_refl)
(XCC 5%nat 6884400 8 618204 eq_refl) (XCC 6%nat 6884116 4 0 eq_refl) (STC1 10%nat 1894624 0 eq_refl eq_refl) (XCC 7%nat 6884136 8 0 eq_refl) (STC1 3%nat 1283024 0 eq_refl eq_refl) (STC 0%nat 1270192 8 1270192 eq_refl)
(STC 2%nat 1282944 8 1 eq_refl) (STC 4%nat 1286736 4 1 eq_refl) (STC 5%nat 1286896 8 0 eq_refl) (STC1 8%nat 1300248 1 eq_refl eq_refl) (STC 7%nat 1296952 8 2147450880 eq_refl) (DSC 1281696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl)
(DSC 1281712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1295004 1 eq_refl eq_refl) (DSC 1281712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1893856 8 18446744073709551615 eq_refl) (STC 1%nat 1270704 8 1207272 eq_refl) (DSC 1281752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1281776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1281840 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1281840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1281880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1281888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1281904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1281904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1281944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1281952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1281968 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1281968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1282032 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(DSC 1282032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1282096 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144512)) ltac:(img_rd) eq_refl) (DSC 1282160 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1282224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1282288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1282288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1282328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1282352 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1282416 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
(DSC 1282416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1282480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1282544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1282608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
(DSC 1282608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl) (DSC 1282672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(DSC 1282720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1282736 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1282736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1282776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1282800 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
(DSC 1282800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1282840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1282848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1282864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1282864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1282904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
(XCC 8%nat 6886088 8 0 eq_refl) (XCC 9%nat 1281648 8 1281416 eq_refl) (XCC 10%nat 1281556 4 4294967295 eq_refl) (XCC 11%nat 1281456 8 0 eq_refl) (XCC 12%nat 1281472 8 0 eq_refl) (XCC 13%nat 1281424 8 0 eq_refl)
(XCC 14%nat 1281432 8 0 eq_refl) (XCC 15%nat 1281408 8 1281176 eq_refl) SOlock SOwpos SOwbase SOrpos
SOrend (XCC 16%nat 1281168 8 1280936 eq_refl) (XCC 17%nat 1281076 4 4294967295 eq_refl) (XCC 18%nat 1280976 8 6886104 eq_refl) (XCC 19%nat 1280992 8 6886104 eq_refl) (XCC 20%nat 1280944 8 0 eq_refl)
(XCC 21%nat 1280952 8 0 eq_refl)) as
(fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
unfold V in XMS; cbn beta iota in XMS.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11575c) M R1 (Z_to_bv 64 0x11546c) MV1 model _ LZ XMS).
intros M' model' MI' SBM' _.
rewrite <- (proj2 (sbm_fds model model' SBM')).
apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11546c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
- left. exact Xr17.
- eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
- exact Hst.
Qed.
End SE.
End ExitM.
End FPX_1.
