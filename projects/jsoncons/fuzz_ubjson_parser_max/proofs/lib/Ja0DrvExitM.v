(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ja0DrvEntry Ja0Drv_defs Ja0DrvLib Ja0DrvRead Ja0DrvPiece Ja0DiagLoopK Ja0DrvStdio Ja0DrvPrintfK Ja0DrvPrintf1 Ja0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem JatFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ja0DrvP_dpXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLiaT.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit. From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0DrvExitM () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanAcct."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIface."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvExit."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DrvExitM.FPX_1.ExitM."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0A"; "1list"; "1option"; "1prod"; "2I"; "2and"; "2eq"; "3Z"; "0LB"; "0LK"; "4mkCfg"; "5Model"; "5m_fs"; "6bvmap"; "0M"; "0MV"]; ["0R"; "7mrestrict"; "8credit"; "9ahid"; "9fframe"; ":stdoutPA"; ";exit_preM"; "<getr"; "<mkst"; "<seg_rom"; "=t_exit"; ">srealizes"; "?loaded_segments"; "0S"; "@le"; "@lt"]; ["0cr"; "0fx"; "0model"; "0scfg"; "0st"; "ABV"; "AZ_to_bv"; "Abv"; "0tid"]]).
Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Definition XCM_CELLS : list (Z * Z * Z) :=
[(6877168, 4, 0); (6877203, 1, 0); (6876640, 8, 6876648); (6876632, 4, 1); (6876656, 8, 1128656); (6876912, 8, 617484); (6876628, 4, 0); (6876648, 8, 0); (6878600, 8, 0); (1274120, 8, 1273888); (1274028, 4, 4294967295); (1273928, 8, 0); (1273944, 8, 0); (1273896, 8, 0); (1273904, 8, 0); (1273880, 8, 1273648); (1273640, 8, 1273408); (1273548, 4, 4294967295); (1273448, 8, 6878616); (1273464, 8, 6878616); (1273416, 8, 0); (1273424, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
cells_at MV XCM_CELLS
/\ rdn ASEGS MV (Z_to_bv 64 6745304) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
/\ (forall i, 0x137140 <= i < 0x137640 -> MV (Z_to_bv 64 i) = None).
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
/\ (forall i, 65536 <= i < 1261568 -> MV (Z_to_bv 64 i) = None)
/\ exitMA tid MV.
Section SE.
Local Abbreviation SEC_T_exit_run_m := (ltac2:(TCodec.tc2 tcn__Ja0DrvExitM "S8'1'3'7%2211%411&D%611&B'Q7yR0%211'2y8%511%311p051';&=y5%2219&Fr:r9r8r7r6r5r3r1%9887654321&A&C%1297%3219'5&Nzr4%3221&O+X0%2241%8241'6&G(Q5+2(4%33N21%52I1&Q6%12Q:J%93Q:31+4%93Q417%;2Q01+V]k\0%72Q@1%?3Q@31+:%?3Q:1=%A2Q71%<2QEQ6%D3QE21&E%11Q7'K&LvQ3(:&HvQ1r;+QR^Y4%H2R11r=&I%11:%8576431r<%;221&J%Q02R9QL&<%115%4231%D4CB61p0F1p0I1p0O1p0Q61p0QA1tQ0R=QK1p0R01pRBRL1pR:RM1pQLRN1pQ2R>1pR6RB1pNRD1p2S01pR2RN1pDS01pBS31")) (only parsing).
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
assert (SHW : forall a n, ((2147468832 <=? a) && (a + n <=? 2147469084) || (2147604916 <=? a) && (a + n <=? 2147604936) || (2147610152 <=? a) && (a + n <=? 2147610312)) = true -> L5Defs.L5.writable ASEGS MV a n)
by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
{ intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x137140 <=? a) && (a + Z.of_nat n <=? 0x137640) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
{ intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
G2 G4 HSr HSa CWR CDF
IMGc (WSG 1275456 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1275536 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1279408 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6876624 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6876632 4%nat ltac:(vm_compute; reflexivity) eq_refl)
(WSG 6876640 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6877168 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468832 1 eq_refl) (SHW 2147468833 1 eq_refl) (SHW 2147468834 1 eq_refl) (SHW 2147468835 1 eq_refl)
(SHW 2147468844 1 eq_refl) (SHW 2147468845 1 eq_refl) (SHW 2147468846 1 eq_refl) (SHW 2147468847 1 eq_refl) (SHW 2147468848 1 eq_refl) (SHW 2147468848 4 eq_refl)
(SHW 2147468849 1 eq_refl) (SHW 2147468850 1 eq_refl) (SHW 2147468851 1 eq_refl) (SHW 2147468852 4 eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468856 4 eq_refl)
(SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl)
(SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl)
(SHW 2147468913 1 eq_refl) (SHW 2147468914 1 eq_refl) (SHW 2147468915 1 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl)
(SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl)
(SHW 2147468924 4 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl)
(SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl)
(SHW 2147468940 4 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl)
(SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 4 eq_refl)
(SHW 2147468956 4 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
(SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468968 4 eq_refl)
(SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468976 4 eq_refl)
(SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl)
(SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468992 4 eq_refl)
(SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl)
(SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469004 4 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl)
(SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl)
(SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl)
(SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl)
(SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl)
(SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl)
(SHW 2147469040 4 eq_refl) (SHW 2147469044 1 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl)
(SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 4 eq_refl)
(SHW 2147469056 4 eq_refl) (SHW 2147469060 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl)
(SHW 2147469064 1 eq_refl) (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469069 1 eq_refl)
(SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl)
(SHW 2147469075 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl)
(SHW 2147469083 1 eq_refl) (SHW 2147604916 1 eq_refl) (SHW 2147604916 4 eq_refl) (SHW 2147604917 1 eq_refl) (SHW 2147604918 1 eq_refl) (SHW 2147604919 1 eq_refl)
(SHW 2147604920 4 eq_refl) (SHW 2147604924 4 eq_refl) (SHW 2147604928 4 eq_refl) (SHW 2147604932 1 eq_refl) (SHW 2147604932 4 eq_refl) (SHW 2147604933 1 eq_refl)
(SHW 2147604934 1 eq_refl) (SHW 2147604935 1 eq_refl) (SHW 2147610152 1 eq_refl) (SHW 2147610152 4 eq_refl) (SHW 2147610153 1 eq_refl) (SHW 2147610154 1 eq_refl)
(SHW 2147610155 1 eq_refl) (SHW 2147610156 4 eq_refl) (SHW 2147610160 4 eq_refl) (SHW 2147610164 4 eq_refl) (SHW 2147610168 4 eq_refl) (SHW 2147610172 4 eq_refl)
(SHW 2147610176 4 eq_refl) (SHW 2147610176 8 eq_refl) (SHW 2147610184 8 eq_refl) (SHW 2147610192 8 eq_refl) (SHW 2147610200 8 eq_refl) (SHW 2147610208 8 eq_refl)
(SHW 2147610216 8 eq_refl) (SHW 2147610224 8 eq_refl) (SHW 2147610232 8 eq_refl) (SHW 2147610240 8 eq_refl) (SHW 2147610248 8 eq_refl) (SHW 2147610256 8 eq_refl)
(SHW 2147610264 8 eq_refl) (SHW 2147610272 8 eq_refl) (SHW 2147610280 8 eq_refl) (SHW 2147610284 4 eq_refl) (SHW 2147610288 4 eq_refl) (SHW 2147610288 8 eq_refl)
(SHW 2147610292 4 eq_refl) (SHW 2147610296 4 eq_refl) (SHW 2147610296 8 eq_refl) (SHW 2147610300 4 eq_refl) (SHW 2147610304 4 eq_refl) (SHW 2147610308 1 eq_refl)
(SHW 2147610308 4 eq_refl) (SHW 2147610309 1 eq_refl) (SHW 2147610310 1 eq_refl) (SHW 2147610311 1 eq_refl) TIDC HTr
(XCC 0%nat 6877168 4 0 eq_refl) (XCC1 1%nat 6877203 0 eq_refl eq_refl) (XCC 2%nat 6876640 8 6876648 eq_refl) (XCC 3%nat 6876632 4 1 eq_refl) (XCC 4%nat 6876656 8 1128656 eq_refl) (XCC 5%nat 6876912 8 617484 eq_refl)
(XCC 6%nat 6876628 4 0 eq_refl) (STC1 10%nat 1887136 0 eq_refl eq_refl) (XCC 7%nat 6876648 8 0 eq_refl) (STC1 3%nat 1275536 0 eq_refl eq_refl) (STC 0%nat 1262664 8 1262664 eq_refl) (STC 2%nat 1275456 8 1 eq_refl)
(STC 4%nat 1279248 4 1 eq_refl) (STC 5%nat 1279408 8 0 eq_refl) (STC1 8%nat 1292760 1 eq_refl eq_refl) (STC 7%nat 1289464 8 2147450880 eq_refl) (DSC 1274176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143616)) ltac:(img_rd) eq_refl) (DSC 1274192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
(STC1 6%nat 1287516 1 eq_refl eq_refl) (DSC 1274192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1886368 8 18446744073709551615 eq_refl) (STC 1%nat 1263176 8 1199536 eq_refl) (DSC 1274232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143712)) ltac:(img_rd) eq_refl)
(DSC 1274256 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1274256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1274296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143744)) ltac:(img_rd) eq_refl) (DSC 1274320 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1274320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1274360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274368 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl) (DSC 1274384 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1274384 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1274424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274432 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl)
(DSC 1274448 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1274448 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1274488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274496 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144288)) ltac:(img_rd) eq_refl) (DSC 1274512 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1274512 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
(DSC 1274552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274560 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1274576 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1274576 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1274616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274624 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl)
(DSC 1274640 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1274640 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1274680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl) (DSC 1274704 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1274704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1274744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1274768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1274768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1274808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
(DSC 1274832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1274832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1274872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1274896 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1274896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
(DSC 1274936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1274944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl) (DSC 1274960 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1274960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1275000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl)
(DSC 1275024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1275024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1275064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1275088 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1275088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
(DSC 1275128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1275152 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1275152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1275192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145344)) ltac:(img_rd) eq_refl)
(DSC 1275216 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1275216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1275256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145472)) ltac:(img_rd) eq_refl) (DSC 1275280 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1275280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
(DSC 1275320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1275344 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1275344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1275384 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1275392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1232288)) ltac:(img_rd) eq_refl)
(DSC 1275408 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl) (DSC 1275408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1275448 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6878600 8 0 eq_refl) (XCC 9%nat 1274120 8 1273888 eq_refl) (XCC 10%nat 1274028 4 4294967295 eq_refl)
(XCC 11%nat 1273928 8 0 eq_refl) (XCC 12%nat 1273944 8 0 eq_refl) (XCC 13%nat 1273896 8 0 eq_refl) (XCC 14%nat 1273904 8 0 eq_refl) (XCC 15%nat 1273880 8 1273648 eq_refl) SOlock
SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1273640 8 1273408 eq_refl) (XCC 17%nat 1273548 4 4294967295 eq_refl)
(XCC 18%nat 1273448 8 6878616 eq_refl) (XCC 19%nat 1273464 8 6878616 eq_refl) (XCC 20%nat 1273416 8 0 eq_refl) (XCC 21%nat 1273424 8 0 eq_refl)) as
(fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
unfold V in XMS; cbn beta iota in XMS.
pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x113924) M R1 (Z_to_bv 64 0x113634) MV1 model _ LZ XMS).
intros M' model' MI' SBM' _.
rewrite <- (proj2 (sbm_fds model model' SBM')).
apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x113634) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
- rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
- left. exact Xr17.
- eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
- exact Hst.
Qed.
End SE.
End ExitM.
End FPX_1.
