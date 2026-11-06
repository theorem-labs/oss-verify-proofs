(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ba0DrvEntry Ba0Drv_defs Ba0DrvLib Ba0DrvRead Ba0DrvPiece Ba0DiagLoopK Ba0DrvStdio Ba0DrvPrintfK Ba0DrvPrintf1 Ba0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem BatFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Ba0DrvP_dpXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6888176, 4, 0); (6888211, 1, 0); (6887648, 8, 6887656); (6887640, 4, 1); (6887664, 8, 1139320); (6887920, 8, 618908); (6887636, 4, 0); (6887656, 8, 0); (6889608, 8, 0); (1284776, 8, 1284544); (1284684, 4, 4294967295); (1284584, 8, 0); (1284600, 8, 0); (1284552, 8, 0); (1284560, 8, 0); (1284536, 8, 1284304); (1284296, 8, 1284064); (1284204, 4, 4294967295); (1284104, 8, 6889624); (1284120, 8, 6889624); (1284072, 8, 0); (1284080, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6756312) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x139ae0 <= i < 0x13a0e0 -> MV (Z_to_bv 64 i) = None).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ExitM.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
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

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6756480 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1162cc) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
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
    assert (SHW : forall a n, ((2147468852 <=? a) && (a + n <=? 2147469100) || (2147606248 <=? a) && (a + n <=? 2147606268) || (2147611484 <=? a) && (a + n <=? 2147611676)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x139ae0 <=? a) && (a + Z.of_nat n <=? 0x13a0e0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
           G2 G4 HSr HSa CWR CDF
           IMGc (WSG 1286400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286480 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1290352 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887632 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887640 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6887648 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6888176 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468852 1 eq_refl) (SHW 2147468853 1 eq_refl) (SHW 2147468854 1 eq_refl) (SHW 2147468855 1 eq_refl)
           (SHW 2147468864 1 eq_refl) (SHW 2147468865 1 eq_refl) (SHW 2147468866 1 eq_refl) (SHW 2147468867 1 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl)
           (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 4 eq_refl) (SHW 2147468876 1 eq_refl) (SHW 2147468876 4 eq_refl)
           (SHW 2147468877 1 eq_refl) (SHW 2147468878 1 eq_refl) (SHW 2147468879 1 eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl)
           (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl)
           (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl)
           (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl) (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl)
           (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl)
           (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 4 eq_refl)
           (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl)
           (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468940 4 eq_refl)
           (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl) (SHW 2147468948 1 eq_refl)
           (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl)
           (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468961 1 eq_refl)
           (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl)
           (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl)
           (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl)
           (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl)
           (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl)
           (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl)
           (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl)
           (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl)
           (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl)
           (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl)
           (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 1 eq_refl)
           (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl)
           (SHW 2147469035 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl)
           (SHW 2147469072 4 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl)
           (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl)
           (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl)
           (SHW 2147469091 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469096 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469097 1 eq_refl) (SHW 2147469098 1 eq_refl)
           (SHW 2147469099 1 eq_refl) (SHW 2147606248 1 eq_refl) (SHW 2147606248 4 eq_refl) (SHW 2147606249 1 eq_refl) (SHW 2147606250 1 eq_refl) (SHW 2147606251 1 eq_refl)
           (SHW 2147606252 4 eq_refl) (SHW 2147606256 4 eq_refl) (SHW 2147606260 4 eq_refl) (SHW 2147606264 1 eq_refl) (SHW 2147606264 4 eq_refl) (SHW 2147606265 1 eq_refl)
           (SHW 2147606266 1 eq_refl) (SHW 2147606267 1 eq_refl) (SHW 2147611484 1 eq_refl) (SHW 2147611484 4 eq_refl) (SHW 2147611485 1 eq_refl) (SHW 2147611486 1 eq_refl)
           (SHW 2147611487 1 eq_refl) (SHW 2147611488 4 eq_refl) (SHW 2147611492 4 eq_refl) (SHW 2147611496 4 eq_refl) (SHW 2147611500 4 eq_refl) (SHW 2147611504 4 eq_refl)
           (SHW 2147611508 4 eq_refl) (SHW 2147611512 8 eq_refl) (SHW 2147611520 8 eq_refl) (SHW 2147611528 8 eq_refl) (SHW 2147611536 8 eq_refl) (SHW 2147611544 8 eq_refl)
           (SHW 2147611552 8 eq_refl) (SHW 2147611560 8 eq_refl) (SHW 2147611568 8 eq_refl) (SHW 2147611576 8 eq_refl) (SHW 2147611584 8 eq_refl) (SHW 2147611592 8 eq_refl)
           (SHW 2147611600 8 eq_refl) (SHW 2147611608 8 eq_refl) (SHW 2147611616 8 eq_refl) (SHW 2147611624 8 eq_refl) (SHW 2147611632 8 eq_refl) (SHW 2147611640 8 eq_refl)
           (SHW 2147611648 4 eq_refl) (SHW 2147611648 8 eq_refl) (SHW 2147611652 4 eq_refl) (SHW 2147611656 4 eq_refl) (SHW 2147611656 8 eq_refl) (SHW 2147611660 4 eq_refl)
           (SHW 2147611664 4 eq_refl) (SHW 2147611664 8 eq_refl) (SHW 2147611668 4 eq_refl) (SHW 2147611672 1 eq_refl) (SHW 2147611672 4 eq_refl) (SHW 2147611673 1 eq_refl)
           (SHW 2147611674 1 eq_refl) (SHW 2147611675 1 eq_refl) TIDC HTr (XCC 0%nat 6888176 4 0 eq_refl) (XCC1 1%nat 6888211 0 eq_refl eq_refl)
           (XCC 2%nat 6887648 8 6887656 eq_refl) (XCC 3%nat 6887640 4 1 eq_refl) (XCC 4%nat 6887664 8 1139320 eq_refl) (XCC 5%nat 6887920 8 618908 eq_refl) (XCC 6%nat 6887636 4 0 eq_refl) (STC1 10%nat 1898080 0 eq_refl eq_refl)
           (XCC 7%nat 6887656 8 0 eq_refl) (STC1 3%nat 1286480 0 eq_refl eq_refl) (STC 0%nat 1273320 8 1273320 eq_refl) (STC 2%nat 1286400 8 1 eq_refl) (STC 4%nat 1290192 4 1 eq_refl) (STC 5%nat 1290352 8 0 eq_refl)
           (STC1 8%nat 1303704 1 eq_refl eq_refl) (STC 7%nat 1300408 8 2147450880 eq_refl) (DSC 1284832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143776)) ltac:(img_rd) eq_refl) (DSC 1284848 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1298460 1 eq_refl eq_refl) (DSC 1284848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 1897312 8 18446744073709551615 eq_refl) (STC 1%nat 1273832 8 1210200 eq_refl) (DSC 1284888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143872)) ltac:(img_rd) eq_refl) (DSC 1284912 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1284912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1284952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1284976 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1284976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl)
           (DSC 1285040 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1285104 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl) (DSC 1285168 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl)
           (DSC 1285232 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1285296 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1285360 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1285360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1285400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl)
           (DSC 1285424 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1285488 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1285552 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl)
           (DSC 1285616 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1285680 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1285744 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl)
           (DSC 1285808 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1285872 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1285936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145184)) ltac:(img_rd) eq_refl)
           (DSC 1286000 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1286000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1286040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1286064 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1286104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl) (DSC 1286128 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1286192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1286256 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1286296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1242944)) ltac:(img_rd) eq_refl) (DSC 1286320 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl) (DSC 1286320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1286360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6889608 8 0 eq_refl)
           (XCC 9%nat 1284776 8 1284544 eq_refl) (XCC 10%nat 1284684 4 4294967295 eq_refl) (XCC 11%nat 1284584 8 0 eq_refl) (XCC 12%nat 1284600 8 0 eq_refl) (XCC 13%nat 1284552 8 0 eq_refl) (XCC 14%nat 1284560 8 0 eq_refl)
           (XCC 15%nat 1284536 8 1284304 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend
           (XCC 16%nat 1284296 8 1284064 eq_refl) (XCC 17%nat 1284204 4 4294967295 eq_refl) (XCC 18%nat 1284104 8 6889624 eq_refl) (XCC 19%nat 1284120 8 6889624 eq_refl) (XCC 20%nat 1284072 8 0 eq_refl) (XCC 21%nat 1284080 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x1162cc) M R1 (Z_to_bv 64 0x115fdc) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x115fdc) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
