(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b Ba0DrvExit_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpXm_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 1); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 6898968); (1293568, 8, 6898968); (1293520, 8, 0); (1293528, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6765656) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x13bfc0 <= i < 0x13c580 -> MV (Z_to_bv 64 i) = None).

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
    /\ (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None)
    /\ exitMA tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bfc0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
           G2 G4 HSr HSa CWR CDF
           IMGc (WSG 1295744 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1295824 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1299696 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896976 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896984 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6896992 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6897520 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl)
           (SHW 2147468868 1 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 1 eq_refl) (SHW 2147468872 4 eq_refl)
           (SHW 2147468873 1 eq_refl) (SHW 2147468874 1 eq_refl) (SHW 2147468875 1 eq_refl) (SHW 2147468876 4 eq_refl) (SHW 2147468880 1 eq_refl) (SHW 2147468880 4 eq_refl)
           (SHW 2147468881 1 eq_refl) (SHW 2147468882 1 eq_refl) (SHW 2147468883 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl)
           (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl)
           (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl)
           (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468913 1 eq_refl) (SHW 2147468914 1 eq_refl) (SHW 2147468915 1 eq_refl)
           (SHW 2147468916 4 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl)
           (SHW 2147468924 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 4 eq_refl)
           (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl)
           (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468944 4 eq_refl)
           (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 1 eq_refl)
           (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl)
           (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl)
           (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl)
           (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl)
           (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl)
           (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl)
           (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl)
           (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl)
           (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 4 eq_refl)
           (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl)
           (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl)
           (SHW 2147469039 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl)
           (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl)
           (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl)
           (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl)
           (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl) (SHW 2147469100 4 eq_refl) (SHW 2147469101 1 eq_refl) (SHW 2147469102 1 eq_refl)
           (SHW 2147469103 1 eq_refl) 
           
           (SHW 2147612664 184 eq_refl) (SHW 2147612664 1 eq_refl) (SHW 2147612664 4 eq_refl) (SHW 2147612665 1 eq_refl) (SHW 2147612666 1 eq_refl)
           (SHW 2147612667 1 eq_refl) (SHW 2147612668 4 eq_refl) (SHW 2147612672 4 eq_refl) (SHW 2147612676 4 eq_refl) (SHW 2147612680 4 eq_refl) (SHW 2147612684 4 eq_refl)
           (SHW 2147612688 4 eq_refl) (SHW 2147612692 8 eq_refl) (SHW 2147612700 8 eq_refl) (SHW 2147612708 8 eq_refl) (SHW 2147612716 8 eq_refl) (SHW 2147612724 8 eq_refl)
           (SHW 2147612732 8 eq_refl) (SHW 2147612740 8 eq_refl) (SHW 2147612748 8 eq_refl) (SHW 2147612756 8 eq_refl) (SHW 2147612764 8 eq_refl) (SHW 2147612772 8 eq_refl)
           (SHW 2147612780 8 eq_refl) (SHW 2147612788 8 eq_refl) (SHW 2147612796 8 eq_refl) (SHW 2147612804 8 eq_refl) (SHW 2147612812 8 eq_refl) (SHW 2147612820 8 eq_refl)
           (SHW 2147612828 4 eq_refl) (SHW 2147612828 8 eq_refl) (SHW 2147612832 4 eq_refl) (SHW 2147612836 4 eq_refl) (SHW 2147612836 8 eq_refl) (SHW 2147612840 4 eq_refl)
           (SHW 2147612844 4 eq_refl) (SHW 2147612844 8 eq_refl) 
           TIDC HTr (XCC 0%nat 6897520 4 0 eq_refl) (XCC1 1%nat 6897555 0 eq_refl eq_refl)
           (XCC 2%nat 6896992 8 6897000 eq_refl) (XCC 3%nat 6896984 4 1 eq_refl) (XCC 4%nat 6897008 8 1148964 eq_refl) (XCC 5%nat 6897264 8 619876 eq_refl) (XCC 6%nat 6896980 4 0 eq_refl) (STC1 10%nat 1907424 0 eq_refl eq_refl)
           (XCC 7%nat 6897000 8 0 eq_refl) (STC1 3%nat 1295824 0 eq_refl eq_refl) (STC 0%nat 1282768 8 1282768 eq_refl) (STC 2%nat 1295744 8 1 eq_refl) (STC 4%nat 1299536 4 1 eq_refl) (STC 5%nat 1299696 8 0 eq_refl)
           (STC1 8%nat 1313048 1 eq_refl eq_refl) (STC 7%nat 1309752 8 2147450880 eq_refl) (DSC 1294272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1294288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1307804 1 eq_refl eq_refl) (DSC 1294288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 1906656 8 18446744073709551615 eq_refl) (STC 1%nat 1283280 8 1219844 eq_refl) (DSC 1294328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1294352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1294392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143936)) ltac:(img_rd) eq_refl) (DSC 1294416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl)
           (DSC 1294480 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144160)) ltac:(img_rd) eq_refl) (DSC 1294544 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1294584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1294608 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144256)) ltac:(img_rd) eq_refl)
           (DSC 1294672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1294736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1294800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1294800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1294840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl)
           (DSC 1294864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1294928 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1294968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144736)) ltac:(img_rd) eq_refl) (DSC 1294992 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl)
           (DSC 1295056 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1295120 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl) (DSC 1295184 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144992)) ltac:(img_rd) eq_refl)
           (DSC 1295248 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1295312 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145120)) ltac:(img_rd) eq_refl) (DSC 1295376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl)
           (DSC 1295440 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1295504 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1295544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1295568 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl)
           (DSC 1295632 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1295696 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1295736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6898952 8 0 eq_refl)
           (XCC 9%nat 1294224 8 1293992 eq_refl) (XCC 10%nat 1294132 4 4294967295 eq_refl) (XCC 11%nat 1294032 8 0 eq_refl) (XCC 12%nat 1294048 8 0 eq_refl) (XCC 13%nat 1294000 8 0 eq_refl) (XCC 14%nat 1294008 8 0 eq_refl)
           (XCC 15%nat 1293984 8 1293752 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend
           (XCC 16%nat 1293744 8 1293512 eq_refl) (XCC 17%nat 1293652 4 4294967295 eq_refl) (XCC 18%nat 1293552 8 6898968 eq_refl) (XCC 19%nat 1293568 8 6898968 eq_refl) (XCC 20%nat 1293520 8 0 eq_refl) (XCC 21%nat 1293528 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x118588) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x118588) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
