(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ea0DrvEntry Ea0Drv_defs Ea0DrvLib Ea0DrvRead Ea0DrvPiece Ea0DiagLoopK Ea0DrvStdio EraDrvPrintfK EraDrvPrintf1 EraDrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require L5Defs L5KnA L5Core ArtMem EarFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import Ea0DrvP_dpXmS8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6905072, 4, 0); (6905107, 1, 0); (6904544, 8, 6904552); (6904536, 4, 1); (6904560, 8, 1156008); (6904816, 8, 622312); (6904532, 4, 0); (6904552, 8, 0); (6906504, 8, 0); (1301640, 8, 1301408); (1301548, 4, 4294967295); (1301448, 8, 0); (1301464, 8, 0); (1301416, 8, 0); (1301424, 8, 0); (1301400, 8, 1301168); (1301160, 8, 1300928); (1301068, 4, 4294967295); (1300968, 8, 6906520); (1300984, 8, 6906520); (1300936, 8, 0); (1300944, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6773208) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x13dcc0 <= i < 0x13e340 -> MV (Z_to_bv 64 i) = None).

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
    /\ (forall i, 65536 <= i < 1286144 -> MV (Z_to_bv 64 i) = None)
    /\ exitMA tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6773376 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11a3fc) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147468860 <=? a) && (a + n <=? 2147469172) || (2147608356 <=? a) && (a + n <=? 2147608376) || (2147613592 <=? a) && (a + n <=? 2147613800)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13dcc0 <=? a) && (a + Z.of_nat n <=? 0x13e340) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
           G2 G4 HSr HSa CWR CDF
           IMGc (WSG 1303360 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1303440 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1307312 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6904528 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6904536 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6904544 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6905072 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468860 1 eq_refl) (SHW 2147468861 1 eq_refl) (SHW 2147468862 1 eq_refl) (SHW 2147468863 1 eq_refl)
           (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl)
           (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl)
           (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl)
           (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl)
           (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl)
           (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl)
           (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl)
           (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl)
           (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl)
           (SHW 2147468955 1 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
           (SHW 2147468960 4 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl)
           (SHW 2147468968 1 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl)
           (SHW 2147468976 4 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl)
           (SHW 2147468984 1 eq_refl) (SHW 2147468984 4 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 4 eq_refl)
           (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl)
           (SHW 2147469008 1 eq_refl) (SHW 2147469008 4 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl)
           (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469020 1 eq_refl)
           (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl)
           (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl)
           (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469036 4 eq_refl) (SHW 2147469037 1 eq_refl)
           (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469044 4 eq_refl) (SHW 2147469048 1 eq_refl) (SHW 2147469048 4 eq_refl)
           (SHW 2147469049 1 eq_refl) (SHW 2147469050 1 eq_refl) (SHW 2147469051 1 eq_refl) (SHW 2147469052 1 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl)
           (SHW 2147469055 1 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 1 eq_refl)
           (SHW 2147469061 1 eq_refl) (SHW 2147469062 1 eq_refl) (SHW 2147469063 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl)
           (SHW 2147469075 1 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl)
           (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl)
           (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl)
           (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl)
           (SHW 2147469100 4 eq_refl) (SHW 2147469101 1 eq_refl) (SHW 2147469102 1 eq_refl) (SHW 2147469103 1 eq_refl) (SHW 2147469148 1 eq_refl) (SHW 2147469148 4 eq_refl)
           (SHW 2147469149 1 eq_refl) (SHW 2147469150 1 eq_refl) (SHW 2147469151 1 eq_refl) (SHW 2147469152 4 eq_refl) (SHW 2147469156 1 eq_refl) (SHW 2147469156 4 eq_refl)
           (SHW 2147469157 1 eq_refl) (SHW 2147469158 1 eq_refl) (SHW 2147469159 1 eq_refl) (SHW 2147469160 1 eq_refl) (SHW 2147469160 4 eq_refl) (SHW 2147469161 1 eq_refl)
           (SHW 2147469162 1 eq_refl) (SHW 2147469163 1 eq_refl) (SHW 2147469164 4 eq_refl) (SHW 2147469168 1 eq_refl) (SHW 2147469168 4 eq_refl) (SHW 2147469169 1 eq_refl)
           (SHW 2147469170 1 eq_refl) (SHW 2147469171 1 eq_refl) (SHW 2147608356 1 eq_refl) (SHW 2147608356 4 eq_refl) (SHW 2147608357 1 eq_refl) (SHW 2147608358 1 eq_refl)
           (SHW 2147608359 1 eq_refl) (SHW 2147608360 4 eq_refl) (SHW 2147608364 4 eq_refl) (SHW 2147608368 4 eq_refl) (SHW 2147608372 1 eq_refl) (SHW 2147608372 4 eq_refl)
           (SHW 2147608373 1 eq_refl) (SHW 2147608374 1 eq_refl) (SHW 2147608375 1 eq_refl) (SHW 2147613592 1 eq_refl) (SHW 2147613592 4 eq_refl) (SHW 2147613593 1 eq_refl)
           (SHW 2147613594 1 eq_refl) (SHW 2147613595 1 eq_refl) (SHW 2147613596 4 eq_refl) (SHW 2147613600 4 eq_refl) (SHW 2147613604 4 eq_refl) (SHW 2147613608 4 eq_refl)
           (SHW 2147613612 4 eq_refl) (SHW 2147613616 4 eq_refl) (SHW 2147613620 8 eq_refl) (SHW 2147613628 8 eq_refl) (SHW 2147613636 8 eq_refl) (SHW 2147613644 8 eq_refl)
           (SHW 2147613652 8 eq_refl) (SHW 2147613660 8 eq_refl) (SHW 2147613668 8 eq_refl) (SHW 2147613676 8 eq_refl) (SHW 2147613684 8 eq_refl) (SHW 2147613692 8 eq_refl)
           (SHW 2147613700 8 eq_refl) (SHW 2147613708 8 eq_refl) (SHW 2147613716 8 eq_refl) (SHW 2147613724 8 eq_refl) (SHW 2147613732 8 eq_refl) (SHW 2147613740 8 eq_refl)
           (SHW 2147613748 8 eq_refl) (SHW 2147613756 8 eq_refl) (SHW 2147613764 8 eq_refl) (SHW 2147613772 4 eq_refl) (SHW 2147613772 8 eq_refl) (SHW 2147613776 4 eq_refl)
           (SHW 2147613780 4 eq_refl) (SHW 2147613784 4 eq_refl) (SHW 2147613788 4 eq_refl) (SHW 2147613792 4 eq_refl) (SHW 2147613796 1 eq_refl) (SHW 2147613796 4 eq_refl)
           (SHW 2147613797 1 eq_refl) (SHW 2147613798 1 eq_refl) (SHW 2147613799 1 eq_refl) TIDC HTr (XCC 0%nat 6905072 4 0 eq_refl)
           (XCC1 1%nat 6905107 0 eq_refl eq_refl) (XCC 2%nat 6904544 8 6904552 eq_refl) (XCC 3%nat 6904536 4 1 eq_refl) (XCC 4%nat 6904560 8 1156008 eq_refl) (XCC 5%nat 6904816 8 622312 eq_refl) (XCC 6%nat 6904532 4 0 eq_refl)
           (STC1 10%nat 1915040 0 eq_refl eq_refl) (XCC 7%nat 6904552 8 0 eq_refl) (STC1 3%nat 1303440 0 eq_refl eq_refl) (STC 0%nat 1290184 8 1290184 eq_refl) (STC 2%nat 1303360 8 1 eq_refl) (STC 4%nat 1307152 4 1 eq_refl)
           (STC 5%nat 1307312 8 0 eq_refl) (STC1 8%nat 1320664 1 eq_refl eq_refl) (STC 7%nat 1317368 8 2147450880 eq_refl) (DSC 1301696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143840)) ltac:(img_rd) eq_refl) (DSC 1301712 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1315420 1 eq_refl eq_refl)
           (DSC 1301712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1914272 8 18446744073709551615 eq_refl) (STC 1%nat 1290696 8 1226892 eq_refl) (DSC 1301752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1301760 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1301776 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1301776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1301816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1301824 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1301840 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1301840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1301880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1301888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl) (DSC 1301904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1301904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1301944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1301952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1301968 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1301968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1302008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1302032 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1302032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1302072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1302080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1302096 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1302096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1302136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1302160 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1302160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1302200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144608)) ltac:(img_rd) eq_refl) (DSC 1302224 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1302224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1302264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1302272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1302288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1302288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1302328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1302352 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1302352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1302392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1302416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1302416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1302456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1302464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1302480 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1302480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1302520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145152)) ltac:(img_rd) eq_refl) (DSC 1302544 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1302544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1302584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145248)) ltac:(img_rd) eq_refl) (DSC 1302608 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1302608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1302648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1302656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145376)) ltac:(img_rd) eq_refl) (DSC 1302672 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1302672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1302712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145440)) ltac:(img_rd) eq_refl) (DSC 1302736 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1302736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1302776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1302800 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1302800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1302840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1302848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145568)) ltac:(img_rd) eq_refl) (DSC 1302864 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1302864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1302904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl) (DSC 1302928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1302928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1302968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1302976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1302992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1302992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1303032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1303040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1303056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1303056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1303096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1303104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1303120 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1303120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1303160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1303168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146144)) ltac:(img_rd) eq_refl) (DSC 1303184 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1303184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1303224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1303232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146240)) ltac:(img_rd) eq_refl) (DSC 1303248 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1303248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1303288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1303296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1259808)) ltac:(img_rd) eq_refl) (DSC 1303312 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl)
           (DSC 1303312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1303352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6906504 8 0 eq_refl) (XCC 9%nat 1301640 8 1301408 eq_refl) (XCC 10%nat 1301548 4 4294967295 eq_refl) (XCC 11%nat 1301448 8 0 eq_refl)
           (XCC 12%nat 1301464 8 0 eq_refl) (XCC 13%nat 1301416 8 0 eq_refl) (XCC 14%nat 1301424 8 0 eq_refl) (XCC 15%nat 1301400 8 1301168 eq_refl) SOlock SOwpos
           SOwbase SOrpos SOrend (XCC 16%nat 1301160 8 1300928 eq_refl) (XCC 17%nat 1301068 4 4294967295 eq_refl) (XCC 18%nat 1300968 8 6906520 eq_refl)
           (XCC 19%nat 1300984 8 6906520 eq_refl) (XCC 20%nat 1300936 8 0 eq_refl) (XCC 21%nat 1300944 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11a3fc) M R1 (Z_to_bv 64 0x11a10c) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11a10c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
