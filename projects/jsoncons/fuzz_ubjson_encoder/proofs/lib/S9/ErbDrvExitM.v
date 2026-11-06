(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Eb0DrvEntry Eb0Drv_defs Eb0DrvLib Eb0DrvRead Eb0DrvPiece Eb0DiagLoopK Eb0DrvStdio ErbDrvPrintfK ErbDrvPrintf1 ErbDrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require L5Defs L5KnA L5Core ArtMem EbrFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import Eb0DrvP_dpXmS9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6923248, 4, 0); (6923283, 1, 0); (6922720, 8, 6922728); (6922712, 4, 1); (6922736, 8, 1174352); (6922992, 8, 624400); (6922708, 4, 0); (6922728, 8, 0); (6924680, 8, 0); (1319832, 8, 1319600); (1319740, 4, 4294967295); (1319640, 8, 0); (1319656, 8, 0); (1319608, 8, 0); (1319616, 8, 0); (1319592, 8, 1319360); (1319352, 8, 1319120); (1319260, 4, 4294967295); (1319160, 8, 6924696); (1319176, 8, 6924696); (1319128, 8, 0); (1319136, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6791384) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x1423d0 <= i < 0x142a10 -> MV (Z_to_bv 64 i) = None).

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
    /\ (forall i, 65536 <= i < 1306624 -> MV (Z_to_bv 64 i) = None)
    /\ exitMA tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6791552 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x11eba4) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147468892 <=? a) && (a + n <=? 2147469204) || (2147615866 <=? a) && (a + n <=? 2147616066)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x1423d0 <=? a) && (a + Z.of_nat n <=? 0x142a10) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V HS64 HT64
           G2 G4 HSr HSa CWR CDF
           IMGc (WSG 1321536 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1321616 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1325488 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922704 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6922712 4%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6922720 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6923248 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl)
           (SHW 2147468924 1 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468929 1 eq_refl)
           (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 1 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 1 eq_refl) (SHW 2147468940 4 eq_refl)
           (SHW 2147468941 1 eq_refl) (SHW 2147468942 1 eq_refl) (SHW 2147468943 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl)
           (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl)
           (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468964 4 eq_refl)
           (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468968 4 eq_refl) (SHW 2147468969 1 eq_refl)
           (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 4 eq_refl) (SHW 2147468976 4 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468980 4 eq_refl)
           (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl)
           (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468988 4 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl)
           (SHW 2147468992 4 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468996 4 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469000 4 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 4 eq_refl)
           (SHW 2147469008 4 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469012 4 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl)
           (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl)
           (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl)
           (SHW 2147469032 1 eq_refl) (SHW 2147469032 4 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 4 eq_refl)
           (SHW 2147469040 1 eq_refl) (SHW 2147469040 4 eq_refl) (SHW 2147469041 1 eq_refl) (SHW 2147469042 1 eq_refl) (SHW 2147469043 1 eq_refl) (SHW 2147469044 1 eq_refl)
           (SHW 2147469044 4 eq_refl) (SHW 2147469045 1 eq_refl) (SHW 2147469046 1 eq_refl) (SHW 2147469047 1 eq_refl) (SHW 2147469048 4 eq_refl) (SHW 2147469052 1 eq_refl)
           (SHW 2147469052 4 eq_refl) (SHW 2147469053 1 eq_refl) (SHW 2147469054 1 eq_refl) (SHW 2147469055 1 eq_refl) (SHW 2147469056 1 eq_refl) (SHW 2147469056 4 eq_refl)
           (SHW 2147469057 1 eq_refl) (SHW 2147469058 1 eq_refl) (SHW 2147469059 1 eq_refl) (SHW 2147469060 4 eq_refl) (SHW 2147469064 1 eq_refl) (SHW 2147469064 4 eq_refl)
           (SHW 2147469065 1 eq_refl) (SHW 2147469066 1 eq_refl) (SHW 2147469067 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl)
           (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl)
           (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl)
           (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl)
           (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469104 1 eq_refl) (SHW 2147469105 1 eq_refl) (SHW 2147469106 1 eq_refl)
           (SHW 2147469107 1 eq_refl) (SHW 2147469108 1 eq_refl) (SHW 2147469109 1 eq_refl) (SHW 2147469110 1 eq_refl) (SHW 2147469111 1 eq_refl) (SHW 2147469112 1 eq_refl)
           (SHW 2147469113 1 eq_refl) (SHW 2147469114 1 eq_refl) (SHW 2147469115 1 eq_refl) (SHW 2147469116 1 eq_refl) (SHW 2147469117 1 eq_refl) (SHW 2147469118 1 eq_refl)
           (SHW 2147469119 1 eq_refl) (SHW 2147469120 1 eq_refl) (SHW 2147469121 1 eq_refl) (SHW 2147469122 1 eq_refl) (SHW 2147469123 1 eq_refl) (SHW 2147469124 1 eq_refl)
           (SHW 2147469124 4 eq_refl) (SHW 2147469125 1 eq_refl) (SHW 2147469126 1 eq_refl) (SHW 2147469127 1 eq_refl) (SHW 2147469128 4 eq_refl) (SHW 2147469132 1 eq_refl)
           (SHW 2147469132 4 eq_refl) (SHW 2147469133 1 eq_refl) (SHW 2147469134 1 eq_refl) (SHW 2147469135 1 eq_refl) (SHW 2147469180 1 eq_refl) (SHW 2147469180 4 eq_refl)
           (SHW 2147469181 1 eq_refl) (SHW 2147469182 1 eq_refl) (SHW 2147469183 1 eq_refl) (SHW 2147469184 4 eq_refl) (SHW 2147469188 1 eq_refl) (SHW 2147469188 4 eq_refl)
           (SHW 2147469189 1 eq_refl) (SHW 2147469190 1 eq_refl) (SHW 2147469191 1 eq_refl) (SHW 2147469192 1 eq_refl) (SHW 2147469192 4 eq_refl) (SHW 2147469193 1 eq_refl)
           (SHW 2147469194 1 eq_refl) (SHW 2147469195 1 eq_refl) (SHW 2147469196 4 eq_refl) (SHW 2147469200 1 eq_refl) (SHW 2147469200 4 eq_refl) (SHW 2147469201 1 eq_refl)
           (SHW 2147469202 1 eq_refl) (SHW 2147469203 1 eq_refl) (SHW 2147615866 1 eq_refl) (SHW 2147615866 4 eq_refl) (SHW 2147615867 1 eq_refl) (SHW 2147615868 1 eq_refl)
           (SHW 2147615869 1 eq_refl) (SHW 2147615870 4 eq_refl) (SHW 2147615874 4 eq_refl) (SHW 2147615878 4 eq_refl) (SHW 2147615882 4 eq_refl) (SHW 2147615886 4 eq_refl)
           (SHW 2147615890 4 eq_refl) (SHW 2147615890 8 eq_refl) (SHW 2147615898 8 eq_refl) (SHW 2147615906 8 eq_refl) (SHW 2147615914 8 eq_refl) (SHW 2147615922 8 eq_refl)
           (SHW 2147615930 8 eq_refl) (SHW 2147615938 8 eq_refl) (SHW 2147615946 8 eq_refl) (SHW 2147615954 8 eq_refl) (SHW 2147615962 8 eq_refl) (SHW 2147615970 8 eq_refl)
           (SHW 2147615978 8 eq_refl) (SHW 2147615986 8 eq_refl) (SHW 2147615994 8 eq_refl) (SHW 2147616002 8 eq_refl) (SHW 2147616010 8 eq_refl) (SHW 2147616018 8 eq_refl)
           (SHW 2147616026 8 eq_refl) (SHW 2147616034 8 eq_refl) (SHW 2147616038 4 eq_refl) (SHW 2147616042 4 eq_refl) (SHW 2147616042 8 eq_refl) (SHW 2147616046 4 eq_refl)
           (SHW 2147616050 4 eq_refl) (SHW 2147616054 4 eq_refl) (SHW 2147616058 4 eq_refl) (SHW 2147616062 1 eq_refl) (SHW 2147616062 4 eq_refl) (SHW 2147616063 1 eq_refl)
           (SHW 2147616064 1 eq_refl) (SHW 2147616065 1 eq_refl) TIDC HTr (XCC 0%nat 6923248 4 0 eq_refl) (XCC1 1%nat 6923283 0 eq_refl eq_refl)
           (XCC 2%nat 6922720 8 6922728 eq_refl) (XCC 3%nat 6922712 4 1 eq_refl) (XCC 4%nat 6922736 8 1174352 eq_refl) (XCC 5%nat 6922992 8 624400 eq_refl) (XCC 6%nat 6922708 4 0 eq_refl) (STC1 10%nat 1933216 0 eq_refl eq_refl)
           (XCC 7%nat 6922728 8 0 eq_refl) (STC1 3%nat 1321616 0 eq_refl eq_refl) (STC 0%nat 1308376 8 1308376 eq_refl) (STC 2%nat 1321536 8 1 eq_refl) (STC 4%nat 1325328 4 1 eq_refl) (STC 5%nat 1325488 8 0 eq_refl)
           (STC1 8%nat 1338840 1 eq_refl eq_refl) (STC 7%nat 1335544 8 2147450880 eq_refl) (DSC 1319888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1319904 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1333596 1 eq_refl eq_refl) (DSC 1319904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (STC 9%nat 1932448 8 18446744073709551615 eq_refl) (STC 1%nat 1308888 8 1245236 eq_refl) (DSC 1319944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1319952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1319968 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1319968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144384)) ltac:(img_rd) eq_refl) (DSC 1320032 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl)
           (DSC 1320096 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1320136 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144480)) ltac:(img_rd) eq_refl) (DSC 1320160 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1320200 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1320224 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320264 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
           (DSC 1320288 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1320352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1320416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl)
           (DSC 1320480 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1320544 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl)
           (DSC 1320584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1320608 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145312)) ltac:(img_rd) eq_refl)
           (DSC 1320672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1320712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145408)) ltac:(img_rd) eq_refl) (DSC 1320736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1320736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1320776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1320800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1320800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1320840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1320864 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1320864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1320904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1320928 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1320968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1320976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145792)) ltac:(img_rd) eq_refl) (DSC 1320992 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1320992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145824)) ltac:(img_rd) eq_refl)
           (DSC 1321056 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145856)) ltac:(img_rd) eq_refl) (DSC 1321120 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1321160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145888)) ltac:(img_rd) eq_refl) (DSC 1321184 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145920)) ltac:(img_rd) eq_refl)
           (DSC 1321248 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1321248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1321288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145952)) ltac:(img_rd) eq_refl) (DSC 1321312 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1321352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146400)) ltac:(img_rd) eq_refl) (DSC 1321376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1321424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 146496)) ltac:(img_rd) eq_refl)
           (DSC 1321440 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1321440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1321480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6924680 8 0 eq_refl) (XCC 9%nat 1319832 8 1319600 eq_refl) (XCC 10%nat 1319740 4 4294967295 eq_refl)
           (XCC 11%nat 1319640 8 0 eq_refl) (XCC 12%nat 1319656 8 0 eq_refl) (XCC 13%nat 1319608 8 0 eq_refl) (XCC 14%nat 1319616 8 0 eq_refl) (XCC 15%nat 1319592 8 1319360 eq_refl) SOlock
           SOwpos SOwbase SOrpos SOrend (XCC 16%nat 1319352 8 1319120 eq_refl) (XCC 17%nat 1319260 4 4294967295 eq_refl)
           (XCC 18%nat 1319160 8 6924696 eq_refl) (XCC 19%nat 1319176 8 6924696 eq_refl) (XCC 20%nat 1319128 8 0 eq_refl) (XCC 21%nat 1319136 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x11eba4) M R1 (Z_to_bv 64 0x11e8b4) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x11e8b4) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
