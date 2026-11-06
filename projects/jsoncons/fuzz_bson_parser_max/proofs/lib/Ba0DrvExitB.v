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
  HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA Ba0DrvEntry Ba0Drv_defs Ba0DrvLib Ba0DrvRead Ba0DrvPiece Ba0DiagLoopK Ba0DrvStdio Ba0DrvPrintfK Ba0DrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem BatFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import Ba0DrvExit Ba0ExitCells
  Ba0DrvP_dpXB Ba0DrvP_dpX2B_pre Ba0DrvP_dpX3B_pre Ba0DrvP_dpX4B_pre Ba0DrvP_dpXd_2 Ba0DrvP_dpXd_3 Ba0DrvP_dpXd_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XC_CELLS : list (Z * Z * Z) :=
  [(6888176, 4, 0); (6888211, 1, 0); (6887648, 8, 6887656); (6887640, 4, 2); (6887664, 8, 1139320); (6887920, 8, 618908); (6887636, 4, 0); (6887656, 8, 0); (6889608, 8, 0); (1284776, 8, 1284544); (1284684, 4, 4294967295); (1284584, 8, 0); (1284600, 8, 0); (1284552, 8, 0); (1284560, 8, 0); (1284536, 8, 1284304); (1284296, 8, 1284064); (1284204, 4, 4294967295); (1284104, 8, 0); (1284120, 8, 0); (1284072, 8, 0); (1284080, 8, 0); (6887672, 8, 1139320); (6887928, 8, 686948); (6749716, 1, 0)].
(* [comment removed for export] *)
Definition XC_CELLS_E : list (Z * Z * Z) :=
  [(6888176, 4, 0); (6888211, 1, 0); (6887648, 8, 6887656); (6887640, 4, 1); (6887664, 8, 1139320); (6887920, 8, 618908); (6887636, 4, 0); (6887656, 8, 0); (6889608, 8, 0); (1284776, 8, 1284544); (1284684, 4, 4294967295); (1284584, 8, 0); (1284600, 8, 0); (1284552, 8, 0); (1284560, 8, 0); (1284536, 8, 1284304); (1284296, 8, 1284064); (1284204, 4, 4294967295); (1284104, 8, 0); (1284120, 8, 0); (1284072, 8, 0); (1284080, 8, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

(* [comment removed for export] *)
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6756312) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x139ae0 <= i < 0x13a0e0 -> MV (Z_to_bv 64 i) = None).

Definition exitE (tid : Z) (MV : word -> option byte) : Prop :=   (* [comment removed for export] *)
  cells_at MV XC_CELLS_E
  /\ rdn ASEGS MV (Z_to_bv 64 6756312) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x139ae0 <= i < 0x13a0e0 -> MV (Z_to_bv 64 i) = None).


Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x115fdc) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msteps_vis_fx : forall (scfg : SpuriousCfg) (H : word -> bool) (A : list (Z * Z)) (fx fx' : PropExec.FPState) R (pc : word) M R' (pc' : word) MV' (model : Model) T,
  lzinv ASEGS H A model ->
  msteps ASEGS (@mkst fx R pc (mrestrict H M) (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) ->
  (forall M' (model' : Model), MInv A model' -> same_but_materialized model model' -> mrestrict H M' = MV' ->
      srealizes ASEGS scfg (mkCfg (@mkst fx' R' pc' M' (seg_rom ASEGS)) model') T) ->
  srealizes ASEGS scfg (mkCfg (@mkst fx R pc M (seg_rom ASEGS)) model) T.
Proof.
  intros scfg H A fx fx' R pc M R' pc' MV' model T (HH & HL & HA & HM & Hh) MS KONT.
  apply (srz_msteps_restricted_T ASEGS scfg H HH asegs_wx A (@mkst fx R pc M (seg_rom ASEGS)) (@mkst fx' R' pc' MV' (seg_rom ASEGS)) model T HL HA HM Hh MS).
  intros model1 MI1 SBM HC.
  change (unrestrict H (ms_mem (@mkst fx R pc M (seg_rom ASEGS))) (@mkst fx' R' pc' MV' (seg_rom ASEGS))) with (@mkst fx' R' pc' (munrestrict H M MV') (seg_rom ASEGS)).
  apply (KONT _ model1 MI1 SBM). apply As0DrvKitA.mrestrict_munrestrict. intros a Ha. exact (HC a Ha).
Qed.

(* [comment removed for export] *)
Definition XC_CELLS_B : list (Z * Z * Z) :=
  [(6888176, 4, 0); (6888211, 1, 0); (6887648, 8, 6887656); (6887640, 4, 4); (6887664, 8, 1139320); (6887920, 8, 618908); (6887636, 4, 0); (6887656, 8, 0); (6889608, 8, 0); (1284776, 8, 1284544); (1284684, 4, 4294967295); (1284584, 8, 0); (1284600, 8, 0); (1284552, 8, 0); (1284560, 8, 0); (1284536, 8, 1284304); (1284296, 8, 1284064); (1284204, 4, 4294967295); (1284104, 8, 0); (1284120, 8, 0); (1284072, 8, 0); (1284080, 8, 0); (6887672, 8, 1139320); (6887928, 8, 686948); (6749716, 1, 0); (6887680, 8, 863096); (6887688, 8, 448212); (6887936, 8, 1283856); (6887944, 8, 0)].
Definition exitB (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_B
  /\ rdn ASEGS MV (Z_to_bv 64 6756312) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x139ae0 <= i < 0x13a0e0 -> MV (Z_to_bv 64 i) = None).


Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Exit.
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
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation rom := (seg_rom ASEGS).
  Local Abbreviation ex_cell_vis := (@Ba0DrvExit.ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0).
  Local Abbreviation sh_writable := (@Ba0DrvExit.sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0).
  Local Abbreviation wsg_writable := (@Ba0DrvExit.wsg_writable sp0 Hsp M0).

  Definition exit_preB (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1269760 -> MV (Z_to_bv 64 i) = None)
    /\ exitB tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0B : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1137416 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6756480 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1162cc) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXB.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468852 <=? a) && (a + n <=? 2147469100) || (2147606248 <=? a) && (a + n <=? 2147606268) || (2147611484 <=? a) && (a + n <=? 2147611676)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x139ae0 <=? a) && (a + Z.of_nat n <=? 0x13a0e0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXB.dpXB_conc fx R MV V HS64 HT64
           G1 G2 G4 HSr HSa CWR
           CDF IMGc (WSG 1286400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286480 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1290352 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887632 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6887640 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887648 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6888176 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468852 1 eq_refl) (SHW 2147468853 1 eq_refl) (SHW 2147468854 1 eq_refl)
           (SHW 2147468855 1 eq_refl) (SHW 2147468864 1 eq_refl) (SHW 2147468865 1 eq_refl) (SHW 2147468866 1 eq_refl) (SHW 2147468867 1 eq_refl) (SHW 2147468868 1 eq_refl)
           (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 4 eq_refl) (SHW 2147468876 1 eq_refl)
           (SHW 2147468876 4 eq_refl) (SHW 2147468877 1 eq_refl) (SHW 2147468878 1 eq_refl) (SHW 2147468879 1 eq_refl) (SHW 2147468892 1 eq_refl) (SHW 2147468893 1 eq_refl)
           (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl)
           (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl)
           (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl) (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl)
           (SHW 2147468911 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468917 1 eq_refl) (SHW 2147468918 1 eq_refl)
           (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl)
           (SHW 2147468924 4 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl) (SHW 2147468931 1 eq_refl)
           (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl) (SHW 2147468936 4 eq_refl)
           (SHW 2147468940 4 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl) (SHW 2147468947 1 eq_refl)
           (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl) (SHW 2147468952 4 eq_refl)
           (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl) (SHW 2147468960 1 eq_refl)
           (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl)
           (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl)
           (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl)
           (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl)
           (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl)
           (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl)
           (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl)
           (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl)
           (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl)
           (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl)
           (SHW 2147469020 4 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl) (SHW 2147469027 1 eq_refl)
           (SHW 2147469028 1 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl)
           (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl) (SHW 2147469070 1 eq_refl)
           (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469077 1 eq_refl) (SHW 2147469078 1 eq_refl)
           (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl)
           (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469088 4 eq_refl) (SHW 2147469089 1 eq_refl)
           (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469096 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469097 1 eq_refl)
           (SHW 2147469098 1 eq_refl) (SHW 2147469099 1 eq_refl) (SHW 2147606248 1 eq_refl) (SHW 2147606248 4 eq_refl) (SHW 2147606249 1 eq_refl) (SHW 2147606250 1 eq_refl)
           (SHW 2147606251 1 eq_refl) (SHW 2147606252 4 eq_refl) (SHW 2147606256 4 eq_refl) (SHW 2147606260 4 eq_refl) (SHW 2147606264 1 eq_refl) (SHW 2147606264 4 eq_refl)
           (SHW 2147606265 1 eq_refl) (SHW 2147606266 1 eq_refl) (SHW 2147606267 1 eq_refl) (SHW 2147611484 1 eq_refl) (SHW 2147611484 4 eq_refl) (SHW 2147611485 1 eq_refl)
           (SHW 2147611486 1 eq_refl) (SHW 2147611487 1 eq_refl) (SHW 2147611488 4 eq_refl) (SHW 2147611492 4 eq_refl) (SHW 2147611496 4 eq_refl) (SHW 2147611500 4 eq_refl)
           (SHW 2147611504 4 eq_refl) (SHW 2147611508 4 eq_refl) (SHW 2147611512 8 eq_refl) (SHW 2147611520 8 eq_refl) (SHW 2147611528 8 eq_refl) (SHW 2147611536 8 eq_refl)
           (SHW 2147611544 8 eq_refl) (SHW 2147611552 8 eq_refl) (SHW 2147611560 8 eq_refl) (SHW 2147611568 8 eq_refl) (SHW 2147611576 8 eq_refl) (SHW 2147611584 8 eq_refl)
           (SHW 2147611592 8 eq_refl) (SHW 2147611600 8 eq_refl) (SHW 2147611608 8 eq_refl) (SHW 2147611616 8 eq_refl) (SHW 2147611624 8 eq_refl) (SHW 2147611632 8 eq_refl)
           (SHW 2147611640 8 eq_refl) (SHW 2147611648 4 eq_refl) (SHW 2147611648 8 eq_refl) (SHW 2147611652 4 eq_refl) (SHW 2147611656 4 eq_refl) (SHW 2147611656 8 eq_refl)
           (SHW 2147611660 4 eq_refl) (SHW 2147611664 4 eq_refl) (SHW 2147611664 8 eq_refl) (SHW 2147611668 4 eq_refl) (SHW 2147611672 1 eq_refl) (SHW 2147611672 4 eq_refl)
           (SHW 2147611673 1 eq_refl) (SHW 2147611674 1 eq_refl) (SHW 2147611675 1 eq_refl) TIDC HTr (XCC 0%nat 6888176 4 0 eq_refl)
           (XCC1 1%nat 6888211 0 eq_refl eq_refl) (XCC 2%nat 6887648 8 6887656 eq_refl) (XCC 3%nat 6887640 4 4 eq_refl) (XCC 26%nat 6887688 8 448212 eq_refl) (XCC 28%nat 6887944 8 0 eq_refl) (XCC 6%nat 6887636 4 0 eq_refl)
           (STC1 11%nat 1290196 0 eq_refl eq_refl) (XCC 25%nat 6887680 8 863096 eq_refl) (XCC 27%nat 6887936 8 1283856 eq_refl) (XCC 22%nat 6887672 8 1139320 eq_refl) (XCC 23%nat 6887928 8 686948 eq_refl) (XCC1 24%nat 6749716 0 eq_refl eq_refl)
           (XCC 4%nat 6887664 8 1139320 eq_refl) (XCC 5%nat 6887920 8 618908 eq_refl) (STC1 10%nat 1898080 0 eq_refl eq_refl) (XCC 7%nat 6887656 8 0 eq_refl) (STC1 3%nat 1286480 0 eq_refl eq_refl) (STC 0%nat 1273320 8 1273320 eq_refl)
           (STC 2%nat 1286400 8 1 eq_refl) (STC 4%nat 1290192 4 1 eq_refl) (STC 5%nat 1290352 8 0 eq_refl) (STC1 8%nat 1303704 1 eq_refl eq_refl) (STC 7%nat 1300408 8 2147450880 eq_refl) (DSC 1284832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143776)) ltac:(img_rd) eq_refl)
           (DSC 1284848 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1298460 1 eq_refl eq_refl) (DSC 1284848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1897312 8 18446744073709551615 eq_refl) (STC 1%nat 1273832 8 1210200 eq_refl) (DSC 1284888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1284896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143872)) ltac:(img_rd) eq_refl) (DSC 1284912 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1284912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1284952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1284976 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1284976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1285040 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1285088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1285104 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl) (DSC 1285168 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1285168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1285232 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1285280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1285296 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl) (DSC 1285360 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1285360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1285400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl) (DSC 1285424 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1285472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1285488 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl) (DSC 1285552 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1285552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1285616 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1285664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1285680 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl) (DSC 1285744 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1285744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1285808 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1285856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1285872 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl) (DSC 1285936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1285936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145184)) ltac:(img_rd) eq_refl) (DSC 1286000 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1286000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1286040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1286048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1286064 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl) (DSC 1286128 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1286128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1286192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1286240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1286256 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1242944)) ltac:(img_rd) eq_refl) (DSC 1286320 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl)
           (DSC 1286320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1286360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6889608 8 0 eq_refl) (XCC 9%nat 1284776 8 1284544 eq_refl) (XCC 10%nat 1284684 4 4294967295 eq_refl) (XCC 11%nat 1284584 8 0 eq_refl)
           (XCC 12%nat 1284600 8 0 eq_refl) (XCC 13%nat 1284552 8 0 eq_refl) (XCC 14%nat 1284560 8 0 eq_refl) (XCC 15%nat 1284536 8 1284304 eq_refl) SOlock SOwpos
           SOwbase SOrpos SOrend (XCC 16%nat 1284296 8 1284064 eq_refl) (XCC 17%nat 1284204 4 4294967295 eq_refl) (XCC 18%nat 1284104 8 0 eq_refl)
           (XCC 19%nat 1284120 8 0 eq_refl) (XCC 20%nat 1284072 8 0 eq_refl) (XCC 21%nat 1284080 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x1162cc) M R1 (Z_to_bv 64 0x115fdc) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x115fdc) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXB.KS_dpXB; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1137416 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6756480 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6887616) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1162cc) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX2B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468852 <=? a) && (a + n <=? 2147469100) || (2147606248 <=? a) && (a + n <=? 2147606268) || (2147611484 <=? a) && (a + n <=? 2147611676)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x139ae0 <=? a) && (a + Z.of_nat n <=? 0x13a0e0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX2B_pre.dpX2B_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1286400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286480 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1290352 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6887632 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887640 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887648 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6888176 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468852 1 eq_refl) (SHW 2147468853 1 eq_refl)
           (SHW 2147468854 1 eq_refl) (SHW 2147468855 1 eq_refl) (SHW 2147468864 1 eq_refl) (SHW 2147468865 1 eq_refl) (SHW 2147468866 1 eq_refl) (SHW 2147468867 1 eq_refl)
           (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 4 eq_refl)
           (SHW 2147468876 1 eq_refl) (SHW 2147468876 4 eq_refl) (SHW 2147468877 1 eq_refl) (SHW 2147468878 1 eq_refl) (SHW 2147468879 1 eq_refl) (SHW 2147468892 1 eq_refl)
           (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl)
           (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl)
           (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl) (SHW 2147468909 1 eq_refl)
           (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468917 1 eq_refl)
           (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
           (SHW 2147468923 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl)
           (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 4 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
           (SHW 2147468947 1 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
           (SHW 2147468960 1 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl)
           (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl)
           (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl)
           (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl)
           (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl)
           (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl)
           (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl)
           (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl)
           (SHW 2147469027 1 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl)
           (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl)
           (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469077 1 eq_refl)
           (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl)
           (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469088 4 eq_refl)
           (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469096 1 eq_refl) (SHW 2147469096 4 eq_refl)
           (SHW 2147469097 1 eq_refl) (SHW 2147469098 1 eq_refl) (SHW 2147469099 1 eq_refl) (SHW 2147606248 1 eq_refl) (SHW 2147606248 4 eq_refl) (SHW 2147606249 1 eq_refl)
           (SHW 2147606250 1 eq_refl) (SHW 2147606251 1 eq_refl) (SHW 2147606252 4 eq_refl) (SHW 2147606256 4 eq_refl) (SHW 2147606260 4 eq_refl) (SHW 2147606264 1 eq_refl)
           (SHW 2147606264 4 eq_refl) (SHW 2147606265 1 eq_refl) (SHW 2147606266 1 eq_refl) (SHW 2147606267 1 eq_refl) (SHW 2147611484 1 eq_refl) (SHW 2147611484 4 eq_refl)
           (SHW 2147611485 1 eq_refl) (SHW 2147611486 1 eq_refl) (SHW 2147611487 1 eq_refl) (SHW 2147611488 4 eq_refl) (SHW 2147611492 4 eq_refl) (SHW 2147611496 4 eq_refl)
           (SHW 2147611500 4 eq_refl) (SHW 2147611504 4 eq_refl) (SHW 2147611508 4 eq_refl) (SHW 2147611512 8 eq_refl) (SHW 2147611520 8 eq_refl) (SHW 2147611528 8 eq_refl)
           (SHW 2147611536 8 eq_refl) (SHW 2147611544 8 eq_refl) (SHW 2147611552 8 eq_refl) (SHW 2147611560 8 eq_refl) (SHW 2147611568 8 eq_refl) (SHW 2147611576 8 eq_refl)
           (SHW 2147611584 8 eq_refl) (SHW 2147611592 8 eq_refl) (SHW 2147611600 8 eq_refl) (SHW 2147611608 8 eq_refl) (SHW 2147611616 8 eq_refl) (SHW 2147611624 8 eq_refl)
           (SHW 2147611632 8 eq_refl) (SHW 2147611640 8 eq_refl) (SHW 2147611648 4 eq_refl) (SHW 2147611648 8 eq_refl) (SHW 2147611652 4 eq_refl) (SHW 2147611656 4 eq_refl)
           (SHW 2147611656 8 eq_refl) (SHW 2147611660 4 eq_refl) (SHW 2147611664 4 eq_refl) (SHW 2147611664 8 eq_refl) (SHW 2147611668 4 eq_refl) (SHW 2147611672 1 eq_refl)
           (SHW 2147611672 4 eq_refl) (SHW 2147611673 1 eq_refl) (SHW 2147611674 1 eq_refl) (SHW 2147611675 1 eq_refl) TIDC HTr
           (XCC 0%nat 6888176 4 0 eq_refl) (XCC1 1%nat 6888211 0 eq_refl eq_refl) (XCC 2%nat 6887648 8 6887656 eq_refl) (XCC 3%nat 6887640 4 4 eq_refl) (XCC 26%nat 6887688 8 448212 eq_refl) (XCC 28%nat 6887944 8 0 eq_refl)
           (XCC 6%nat 6887636 4 0 eq_refl) (STC1 11%nat 1290196 0 eq_refl eq_refl) (XCC 25%nat 6887680 8 863096 eq_refl) (XCC 27%nat 6887936 8 1283856 eq_refl) (XCC 22%nat 6887672 8 1139320 eq_refl) (XCC 23%nat 6887928 8 686948 eq_refl)
           (XCC1 24%nat 6749716 0 eq_refl eq_refl) (XCC 4%nat 6887664 8 1139320 eq_refl) (XCC 5%nat 6887920 8 618908 eq_refl) (STC1 10%nat 1898080 0 eq_refl eq_refl) (XCC 7%nat 6887656 8 0 eq_refl) (STC1 3%nat 1286480 0 eq_refl eq_refl)
           (STC 0%nat 1273320 8 1273320 eq_refl) (STC 2%nat 1286400 8 1 eq_refl) (STC 4%nat 1290192 4 1 eq_refl) (STC 5%nat 1290352 8 0 eq_refl) (STC1 8%nat 1303704 1 eq_refl eq_refl) (STC 7%nat 1300408 8 2147450880 eq_refl)
           (DSC 1284832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143776)) ltac:(img_rd) eq_refl) (DSC 1284848 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1298460 1 eq_refl eq_refl) (DSC 1284848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1897312 8 18446744073709551615 eq_refl) (STC 1%nat 1273832 8 1210200 eq_refl)
           (DSC 1284888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143872)) ltac:(img_rd) eq_refl) (DSC 1284912 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1284912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1284952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl)
           (DSC 1284976 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1284976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1285040 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1285080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1285104 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl)
           (DSC 1285168 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1285232 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1285296 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl)
           (DSC 1285360 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1285360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1285400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl) (DSC 1285424 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1285488 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
           (DSC 1285552 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1285616 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1285680 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl)
           (DSC 1285744 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1285808 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1285872 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl)
           (DSC 1285936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145184)) ltac:(img_rd) eq_refl) (DSC 1286000 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1286000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1286040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1286064 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl)
           (DSC 1286128 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1286192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1286232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1286256 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1242944)) ltac:(img_rd) eq_refl)
           (DSC 1286320 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl) (DSC 1286320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1286360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6889608 8 0 eq_refl) (XCC 9%nat 1284776 8 1284544 eq_refl) (XCC 10%nat 1284684 4 4294967295 eq_refl)
           (XCC 11%nat 1284584 8 0 eq_refl) (XCC 12%nat 1284600 8 0 eq_refl) (XCC 13%nat 1284552 8 0 eq_refl) (XCC 14%nat 1284560 8 0 eq_refl) (XCC 15%nat 1284536 8 1284304 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1286368 \/ 1290360 <= i < 6887632 \/ 6887656 <= i < 6888176 \/ 6888180 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x1162cc) M R1 (Z_to_bv 64 0x11dcac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6889632) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 6889632 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1284304 /\ (1284304 + 124 <= q \/ q + 32 + 16 <= 1284304 + 120) /\ 1284304 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1284304 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 6889632 (2 * 1) 0 0 (zero_lines 1%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
    (* [comment removed for export] *)
    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1284304 <= a -> a + n <= 1284304 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1284304) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6887616) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_2.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_2.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1284336 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284344 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284360 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1284392 8%nat _ SObuf eq_refl)
           (LIT3 1284400 8%nat _ SObufsz eq_refl) (LIT3 6887616 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1284312 8%nat _ SOrpos eq_refl)
           (LIT3 1284320 8%nat _ SOrend eq_refl) (LIT3 1284296 8%nat _ (XCC 16%nat 1284296 8 1284064 eq_refl) eq_refl) (LIT3 1284204 4%nat _ (XCC 17%nat 1284204 4 4294967295 eq_refl) eq_refl) (LIT3 1284104 8%nat _ (XCC 18%nat 1284104 8 0 eq_refl) eq_refl) (LIT3 1284120 8%nat _ (XCC 19%nat 1284120 8 0 eq_refl) eq_refl) (LIT3 1284072 8%nat _ (XCC 20%nat 1284072 8 0 eq_refl) eq_refl)
           (LIT3 1284080 8%nat _ (XCC 21%nat 1284080 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11dcb8) M3 R4 (Z_to_bv 64 0x115fdc) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x115fdc) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1137416 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6756480 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6887616) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1162cc) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX3B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468852 <=? a) && (a + n <=? 2147469100) || (2147606248 <=? a) && (a + n <=? 2147606268) || (2147611484 <=? a) && (a + n <=? 2147611676)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x139ae0 <=? a) && (a + Z.of_nat n <=? 0x13a0e0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX3B_pre.dpX3B_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1286400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286480 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1290352 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6887632 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887640 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887648 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6888176 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468852 1 eq_refl) (SHW 2147468853 1 eq_refl)
           (SHW 2147468854 1 eq_refl) (SHW 2147468855 1 eq_refl) (SHW 2147468864 1 eq_refl) (SHW 2147468865 1 eq_refl) (SHW 2147468866 1 eq_refl) (SHW 2147468867 1 eq_refl)
           (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 4 eq_refl)
           (SHW 2147468876 1 eq_refl) (SHW 2147468876 4 eq_refl) (SHW 2147468877 1 eq_refl) (SHW 2147468878 1 eq_refl) (SHW 2147468879 1 eq_refl) (SHW 2147468892 1 eq_refl)
           (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl)
           (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl)
           (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl) (SHW 2147468909 1 eq_refl)
           (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468917 1 eq_refl)
           (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
           (SHW 2147468923 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl)
           (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 4 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
           (SHW 2147468947 1 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
           (SHW 2147468960 1 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl)
           (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl)
           (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl)
           (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl)
           (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl)
           (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl)
           (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl)
           (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl)
           (SHW 2147469027 1 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl)
           (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl)
           (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469077 1 eq_refl)
           (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl)
           (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469088 4 eq_refl)
           (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469096 1 eq_refl) (SHW 2147469096 4 eq_refl)
           (SHW 2147469097 1 eq_refl) (SHW 2147469098 1 eq_refl) (SHW 2147469099 1 eq_refl) (SHW 2147606248 1 eq_refl) (SHW 2147606248 4 eq_refl) (SHW 2147606249 1 eq_refl)
           (SHW 2147606250 1 eq_refl) (SHW 2147606251 1 eq_refl) (SHW 2147606252 4 eq_refl) (SHW 2147606256 4 eq_refl) (SHW 2147606260 4 eq_refl) (SHW 2147606264 1 eq_refl)
           (SHW 2147606264 4 eq_refl) (SHW 2147606265 1 eq_refl) (SHW 2147606266 1 eq_refl) (SHW 2147606267 1 eq_refl) (SHW 2147611484 1 eq_refl) (SHW 2147611484 4 eq_refl)
           (SHW 2147611485 1 eq_refl) (SHW 2147611486 1 eq_refl) (SHW 2147611487 1 eq_refl) (SHW 2147611488 4 eq_refl) (SHW 2147611492 4 eq_refl) (SHW 2147611496 4 eq_refl)
           (SHW 2147611500 4 eq_refl) (SHW 2147611504 4 eq_refl) (SHW 2147611508 4 eq_refl) (SHW 2147611512 8 eq_refl) (SHW 2147611520 8 eq_refl) (SHW 2147611528 8 eq_refl)
           (SHW 2147611536 8 eq_refl) (SHW 2147611544 8 eq_refl) (SHW 2147611552 8 eq_refl) (SHW 2147611560 8 eq_refl) (SHW 2147611568 8 eq_refl) (SHW 2147611576 8 eq_refl)
           (SHW 2147611584 8 eq_refl) (SHW 2147611592 8 eq_refl) (SHW 2147611600 8 eq_refl) (SHW 2147611608 8 eq_refl) (SHW 2147611616 8 eq_refl) (SHW 2147611624 8 eq_refl)
           (SHW 2147611632 8 eq_refl) (SHW 2147611640 8 eq_refl) (SHW 2147611648 4 eq_refl) (SHW 2147611648 8 eq_refl) (SHW 2147611652 4 eq_refl) (SHW 2147611656 4 eq_refl)
           (SHW 2147611656 8 eq_refl) (SHW 2147611660 4 eq_refl) (SHW 2147611664 4 eq_refl) (SHW 2147611664 8 eq_refl) (SHW 2147611668 4 eq_refl) (SHW 2147611672 1 eq_refl)
           (SHW 2147611672 4 eq_refl) (SHW 2147611673 1 eq_refl) (SHW 2147611674 1 eq_refl) (SHW 2147611675 1 eq_refl) TIDC HTr
           (XCC 0%nat 6888176 4 0 eq_refl) (XCC1 1%nat 6888211 0 eq_refl eq_refl) (XCC 2%nat 6887648 8 6887656 eq_refl) (XCC 3%nat 6887640 4 4 eq_refl) (XCC 26%nat 6887688 8 448212 eq_refl) (XCC 28%nat 6887944 8 0 eq_refl)
           (XCC 6%nat 6887636 4 0 eq_refl) (STC1 11%nat 1290196 0 eq_refl eq_refl) (XCC 25%nat 6887680 8 863096 eq_refl) (XCC 27%nat 6887936 8 1283856 eq_refl) (XCC 22%nat 6887672 8 1139320 eq_refl) (XCC 23%nat 6887928 8 686948 eq_refl)
           (XCC1 24%nat 6749716 0 eq_refl eq_refl) (XCC 4%nat 6887664 8 1139320 eq_refl) (XCC 5%nat 6887920 8 618908 eq_refl) (STC1 10%nat 1898080 0 eq_refl eq_refl) (XCC 7%nat 6887656 8 0 eq_refl) (STC1 3%nat 1286480 0 eq_refl eq_refl)
           (STC 0%nat 1273320 8 1273320 eq_refl) (STC 2%nat 1286400 8 1 eq_refl) (STC 4%nat 1290192 4 1 eq_refl) (STC 5%nat 1290352 8 0 eq_refl) (STC1 8%nat 1303704 1 eq_refl eq_refl) (STC 7%nat 1300408 8 2147450880 eq_refl)
           (DSC 1284832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143776)) ltac:(img_rd) eq_refl) (DSC 1284848 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1298460 1 eq_refl eq_refl) (DSC 1284848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1897312 8 18446744073709551615 eq_refl) (STC 1%nat 1273832 8 1210200 eq_refl)
           (DSC 1284888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143872)) ltac:(img_rd) eq_refl) (DSC 1284912 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1284912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1284952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl)
           (DSC 1284976 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1284976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1285040 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1285080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1285104 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl)
           (DSC 1285168 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1285232 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1285296 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl)
           (DSC 1285360 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1285360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1285400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl) (DSC 1285424 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1285488 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
           (DSC 1285552 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1285616 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1285680 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl)
           (DSC 1285744 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1285808 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1285872 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl)
           (DSC 1285936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145184)) ltac:(img_rd) eq_refl) (DSC 1286000 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1286000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1286040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1286064 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl)
           (DSC 1286128 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1286192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1286232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1286256 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1242944)) ltac:(img_rd) eq_refl)
           (DSC 1286320 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl) (DSC 1286320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1286360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6889608 8 0 eq_refl) (XCC 9%nat 1284776 8 1284544 eq_refl) (XCC 10%nat 1284684 4 4294967295 eq_refl)
           (XCC 11%nat 1284584 8 0 eq_refl) (XCC 12%nat 1284600 8 0 eq_refl) (XCC 13%nat 1284552 8 0 eq_refl) (XCC 14%nat 1284560 8 0 eq_refl) (XCC 15%nat 1284536 8 1284304 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1286368 \/ 1290360 <= i < 6887632 \/ 6887656 <= i < 6888176 \/ 6888180 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x1162cc) M R1 (Z_to_bv 64 0x11dcac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6889632) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 6889632 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1284304 /\ (1284304 + 124 <= q \/ q + 32 + 16 <= 1284304 + 120) /\ 1284304 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1284304 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 6889632 (2 * 2) 0 0 (zero_lines 2%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
    (* [comment removed for export] *)
    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1284304 <= a -> a + n <= 1284304 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1284304) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6887616) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_3.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_3.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1284336 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284344 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284360 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1284392 8%nat _ SObuf eq_refl)
           (LIT3 1284400 8%nat _ SObufsz eq_refl) (LIT3 6887616 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1284312 8%nat _ SOrpos eq_refl)
           (LIT3 1284320 8%nat _ SOrend eq_refl) (LIT3 1284296 8%nat _ (XCC 16%nat 1284296 8 1284064 eq_refl) eq_refl) (LIT3 1284204 4%nat _ (XCC 17%nat 1284204 4 4294967295 eq_refl) eq_refl) (LIT3 1284104 8%nat _ (XCC 18%nat 1284104 8 0 eq_refl) eq_refl) (LIT3 1284120 8%nat _ (XCC 19%nat 1284120 8 0 eq_refl) eq_refl) (LIT3 1284072 8%nat _ (XCC 20%nat 1284072 8 0 eq_refl) eq_refl)
           (LIT3 1284080 8%nat _ (XCC 21%nat 1284080 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11dcb8) M3 R4 (Z_to_bv 64 0x115fdc) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x115fdc) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1137416 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6756480 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6887616) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x1162cc) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX4B_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468852 <=? a) && (a + n <=? 2147469100) || (2147606248 <=? a) && (a + n <=? 2147606268) || (2147611484 <=? a) && (a + n <=? 2147611676)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_B i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_B i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_B i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x139ae0 <=? a) && (a + Z.of_nat n <=? 0x13a0e0) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX4B_pre.dpX4B_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1286400 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1286480 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1290352 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6887632 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887640 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6887648 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6888176 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468852 1 eq_refl) (SHW 2147468853 1 eq_refl)
           (SHW 2147468854 1 eq_refl) (SHW 2147468855 1 eq_refl) (SHW 2147468864 1 eq_refl) (SHW 2147468865 1 eq_refl) (SHW 2147468866 1 eq_refl) (SHW 2147468867 1 eq_refl)
           (SHW 2147468868 1 eq_refl) (SHW 2147468868 4 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 4 eq_refl)
           (SHW 2147468876 1 eq_refl) (SHW 2147468876 4 eq_refl) (SHW 2147468877 1 eq_refl) (SHW 2147468878 1 eq_refl) (SHW 2147468879 1 eq_refl) (SHW 2147468892 1 eq_refl)
           (SHW 2147468893 1 eq_refl) (SHW 2147468894 1 eq_refl) (SHW 2147468895 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl)
           (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl)
           (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468908 4 eq_refl) (SHW 2147468909 1 eq_refl)
           (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468916 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468917 1 eq_refl)
           (SHW 2147468918 1 eq_refl) (SHW 2147468919 1 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
           (SHW 2147468923 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468928 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468929 1 eq_refl) (SHW 2147468930 1 eq_refl)
           (SHW 2147468931 1 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 4 eq_refl) (SHW 2147468940 4 eq_refl) (SHW 2147468944 1 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468945 1 eq_refl) (SHW 2147468946 1 eq_refl)
           (SHW 2147468947 1 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl)
           (SHW 2147468952 4 eq_refl) (SHW 2147468956 1 eq_refl) (SHW 2147468956 4 eq_refl) (SHW 2147468957 1 eq_refl) (SHW 2147468958 1 eq_refl) (SHW 2147468959 1 eq_refl)
           (SHW 2147468960 1 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl)
           (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl)
           (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl)
           (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl)
           (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl)
           (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl)
           (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl)
           (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl)
           (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl)
           (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469016 4 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469024 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469025 1 eq_refl) (SHW 2147469026 1 eq_refl)
           (SHW 2147469027 1 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl)
           (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469068 1 eq_refl) (SHW 2147469068 4 eq_refl) (SHW 2147469069 1 eq_refl)
           (SHW 2147469070 1 eq_refl) (SHW 2147469071 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469076 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469077 1 eq_refl)
           (SHW 2147469078 1 eq_refl) (SHW 2147469079 1 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl)
           (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl) (SHW 2147469088 4 eq_refl)
           (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469096 1 eq_refl) (SHW 2147469096 4 eq_refl)
           (SHW 2147469097 1 eq_refl) (SHW 2147469098 1 eq_refl) (SHW 2147469099 1 eq_refl) (SHW 2147606248 1 eq_refl) (SHW 2147606248 4 eq_refl) (SHW 2147606249 1 eq_refl)
           (SHW 2147606250 1 eq_refl) (SHW 2147606251 1 eq_refl) (SHW 2147606252 4 eq_refl) (SHW 2147606256 4 eq_refl) (SHW 2147606260 4 eq_refl) (SHW 2147606264 1 eq_refl)
           (SHW 2147606264 4 eq_refl) (SHW 2147606265 1 eq_refl) (SHW 2147606266 1 eq_refl) (SHW 2147606267 1 eq_refl) (SHW 2147611484 1 eq_refl) (SHW 2147611484 4 eq_refl)
           (SHW 2147611485 1 eq_refl) (SHW 2147611486 1 eq_refl) (SHW 2147611487 1 eq_refl) (SHW 2147611488 4 eq_refl) (SHW 2147611492 4 eq_refl) (SHW 2147611496 4 eq_refl)
           (SHW 2147611500 4 eq_refl) (SHW 2147611504 4 eq_refl) (SHW 2147611508 4 eq_refl) (SHW 2147611512 8 eq_refl) (SHW 2147611520 8 eq_refl) (SHW 2147611528 8 eq_refl)
           (SHW 2147611536 8 eq_refl) (SHW 2147611544 8 eq_refl) (SHW 2147611552 8 eq_refl) (SHW 2147611560 8 eq_refl) (SHW 2147611568 8 eq_refl) (SHW 2147611576 8 eq_refl)
           (SHW 2147611584 8 eq_refl) (SHW 2147611592 8 eq_refl) (SHW 2147611600 8 eq_refl) (SHW 2147611608 8 eq_refl) (SHW 2147611616 8 eq_refl) (SHW 2147611624 8 eq_refl)
           (SHW 2147611632 8 eq_refl) (SHW 2147611640 8 eq_refl) (SHW 2147611648 4 eq_refl) (SHW 2147611648 8 eq_refl) (SHW 2147611652 4 eq_refl) (SHW 2147611656 4 eq_refl)
           (SHW 2147611656 8 eq_refl) (SHW 2147611660 4 eq_refl) (SHW 2147611664 4 eq_refl) (SHW 2147611664 8 eq_refl) (SHW 2147611668 4 eq_refl) (SHW 2147611672 1 eq_refl)
           (SHW 2147611672 4 eq_refl) (SHW 2147611673 1 eq_refl) (SHW 2147611674 1 eq_refl) (SHW 2147611675 1 eq_refl) TIDC HTr
           (XCC 0%nat 6888176 4 0 eq_refl) (XCC1 1%nat 6888211 0 eq_refl eq_refl) (XCC 2%nat 6887648 8 6887656 eq_refl) (XCC 3%nat 6887640 4 4 eq_refl) (XCC 26%nat 6887688 8 448212 eq_refl) (XCC 28%nat 6887944 8 0 eq_refl)
           (XCC 6%nat 6887636 4 0 eq_refl) (STC1 11%nat 1290196 0 eq_refl eq_refl) (XCC 25%nat 6887680 8 863096 eq_refl) (XCC 27%nat 6887936 8 1283856 eq_refl) (XCC 22%nat 6887672 8 1139320 eq_refl) (XCC 23%nat 6887928 8 686948 eq_refl)
           (XCC1 24%nat 6749716 0 eq_refl eq_refl) (XCC 4%nat 6887664 8 1139320 eq_refl) (XCC 5%nat 6887920 8 618908 eq_refl) (STC1 10%nat 1898080 0 eq_refl eq_refl) (XCC 7%nat 6887656 8 0 eq_refl) (STC1 3%nat 1286480 0 eq_refl eq_refl)
           (STC 0%nat 1273320 8 1273320 eq_refl) (STC 2%nat 1286400 8 1 eq_refl) (STC 4%nat 1290192 4 1 eq_refl) (STC 5%nat 1290352 8 0 eq_refl) (STC1 8%nat 1303704 1 eq_refl eq_refl) (STC 7%nat 1300408 8 2147450880 eq_refl)
           (DSC 1284832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143776)) ltac:(img_rd) eq_refl) (DSC 1284848 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1298460 1 eq_refl eq_refl) (DSC 1284848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1897312 8 18446744073709551615 eq_refl) (STC 1%nat 1273832 8 1210200 eq_refl)
           (DSC 1284888 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143872)) ltac:(img_rd) eq_refl) (DSC 1284912 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1284912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1284952 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1284960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl)
           (DSC 1284976 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1284976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285016 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144096)) ltac:(img_rd) eq_refl) (DSC 1285040 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1285080 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1285104 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285144 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285152 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144192)) ltac:(img_rd) eq_refl)
           (DSC 1285168 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1285168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1285208 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285216 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1285232 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285280 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144320)) ltac:(img_rd) eq_refl) (DSC 1285296 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285344 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144416)) ltac:(img_rd) eq_refl)
           (DSC 1285360 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1285360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1285400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285408 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144544)) ltac:(img_rd) eq_refl) (DSC 1285424 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1285464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285472 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144640)) ltac:(img_rd) eq_refl) (DSC 1285488 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285536 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144704)) ltac:(img_rd) eq_refl)
           (DSC 1285552 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144768)) ltac:(img_rd) eq_refl) (DSC 1285616 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144832)) ltac:(img_rd) eq_refl) (DSC 1285680 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144896)) ltac:(img_rd) eq_refl)
           (DSC 1285744 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144960)) ltac:(img_rd) eq_refl) (DSC 1285808 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1285848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145024)) ltac:(img_rd) eq_refl) (DSC 1285872 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1285872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1285912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145088)) ltac:(img_rd) eq_refl)
           (DSC 1285936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1285936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1285976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1285984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145184)) ltac:(img_rd) eq_refl) (DSC 1286000 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1286000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1286040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286048 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145504)) ltac:(img_rd) eq_refl) (DSC 1286064 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286112 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145600)) ltac:(img_rd) eq_refl)
           (DSC 1286128 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1286168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286176 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1286192 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1286192 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1286232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286240 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1286256 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1286256 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1286296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1286304 8%nat (word_to_le_bytes 8 (Z_to_bv 64 1242944)) ltac:(img_rd) eq_refl)
           (DSC 1286320 1%nat [Z_to_bv 8 160] ltac:(img_rd) eq_refl) (DSC 1286320 8%nat (word_to_le_bytes 8 (Z_to_bv 64 160)) ltac:(img_rd) eq_refl) (DSC 1286360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6889608 8 0 eq_refl) (XCC 9%nat 1284776 8 1284544 eq_refl) (XCC 10%nat 1284684 4 4294967295 eq_refl)
           (XCC 11%nat 1284584 8 0 eq_refl) (XCC 12%nat 1284600 8 0 eq_refl) (XCC 13%nat 1284552 8 0 eq_refl) (XCC 14%nat 1284560 8 0 eq_refl) (XCC 15%nat 1284536 8 1284304 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1286368 \/ 1290360 <= i < 6887632 \/ 6887656 <= i < 6888176 \/ 6888180 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x1162cc) M R1 (Z_to_bv 64 0x11dcac) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6889632) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 6889632 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1284304 /\ (1284304 + 124 <= q \/ q + 32 + 16 <= 1284304 + 120) /\ 1284304 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1284304 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 6889632 (2 * 3) 0 0 (zero_lines 3%nat) []).
    { cbn. lia. }
    { exact (sbm_lazy_eq _ _ SBM1). }
    { exact MI1. }
    { rewrite (sbm_halted_eq _ _ SBM1). exact Hh. }
    { rewrite (sbm_fds' _ _ SBM1). exact FD1. }
    { unfold wv_regs. repeat split; assumption. }
    { rewrite VIS1. unfold wv_iov. split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [exact Xm136|]. split; [replace (q + 8) with (S - 128) by (unfold q; ring); exact Xm128|].
      split; [replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 0)) by (f_equal; lia); apply (WIN1 q 32); [unfold q; clear - Hsp' HS1 HS2; lia | unfold q; clear - Hsp' HS1 HS2; lia | lia | cbn; lia]|].
      split; [unfold wv_buf; split; [lia|]; split; [lia|]; split; [lia|]; split; [right; left; unfold q; clear - Hsp' HS1 HS2; lia|]; split; [exact DATA|];
              intros x Hx; apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); lia|].
      split; [intros X; discriminate X|]. intros _.
      split; [replace (q + 16) with (S - 120) by (unfold q; ring); exact Xm120|].
      split; [replace (q + 24) with (S - 112) by (unfold q; ring); exact Xm112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|]. intros x Hx. lia. }
    { lia. }
    { rewrite VIS1. exact (LITX _ _ _ SOfd eq_refl). }
    (* [comment removed for export] *)
    intros R3 M3 model3 MI3 SBM3 KR3 _ FRV3 _ GRV3. rewrite VIS1 in FRV3, GRV3.
    set (MV3 := mrestrict (ahid A model) M3) in *.
    assert (LIT3 : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1286368) || ((1290360 <=? a) && (a + Z.of_nat n <=? 6887632)) || ((6888180 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. pose proof (LITX a n bs Hr Hb) as Y. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV1 MV3 a n bs Y B1); [lia|]. intros i Hi. apply FRV3; [lia|]. unfold q. clear - Hsp' HS1 HS2 B1 B2 Hi. lia. }
    assert (cellS : forall off k (n : nat) bs, rdn ASEGS MV1 (Z_to_bv 64 (S - k)) n = Some bs ->
              (off + k =? 144) && (Z.of_nat n <=? k) && (k <=? 104) = true -> rdn ASEGS MV3 (Z_to_bv 64 (S - 144 + off)) n = Some bs).
    { intros off k n bs Hr Hb. apply andb_prop in Hb as (Hb & Hb3). apply andb_prop in Hb as (Hb1 & Hb2).
      apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2, Hb3. replace (S - 144 + off) with (S - k) by lia.
      apply (rdn_tr MV1 MV3 _ _ _ Hr); [clear - Hsp' HS1 HS2 Hb3; lia | clear - Hsp' HS1 HS2 Hb2; lia|].
      intros i Hi. apply FRV3; unfold q; clear - Hsp' HS1 HS2 Hb2 Hb3 Hi; lia. }
    assert (WIN3 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (WIN1 a n); assumption).
    assert (FW3 : forall a n, 1284304 <= a -> a + n <= 1284304 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1269760 -> MV3 (Z_to_bv 64 i) = None).
    { intros i Hi. rewrite FRV3; [rewrite FRX; [apply IMGc; exact Hi | lia | unfold good; lia] | lia | unfold q; clear - Hsp' HS1 HS2 Hi; lia]. }
    set (VD := fun n : nat => match n with
               | 2%nat => S - 144 | 40%nat => canz
               | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))) | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
               | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))) | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
               | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))) | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
               | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
               | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10))) | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
               | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19))) | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
               | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
               | _ => 0 end).
    assert (Dg2 : getr R3 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (VD 2%nat)) by (eapply eq_trans; [exact (KR3 2%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr2]).
    assert (Dg8 : getr R3 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (eapply eq_trans; [exact (KR3 8%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr8]).
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1284304) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6887616) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
    assert (Dg10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (VD 110%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg18 : getr R3 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 (VD 118%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg19 : getr R3 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (VD 119%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg20 : getr R3 (Z_to_bv 5 (Z.of_nat 20)) = Z_to_bv 64 (VD 120%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Dg22 : getr R3 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 (VD 122%nat)) by (cbn [VD]; symmetry; apply Z_to_bv_bv_unsigned).
    assert (HD64 : 0 <= VD 2%nat < 2 ^ 64) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDr : 140735332552704 <= VD 2%nat <= 140737488355328) by (cbn [VD]; clear - Hsp' HS1 HS2; lia).
    assert (HDa : AS0DRVP_dpXd_4.aligned (VD 2%nat) 16).
    { cbn [VD]. unfold AS0DRVP_dpXd_4.aligned. clear - HS16. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (DWR : L5Defs.L5.writable ASEGS MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros d k Hd Hk. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (DDF : L5Defs.L5.defined MV3 (VD 2%nat - 16) 16).
    { cbn [VD]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN3 (S - 144 - 16) 16); clear - Hsp' HS1 HS2 Hi; lia. }
    destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD HD64 (u64_range _)
           (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           Dg2 Dg8 Dg9 Dg10 Dg18 Dg19
           Dg20 Dg21 Dg22 HDr HDa DWR
           DDF IMG3 (fun d k Hd Hk => FW3 1284336 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284344 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1284360 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1284392 8%nat _ SObuf eq_refl)
           (LIT3 1284400 8%nat _ SObufsz eq_refl) (LIT3 6887616 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1284312 8%nat _ SOrpos eq_refl)
           (LIT3 1284320 8%nat _ SOrend eq_refl) (LIT3 1284296 8%nat _ (XCC 16%nat 1284296 8 1284064 eq_refl) eq_refl) (LIT3 1284204 4%nat _ (XCC 17%nat 1284204 4 4294967295 eq_refl) eq_refl) (LIT3 1284104 8%nat _ (XCC 18%nat 1284104 8 0 eq_refl) eq_refl) (LIT3 1284120 8%nat _ (XCC 19%nat 1284120 8 0 eq_refl) eq_refl) (LIT3 1284072 8%nat _ (XCC 20%nat 1284072 8 0 eq_refl) eq_refl)
           (LIT3 1284080 8%nat _ (XCC 21%nat 1284080 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x11dcb8) M3 R4 (Z_to_bv 64 0x115fdc) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x115fdc) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
End Exit.
End FPX_1.
