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
  HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvExit_b Ba0ExitCells_b.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpXS_b Ba0DrvP_dpX2S_pre_b Ba0DrvP_dpX3S_pre_b Ba0DrvP_dpX4S_pre_b Ba0DrvP_dpXd_2_b Ba0DrvP_dpXd_3_b Ba0DrvP_dpXd_4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XC_CELLS : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 2); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0); (6897016, 8, 1148964); (6897272, 8, 687916); (6759060, 1, 0)].
(* [comment removed for export] *)
Definition XC_CELLS_E : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 1); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

(* [comment removed for export] *)
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6765656) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x13bfc0 <= i < 0x13c580 -> MV (Z_to_bv 64 i) = None).

Definition exitE (tid : Z) (MV : word -> option byte) : Prop :=   (* [comment removed for export] *)
  cells_at MV XC_CELLS_E
  /\ rdn ASEGS MV (Z_to_bv 64 6765656) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x13bfc0 <= i < 0x13c580 -> MV (Z_to_bv 64 i) = None).


Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0x118588) = Some ECALLW.
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
Definition XC_CELLS_S : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 6); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0); (6897016, 8, 1148964); (6897272, 8, 687916); (6759060, 1, 0); (6759112, 1, 16); (6759144, 1, 6); (6897024, 8, 874172); (6897032, 8, 449180); (6897040, 8, 874172); (6897048, 8, 449180); (6897280, 8, 6759112); (6897288, 8, 0); (6897296, 8, 6759144); (6897304, 8, 0)].
Definition exitS (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_S
  /\ rdn ASEGS MV (Z_to_bv 64 6765656) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0x13bfc0 <= i < 0x13c580 -> MV (Z_to_bv 64 i) = None).


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
  Local Abbreviation ex_cell_vis := (@Ba0DrvExit_b.ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0).
  Local Abbreviation sh_writable := (@Ba0DrvExit_b.sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0).
  Local Abbreviation wsg_writable := (@Ba0DrvExit_b.wsg_writable sp0 Hsp M0).

  Definition exit_preS (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 1282048 -> MV (Z_to_bv 64 i) = None)
    /\ exitS tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0S : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXS.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_S i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_S i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_S i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bfc0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXS.dpXS_conc fx R MV V HS64 HT64
           G1 G2 G4 HSr HSa CWR
           CDF IMGc (WSG 1295744 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1295824 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1299696 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896976 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6896984 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896992 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6897520 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl) (SHW 2147468858 1 eq_refl)
           (SHW 2147468859 1 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl) (SHW 2147468872 1 eq_refl)
           (SHW 2147468872 4 eq_refl) (SHW 2147468873 1 eq_refl) (SHW 2147468874 1 eq_refl) (SHW 2147468875 1 eq_refl) (SHW 2147468876 4 eq_refl) (SHW 2147468880 1 eq_refl)
           (SHW 2147468880 4 eq_refl) (SHW 2147468881 1 eq_refl) (SHW 2147468882 1 eq_refl) (SHW 2147468883 1 eq_refl) (SHW 2147468896 1 eq_refl) (SHW 2147468897 1 eq_refl)
           (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl) (SHW 2147468903 1 eq_refl)
           (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl) (SHW 2147468909 1 eq_refl)
           (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468913 1 eq_refl) (SHW 2147468914 1 eq_refl)
           (SHW 2147468915 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl) (SHW 2147468922 1 eq_refl)
           (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl) (SHW 2147468927 1 eq_refl)
           (SHW 2147468928 4 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl) (SHW 2147468935 1 eq_refl)
           (SHW 2147468936 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl) (SHW 2147468940 4 eq_refl)
           (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl) (SHW 2147468951 1 eq_refl)
           (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl) (SHW 2147468956 4 eq_refl)
           (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl) (SHW 2147468964 1 eq_refl)
           (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl) (SHW 2147468970 1 eq_refl)
           (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl) (SHW 2147468976 1 eq_refl)
           (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl) (SHW 2147468982 1 eq_refl)
           (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl) (SHW 2147468988 1 eq_refl)
           (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl) (SHW 2147468994 1 eq_refl)
           (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl) (SHW 2147469000 1 eq_refl)
           (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl) (SHW 2147469006 1 eq_refl)
           (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl) (SHW 2147469012 1 eq_refl)
           (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469017 1 eq_refl) (SHW 2147469018 1 eq_refl)
           (SHW 2147469019 1 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl) (SHW 2147469023 1 eq_refl)
           (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl) (SHW 2147469031 1 eq_refl)
           (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl) (SHW 2147469037 1 eq_refl)
           (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl) (SHW 2147469074 1 eq_refl)
           (SHW 2147469075 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl) (SHW 2147469082 1 eq_refl)
           (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl) (SHW 2147469088 1 eq_refl)
           (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl) (SHW 2147469093 1 eq_refl)
           (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl) (SHW 2147469100 4 eq_refl) (SHW 2147469101 1 eq_refl)
           (SHW 2147469102 1 eq_refl) (SHW 2147469103 1 eq_refl) 
           
           (SHW 2147612664 184 eq_refl) (SHW 2147612664 1 eq_refl) (SHW 2147612664 4 eq_refl) (SHW 2147612665 1 eq_refl)
           (SHW 2147612666 1 eq_refl) (SHW 2147612667 1 eq_refl) (SHW 2147612668 4 eq_refl) (SHW 2147612672 4 eq_refl) (SHW 2147612676 4 eq_refl) (SHW 2147612680 4 eq_refl)
           (SHW 2147612684 4 eq_refl) (SHW 2147612688 4 eq_refl) (SHW 2147612692 8 eq_refl) (SHW 2147612700 8 eq_refl) (SHW 2147612708 8 eq_refl) (SHW 2147612716 8 eq_refl)
           (SHW 2147612724 8 eq_refl) (SHW 2147612732 8 eq_refl) (SHW 2147612740 8 eq_refl) (SHW 2147612748 8 eq_refl) (SHW 2147612756 8 eq_refl) (SHW 2147612764 8 eq_refl)
           (SHW 2147612772 8 eq_refl) (SHW 2147612780 8 eq_refl) (SHW 2147612788 8 eq_refl) (SHW 2147612796 8 eq_refl) (SHW 2147612804 8 eq_refl) (SHW 2147612812 8 eq_refl)
           (SHW 2147612820 8 eq_refl) (SHW 2147612828 4 eq_refl) (SHW 2147612828 8 eq_refl) (SHW 2147612832 4 eq_refl) (SHW 2147612836 4 eq_refl) (SHW 2147612836 8 eq_refl)
           (SHW 2147612840 4 eq_refl) (SHW 2147612844 4 eq_refl) (SHW 2147612844 8 eq_refl) 
           TIDC HTr (XCC 0%nat 6897520 4 0 eq_refl)
           (XCC1 1%nat 6897555 0 eq_refl eq_refl) (XCC 2%nat 6896992 8 6897000 eq_refl) (XCC 3%nat 6896984 4 6 eq_refl) (XCC 30%nat 6897048 8 449180 eq_refl) (XCC 34%nat 6897304 8 0 eq_refl) (XCC 6%nat 6896980 4 0 eq_refl)
           (STC1 11%nat 1299540 0 eq_refl eq_refl) (XCC 29%nat 6897040 8 874172 eq_refl) (XCC 33%nat 6897296 8 6759144 eq_refl) (XCC1 26%nat 6759144 6 eq_refl eq_refl) (XCC 28%nat 6897032 8 449180 eq_refl) (XCC 32%nat 6897288 8 0 eq_refl)
           (XCC 27%nat 6897024 8 874172 eq_refl) (XCC 31%nat 6897280 8 6759112 eq_refl) (XCC1 25%nat 6759112 16 eq_refl eq_refl) (XCC 22%nat 6897016 8 1148964 eq_refl) (XCC 23%nat 6897272 8 687916 eq_refl) (XCC1 24%nat 6759060 0 eq_refl eq_refl)
           (XCC 4%nat 6897008 8 1148964 eq_refl) (XCC 5%nat 6897264 8 619876 eq_refl) (STC1 10%nat 1907424 0 eq_refl eq_refl) (XCC 7%nat 6897000 8 0 eq_refl) (STC1 3%nat 1295824 0 eq_refl eq_refl) (STC 0%nat 1282768 8 1282768 eq_refl)
           (STC 2%nat 1295744 8 1 eq_refl) (STC 4%nat 1299536 4 1 eq_refl) (STC 5%nat 1299696 8 0 eq_refl) (STC1 8%nat 1313048 1 eq_refl eq_refl) (STC 7%nat 1309752 8 2147450880 eq_refl) (DSC 1294272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl)
           (DSC 1294288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1307804 1 eq_refl eq_refl) (DSC 1294288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1906656 8 18446744073709551615 eq_refl) (STC 1%nat 1283280 8 1219844 eq_refl) (DSC 1294328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1294336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1294352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143936)) ltac:(img_rd) eq_refl) (DSC 1294416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1294416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1294480 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1294528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144160)) ltac:(img_rd) eq_refl) (DSC 1294544 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl) (DSC 1294608 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1294608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144256)) ltac:(img_rd) eq_refl) (DSC 1294672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1294720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1294736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl) (DSC 1294800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl)
           (DSC 1294800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1294840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1294864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1294912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1294928 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144736)) ltac:(img_rd) eq_refl) (DSC 1294992 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1294992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1295056 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1295104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1295120 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl) (DSC 1295184 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl)
           (DSC 1295184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144992)) ltac:(img_rd) eq_refl) (DSC 1295248 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1295296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1295312 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145120)) ltac:(img_rd) eq_refl) (DSC 1295376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 1295376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1295440 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1295488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1295504 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl) (DSC 1295568 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 1295568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1295632 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 1295680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1295696 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) 
           (XCC 8%nat 6898952 8 0 eq_refl) (XCC 9%nat 1294224 8 1293992 eq_refl) (XCC 10%nat 1294132 4 4294967295 eq_refl) (XCC 11%nat 1294032 8 0 eq_refl)
           (XCC 12%nat 1294048 8 0 eq_refl) (XCC 13%nat 1294000 8 0 eq_refl) (XCC 14%nat 1294008 8 0 eq_refl) (XCC 15%nat 1293984 8 1293752 eq_refl) SOlock SOwpos
           SOwbase SOrpos SOrend (XCC 16%nat 1293744 8 1293512 eq_refl) (XCC 17%nat 1293652 4 4294967295 eq_refl) (XCC 18%nat 1293552 8 0 eq_refl)
           (XCC 19%nat 1293568 8 0 eq_refl) (XCC 20%nat 1293520 8 0 eq_refl) (XCC 21%nat 1293528 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x118588) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0x118588) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXS.KS_dpXS; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2S : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX2S_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_S i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_S i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_S i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bfc0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX2S_pre.dpX2S_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1295744 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1295824 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1299696 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6896976 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896984 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896992 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6897520 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl)
           (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl)
           (SHW 2147468872 1 eq_refl) (SHW 2147468872 4 eq_refl) (SHW 2147468873 1 eq_refl) (SHW 2147468874 1 eq_refl) (SHW 2147468875 1 eq_refl) (SHW 2147468876 4 eq_refl)
           (SHW 2147468880 1 eq_refl) (SHW 2147468880 4 eq_refl) (SHW 2147468881 1 eq_refl) (SHW 2147468882 1 eq_refl) (SHW 2147468883 1 eq_refl) (SHW 2147468896 1 eq_refl)
           (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl)
           (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl)
           (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468913 1 eq_refl)
           (SHW 2147468914 1 eq_refl) (SHW 2147468915 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl)
           (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl)
           (SHW 2147468927 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
           (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 4 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl)
           (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl)
           (SHW 2147468956 4 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl)
           (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl)
           (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl)
           (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl)
           (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl)
           (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl)
           (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl)
           (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469017 1 eq_refl)
           (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl)
           (SHW 2147469023 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl)
           (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl)
           (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
           (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl)
           (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl)
           (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
           (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl) (SHW 2147469100 4 eq_refl)
           (SHW 2147469101 1 eq_refl) (SHW 2147469102 1 eq_refl) (SHW 2147469103 1 eq_refl) 
           
           (SHW 2147612664 184 eq_refl) (SHW 2147612664 1 eq_refl) (SHW 2147612664 4 eq_refl)
           (SHW 2147612665 1 eq_refl) (SHW 2147612666 1 eq_refl) (SHW 2147612667 1 eq_refl) (SHW 2147612668 4 eq_refl) (SHW 2147612672 4 eq_refl) (SHW 2147612676 4 eq_refl)
           (SHW 2147612680 4 eq_refl) (SHW 2147612684 4 eq_refl) (SHW 2147612688 4 eq_refl) (SHW 2147612692 8 eq_refl) (SHW 2147612700 8 eq_refl) (SHW 2147612708 8 eq_refl)
           (SHW 2147612716 8 eq_refl) (SHW 2147612724 8 eq_refl) (SHW 2147612732 8 eq_refl) (SHW 2147612740 8 eq_refl) (SHW 2147612748 8 eq_refl) (SHW 2147612756 8 eq_refl)
           (SHW 2147612764 8 eq_refl) (SHW 2147612772 8 eq_refl) (SHW 2147612780 8 eq_refl) (SHW 2147612788 8 eq_refl) (SHW 2147612796 8 eq_refl) (SHW 2147612804 8 eq_refl)
           (SHW 2147612812 8 eq_refl) (SHW 2147612820 8 eq_refl) (SHW 2147612828 4 eq_refl) (SHW 2147612828 8 eq_refl) (SHW 2147612832 4 eq_refl) (SHW 2147612836 4 eq_refl)
           (SHW 2147612836 8 eq_refl) (SHW 2147612840 4 eq_refl) (SHW 2147612844 4 eq_refl) (SHW 2147612844 8 eq_refl) 
           TIDC HTr
           (XCC 0%nat 6897520 4 0 eq_refl) (XCC1 1%nat 6897555 0 eq_refl eq_refl) (XCC 2%nat 6896992 8 6897000 eq_refl) (XCC 3%nat 6896984 4 6 eq_refl) (XCC 30%nat 6897048 8 449180 eq_refl) (XCC 34%nat 6897304 8 0 eq_refl)
           (XCC 6%nat 6896980 4 0 eq_refl) (STC1 11%nat 1299540 0 eq_refl eq_refl) (XCC 29%nat 6897040 8 874172 eq_refl) (XCC 33%nat 6897296 8 6759144 eq_refl) (XCC1 26%nat 6759144 6 eq_refl eq_refl) (XCC 28%nat 6897032 8 449180 eq_refl)
           (XCC 32%nat 6897288 8 0 eq_refl) (XCC 27%nat 6897024 8 874172 eq_refl) (XCC 31%nat 6897280 8 6759112 eq_refl) (XCC1 25%nat 6759112 16 eq_refl eq_refl) (XCC 22%nat 6897016 8 1148964 eq_refl) (XCC 23%nat 6897272 8 687916 eq_refl)
           (XCC1 24%nat 6759060 0 eq_refl eq_refl) (XCC 4%nat 6897008 8 1148964 eq_refl) (XCC 5%nat 6897264 8 619876 eq_refl) (STC1 10%nat 1907424 0 eq_refl eq_refl) (XCC 7%nat 6897000 8 0 eq_refl) (STC1 3%nat 1295824 0 eq_refl eq_refl)
           (STC 0%nat 1282768 8 1282768 eq_refl) (STC 2%nat 1295744 8 1 eq_refl) (STC 4%nat 1299536 4 1 eq_refl) (STC 5%nat 1299696 8 0 eq_refl) (STC1 8%nat 1313048 1 eq_refl eq_refl) (STC 7%nat 1309752 8 2147450880 eq_refl)
           (DSC 1294272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1294288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1307804 1 eq_refl eq_refl) (DSC 1294288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1906656 8 18446744073709551615 eq_refl) (STC 1%nat 1283280 8 1219844 eq_refl)
           (DSC 1294328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1294352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143936)) ltac:(img_rd) eq_refl)
           (DSC 1294416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1294480 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1294520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144160)) ltac:(img_rd) eq_refl) (DSC 1294544 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl)
           (DSC 1294608 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144256)) ltac:(img_rd) eq_refl) (DSC 1294672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1294736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl)
           (DSC 1294800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1294800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1294840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1294864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1294928 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144736)) ltac:(img_rd) eq_refl)
           (DSC 1294992 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1295056 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1295120 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl)
           (DSC 1295184 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144992)) ltac:(img_rd) eq_refl) (DSC 1295248 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1295312 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145120)) ltac:(img_rd) eq_refl)
           (DSC 1295376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1295440 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1295504 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1295568 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1295632 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1295672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1295696 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) 
           (XCC 8%nat 6898952 8 0 eq_refl) (XCC 9%nat 1294224 8 1293992 eq_refl) (XCC 10%nat 1294132 4 4294967295 eq_refl)
           (XCC 11%nat 1294032 8 0 eq_refl) (XCC 12%nat 1294048 8 0 eq_refl) (XCC 13%nat 1294000 8 0 eq_refl) (XCC 14%nat 1294008 8 0 eq_refl) (XCC 15%nat 1293984 8 1293752 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897000 <= i < 6897520 \/ 6897524 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6898976) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 6898976 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1293752 /\ (1293752 + 124 <= q \/ q + 32 + 16 <= 1293752 + 120) /\ 1293752 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1293752 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 6898976 (2 * 1) 0 0 (zero_lines 1%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1282048 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1293784 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293792 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293808 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1293840 8%nat _ SObuf eq_refl)
           (LIT3 1293848 8%nat _ SObufsz eq_refl) (LIT3 6896960 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1293760 8%nat _ SOrpos eq_refl)
           (LIT3 1293768 8%nat _ SOrend eq_refl) (LIT3 1293744 8%nat _ (XCC 16%nat 1293744 8 1293512 eq_refl) eq_refl) (LIT3 1293652 4%nat _ (XCC 17%nat 1293652 4 4294967295 eq_refl) eq_refl) (LIT3 1293552 8%nat _ (XCC 18%nat 1293552 8 0 eq_refl) eq_refl) (LIT3 1293568 8%nat _ (XCC 19%nat 1293568 8 0 eq_refl) eq_refl) (LIT3 1293520 8%nat _ (XCC 20%nat 1293520 8 0 eq_refl) eq_refl)
           (LIT3 1293528 8%nat _ (XCC 21%nat 1293528 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x120264) M3 R4 (Z_to_bv 64 0x118588) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x118588) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3S : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX3S_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_S i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_S i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_S i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bfc0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX3S_pre.dpX3S_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1295744 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1295824 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1299696 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6896976 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896984 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896992 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6897520 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl)
           (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl)
           (SHW 2147468872 1 eq_refl) (SHW 2147468872 4 eq_refl) (SHW 2147468873 1 eq_refl) (SHW 2147468874 1 eq_refl) (SHW 2147468875 1 eq_refl) (SHW 2147468876 4 eq_refl)
           (SHW 2147468880 1 eq_refl) (SHW 2147468880 4 eq_refl) (SHW 2147468881 1 eq_refl) (SHW 2147468882 1 eq_refl) (SHW 2147468883 1 eq_refl) (SHW 2147468896 1 eq_refl)
           (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl)
           (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl)
           (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468913 1 eq_refl)
           (SHW 2147468914 1 eq_refl) (SHW 2147468915 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl)
           (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl)
           (SHW 2147468927 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
           (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 4 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl)
           (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl)
           (SHW 2147468956 4 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl)
           (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl)
           (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl)
           (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl)
           (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl)
           (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl)
           (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl)
           (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469017 1 eq_refl)
           (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl)
           (SHW 2147469023 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl)
           (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl)
           (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
           (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl)
           (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl)
           (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
           (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl) (SHW 2147469100 4 eq_refl)
           (SHW 2147469101 1 eq_refl) (SHW 2147469102 1 eq_refl) (SHW 2147469103 1 eq_refl) 
           
           (SHW 2147612664 184 eq_refl) (SHW 2147612664 1 eq_refl) (SHW 2147612664 4 eq_refl)
           (SHW 2147612665 1 eq_refl) (SHW 2147612666 1 eq_refl) (SHW 2147612667 1 eq_refl) (SHW 2147612668 4 eq_refl) (SHW 2147612672 4 eq_refl) (SHW 2147612676 4 eq_refl)
           (SHW 2147612680 4 eq_refl) (SHW 2147612684 4 eq_refl) (SHW 2147612688 4 eq_refl) (SHW 2147612692 8 eq_refl) (SHW 2147612700 8 eq_refl) (SHW 2147612708 8 eq_refl)
           (SHW 2147612716 8 eq_refl) (SHW 2147612724 8 eq_refl) (SHW 2147612732 8 eq_refl) (SHW 2147612740 8 eq_refl) (SHW 2147612748 8 eq_refl) (SHW 2147612756 8 eq_refl)
           (SHW 2147612764 8 eq_refl) (SHW 2147612772 8 eq_refl) (SHW 2147612780 8 eq_refl) (SHW 2147612788 8 eq_refl) (SHW 2147612796 8 eq_refl) (SHW 2147612804 8 eq_refl)
           (SHW 2147612812 8 eq_refl) (SHW 2147612820 8 eq_refl) (SHW 2147612828 4 eq_refl) (SHW 2147612828 8 eq_refl) (SHW 2147612832 4 eq_refl) (SHW 2147612836 4 eq_refl)
           (SHW 2147612836 8 eq_refl) (SHW 2147612840 4 eq_refl) (SHW 2147612844 4 eq_refl) (SHW 2147612844 8 eq_refl) 
           TIDC HTr
           (XCC 0%nat 6897520 4 0 eq_refl) (XCC1 1%nat 6897555 0 eq_refl eq_refl) (XCC 2%nat 6896992 8 6897000 eq_refl) (XCC 3%nat 6896984 4 6 eq_refl) (XCC 30%nat 6897048 8 449180 eq_refl) (XCC 34%nat 6897304 8 0 eq_refl)
           (XCC 6%nat 6896980 4 0 eq_refl) (STC1 11%nat 1299540 0 eq_refl eq_refl) (XCC 29%nat 6897040 8 874172 eq_refl) (XCC 33%nat 6897296 8 6759144 eq_refl) (XCC1 26%nat 6759144 6 eq_refl eq_refl) (XCC 28%nat 6897032 8 449180 eq_refl)
           (XCC 32%nat 6897288 8 0 eq_refl) (XCC 27%nat 6897024 8 874172 eq_refl) (XCC 31%nat 6897280 8 6759112 eq_refl) (XCC1 25%nat 6759112 16 eq_refl eq_refl) (XCC 22%nat 6897016 8 1148964 eq_refl) (XCC 23%nat 6897272 8 687916 eq_refl)
           (XCC1 24%nat 6759060 0 eq_refl eq_refl) (XCC 4%nat 6897008 8 1148964 eq_refl) (XCC 5%nat 6897264 8 619876 eq_refl) (STC1 10%nat 1907424 0 eq_refl eq_refl) (XCC 7%nat 6897000 8 0 eq_refl) (STC1 3%nat 1295824 0 eq_refl eq_refl)
           (STC 0%nat 1282768 8 1282768 eq_refl) (STC 2%nat 1295744 8 1 eq_refl) (STC 4%nat 1299536 4 1 eq_refl) (STC 5%nat 1299696 8 0 eq_refl) (STC1 8%nat 1313048 1 eq_refl eq_refl) (STC 7%nat 1309752 8 2147450880 eq_refl)
           (DSC 1294272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1294288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1307804 1 eq_refl eq_refl) (DSC 1294288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1906656 8 18446744073709551615 eq_refl) (STC 1%nat 1283280 8 1219844 eq_refl)
           (DSC 1294328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1294352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143936)) ltac:(img_rd) eq_refl)
           (DSC 1294416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1294480 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1294520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144160)) ltac:(img_rd) eq_refl) (DSC 1294544 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl)
           (DSC 1294608 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144256)) ltac:(img_rd) eq_refl) (DSC 1294672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1294736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl)
           (DSC 1294800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1294800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1294840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1294864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1294928 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144736)) ltac:(img_rd) eq_refl)
           (DSC 1294992 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1295056 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1295120 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl)
           (DSC 1295184 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144992)) ltac:(img_rd) eq_refl) (DSC 1295248 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1295312 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145120)) ltac:(img_rd) eq_refl)
           (DSC 1295376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1295440 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1295504 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1295568 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1295632 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1295672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1295696 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) 
           (XCC 8%nat 6898952 8 0 eq_refl) (XCC 9%nat 1294224 8 1293992 eq_refl) (XCC 10%nat 1294132 4 4294967295 eq_refl)
           (XCC 11%nat 1294032 8 0 eq_refl) (XCC 12%nat 1294048 8 0 eq_refl) (XCC 13%nat 1294000 8 0 eq_refl) (XCC 14%nat 1294008 8 0 eq_refl) (XCC 15%nat 1293984 8 1293752 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897000 <= i < 6897520 \/ 6897524 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6898976) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 6898976 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1293752 /\ (1293752 + 124 <= q \/ q + 32 + 16 <= 1293752 + 120) /\ 1293752 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1293752 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 6898976 (2 * 2) 0 0 (zero_lines 2%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1282048 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1293784 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293792 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293808 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1293840 8%nat _ SObuf eq_refl)
           (LIT3 1293848 8%nat _ SObufsz eq_refl) (LIT3 6896960 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1293760 8%nat _ SOrpos eq_refl)
           (LIT3 1293768 8%nat _ SOrend eq_refl) (LIT3 1293744 8%nat _ (XCC 16%nat 1293744 8 1293512 eq_refl) eq_refl) (LIT3 1293652 4%nat _ (XCC 17%nat 1293652 4 4294967295 eq_refl) eq_refl) (LIT3 1293552 8%nat _ (XCC 18%nat 1293552 8 0 eq_refl) eq_refl) (LIT3 1293568 8%nat _ (XCC 19%nat 1293568 8 0 eq_refl) eq_refl) (LIT3 1293520 8%nat _ (XCC 20%nat 1293520 8 0 eq_refl) eq_refl)
           (LIT3 1293528 8%nat _ (XCC 21%nat 1293528 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x120264) M3 R4 (Z_to_bv 64 0x118588) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x118588) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4S : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX4S_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_S i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_S i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_S i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0x13bfc0 <=? a) && (a + Z.of_nat n <=? 0x13c580) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX4S_pre.dpX4S_pre_conc fx R MV V HS64 Hcan
           HT64 G1 G2 G4 HSr HSa
           CWR CDF IMGc (WSG 1295744 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1295824 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 1299696 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6896976 1%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896984 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6896992 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6897520 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468856 1 eq_refl) (SHW 2147468857 1 eq_refl)
           (SHW 2147468858 1 eq_refl) (SHW 2147468859 1 eq_refl) (SHW 2147468868 1 eq_refl) (SHW 2147468869 1 eq_refl) (SHW 2147468870 1 eq_refl) (SHW 2147468871 1 eq_refl)
           (SHW 2147468872 1 eq_refl) (SHW 2147468872 4 eq_refl) (SHW 2147468873 1 eq_refl) (SHW 2147468874 1 eq_refl) (SHW 2147468875 1 eq_refl) (SHW 2147468876 4 eq_refl)
           (SHW 2147468880 1 eq_refl) (SHW 2147468880 4 eq_refl) (SHW 2147468881 1 eq_refl) (SHW 2147468882 1 eq_refl) (SHW 2147468883 1 eq_refl) (SHW 2147468896 1 eq_refl)
           (SHW 2147468897 1 eq_refl) (SHW 2147468898 1 eq_refl) (SHW 2147468899 1 eq_refl) (SHW 2147468900 1 eq_refl) (SHW 2147468901 1 eq_refl) (SHW 2147468902 1 eq_refl)
           (SHW 2147468903 1 eq_refl) (SHW 2147468904 1 eq_refl) (SHW 2147468905 1 eq_refl) (SHW 2147468906 1 eq_refl) (SHW 2147468907 1 eq_refl) (SHW 2147468908 1 eq_refl)
           (SHW 2147468909 1 eq_refl) (SHW 2147468910 1 eq_refl) (SHW 2147468911 1 eq_refl) (SHW 2147468912 1 eq_refl) (SHW 2147468912 4 eq_refl) (SHW 2147468913 1 eq_refl)
           (SHW 2147468914 1 eq_refl) (SHW 2147468915 1 eq_refl) (SHW 2147468916 4 eq_refl) (SHW 2147468920 1 eq_refl) (SHW 2147468920 4 eq_refl) (SHW 2147468921 1 eq_refl)
           (SHW 2147468922 1 eq_refl) (SHW 2147468923 1 eq_refl) (SHW 2147468924 1 eq_refl) (SHW 2147468924 4 eq_refl) (SHW 2147468925 1 eq_refl) (SHW 2147468926 1 eq_refl)
           (SHW 2147468927 1 eq_refl) (SHW 2147468928 4 eq_refl) (SHW 2147468932 1 eq_refl) (SHW 2147468932 4 eq_refl) (SHW 2147468933 1 eq_refl) (SHW 2147468934 1 eq_refl)
           (SHW 2147468935 1 eq_refl) (SHW 2147468936 1 eq_refl) (SHW 2147468936 4 eq_refl) (SHW 2147468937 1 eq_refl) (SHW 2147468938 1 eq_refl) (SHW 2147468939 1 eq_refl)
           (SHW 2147468940 4 eq_refl) (SHW 2147468944 4 eq_refl) (SHW 2147468948 1 eq_refl) (SHW 2147468948 4 eq_refl) (SHW 2147468949 1 eq_refl) (SHW 2147468950 1 eq_refl)
           (SHW 2147468951 1 eq_refl) (SHW 2147468952 1 eq_refl) (SHW 2147468952 4 eq_refl) (SHW 2147468953 1 eq_refl) (SHW 2147468954 1 eq_refl) (SHW 2147468955 1 eq_refl)
           (SHW 2147468956 4 eq_refl) (SHW 2147468960 1 eq_refl) (SHW 2147468960 4 eq_refl) (SHW 2147468961 1 eq_refl) (SHW 2147468962 1 eq_refl) (SHW 2147468963 1 eq_refl)
           (SHW 2147468964 1 eq_refl) (SHW 2147468965 1 eq_refl) (SHW 2147468966 1 eq_refl) (SHW 2147468967 1 eq_refl) (SHW 2147468968 1 eq_refl) (SHW 2147468969 1 eq_refl)
           (SHW 2147468970 1 eq_refl) (SHW 2147468971 1 eq_refl) (SHW 2147468972 1 eq_refl) (SHW 2147468973 1 eq_refl) (SHW 2147468974 1 eq_refl) (SHW 2147468975 1 eq_refl)
           (SHW 2147468976 1 eq_refl) (SHW 2147468977 1 eq_refl) (SHW 2147468978 1 eq_refl) (SHW 2147468979 1 eq_refl) (SHW 2147468980 1 eq_refl) (SHW 2147468981 1 eq_refl)
           (SHW 2147468982 1 eq_refl) (SHW 2147468983 1 eq_refl) (SHW 2147468984 1 eq_refl) (SHW 2147468985 1 eq_refl) (SHW 2147468986 1 eq_refl) (SHW 2147468987 1 eq_refl)
           (SHW 2147468988 1 eq_refl) (SHW 2147468989 1 eq_refl) (SHW 2147468990 1 eq_refl) (SHW 2147468991 1 eq_refl) (SHW 2147468992 1 eq_refl) (SHW 2147468993 1 eq_refl)
           (SHW 2147468994 1 eq_refl) (SHW 2147468995 1 eq_refl) (SHW 2147468996 1 eq_refl) (SHW 2147468997 1 eq_refl) (SHW 2147468998 1 eq_refl) (SHW 2147468999 1 eq_refl)
           (SHW 2147469000 1 eq_refl) (SHW 2147469001 1 eq_refl) (SHW 2147469002 1 eq_refl) (SHW 2147469003 1 eq_refl) (SHW 2147469004 1 eq_refl) (SHW 2147469005 1 eq_refl)
           (SHW 2147469006 1 eq_refl) (SHW 2147469007 1 eq_refl) (SHW 2147469008 1 eq_refl) (SHW 2147469009 1 eq_refl) (SHW 2147469010 1 eq_refl) (SHW 2147469011 1 eq_refl)
           (SHW 2147469012 1 eq_refl) (SHW 2147469013 1 eq_refl) (SHW 2147469014 1 eq_refl) (SHW 2147469015 1 eq_refl) (SHW 2147469016 1 eq_refl) (SHW 2147469017 1 eq_refl)
           (SHW 2147469018 1 eq_refl) (SHW 2147469019 1 eq_refl) (SHW 2147469020 1 eq_refl) (SHW 2147469020 4 eq_refl) (SHW 2147469021 1 eq_refl) (SHW 2147469022 1 eq_refl)
           (SHW 2147469023 1 eq_refl) (SHW 2147469024 4 eq_refl) (SHW 2147469028 1 eq_refl) (SHW 2147469028 4 eq_refl) (SHW 2147469029 1 eq_refl) (SHW 2147469030 1 eq_refl)
           (SHW 2147469031 1 eq_refl) (SHW 2147469032 1 eq_refl) (SHW 2147469033 1 eq_refl) (SHW 2147469034 1 eq_refl) (SHW 2147469035 1 eq_refl) (SHW 2147469036 1 eq_refl)
           (SHW 2147469037 1 eq_refl) (SHW 2147469038 1 eq_refl) (SHW 2147469039 1 eq_refl) (SHW 2147469072 1 eq_refl) (SHW 2147469072 4 eq_refl) (SHW 2147469073 1 eq_refl)
           (SHW 2147469074 1 eq_refl) (SHW 2147469075 1 eq_refl) (SHW 2147469076 4 eq_refl) (SHW 2147469080 1 eq_refl) (SHW 2147469080 4 eq_refl) (SHW 2147469081 1 eq_refl)
           (SHW 2147469082 1 eq_refl) (SHW 2147469083 1 eq_refl) (SHW 2147469084 1 eq_refl) (SHW 2147469085 1 eq_refl) (SHW 2147469086 1 eq_refl) (SHW 2147469087 1 eq_refl)
           (SHW 2147469088 1 eq_refl) (SHW 2147469089 1 eq_refl) (SHW 2147469090 1 eq_refl) (SHW 2147469091 1 eq_refl) (SHW 2147469092 1 eq_refl) (SHW 2147469092 4 eq_refl)
           (SHW 2147469093 1 eq_refl) (SHW 2147469094 1 eq_refl) (SHW 2147469095 1 eq_refl) (SHW 2147469096 4 eq_refl) (SHW 2147469100 1 eq_refl) (SHW 2147469100 4 eq_refl)
           (SHW 2147469101 1 eq_refl) (SHW 2147469102 1 eq_refl) (SHW 2147469103 1 eq_refl) 
           
           (SHW 2147612664 184 eq_refl) (SHW 2147612664 1 eq_refl) (SHW 2147612664 4 eq_refl)
           (SHW 2147612665 1 eq_refl) (SHW 2147612666 1 eq_refl) (SHW 2147612667 1 eq_refl) (SHW 2147612668 4 eq_refl) (SHW 2147612672 4 eq_refl) (SHW 2147612676 4 eq_refl)
           (SHW 2147612680 4 eq_refl) (SHW 2147612684 4 eq_refl) (SHW 2147612688 4 eq_refl) (SHW 2147612692 8 eq_refl) (SHW 2147612700 8 eq_refl) (SHW 2147612708 8 eq_refl)
           (SHW 2147612716 8 eq_refl) (SHW 2147612724 8 eq_refl) (SHW 2147612732 8 eq_refl) (SHW 2147612740 8 eq_refl) (SHW 2147612748 8 eq_refl) (SHW 2147612756 8 eq_refl)
           (SHW 2147612764 8 eq_refl) (SHW 2147612772 8 eq_refl) (SHW 2147612780 8 eq_refl) (SHW 2147612788 8 eq_refl) (SHW 2147612796 8 eq_refl) (SHW 2147612804 8 eq_refl)
           (SHW 2147612812 8 eq_refl) (SHW 2147612820 8 eq_refl) (SHW 2147612828 4 eq_refl) (SHW 2147612828 8 eq_refl) (SHW 2147612832 4 eq_refl) (SHW 2147612836 4 eq_refl)
           (SHW 2147612836 8 eq_refl) (SHW 2147612840 4 eq_refl) (SHW 2147612844 4 eq_refl) (SHW 2147612844 8 eq_refl) 
           TIDC HTr
           (XCC 0%nat 6897520 4 0 eq_refl) (XCC1 1%nat 6897555 0 eq_refl eq_refl) (XCC 2%nat 6896992 8 6897000 eq_refl) (XCC 3%nat 6896984 4 6 eq_refl) (XCC 30%nat 6897048 8 449180 eq_refl) (XCC 34%nat 6897304 8 0 eq_refl)
           (XCC 6%nat 6896980 4 0 eq_refl) (STC1 11%nat 1299540 0 eq_refl eq_refl) (XCC 29%nat 6897040 8 874172 eq_refl) (XCC 33%nat 6897296 8 6759144 eq_refl) (XCC1 26%nat 6759144 6 eq_refl eq_refl) (XCC 28%nat 6897032 8 449180 eq_refl)
           (XCC 32%nat 6897288 8 0 eq_refl) (XCC 27%nat 6897024 8 874172 eq_refl) (XCC 31%nat 6897280 8 6759112 eq_refl) (XCC1 25%nat 6759112 16 eq_refl eq_refl) (XCC 22%nat 6897016 8 1148964 eq_refl) (XCC 23%nat 6897272 8 687916 eq_refl)
           (XCC1 24%nat 6759060 0 eq_refl eq_refl) (XCC 4%nat 6897008 8 1148964 eq_refl) (XCC 5%nat 6897264 8 619876 eq_refl) (STC1 10%nat 1907424 0 eq_refl eq_refl) (XCC 7%nat 6897000 8 0 eq_refl) (STC1 3%nat 1295824 0 eq_refl eq_refl)
           (STC 0%nat 1282768 8 1282768 eq_refl) (STC 2%nat 1295744 8 1 eq_refl) (STC 4%nat 1299536 4 1 eq_refl) (STC 5%nat 1299696 8 0 eq_refl) (STC1 8%nat 1313048 1 eq_refl eq_refl) (STC 7%nat 1309752 8 2147450880 eq_refl)
           (DSC 1294272 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143808)) ltac:(img_rd) eq_refl) (DSC 1294288 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (STC1 6%nat 1307804 1 eq_refl eq_refl) (DSC 1294288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (STC 9%nat 1906656 8 18446744073709551615 eq_refl) (STC 1%nat 1283280 8 1219844 eq_refl)
           (DSC 1294328 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294336 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143904)) ltac:(img_rd) eq_refl) (DSC 1294352 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294392 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294400 8%nat (word_to_le_bytes 8 (Z_to_bv 64 143936)) ltac:(img_rd) eq_refl)
           (DSC 1294416 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294456 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294464 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144128)) ltac:(img_rd) eq_refl) (DSC 1294480 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1294520 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294528 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144160)) ltac:(img_rd) eq_refl) (DSC 1294544 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294584 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294592 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144224)) ltac:(img_rd) eq_refl)
           (DSC 1294608 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1294608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1294648 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144256)) ltac:(img_rd) eq_refl) (DSC 1294672 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294712 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144352)) ltac:(img_rd) eq_refl) (DSC 1294736 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1294776 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144448)) ltac:(img_rd) eq_refl)
           (DSC 1294800 1%nat [Z_to_bv 8 128] ltac:(img_rd) eq_refl) (DSC 1294800 8%nat (word_to_le_bytes 8 (Z_to_bv 64 128)) ltac:(img_rd) eq_refl) (DSC 1294840 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144576)) ltac:(img_rd) eq_refl) (DSC 1294864 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1294864 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 1294904 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144672)) ltac:(img_rd) eq_refl) (DSC 1294928 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294928 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1294968 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1294976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144736)) ltac:(img_rd) eq_refl)
           (DSC 1294992 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1294992 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295032 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144800)) ltac:(img_rd) eq_refl) (DSC 1295056 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295056 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295096 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295104 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144864)) ltac:(img_rd) eq_refl) (DSC 1295120 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295120 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295160 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295168 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144928)) ltac:(img_rd) eq_refl)
           (DSC 1295184 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295184 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295224 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295232 8%nat (word_to_le_bytes 8 (Z_to_bv 64 144992)) ltac:(img_rd) eq_refl) (DSC 1295248 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295248 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295288 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295296 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145056)) ltac:(img_rd) eq_refl) (DSC 1295312 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295312 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl) (DSC 1295352 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295360 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145120)) ltac:(img_rd) eq_refl)
           (DSC 1295376 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295376 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295416 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295424 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145216)) ltac:(img_rd) eq_refl) (DSC 1295440 1%nat [Z_to_bv 8 64] ltac:(img_rd) eq_refl) (DSC 1295440 8%nat (word_to_le_bytes 8 (Z_to_bv 64 64)) ltac:(img_rd) eq_refl)
           (DSC 1295480 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295488 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145536)) ltac:(img_rd) eq_refl) (DSC 1295504 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295504 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295544 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295552 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145632)) ltac:(img_rd) eq_refl)
           (DSC 1295568 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295568 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl) (DSC 1295608 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145664)) ltac:(img_rd) eq_refl) (DSC 1295632 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl) (DSC 1295632 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 1295672 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (DSC 1295680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 145696)) ltac:(img_rd) eq_refl) (DSC 1295696 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (DSC 1295696 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (DSC 1295736 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) 
           (XCC 8%nat 6898952 8 0 eq_refl) (XCC 9%nat 1294224 8 1293992 eq_refl) (XCC 10%nat 1294132 4 4294967295 eq_refl)
           (XCC 11%nat 1294032 8 0 eq_refl) (XCC 12%nat 1294048 8 0 eq_refl) (XCC 13%nat 1294000 8 0 eq_refl) (XCC 14%nat 1294008 8 0 eq_refl) (XCC 15%nat 1293984 8 1293752 eq_refl) SOlock
           SOwpos SOwbase SOwrite CANc SOfd) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897000 <= i < 6897520 \/ 6897524 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6898976) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 6898976 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 1293752 /\ (1293752 + 124 <= q \/ q + 32 + 16 <= 1293752 + 120) /\ 1293752 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 1293752 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 6898976 (2 * 3) 0 0 (zero_lines 3%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 1295744) || ((1299704 <=? a) && (a + Z.of_nat n <=? 6896976)) || ((6897524 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 1293752 <= a -> a + n <= 1293752 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 1282048 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
           DDF IMG3 (fun d k Hd Hk => FW3 1293784 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293792 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 1293808 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 1293840 8%nat _ SObuf eq_refl)
           (LIT3 1293848 8%nat _ SObufsz eq_refl) (LIT3 6896960 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl) (cellS 88 56 _ _ Xm56 eq_refl)
           (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl) (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 1293760 8%nat _ SOrpos eq_refl)
           (LIT3 1293768 8%nat _ SOrend eq_refl) (LIT3 1293744 8%nat _ (XCC 16%nat 1293744 8 1293512 eq_refl) eq_refl) (LIT3 1293652 4%nat _ (XCC 17%nat 1293652 4 4294967295 eq_refl) eq_refl) (LIT3 1293552 8%nat _ (XCC 18%nat 1293552 8 0 eq_refl) eq_refl) (LIT3 1293568 8%nat _ (XCC 19%nat 1293568 8 0 eq_refl) eq_refl) (LIT3 1293520 8%nat _ (XCC 20%nat 1293520 8 0 eq_refl) eq_refl)
           (LIT3 1293528 8%nat _ (XCC 21%nat 1293528 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl) (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0x120264) M3 R4 (Z_to_bv 64 0x118588) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0x118588) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.
End Exit.
End FPX_1.
