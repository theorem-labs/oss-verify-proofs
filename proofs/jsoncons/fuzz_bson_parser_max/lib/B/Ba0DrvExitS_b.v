(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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

  Definition exit_preS (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z))
      (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model
    /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS MV a n)
    /\ L5Defs.L5.img_clear MV 65536 1282048
    /\ exitS tid MV.

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0S : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
  intros LB LK cr A M model R S st tid Pre MV StRange R1v R2v R4v R10v Out OutX.
  destruct Pre as (Dinv & Sbot & Stop & Sal & StackW & RomZ & XCells & TidAt & TidIn & HoleZ).
  destruct Out as (FFlags & FBufSz & FWend & FWpos & FWbase & FLock & FLock2 & FStructW & FBufW & FBufData).
  destruct OutX as (FWrite & FFd & FBuf & FRpos & FRend).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dinv) as Lz.
  assert (CellAt : forall a n v,
            existsb (fun c => (fst (fst c) =? a) && (snd (fst c) =? n) && (snd c =? v)) (XC_CELLS_S ++ EX_CELLS) = true ->
            rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
  { intros a n v Found. apply existsb_exists in Found as ([[a' n'] v'] & InTab & Match).
    cbn [fst snd] in Match. apply andb_prop in Match as (Match & Ev). apply andb_prop in Match as (Ea & En).
    apply Z.eqb_eq in Ea, En, Ev. subst a' n' v'.
    destruct (in_app_or _ _ _ InTab) as [InX | InE].
    - exact (proj1 (Forall_forall _ _) XCells _ InX).
    - exact (ex_cell_vis LB LK cr A M model a n v Dinv InE). }
  pose proof (AS0DRVP_dpXS.dpXS_conc fx R MV (fun k : nat => if Nat.eqb k 44 then tid else S)) as Run.
  cbv beta iota delta [Nat.eqb] in Run.
  let cell a w v :=
    first
      [ refine (CellAt a w v _); vm_compute; reflexivity
      | cbv beta delta [L5Defs.L5.u8_at L5Defs.L5.u32_at L5Defs.L5.u64_at];
        first
          [ match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end
          | apply (img_cell MV a (Z.to_nat w));
            [img_rd | lia | cbn; lia | intros i Bi; cbn in Bi; first [apply HoleZ | apply RomZ]; lia] ] ] in
  let prem _ :=
    match goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact R1v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact R2v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact R4v
    | |- AS0DRVP_dpXS.aligned _ _ => exact Sal
    | |- L5Defs.L5.img_clear _ _ _ => exact RomZ
    | |- L5Defs.L5.defined _ ?a ?n =>
      intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
    | |- L5Defs.L5.writable _ _ (Z.pos ?p) ?n =>
      first
        [ apply (sh_writable LB LK cr A M model (Z.pos p) n Dinv); vm_compute; reflexivity
        | refine (wsg_writable MV (Z.pos p) (Z.to_nat n) _ _ _); [vm_compute; reflexivity | lia | cbn; lia] ]
    | |- L5Defs.L5.writable _ _ ?a ?n => apply StackW; lia
    | |- L5Defs.L5.u8_at _ _ ?a ?v => cell a 1 v
    | |- L5Defs.L5.u32_at _ _ ?a ?v => cell a 4 v
    | |- L5Defs.L5.u64_at _ _ ?a ?v => cell a 8 v
    | |- _ => lia
    end in
  repeat specialize (Run ltac:(prem ())).
  destruct Run as (fx1 & R1 & M1 & _ & _ & _ & Steps & Keep & Outs).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ M1 model _ Lz Steps).
  intros M2 model2 MInv2 Same2 _.
  destruct (lzinv_sbm ASEGS (ahid A model) A model model2 Lz MInv2 Same2) as (_ & _ & _ & _ & Live2).
  rewrite <- (proj2 (sbm_fds model model2 Same2)).
  apply (rz_exit_at_lit_lz ASEGS scfg R1 _ M2 _ model2 ECALLW st fetch_exitA is_ecall_ECALLW Live2); [| | exact StRange].
  - left. decompose [and] Outs. assumption.
  - rewrite <- R10v. apply (Keep 10%nat). cbn. intuition.
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
  intros LB LK cr A M model R S st tid canz Pre MV StRange CanRange R1v R2v R4v R10v CanAt Out OutX Fd1.
  destruct Pre as (Dinv & Sbot & Stop & Sal & StackW & RomZ & XCells & TidAt & TidIn & HoleZ).
  destruct Out as (FFlags & FBufSz & FWend & FWpos & FWbase & FLock & FLock2 & FStructW & FBufW & FBufData).
  destruct OutX as (FWrite & FFd & FBuf & FRpos & FRend).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dinv) as Lz.
  assert (CellAt : forall a n v,
            existsb (fun c => (fst (fst c) =? a) && (snd (fst c) =? n) && (snd c =? v)) (XC_CELLS_S ++ EX_CELLS) = true ->
            rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
  { intros a n v Found. apply existsb_exists in Found as ([[a' n'] v'] & InTab & Match).
    cbn [fst snd] in Match. apply andb_prop in Match as (Match & Ev). apply andb_prop in Match as (Ea & En).
    apply Z.eqb_eq in Ea, En, Ev. subst a' n' v'.
    destruct (in_app_or _ _ _ InTab) as [InX | InE].
    - exact (proj1 (Forall_forall _ _) XCells _ InX).
    - exact (ex_cell_vis LB LK cr A M model a n v Dinv InE). }
  pose proof (AS0DRVP_dpX2S_pre.dpX2S_pre_conc fx R MV
                (fun k : nat => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Run.
  cbv beta iota delta [Nat.eqb] in Run.
  let cell a w v :=
    first
      [ refine (CellAt a w v _); vm_compute; reflexivity
      | cbv beta delta [L5Defs.L5.u8_at L5Defs.L5.u32_at L5Defs.L5.u64_at];
        first
          [ match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end
          | apply (img_cell MV a (Z.to_nat w));
            [img_rd | lia | cbn; lia | intros i Bi; cbn in Bi; first [apply HoleZ | apply RomZ]; lia] ] ] in
  let prem _ :=
    match goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact R1v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact R2v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact R4v
    | |- AS0DRVP_dpX2S_pre.aligned _ _ => exact Sal
    | |- L5Defs.L5.img_clear _ _ _ => exact RomZ
    | |- L5Defs.L5.defined _ ?a ?n =>
      intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
    | |- L5Defs.L5.writable _ _ (Z.pos ?p) ?n =>
      first
        [ apply (sh_writable LB LK cr A M model (Z.pos p) n Dinv); vm_compute; reflexivity
        | refine (wsg_writable MV (Z.pos p) (Z.to_nat n) _ _ _); [vm_compute; reflexivity | lia | cbn; lia] ]
    | |- L5Defs.L5.writable _ _ ?a ?n => apply StackW; lia
    | |- L5Defs.L5.u8_at _ _ ?a ?v => cell a 1 v
    | |- L5Defs.L5.u32_at _ _ ?a ?v => cell a 4 v
    | |- L5Defs.L5.u64_at _ _ ?a ?v => cell a 8 v
    | |- _ => lia
    end in
  repeat specialize (Run ltac:(prem ())).
  destruct Run as (fx1 & R1 & M1' & Grow1 & _ & Fr1 & Steps1 & _ & Outs1).
  decompose [and] Outs1. clear Outs1.
  repeat match goal with Junk : L5Defs.L5.u8_at _ M1' _ _ |- _ => clear Junk | Junk : L5Defs.L5.u32_at _ M1' _ _ |- _ => clear Junk end.
  assert (Kept1 : forall i, 65536 <= i < 1294300 \/ 6896960 <= i < 6896968 \/ 6898976 <= i < 6899000 ->
            M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Zone. apply Fr1; lia. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ M1' model _ Lz Steps1).
  intros M1 model1 MInv1 Same1 View1.
  pose proof Lz as (OffSeg & Cover & Awf & _ & _).
  pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 Lz MInv1 Same1) as Lz1.
  apply (@wv_loop fx1 scfg (ahid A model) A OffSeg (m_vm_lazy model) Cover Awf 1293752 1 ltac:(lia)
           (S - 136) (S - 104) ltac:(lia) ltac:(lia)
           (fun x Bx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv ltac:(lia) ltac:(right; lia))
           (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) (length (zero_lines 1)) true R1 M1 model1
           (S - 136) 2 6898976 2 0 0 (zero_lines 1) []).
  - apply le_n.
  - exact (sbm_lazy_eq _ _ Same1).
  - exact MInv1.
  - apply Lz1.
  - rewrite (sbm_fds' _ _ Same1). exact Fd1.
  - unfold wv_regs. repeat split; assumption.
  - rewrite View1. unfold wv_iov.
    pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (StackW (S - 136) 32 ltac:(lia) ltac:(lia))) as IovW.
    repeat match goal with |- _ /\ _ => split end.
    + lia.
    + lia.
    + right. reflexivity.
    + assumption.
    + replace (S - 136 + 8) with (S - 128) by ring. assumption.
    + pose proof (IovW 0 32%nat ltac:(lia) ltac:(cbn; lia)) as IovOk. rewrite Z.add_0_r in IovOk. exact IovOk.
    + unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | right; left; lia | |].
      * apply (rdn_tr MV M1' 6898976 (Z.to_nat 2)); [| lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
        change (Z.to_nat 2) with 2%nat. cbn [zero_lines].
        let rec bytes i :=
          first
            [ reflexivity
            | apply rdn_cons1; [lia | exact (proj1 (FBufData i ltac:(lia))) |];
              apply rdn_cons1; [lia | exact (proj2 (FBufData i ltac:(lia))) |];
              bytes (i + 1) ] in
        bytes 0.
      * intros x Bx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv); lia.
    + discriminate.
    + intros _. repeat match goal with |- _ /\ _ => split end.
      * replace (S - 136 + 16) with (S - 120) by ring. assumption.
      * replace (S - 136 + 24) with (S - 112) by ring. assumption.
      * unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | left; reflexivity | reflexivity | intros x Bx; lia].
      * lia.
  - lia.
  - rewrite View1. apply (rdn_tr MV M1' 1293872 4); [exact FFd | lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
  - intros R2 M2 model2 MInv2 Same2 Keep2 _ View2 _ Grow2.
    rewrite View1 in View2, Grow2.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 Lz1 MInv2 Same2) as Lz2.
    pose proof (mem_grows_trans MV M1' (mrestrict (ahid A model) M2) Grow1 Grow2) as Grow02.
    pose proof (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R2 (mrestrict (ahid A model) M2)
                  (fun k : nat => if Nat.eqb k 2 then S - 144 else if Nat.eqb k 40 then canz
                                  else if Nat.leb 100 k then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat (k - 100))))
                                  else bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k))))) as Run2.
    cbv beta iota delta [Nat.eqb Nat.leb Nat.sub] in Run2.
    let carry a w v :=
      assert (InMV : rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)))
        by first [ exact (CellAt a w v ltac:(vm_compute; reflexivity))
                 | match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end ];
      cbv beta delta [L5Defs.L5.u32_at L5Defs.L5.u64_at]; apply (rdn_tr M1' _ a (Z.to_nat w));
      [ apply (rdn_tr MV M1' a (Z.to_nat w)); [exact InMV | lia | cbn; lia | intros i Bi; cbn in Bi; apply Kept1; lia]
      | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia ] in
    let prem3 _ :=
      match goal with
      | |- 0 <= bv_unsigned _ < _ => apply u64_range
      | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
      | |- getr _ _ = _ => rewrite Keep2 by (cbn [In WV_KEEP]; intuition (apply bv_eq; reflexivity)); assumption
      | |- AS0DRVP_dpXd_2.aligned _ _ =>
        unfold AS0DRVP_dpXd_2.aligned; rewrite <- (Z.mod_add (S - 144) 9 16) by discriminate;
        replace (S - 144 + 9 * 16) with S by ring; exact Sal
      | |- L5Defs.L5.img_clear _ _ _ =>
        intros i Bi; rewrite View2 by lia; rewrite Kept1 by lia; exact (RomZ i Bi)
      | |- L5Defs.L5.defined _ ?a ?n =>
        apply (L5Defs.L5.defined_grows MV _ _ _ Grow02);
        intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
      | |- L5Defs.L5.writable _ _ ?a ?n =>
        apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ Grow02);
        first [apply StackW; lia | intros d k Bd Bk; apply (FStructW a n); lia]
      | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
        let d := eval vm_compute in (144 - k) in
        replace (S - 144 + k) with (S - d) by ring;
        apply (rdn_tr M1' _ (S - d) 8); [assumption | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia]
      | |- L5Defs.L5.u64_at _ _ ?a ?v => carry a 8 v
      | |- L5Defs.L5.u32_at _ _ ?a ?v => carry a 4 v
      | |- _ => lia
      end in
    repeat specialize (Run2 ltac:(prem3 ())).
    destruct Run2 as (fx3 & R3 & M3' & _ & _ & _ & Steps3 & _ & Outs3).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 _ M2 R3 _ M3' model2 _ Lz2 Steps3).
    intros M3 model3 MInv3 Same3 _.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 Lz2 MInv3 Same3) as (_ & _ & _ & _ & Live3).
    assert (FsEq : m_fs model3 = m_fs model).
    { rewrite (proj2 (sbm_fds _ _ Same3)), (proj2 (sbm_fds _ _ Same2)). exact (proj2 (sbm_fds _ _ Same1)). }
    rewrite <- FsEq.
    decompose [and] Outs3.
    apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW Live3); [| | exact StRange].
    + left. assumption.
    + rewrite <- R10v, <- (Z_to_bv_bv_unsigned _ (getr R 10%bv)). assumption.
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
  intros LB LK cr A M model R S st tid canz Pre MV StRange CanRange R1v R2v R4v R10v CanAt Out OutX Fd1.
  destruct Pre as (Dinv & Sbot & Stop & Sal & StackW & RomZ & XCells & TidAt & TidIn & HoleZ).
  destruct Out as (FFlags & FBufSz & FWend & FWpos & FWbase & FLock & FLock2 & FStructW & FBufW & FBufData).
  destruct OutX as (FWrite & FFd & FBuf & FRpos & FRend).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dinv) as Lz.
  assert (CellAt : forall a n v,
            existsb (fun c => (fst (fst c) =? a) && (snd (fst c) =? n) && (snd c =? v)) (XC_CELLS_S ++ EX_CELLS) = true ->
            rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
  { intros a n v Found. apply existsb_exists in Found as ([[a' n'] v'] & InTab & Match).
    cbn [fst snd] in Match. apply andb_prop in Match as (Match & Ev). apply andb_prop in Match as (Ea & En).
    apply Z.eqb_eq in Ea, En, Ev. subst a' n' v'.
    destruct (in_app_or _ _ _ InTab) as [InX | InE].
    - exact (proj1 (Forall_forall _ _) XCells _ InX).
    - exact (ex_cell_vis LB LK cr A M model a n v Dinv InE). }
  pose proof (AS0DRVP_dpX3S_pre.dpX3S_pre_conc fx R MV
                (fun k : nat => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Run.
  cbv beta iota delta [Nat.eqb] in Run.
  let cell a w v :=
    first
      [ refine (CellAt a w v _); vm_compute; reflexivity
      | cbv beta delta [L5Defs.L5.u8_at L5Defs.L5.u32_at L5Defs.L5.u64_at];
        first
          [ match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end
          | apply (img_cell MV a (Z.to_nat w));
            [img_rd | lia | cbn; lia | intros i Bi; cbn in Bi; first [apply HoleZ | apply RomZ]; lia] ] ] in
  let prem _ :=
    match goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact R1v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact R2v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact R4v
    | |- AS0DRVP_dpX3S_pre.aligned _ _ => exact Sal
    | |- L5Defs.L5.img_clear _ _ _ => exact RomZ
    | |- L5Defs.L5.defined _ ?a ?n =>
      intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
    | |- L5Defs.L5.writable _ _ (Z.pos ?p) ?n =>
      first
        [ apply (sh_writable LB LK cr A M model (Z.pos p) n Dinv); vm_compute; reflexivity
        | refine (wsg_writable MV (Z.pos p) (Z.to_nat n) _ _ _); [vm_compute; reflexivity | lia | cbn; lia] ]
    | |- L5Defs.L5.writable _ _ ?a ?n => apply StackW; lia
    | |- L5Defs.L5.u8_at _ _ ?a ?v => cell a 1 v
    | |- L5Defs.L5.u32_at _ _ ?a ?v => cell a 4 v
    | |- L5Defs.L5.u64_at _ _ ?a ?v => cell a 8 v
    | |- _ => lia
    end in
  repeat specialize (Run ltac:(prem ())).
  destruct Run as (fx1 & R1 & M1' & Grow1 & _ & Fr1 & Steps1 & _ & Outs1).
  decompose [and] Outs1. clear Outs1.
  repeat match goal with Junk : L5Defs.L5.u8_at _ M1' _ _ |- _ => clear Junk | Junk : L5Defs.L5.u32_at _ M1' _ _ |- _ => clear Junk end.
  assert (Kept1 : forall i, 65536 <= i < 1294300 \/ 6896960 <= i < 6896968 \/ 6898976 <= i < 6899000 ->
            M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Zone. apply Fr1; lia. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ M1' model _ Lz Steps1).
  intros M1 model1 MInv1 Same1 View1.
  pose proof Lz as (OffSeg & Cover & Awf & _ & _).
  pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 Lz MInv1 Same1) as Lz1.
  apply (@wv_loop fx1 scfg (ahid A model) A OffSeg (m_vm_lazy model) Cover Awf 1293752 1 ltac:(lia)
           (S - 136) (S - 104) ltac:(lia) ltac:(lia)
           (fun x Bx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv ltac:(lia) ltac:(right; lia))
           (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) (length (zero_lines 2)) true R1 M1 model1
           (S - 136) 2 6898976 4 0 0 (zero_lines 2) []).
  - apply le_n.
  - exact (sbm_lazy_eq _ _ Same1).
  - exact MInv1.
  - apply Lz1.
  - rewrite (sbm_fds' _ _ Same1). exact Fd1.
  - unfold wv_regs. repeat split; assumption.
  - rewrite View1. unfold wv_iov.
    pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (StackW (S - 136) 32 ltac:(lia) ltac:(lia))) as IovW.
    repeat match goal with |- _ /\ _ => split end.
    + lia.
    + lia.
    + right. reflexivity.
    + assumption.
    + replace (S - 136 + 8) with (S - 128) by ring. assumption.
    + pose proof (IovW 0 32%nat ltac:(lia) ltac:(cbn; lia)) as IovOk. rewrite Z.add_0_r in IovOk. exact IovOk.
    + unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | right; left; lia | |].
      * apply (rdn_tr MV M1' 6898976 (Z.to_nat 4)); [| lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
        change (Z.to_nat 4) with 4%nat. cbn [zero_lines].
        let rec bytes i :=
          first
            [ reflexivity
            | apply rdn_cons1; [lia | exact (proj1 (FBufData i ltac:(lia))) |];
              apply rdn_cons1; [lia | exact (proj2 (FBufData i ltac:(lia))) |];
              bytes (i + 1) ] in
        bytes 0.
      * intros x Bx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv); lia.
    + discriminate.
    + intros _. repeat match goal with |- _ /\ _ => split end.
      * replace (S - 136 + 16) with (S - 120) by ring. assumption.
      * replace (S - 136 + 24) with (S - 112) by ring. assumption.
      * unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | left; reflexivity | reflexivity | intros x Bx; lia].
      * lia.
  - lia.
  - rewrite View1. apply (rdn_tr MV M1' 1293872 4); [exact FFd | lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
  - intros R2 M2 model2 MInv2 Same2 Keep2 _ View2 _ Grow2.
    rewrite View1 in View2, Grow2.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 Lz1 MInv2 Same2) as Lz2.
    pose proof (mem_grows_trans MV M1' (mrestrict (ahid A model) M2) Grow1 Grow2) as Grow02.
    pose proof (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R2 (mrestrict (ahid A model) M2)
                  (fun k : nat => if Nat.eqb k 2 then S - 144 else if Nat.eqb k 40 then canz
                                  else if Nat.leb 100 k then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat (k - 100))))
                                  else bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k))))) as Run2.
    cbv beta iota delta [Nat.eqb Nat.leb Nat.sub] in Run2.
    let carry a w v :=
      assert (InMV : rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)))
        by first [ exact (CellAt a w v ltac:(vm_compute; reflexivity))
                 | match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end ];
      cbv beta delta [L5Defs.L5.u32_at L5Defs.L5.u64_at]; apply (rdn_tr M1' _ a (Z.to_nat w));
      [ apply (rdn_tr MV M1' a (Z.to_nat w)); [exact InMV | lia | cbn; lia | intros i Bi; cbn in Bi; apply Kept1; lia]
      | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia ] in
    let prem3 _ :=
      match goal with
      | |- 0 <= bv_unsigned _ < _ => apply u64_range
      | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
      | |- getr _ _ = _ => rewrite Keep2 by (cbn [In WV_KEEP]; intuition (apply bv_eq; reflexivity)); assumption
      | |- AS0DRVP_dpXd_3.aligned _ _ =>
        unfold AS0DRVP_dpXd_3.aligned; rewrite <- (Z.mod_add (S - 144) 9 16) by discriminate;
        replace (S - 144 + 9 * 16) with S by ring; exact Sal
      | |- L5Defs.L5.img_clear _ _ _ =>
        intros i Bi; rewrite View2 by lia; rewrite Kept1 by lia; exact (RomZ i Bi)
      | |- L5Defs.L5.defined _ ?a ?n =>
        apply (L5Defs.L5.defined_grows MV _ _ _ Grow02);
        intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
      | |- L5Defs.L5.writable _ _ ?a ?n =>
        apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ Grow02);
        first [apply StackW; lia | intros d k Bd Bk; apply (FStructW a n); lia]
      | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
        let d := eval vm_compute in (144 - k) in
        replace (S - 144 + k) with (S - d) by ring;
        apply (rdn_tr M1' _ (S - d) 8); [assumption | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia]
      | |- L5Defs.L5.u64_at _ _ ?a ?v => carry a 8 v
      | |- L5Defs.L5.u32_at _ _ ?a ?v => carry a 4 v
      | |- _ => lia
      end in
    repeat specialize (Run2 ltac:(prem3 ())).
    destruct Run2 as (fx3 & R3 & M3' & _ & _ & _ & Steps3 & _ & Outs3).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 _ M2 R3 _ M3' model2 _ Lz2 Steps3).
    intros M3 model3 MInv3 Same3 _.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 Lz2 MInv3 Same3) as (_ & _ & _ & _ & Live3).
    assert (FsEq : m_fs model3 = m_fs model).
    { rewrite (proj2 (sbm_fds _ _ Same3)), (proj2 (sbm_fds _ _ Same2)). exact (proj2 (sbm_fds _ _ Same1)). }
    rewrite <- FsEq.
    decompose [and] Outs3.
    apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW Live3); [| | exact StRange].
    + left. assumption.
    + rewrite <- R10v, <- (Z_to_bv_bv_unsigned _ (getr R 10%bv)). assumption.
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
  intros LB LK cr A M model R S st tid canz Pre MV StRange CanRange R1v R2v R4v R10v CanAt Out OutX Fd1.
  destruct Pre as (Dinv & Sbot & Stop & Sal & StackW & RomZ & XCells & TidAt & TidIn & HoleZ).
  destruct Out as (FFlags & FBufSz & FWend & FWpos & FWbase & FLock & FLock2 & FStructW & FBufW & FBufData).
  destruct OutX as (FWrite & FFd & FBuf & FRpos & FRend).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dinv) as Lz.
  assert (CellAt : forall a n v,
            existsb (fun c => (fst (fst c) =? a) && (snd (fst c) =? n) && (snd c =? v)) (XC_CELLS_S ++ EX_CELLS) = true ->
            rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v))).
  { intros a n v Found. apply existsb_exists in Found as ([[a' n'] v'] & InTab & Match).
    cbn [fst snd] in Match. apply andb_prop in Match as (Match & Ev). apply andb_prop in Match as (Ea & En).
    apply Z.eqb_eq in Ea, En, Ev. subst a' n' v'.
    destruct (in_app_or _ _ _ InTab) as [InX | InE].
    - exact (proj1 (Forall_forall _ _) XCells _ InX).
    - exact (ex_cell_vis LB LK cr A M model a n v Dinv InE). }
  pose proof (AS0DRVP_dpX4S_pre.dpX4S_pre_conc fx R MV
                (fun k : nat => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Run.
  cbv beta iota delta [Nat.eqb] in Run.
  let cell a w v :=
    first
      [ refine (CellAt a w v _); vm_compute; reflexivity
      | cbv beta delta [L5Defs.L5.u8_at L5Defs.L5.u32_at L5Defs.L5.u64_at];
        first
          [ match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end
          | apply (img_cell MV a (Z.to_nat w));
            [img_rd | lia | cbn; lia | intros i Bi; cbn in Bi; first [apply HoleZ | apply RomZ]; lia] ] ] in
  let prem _ :=
    match goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact R1v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact R2v
    | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact R4v
    | |- AS0DRVP_dpX4S_pre.aligned _ _ => exact Sal
    | |- L5Defs.L5.img_clear _ _ _ => exact RomZ
    | |- L5Defs.L5.defined _ ?a ?n =>
      intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
    | |- L5Defs.L5.writable _ _ (Z.pos ?p) ?n =>
      first
        [ apply (sh_writable LB LK cr A M model (Z.pos p) n Dinv); vm_compute; reflexivity
        | refine (wsg_writable MV (Z.pos p) (Z.to_nat n) _ _ _); [vm_compute; reflexivity | lia | cbn; lia] ]
    | |- L5Defs.L5.writable _ _ ?a ?n => apply StackW; lia
    | |- L5Defs.L5.u8_at _ _ ?a ?v => cell a 1 v
    | |- L5Defs.L5.u32_at _ _ ?a ?v => cell a 4 v
    | |- L5Defs.L5.u64_at _ _ ?a ?v => cell a 8 v
    | |- _ => lia
    end in
  repeat specialize (Run ltac:(prem ())).
  destruct Run as (fx1 & R1 & M1' & Grow1 & _ & Fr1 & Steps1 & _ & Outs1).
  decompose [and] Outs1. clear Outs1.
  repeat match goal with Junk : L5Defs.L5.u8_at _ M1' _ _ |- _ => clear Junk | Junk : L5Defs.L5.u32_at _ M1' _ _ |- _ => clear Junk end.
  assert (Kept1 : forall i, 65536 <= i < 1294300 \/ 6896960 <= i < 6896968 \/ 6898976 <= i < 6899000 ->
            M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Zone. apply Fr1; lia. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ M1' model _ Lz Steps1).
  intros M1 model1 MInv1 Same1 View1.
  pose proof Lz as (OffSeg & Cover & Awf & _ & _).
  pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 Lz MInv1 Same1) as Lz1.
  apply (@wv_loop fx1 scfg (ahid A model) A OffSeg (m_vm_lazy model) Cover Awf 1293752 1 ltac:(lia)
           (S - 136) (S - 104) ltac:(lia) ltac:(lia)
           (fun x Bx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv ltac:(lia) ltac:(right; lia))
           (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) (length (zero_lines 3)) true R1 M1 model1
           (S - 136) 2 6898976 6 0 0 (zero_lines 3) []).
  - apply le_n.
  - exact (sbm_lazy_eq _ _ Same1).
  - exact MInv1.
  - apply Lz1.
  - rewrite (sbm_fds' _ _ Same1). exact Fd1.
  - unfold wv_regs. repeat split; assumption.
  - rewrite View1. unfold wv_iov.
    pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (StackW (S - 136) 32 ltac:(lia) ltac:(lia))) as IovW.
    repeat match goal with |- _ /\ _ => split end.
    + lia.
    + lia.
    + right. reflexivity.
    + assumption.
    + replace (S - 136 + 8) with (S - 128) by ring. assumption.
    + pose proof (IovW 0 32%nat ltac:(lia) ltac:(cbn; lia)) as IovOk. rewrite Z.add_0_r in IovOk. exact IovOk.
    + unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | right; left; lia | |].
      * apply (rdn_tr MV M1' 6898976 (Z.to_nat 6)); [| lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
        change (Z.to_nat 6) with 6%nat. cbn [zero_lines].
        let rec bytes i :=
          first
            [ reflexivity
            | apply rdn_cons1; [lia | exact (proj1 (FBufData i ltac:(lia))) |];
              apply rdn_cons1; [lia | exact (proj2 (FBufData i ltac:(lia))) |];
              bytes (i + 1) ] in
        bytes 0.
      * intros x Bx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dinv); lia.
    + discriminate.
    + intros _. repeat match goal with |- _ /\ _ => split end.
      * replace (S - 136 + 16) with (S - 120) by ring. assumption.
      * replace (S - 136 + 24) with (S - 112) by ring. assumption.
      * unfold wv_buf. repeat match goal with |- _ /\ _ => split end; [lia | lia | lia | left; reflexivity | reflexivity | intros x Bx; lia].
      * lia.
  - lia.
  - rewrite View1. apply (rdn_tr MV M1' 1293872 4); [exact FFd | lia | cbn; lia | intros i Bi; apply Kept1; cbn in Bi; lia].
  - intros R2 M2 model2 MInv2 Same2 Keep2 _ View2 _ Grow2.
    rewrite View1 in View2, Grow2.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 Lz1 MInv2 Same2) as Lz2.
    pose proof (mem_grows_trans MV M1' (mrestrict (ahid A model) M2) Grow1 Grow2) as Grow02.
    pose proof (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R2 (mrestrict (ahid A model) M2)
                  (fun k : nat => if Nat.eqb k 2 then S - 144 else if Nat.eqb k 40 then canz
                                  else if Nat.leb 100 k then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat (k - 100))))
                                  else bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat k))))) as Run2.
    cbv beta iota delta [Nat.eqb Nat.leb Nat.sub] in Run2.
    let carry a w v :=
      assert (InMV : rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)))
        by first [ exact (CellAt a w v ltac:(vm_compute; reflexivity))
                 | match goal with Known : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Known end ];
      cbv beta delta [L5Defs.L5.u32_at L5Defs.L5.u64_at]; apply (rdn_tr M1' _ a (Z.to_nat w));
      [ apply (rdn_tr MV M1' a (Z.to_nat w)); [exact InMV | lia | cbn; lia | intros i Bi; cbn in Bi; apply Kept1; lia]
      | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia ] in
    let prem3 _ :=
      match goal with
      | |- 0 <= bv_unsigned _ < _ => apply u64_range
      | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
      | |- getr _ _ = _ => rewrite Keep2 by (cbn [In WV_KEEP]; intuition (apply bv_eq; reflexivity)); assumption
      | |- AS0DRVP_dpXd_4.aligned _ _ =>
        unfold AS0DRVP_dpXd_4.aligned; rewrite <- (Z.mod_add (S - 144) 9 16) by discriminate;
        replace (S - 144 + 9 * 16) with S by ring; exact Sal
      | |- L5Defs.L5.img_clear _ _ _ =>
        intros i Bi; rewrite View2 by lia; rewrite Kept1 by lia; exact (RomZ i Bi)
      | |- L5Defs.L5.defined _ ?a ?n =>
        apply (L5Defs.L5.defined_grows MV _ _ _ Grow02);
        intros i Bi; apply (store_ok_defined sp0 MV (a + i)); [lia | apply (StackW a n); lia]
      | |- L5Defs.L5.writable _ _ ?a ?n =>
        apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ Grow02);
        first [apply StackW; lia | intros d k Bd Bk; apply (FStructW a n); lia]
      | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
        let d := eval vm_compute in (144 - k) in
        replace (S - 144 + k) with (S - d) by ring;
        apply (rdn_tr M1' _ (S - d) 8); [assumption | lia | cbn; lia | intros i Bi; cbn in Bi; apply View2; lia]
      | |- L5Defs.L5.u64_at _ _ ?a ?v => carry a 8 v
      | |- L5Defs.L5.u32_at _ _ ?a ?v => carry a 4 v
      | |- _ => lia
      end in
    repeat specialize (Run2 ltac:(prem3 ())).
    destruct Run2 as (fx3 & R3 & M3' & _ & _ & _ & Steps3 & _ & Outs3).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 _ M2 R3 _ M3' model2 _ Lz2 Steps3).
    intros M3 model3 MInv3 Same3 _.
    pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 Lz2 MInv3 Same3) as (_ & _ & _ & _ & Live3).
    assert (FsEq : m_fs model3 = m_fs model).
    { rewrite (proj2 (sbm_fds _ _ Same3)), (proj2 (sbm_fds _ _ Same2)). exact (proj2 (sbm_fds _ _ Same1)). }
    rewrite <- FsEq.
    decompose [and] Outs3.
    apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW Live3); [| | exact StRange].
    + left. assumption.
    + rewrite <- R10v, <- (Z_to_bv_bv_unsigned _ (getr R 10%bv)). assumption.
Qed.
End Exit.
End FPX_1.
