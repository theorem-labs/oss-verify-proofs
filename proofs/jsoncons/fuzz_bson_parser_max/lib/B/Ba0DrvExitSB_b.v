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
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpXSB_b Ba0DrvP_dpX2SB_pre_b Ba0DrvP_dpX3SB_pre_b Ba0DrvP_dpX4SB_pre_b Ba0DrvP_dpXd_2_b Ba0DrvP_dpXd_3_b Ba0DrvP_dpXd_4_b.
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
Definition XC_CELLS_SB : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 8); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0); (6897016, 8, 1148964); (6897272, 8, 687916); (6759060, 1, 0); (6759112, 1, 16); (6759144, 1, 6); (6897024, 8, 874172); (6897032, 8, 449180); (6897040, 8, 874172); (6897048, 8, 449180); (6897056, 8, 872740); (6897064, 8, 449180); (6897280, 8, 6759112); (6897288, 8, 0); (6897296, 8, 6759144); (6897304, 8, 0); (6897312, 8, 1293304); (6897320, 8, 0)].
Definition exitSB (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_SB
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

  Definition exit_preSB (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z))
      (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    dinvA LB LK cr A M model
    /\ usp - 0x1000 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 0x800000 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n)
    /\ L5Defs.L5.img_clear (mrestrict (ahid A model) M) 0x10000 0x139000
    /\ exitSB tid (mrestrict (ahid A model) M).

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0SB : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preSB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
  intros LB LK cr A M model R S st tid PRE MV STR G1 G2 G4 G10 SO SOX.
  destruct PRE as (DI & SLO & SHI & SAL & STKW & IMGC & XSB).
  unfold exitSB in XSB. destruct XSB as (CELLS & TIDC & TIDR & CLR).
  destruct SO as (SO_mode & SO_size & SO_end & SO_wpos & SO_wbase & SO_lk1 & SO_lk2 & SO_fwr & SO_bwr & SO_ln).
  destruct SOX as (SOX_wr & SOX_fd & SOX_buf & SOX_z1 & SOX_z2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model DI) as LZ.
  assert (XCV : forall a n v, In (a, n, v) XC_CELLS_SB -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
    by (intros a n v IN; exact (proj1 (Forall_forall _ _) CELLS _ IN)).
  pose proof (ex_cell_vis LB LK cr A M model) as EXV.
  pose proof (AS0DRVP_dpXSB.dpXSB_conc fx R MV (fun k => match k with 2%nat => S | 44%nat => tid | _ => 0 end)) as RUN.
  cbv beta iota in RUN.
  repeat lazymatch type of RUN with
  | ?P -> _ =>
      let PF := fresh "PF" in
      assert (PF : P);
      [ lazymatch P with
        | _ <= _ < _ => lia
        | _ <= _ <= _ => lia
        | getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | AS0DRVP_dpXSB.aligned _ _ => exact SAL
        | L5Defs.L5.img_clear _ _ _ => exact IMGC
        | L5Defs.L5.writable _ _ ?a ?n =>
            lazymatch a with
            | context [S] => apply STKW; lia
            | _ => first [ exact (sh_writable LB LK cr A M model a n DI eq_refl)
                         | let k := eval vm_compute in (Z.to_nat n) in
                           exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) ]
            end
        | L5Defs.L5.defined _ ?a ?n =>
            intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
            exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
        | L5Defs.L5.u32_at _ _ 6765656 _ => exact TIDC
        | L5Defs.L5.u32_at _ _ 1293892 _ => exact SO_lk1
        | L5Defs.L5.u64_at _ _ 1293792 _ => exact SO_wpos
        | L5Defs.L5.u64_at _ _ 1293808 _ => exact SO_wbase
        | L5Defs.L5.u64_at _ _ 1293760 _ => exact SOX_z1
        | L5Defs.L5.u64_at _ _ 1293768 _ => exact SOX_z2
        | ?cell =>
            let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
            let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
            let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            first [ solve [ refine (eq_trans (XCV a w v _) _);
                            [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ refine (eq_trans (EXV a w v DI _) _);
                            [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ apply img_cell; [ img_rd | lia | simpl Z.of_nat; lia | intros i RNG; apply CLR; simpl Z.of_nat in RNG; lia ] ] ]
        end
      | specialize (RUN PF); clear PF ]
  end.
  destruct RUN as (fx1 & R1 & M1 & _ & _ & _ & STEPS & KEEP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R1_17 & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 1148296) M1 model _ LZ STEPS).
  intros M' model' MI' SBM' _.
  destruct (lzinv_sbm ASEGS (ahid A model) A model model' LZ MI' SBM') as (_ & _ & _ & _ & HALT').
  destruct (sbm_fds model model' SBM') as (_ & FS').
  rewrite <- FS'.
  apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 1148296) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW HALT').
  - left. exact R1_17.
  - exact (eq_trans (KEEP 10%nat ltac:(unfold AS0DRVP_dpXSB.KS_dpXSB; repeat first [apply in_eq | apply in_cons])) G10).
  - exact STR.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2SB : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preSB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz PRE MV STR CZ G1 G2 G4 G10 CAN SO SOX FD1.
  destruct PRE as (DI & SLO & SHI & SAL & STKW & IMGC & XSB).
  unfold exitSB in XSB. destruct XSB as (CELLS & TIDC & TIDR & CLR).
  destruct SO as (SO_mode & SO_size & SO_end & SO_wpos & SO_wbase & SO_lk1 & SO_lk2 & SO_fwr & SO_bwr & SO_ln).
  destruct SOX as (SOX_wr & SOX_fd & SOX_buf & SOX_z1 & SOX_z2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model DI) as LZ.
  pose proof (proj1 LZ) as HOFF. pose proof (proj1 (proj2 LZ)) as LCOV.
  pose proof (proj1 (proj2 (proj2 LZ))) as AWF. pose proof (proj1 (proj2 (proj2 (proj2 LZ)))) as MINV.
  pose proof (proj2 (proj2 (proj2 (proj2 LZ)))) as HALT.
  assert (XCV : forall a n v, In (a, n, v) XC_CELLS_SB -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
    by (intros a n v IN; exact (proj1 (Forall_forall _ _) CELLS _ IN)).
  pose proof (ex_cell_vis LB LK cr A M model) as EXV.
  assert (BS1 : rdn ASEGS MV (Z_to_bv 64 6898977) 1%nat = Some (Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898977 (Z_to_bv 8 10) 0%nat [] ltac:(lia) (proj2 (SO_ln 0 ltac:(lia))) (eq_refl : rdn ASEGS MV (Z_to_bv 64 6898978) 0%nat = Some []))).
  assert (BS : rdn ASEGS MV (Z_to_bv 64 6898976) 2%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898976 (Z_to_bv 8 48) 1%nat [Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 0 ltac:(lia))) BS1)).
  pose proof (AS0DRVP_dpX2SB_pre.dpX2SB_pre_conc fx R MV
     (fun k => match k with 2%nat => S | 40%nat => canz | 44%nat => tid | _ => 0 end)) as RUN.
  cbv beta iota in RUN.
  repeat lazymatch type of RUN with
  | ?P -> _ =>
      let PF := fresh "PF" in
      assert (PF : P);
      [ lazymatch P with
        | _ <= _ < _ => lia
        | _ <= _ <= _ => lia
        | getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | AS0DRVP_dpX2SB_pre.aligned _ _ => exact SAL
        | L5Defs.L5.img_clear _ _ _ => exact IMGC
        | L5Defs.L5.writable _ _ ?a ?n =>
            lazymatch a with
            | context [S] => apply STKW; lia
            | _ => first [ exact (sh_writable LB LK cr A M model a n DI eq_refl)
                         | let k := eval vm_compute in (Z.to_nat n) in
                           exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) ]
            end
        | L5Defs.L5.defined _ ?a ?n =>
            intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
            exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
        | L5Defs.L5.u32_at _ _ 6765656 _ => exact TIDC
        | L5Defs.L5.u32_at _ _ 1293892 _ => exact SO_lk1
        | L5Defs.L5.u32_at _ _ 1293872 _ => exact SOX_fd
        | L5Defs.L5.u64_at _ _ 1293792 _ => exact SO_wpos
        | L5Defs.L5.u64_at _ _ 1293808 _ => exact SO_wbase
        | L5Defs.L5.u64_at _ _ 1293824 _ => exact SOX_wr
        | L5Defs.L5.u64_at _ _ 1293760 _ => exact SOX_z1
        | L5Defs.L5.u64_at _ _ 1293768 _ => exact SOX_z2
        | L5Defs.L5.u64_at _ _ 6896960 _ => exact CAN
        | ?cell =>
            let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
            let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
            let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            first [ solve [ refine (eq_trans (XCV a w v _) _);
                            [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ refine (eq_trans (EXV a w v DI _) _);
                            [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ apply img_cell; [ img_rd | lia | simpl Z.of_nat; lia | intros i RNG; apply CLR; simpl Z.of_nat in RNG; lia ] ] ]
        end
      | specialize (RUN PF); clear PF ]
  end.
  destruct RUN as (
    fx1 & R1 & M1 & GROW1 & FRW1 & FRZ1 & STEPS1 & KEEP1 & _ & Q2 & _ & _ & _ & Q8 & Q9 & Q10 & Q11 & Q12 & _ & _ & _ & _ & Q17 & Q18 & Q19 & Q21 &
    Q22 & _ & C112 & C120 & C128 & C136 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 1180248) M1 model _ LZ STEPS1).
  intros M2 model2 MI2 SBM2 RS2.
  assert (FR1 : forall i : Z, (0 <= i < 1295744 \/ (6896960 <= i /\ i < 6896968) \/ (6898900 <= i /\ i < 6899000)) ->
                 M1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRZ1; lia).
  assert (FR1w : forall x : word, (0 <= bv_unsigned x < 1295744 \/ (6896960 <= bv_unsigned x /\ bv_unsigned x < 6896968) \/ (6898900 <= bv_unsigned x /\ bv_unsigned x < 6899000)) ->
                 M1 x = MV x)
    by (intros x CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRW1; lia).
  assert (TR1 : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                 rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs ANN BND RD. apply (rdn_frame_w MV M1 a n bs RD ANN ltac:(destruct BND as [BND|[BND|BND]]; lia)).
    intros x XIN. apply FR1w. destruct BND as [BND | [BND | BND]]; [left | right; left | right; right]; lia. }
  assert (NLQ : forall x : Z, S - 136 <= x < S - 104 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
  { intros x XIN.
    pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 (S - 136)) 32
       (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NL.
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    specialize (NL ltac:(lia) ltac:(intros k KIN; right; left; lia) (x - (S - 136)) ltac:(lia)).
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    replace (S - 136 + (x - (S - 136))) with x in NL by lia. exact NL. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A HOFF (m_vm_lazy model) LCOV AWF 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(repeat split; lia) ltac:(split; [lia | split; [left; lia | lia]]) NLQ
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 2%nat) as WV.
  unfold W. apply (WV true R1 M2 model2 (S - 136) 2 6898976 2 0 0 (zero_lines 1) []).
  - reflexivity.
  - apply (sbm_lazy_eq model model2 SBM2).
  - exact MI2.
  - rewrite (sbm_halted_eq model model2 SBM2). exact HALT.
  - rewrite (proj1 (sbm_fds model model2 SBM2)). exact FD1.
  - split; [exact Q17 | split; [exact Q10 | split; [exact Q11 | split; [exact Q12 | split; [exact Q9 | split; [exact Q18 | split; [exact Q22 | exact Q19]]]]]]].
  - rewrite RS2. split; [lia | split; [lia | split; [right; reflexivity | ]]].
    split; [exact C136 | ].
    replace (S - 136 + 8) with (S - 128) by lia. split; [exact C128 | ].
    split.
    { pose proof (L5Defs.L5.writable_grows ASEGS MV M1 (S - 136) 32 GROW1
        (STKW (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(simpl Z.of_nat; lia)) as SW.
      rewrite Z.add_0_r in SW. change (Z.to_nat (16 * 2)) with 32%nat. exact SW. }
    split.
    + split; [lia | split; [lia | split; [lia | split; [right; left; lia | split ]]]].
      * exact (TR1 6898976 2%nat (zero_lines 1) ltac:(lia) ltac:(right; right; split; [lia | simpl Z.of_nat; lia]) BS).
      * intros x XIN.
        pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 6898976) 2
          (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NLB.
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        specialize (NLB ltac:(lia) ltac:(intros k KIN; left; lia) (x - 6898976) ltac:(lia)).
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        replace (6898976 + (x - 6898976)) with x in NLB by lia. exact NLB.
    + split; [intros CC; discriminate CC | intros _ ].
      replace (S - 136 + 16) with (S - 120) by lia. split; [exact C120 | ].
      replace (S - 136 + 24) with (S - 112) by lia. split; [exact C112 | ].
      split; [ split; [lia | split; [lia | split; [lia | split; [left; reflexivity | split; [reflexivity | intros x XIN; exfalso; lia]]]]] | lia ].
  - lia.
  - rewrite RS2. exact (TR1 1293872 4%nat _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia) SOX_fd).
  - intros R3 M3 model3 MI3 SBM3 KEEP3 FRM3 FRV3 GR3 GRV3.
    assert (SBM13 : same_but_materialized model model3) by (exact (same_but_materialized_trans model model2 model3 SBM2 SBM3)).
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3) by (exact (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3 SBM13)).
    assert (GRW : mem_grows MV (mrestrict (ahid A model) M3)) by (intros x XIN; apply GRV3; rewrite RS2; exact (GROW1 x XIN)).
    assert (FR3w : forall x : word, (bv_unsigned x < S - 136 \/ S - 104 <= bv_unsigned x) -> mrestrict (ahid A model) M3 x = M1 x).
    { intros x CASE. pose proof (u64_range x) as XR. rewrite <- RS2. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      destruct CASE as [CASE|CASE]; apply FRV3; lia. }
    assert (TR3 : forall a (n : nat) bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= S - 136 \/ S - 104 <= a) ->
                    rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND SIDE RD. apply (rdn_frame_w M1 _ a n bs RD ANN BND).
      intros x XIN. apply FR3w. destruct SIDE as [SIDE|SIDE]; [left | right]; lia. }
    assert (TRV : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                    rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND RD.
      apply (TR3 a n bs ANN ltac:(destruct BND as [BND|[BND|BND]]; lia) ltac:(left; destruct BND as [BND|[BND|BND]]; lia) (TR1 a n bs ANN BND RD)). }
    change (getr R (Z_to_bv 5 (Z.of_nat 10))) with (getr R 10%bv) in C32. rewrite G10, Z_to_bv_unsigned in C32.
    rewrite (bv_wrap_small 64 st) in C32 by (unfold bv_modulus; simpl Z.of_N; lia).
    pose proof (u64_range (getr R 9%bv)). pose proof (u64_range (getr R 18%bv)). pose proof (u64_range (getr R 19%bv)).
    pose proof (u64_range (getr R 20%bv)). pose proof (u64_range (getr R 21%bv)). pose proof (u64_range (getr R 22%bv)).
    pose proof (u64_range (getr R3 10%bv)). pose proof (u64_range (getr R3 18%bv)). pose proof (u64_range (getr R3 19%bv)).
    pose proof (u64_range (getr R3 20%bv)). pose proof (u64_range (getr R3 22%bv)).
    pose proof (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 (mrestrict (ahid A model) M3)
      (fun k => match k with
                | 2%nat => S - 144 | 9%nat => bv_unsigned (getr R 9%bv) | 10%nat => st
                | 18%nat => bv_unsigned (getr R 18%bv) | 19%nat => bv_unsigned (getr R 19%bv)
                | 20%nat => bv_unsigned (getr R 20%bv) | 21%nat => bv_unsigned (getr R 21%bv)
                | 22%nat => bv_unsigned (getr R 22%bv) | 40%nat => canz
                | 110%nat => bv_unsigned (getr R3 10%bv) | 118%nat => bv_unsigned (getr R3 18%bv)
                | 119%nat => bv_unsigned (getr R3 19%bv) | 120%nat => bv_unsigned (getr R3 20%bv)
                | 122%nat => bv_unsigned (getr R3 22%bv) | _ => 0 end)) as RUN3.
    cbv beta iota in RUN3.
    replace (S - 144 + 40) with (S - 104) in RUN3 by lia.
    replace (S - 144 + 48) with (S - 96) in RUN3 by lia.
    replace (S - 144 + 56) with (S - 88) in RUN3 by lia.
    replace (S - 144 + 64) with (S - 80) in RUN3 by lia.
    replace (S - 144 + 72) with (S - 72) in RUN3 by lia.
    replace (S - 144 + 80) with (S - 64) in RUN3 by lia.
    replace (S - 144 + 88) with (S - 56) in RUN3 by lia.
    replace (S - 144 + 96) with (S - 48) in RUN3 by lia.
    replace (S - 144 + 104) with (S - 40) in RUN3 by lia.
    replace (S - 144 + 112) with (S - 32) in RUN3 by lia.
    replace (S - 144 + 120) with (S - 24) in RUN3 by lia.
    replace (S - 144 - 16) with (S - 160) in RUN3 by lia.
    repeat lazymatch type of RUN3 with
    | ?P -> _ =>
        let PF := fresh "PF" in
        assert (PF : P);
        [ lazymatch P with
          | _ <= _ < _ => lia
          | _ <= _ <= _ => lia
          | getr _ _ = _ =>
              first [ exact (eq_trans (KEEP3 2%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q2)
                    | exact (eq_trans (KEEP3 8%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q8)
                    | exact (eq_trans (KEEP3 9%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q9)
                    | exact (eq_trans (KEEP3 21%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q21)
                    | symmetry; apply Z_to_bv_bv_unsigned ]
          | AS0DRVP_dpXd_2.aligned _ _ => unfold AS0DRVP_dpXd_2.aligned; rewrite Zminus_mod, SAL; reflexivity
          | L5Defs.L5.img_clear _ _ _ =>
              intros i RNG;
              rewrite (FR3w (Z_to_bv 64 i) ltac:(left; rewrite Z_to_bv_unsigned, (bv_wrap_small 64 i) by (unfold bv_modulus; simpl Z.of_N; lia); lia));
              rewrite (FR1 i ltac:(left; lia)); apply IMGC; lia
          | L5Defs.L5.writable _ _ ?a ?n =>
              lazymatch a with
              | context [S] => apply (L5Defs.L5.writable_grows ASEGS MV _ a n GRW); apply STKW; lia
              | _ => let k := eval vm_compute in (Z.to_nat n) in
                     exact (wsg_writable (mrestrict (ahid A model) M3) a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))
              end
          | L5Defs.L5.defined _ ?a ?n =>
              apply (L5Defs.L5.defined_grows MV _ a n GRW);
              intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
              exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
          | ?cell =>
              let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
              let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
              let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
              let wn := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8%nat) | L5Defs.L5.u32_at _ _ _ _ => constr:(4%nat) | L5Defs.L5.u8_at _ _ _ _ => constr:(1%nat) end in
              unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
              lazymatch a with
              | context [S] =>
                  apply (TR3 a wn _ ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(right; lia));
                  lazymatch a with
                  | S - 24 => exact C24 | S - 32 => exact C32 | S - 40 => exact C40 | S - 48 => exact C48
                  | S - 56 => exact C56 | S - 64 => exact C64 | S - 72 => exact C72 | S - 80 => exact C80
                  | S - 88 => exact C88 | S - 96 => exact C96 | S - 104 => exact C104
                  end
              | 6896960 =>
                  apply (TRV a wn _ ltac:(lia) ltac:(right; left; split; [lia | simpl Z.of_nat; lia])); exact CAN
              | _ =>
                  apply (TRV a wn _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia));
                  lazymatch a with
                  | 1293752 => exact SO_mode | 1293848 => exact SO_size | 1293784 => exact SO_end
                  | 1293792 => exact SO_wpos | 1293808 => exact SO_wbase | 1293892 => exact SO_lk1 | 1293896 => exact SO_lk2
                  | 1293824 => exact SOX_wr | 1293872 => exact SOX_fd | 1293840 => exact SOX_buf
                  | 1293760 => exact SOX_z1 | 1293768 => exact SOX_z2
                  | _ => first [ solve [ refine (eq_trans (XCV a w v _) _);
                                         [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                               | solve [ refine (eq_trans (EXV a w v DI _) _);
                                         [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ] ]
                  end
              end
          end
        | specialize (RUN3 PF); clear PF ]
    end.
    destruct RUN3 as (fx4 & R4 & M4 & GROW3 & FRW3 & FRZ3 & STEPS3 & _ & _ & _ & _ & _ & T10 & _ & _ & T17 & _ & _ & _ & _ & _ & _ & _ & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 (Z_to_bv 64 1180260) M3 R4 (Z_to_bv 64 1148296) M4 model3 _ LZ3 STEPS3).
    intros M5 model4 MI4 SBM4 RS4.
    assert (SBM14 : same_but_materialized model model4) by (exact (same_but_materialized_trans model model3 model4 SBM13 SBM4)).
    destruct (lzinv_sbm ASEGS (ahid A model) A model model4 LZ MI4 SBM14) as (_ & _ & _ & _ & HALT4).
    rewrite <- (proj2 (sbm_fds model model4 SBM14)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 1148296) M5 rom model4 ECALLW st fetch_exitA is_ecall_ECALLW HALT4).
    + left. exact T17.
    + exact T10.
    + exact STR.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3SB : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preSB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz PRE MV STR CZ G1 G2 G4 G10 CAN SO SOX FD1.
  destruct PRE as (DI & SLO & SHI & SAL & STKW & IMGC & XSB).
  unfold exitSB in XSB. destruct XSB as (CELLS & TIDC & TIDR & CLR).
  destruct SO as (SO_mode & SO_size & SO_end & SO_wpos & SO_wbase & SO_lk1 & SO_lk2 & SO_fwr & SO_bwr & SO_ln).
  destruct SOX as (SOX_wr & SOX_fd & SOX_buf & SOX_z1 & SOX_z2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model DI) as LZ.
  pose proof (proj1 LZ) as HOFF. pose proof (proj1 (proj2 LZ)) as LCOV.
  pose proof (proj1 (proj2 (proj2 LZ))) as AWF. pose proof (proj1 (proj2 (proj2 (proj2 LZ)))) as MINV.
  pose proof (proj2 (proj2 (proj2 (proj2 LZ)))) as HALT.
  assert (XCV : forall a n v, In (a, n, v) XC_CELLS_SB -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
    by (intros a n v IN; exact (proj1 (Forall_forall _ _) CELLS _ IN)).
  pose proof (ex_cell_vis LB LK cr A M model) as EXV.
  assert (BS3 : rdn ASEGS MV (Z_to_bv 64 6898979) 1%nat = Some (Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898979 (Z_to_bv 8 10) 0%nat [] ltac:(lia) (proj2 (SO_ln 1 ltac:(lia))) (eq_refl : rdn ASEGS MV (Z_to_bv 64 6898980) 0%nat = Some []))).
  assert (BS2 : rdn ASEGS MV (Z_to_bv 64 6898978) 2%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898978 (Z_to_bv 8 48) 1%nat [Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 1 ltac:(lia))) BS3)).
  assert (BS1 : rdn ASEGS MV (Z_to_bv 64 6898977) 3%nat = Some (Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898977 (Z_to_bv 8 10) 2%nat [Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj2 (SO_ln 0 ltac:(lia))) BS2)).
  assert (BS : rdn ASEGS MV (Z_to_bv 64 6898976) 4%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898976 (Z_to_bv 8 48) 3%nat [Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 0 ltac:(lia))) BS1)).
  pose proof (AS0DRVP_dpX3SB_pre.dpX3SB_pre_conc fx R MV
     (fun k => match k with 2%nat => S | 40%nat => canz | 44%nat => tid | _ => 0 end)) as RUN.
  cbv beta iota in RUN.
  repeat lazymatch type of RUN with
  | ?P -> _ =>
      let PF := fresh "PF" in
      assert (PF : P);
      [ lazymatch P with
        | _ <= _ < _ => lia
        | _ <= _ <= _ => lia
        | getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | AS0DRVP_dpX3SB_pre.aligned _ _ => exact SAL
        | L5Defs.L5.img_clear _ _ _ => exact IMGC
        | L5Defs.L5.writable _ _ ?a ?n =>
            lazymatch a with
            | context [S] => apply STKW; lia
            | _ => first [ exact (sh_writable LB LK cr A M model a n DI eq_refl)
                         | let k := eval vm_compute in (Z.to_nat n) in
                           exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) ]
            end
        | L5Defs.L5.defined _ ?a ?n =>
            intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
            exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
        | L5Defs.L5.u32_at _ _ 6765656 _ => exact TIDC
        | L5Defs.L5.u32_at _ _ 1293892 _ => exact SO_lk1
        | L5Defs.L5.u32_at _ _ 1293872 _ => exact SOX_fd
        | L5Defs.L5.u64_at _ _ 1293792 _ => exact SO_wpos
        | L5Defs.L5.u64_at _ _ 1293808 _ => exact SO_wbase
        | L5Defs.L5.u64_at _ _ 1293824 _ => exact SOX_wr
        | L5Defs.L5.u64_at _ _ 1293760 _ => exact SOX_z1
        | L5Defs.L5.u64_at _ _ 1293768 _ => exact SOX_z2
        | L5Defs.L5.u64_at _ _ 6896960 _ => exact CAN
        | ?cell =>
            let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
            let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
            let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            first [ solve [ refine (eq_trans (XCV a w v _) _);
                            [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ refine (eq_trans (EXV a w v DI _) _);
                            [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ apply img_cell; [ img_rd | lia | simpl Z.of_nat; lia | intros i RNG; apply CLR; simpl Z.of_nat in RNG; lia ] ] ]
        end
      | specialize (RUN PF); clear PF ]
  end.
  destruct RUN as (
    fx1 & R1 & M1 & GROW1 & FRW1 & FRZ1 & STEPS1 & KEEP1 & _ & Q2 & _ & _ & _ & Q8 & Q9 & Q10 & Q11 & Q12 & _ & _ & _ & _ & Q17 & Q18 & Q19 & Q21 &
    Q22 & _ & C112 & C120 & C128 & C136 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 1180248) M1 model _ LZ STEPS1).
  intros M2 model2 MI2 SBM2 RS2.
  assert (FR1 : forall i : Z, (0 <= i < 1295744 \/ (6896960 <= i /\ i < 6896968) \/ (6898900 <= i /\ i < 6899000)) ->
                 M1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRZ1; lia).
  assert (FR1w : forall x : word, (0 <= bv_unsigned x < 1295744 \/ (6896960 <= bv_unsigned x /\ bv_unsigned x < 6896968) \/ (6898900 <= bv_unsigned x /\ bv_unsigned x < 6899000)) ->
                 M1 x = MV x)
    by (intros x CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRW1; lia).
  assert (TR1 : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                 rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs ANN BND RD. apply (rdn_frame_w MV M1 a n bs RD ANN ltac:(destruct BND as [BND|[BND|BND]]; lia)).
    intros x XIN. apply FR1w. destruct BND as [BND | [BND | BND]]; [left | right; left | right; right]; lia. }
  assert (NLQ : forall x : Z, S - 136 <= x < S - 104 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
  { intros x XIN.
    pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 (S - 136)) 32
       (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NL.
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    specialize (NL ltac:(lia) ltac:(intros k KIN; right; left; lia) (x - (S - 136)) ltac:(lia)).
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    replace (S - 136 + (x - (S - 136))) with x in NL by lia. exact NL. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A HOFF (m_vm_lazy model) LCOV AWF 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(repeat split; lia) ltac:(split; [lia | split; [left; lia | lia]]) NLQ
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 4%nat) as WV.
  unfold W. apply (WV true R1 M2 model2 (S - 136) 2 6898976 4 0 0 (zero_lines 2) []).
  - reflexivity.
  - apply (sbm_lazy_eq model model2 SBM2).
  - exact MI2.
  - rewrite (sbm_halted_eq model model2 SBM2). exact HALT.
  - rewrite (proj1 (sbm_fds model model2 SBM2)). exact FD1.
  - split; [exact Q17 | split; [exact Q10 | split; [exact Q11 | split; [exact Q12 | split; [exact Q9 | split; [exact Q18 | split; [exact Q22 | exact Q19]]]]]]].
  - rewrite RS2. split; [lia | split; [lia | split; [right; reflexivity | ]]].
    split; [exact C136 | ].
    replace (S - 136 + 8) with (S - 128) by lia. split; [exact C128 | ].
    split.
    { pose proof (L5Defs.L5.writable_grows ASEGS MV M1 (S - 136) 32 GROW1
        (STKW (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(simpl Z.of_nat; lia)) as SW.
      rewrite Z.add_0_r in SW. change (Z.to_nat (16 * 2)) with 32%nat. exact SW. }
    split.
    + split; [lia | split; [lia | split; [lia | split; [right; left; lia | split ]]]].
      * exact (TR1 6898976 4%nat (zero_lines 2) ltac:(lia) ltac:(right; right; split; [lia | simpl Z.of_nat; lia]) BS).
      * intros x XIN.
        pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 6898976) 4
          (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NLB.
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        specialize (NLB ltac:(lia) ltac:(intros k KIN; left; lia) (x - 6898976) ltac:(lia)).
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        replace (6898976 + (x - 6898976)) with x in NLB by lia. exact NLB.
    + split; [intros CC; discriminate CC | intros _ ].
      replace (S - 136 + 16) with (S - 120) by lia. split; [exact C120 | ].
      replace (S - 136 + 24) with (S - 112) by lia. split; [exact C112 | ].
      split; [ split; [lia | split; [lia | split; [lia | split; [left; reflexivity | split; [reflexivity | intros x XIN; exfalso; lia]]]]] | lia ].
  - lia.
  - rewrite RS2. exact (TR1 1293872 4%nat _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia) SOX_fd).
  - intros R3 M3 model3 MI3 SBM3 KEEP3 FRM3 FRV3 GR3 GRV3.
    assert (SBM13 : same_but_materialized model model3) by (exact (same_but_materialized_trans model model2 model3 SBM2 SBM3)).
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3) by (exact (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3 SBM13)).
    assert (GRW : mem_grows MV (mrestrict (ahid A model) M3)) by (intros x XIN; apply GRV3; rewrite RS2; exact (GROW1 x XIN)).
    assert (FR3w : forall x : word, (bv_unsigned x < S - 136 \/ S - 104 <= bv_unsigned x) -> mrestrict (ahid A model) M3 x = M1 x).
    { intros x CASE. pose proof (u64_range x) as XR. rewrite <- RS2. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      destruct CASE as [CASE|CASE]; apply FRV3; lia. }
    assert (TR3 : forall a (n : nat) bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= S - 136 \/ S - 104 <= a) ->
                    rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND SIDE RD. apply (rdn_frame_w M1 _ a n bs RD ANN BND).
      intros x XIN. apply FR3w. destruct SIDE as [SIDE|SIDE]; [left | right]; lia. }
    assert (TRV : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                    rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND RD.
      apply (TR3 a n bs ANN ltac:(destruct BND as [BND|[BND|BND]]; lia) ltac:(left; destruct BND as [BND|[BND|BND]]; lia) (TR1 a n bs ANN BND RD)). }
    change (getr R (Z_to_bv 5 (Z.of_nat 10))) with (getr R 10%bv) in C32. rewrite G10, Z_to_bv_unsigned in C32.
    rewrite (bv_wrap_small 64 st) in C32 by (unfold bv_modulus; simpl Z.of_N; lia).
    pose proof (u64_range (getr R 9%bv)). pose proof (u64_range (getr R 18%bv)). pose proof (u64_range (getr R 19%bv)).
    pose proof (u64_range (getr R 20%bv)). pose proof (u64_range (getr R 21%bv)). pose proof (u64_range (getr R 22%bv)).
    pose proof (u64_range (getr R3 10%bv)). pose proof (u64_range (getr R3 18%bv)). pose proof (u64_range (getr R3 19%bv)).
    pose proof (u64_range (getr R3 20%bv)). pose proof (u64_range (getr R3 22%bv)).
    pose proof (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 (mrestrict (ahid A model) M3)
      (fun k => match k with
                | 2%nat => S - 144 | 9%nat => bv_unsigned (getr R 9%bv) | 10%nat => st
                | 18%nat => bv_unsigned (getr R 18%bv) | 19%nat => bv_unsigned (getr R 19%bv)
                | 20%nat => bv_unsigned (getr R 20%bv) | 21%nat => bv_unsigned (getr R 21%bv)
                | 22%nat => bv_unsigned (getr R 22%bv) | 40%nat => canz
                | 110%nat => bv_unsigned (getr R3 10%bv) | 118%nat => bv_unsigned (getr R3 18%bv)
                | 119%nat => bv_unsigned (getr R3 19%bv) | 120%nat => bv_unsigned (getr R3 20%bv)
                | 122%nat => bv_unsigned (getr R3 22%bv) | _ => 0 end)) as RUN3.
    cbv beta iota in RUN3.
    replace (S - 144 + 40) with (S - 104) in RUN3 by lia.
    replace (S - 144 + 48) with (S - 96) in RUN3 by lia.
    replace (S - 144 + 56) with (S - 88) in RUN3 by lia.
    replace (S - 144 + 64) with (S - 80) in RUN3 by lia.
    replace (S - 144 + 72) with (S - 72) in RUN3 by lia.
    replace (S - 144 + 80) with (S - 64) in RUN3 by lia.
    replace (S - 144 + 88) with (S - 56) in RUN3 by lia.
    replace (S - 144 + 96) with (S - 48) in RUN3 by lia.
    replace (S - 144 + 104) with (S - 40) in RUN3 by lia.
    replace (S - 144 + 112) with (S - 32) in RUN3 by lia.
    replace (S - 144 + 120) with (S - 24) in RUN3 by lia.
    replace (S - 144 - 16) with (S - 160) in RUN3 by lia.
    repeat lazymatch type of RUN3 with
    | ?P -> _ =>
        let PF := fresh "PF" in
        assert (PF : P);
        [ lazymatch P with
          | _ <= _ < _ => lia
          | _ <= _ <= _ => lia
          | getr _ _ = _ =>
              first [ exact (eq_trans (KEEP3 2%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q2)
                    | exact (eq_trans (KEEP3 8%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q8)
                    | exact (eq_trans (KEEP3 9%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q9)
                    | exact (eq_trans (KEEP3 21%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q21)
                    | symmetry; apply Z_to_bv_bv_unsigned ]
          | AS0DRVP_dpXd_3.aligned _ _ => unfold AS0DRVP_dpXd_3.aligned; rewrite Zminus_mod, SAL; reflexivity
          | L5Defs.L5.img_clear _ _ _ =>
              intros i RNG;
              rewrite (FR3w (Z_to_bv 64 i) ltac:(left; rewrite Z_to_bv_unsigned, (bv_wrap_small 64 i) by (unfold bv_modulus; simpl Z.of_N; lia); lia));
              rewrite (FR1 i ltac:(left; lia)); apply IMGC; lia
          | L5Defs.L5.writable _ _ ?a ?n =>
              lazymatch a with
              | context [S] => apply (L5Defs.L5.writable_grows ASEGS MV _ a n GRW); apply STKW; lia
              | _ => let k := eval vm_compute in (Z.to_nat n) in
                     exact (wsg_writable (mrestrict (ahid A model) M3) a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))
              end
          | L5Defs.L5.defined _ ?a ?n =>
              apply (L5Defs.L5.defined_grows MV _ a n GRW);
              intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
              exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
          | ?cell =>
              let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
              let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
              let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
              let wn := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8%nat) | L5Defs.L5.u32_at _ _ _ _ => constr:(4%nat) | L5Defs.L5.u8_at _ _ _ _ => constr:(1%nat) end in
              unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
              lazymatch a with
              | context [S] =>
                  apply (TR3 a wn _ ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(right; lia));
                  lazymatch a with
                  | S - 24 => exact C24 | S - 32 => exact C32 | S - 40 => exact C40 | S - 48 => exact C48
                  | S - 56 => exact C56 | S - 64 => exact C64 | S - 72 => exact C72 | S - 80 => exact C80
                  | S - 88 => exact C88 | S - 96 => exact C96 | S - 104 => exact C104
                  end
              | 6896960 =>
                  apply (TRV a wn _ ltac:(lia) ltac:(right; left; split; [lia | simpl Z.of_nat; lia])); exact CAN
              | _ =>
                  apply (TRV a wn _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia));
                  lazymatch a with
                  | 1293752 => exact SO_mode | 1293848 => exact SO_size | 1293784 => exact SO_end
                  | 1293792 => exact SO_wpos | 1293808 => exact SO_wbase | 1293892 => exact SO_lk1 | 1293896 => exact SO_lk2
                  | 1293824 => exact SOX_wr | 1293872 => exact SOX_fd | 1293840 => exact SOX_buf
                  | 1293760 => exact SOX_z1 | 1293768 => exact SOX_z2
                  | _ => first [ solve [ refine (eq_trans (XCV a w v _) _);
                                         [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                               | solve [ refine (eq_trans (EXV a w v DI _) _);
                                         [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ] ]
                  end
              end
          end
        | specialize (RUN3 PF); clear PF ]
    end.
    destruct RUN3 as (fx4 & R4 & M4 & GROW3 & FRW3 & FRZ3 & STEPS3 & _ & _ & _ & _ & _ & T10 & _ & _ & T17 & _ & _ & _ & _ & _ & _ & _ & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 (Z_to_bv 64 1180260) M3 R4 (Z_to_bv 64 1148296) M4 model3 _ LZ3 STEPS3).
    intros M5 model4 MI4 SBM4 RS4.
    assert (SBM14 : same_but_materialized model model4) by (exact (same_but_materialized_trans model model3 model4 SBM13 SBM4)).
    destruct (lzinv_sbm ASEGS (ahid A model) A model model4 LZ MI4 SBM14) as (_ & _ & _ & _ & HALT4).
    rewrite <- (proj2 (sbm_fds model model4 SBM14)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 1148296) M5 rom model4 ECALLW st fetch_exitA is_ecall_ECALLW HALT4).
    + left. exact T17.
    + exact T10.
    + exact STR.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4SB : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preSB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz PRE MV STR CZ G1 G2 G4 G10 CAN SO SOX FD1.
  destruct PRE as (DI & SLO & SHI & SAL & STKW & IMGC & XSB).
  unfold exitSB in XSB. destruct XSB as (CELLS & TIDC & TIDR & CLR).
  destruct SO as (SO_mode & SO_size & SO_end & SO_wpos & SO_wbase & SO_lk1 & SO_lk2 & SO_fwr & SO_bwr & SO_ln).
  destruct SOX as (SOX_wr & SOX_fd & SOX_buf & SOX_z1 & SOX_z2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model DI) as LZ.
  pose proof (proj1 LZ) as HOFF. pose proof (proj1 (proj2 LZ)) as LCOV.
  pose proof (proj1 (proj2 (proj2 LZ))) as AWF. pose proof (proj1 (proj2 (proj2 (proj2 LZ)))) as MINV.
  pose proof (proj2 (proj2 (proj2 (proj2 LZ)))) as HALT.
  assert (XCV : forall a n v, In (a, n, v) XC_CELLS_SB -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
    by (intros a n v IN; exact (proj1 (Forall_forall _ _) CELLS _ IN)).
  pose proof (ex_cell_vis LB LK cr A M model) as EXV.
  assert (BS5 : rdn ASEGS MV (Z_to_bv 64 6898981) 1%nat = Some (Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898981 (Z_to_bv 8 10) 0%nat [] ltac:(lia) (proj2 (SO_ln 2 ltac:(lia))) (eq_refl : rdn ASEGS MV (Z_to_bv 64 6898982) 0%nat = Some []))).
  assert (BS4 : rdn ASEGS MV (Z_to_bv 64 6898980) 2%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898980 (Z_to_bv 8 48) 1%nat [Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 2 ltac:(lia))) BS5)).
  assert (BS3 : rdn ASEGS MV (Z_to_bv 64 6898979) 3%nat = Some (Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898979 (Z_to_bv 8 10) 2%nat [Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj2 (SO_ln 1 ltac:(lia))) BS4)).
  assert (BS2 : rdn ASEGS MV (Z_to_bv 64 6898978) 4%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898978 (Z_to_bv 8 48) 3%nat [Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 1 ltac:(lia))) BS3)).
  assert (BS1 : rdn ASEGS MV (Z_to_bv 64 6898977) 5%nat = Some (Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898977 (Z_to_bv 8 10) 4%nat [Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj2 (SO_ln 0 ltac:(lia))) BS2)).
  assert (BS : rdn ASEGS MV (Z_to_bv 64 6898976) 6%nat = Some (Z_to_bv 8 48 :: Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: Z_to_bv 8 48 :: Z_to_bv 8 10 :: nil)) by (exact (rdn_cons1 MV 6898976 (Z_to_bv 8 48) 5%nat [Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ltac:(lia) (proj1 (SO_ln 0 ltac:(lia))) BS1)).
  pose proof (AS0DRVP_dpX4SB_pre.dpX4SB_pre_conc fx R MV
     (fun k => match k with 2%nat => S | 40%nat => canz | 44%nat => tid | _ => 0 end)) as RUN.
  cbv beta iota in RUN.
  repeat lazymatch type of RUN with
  | ?P -> _ =>
      let PF := fresh "PF" in
      assert (PF : P);
      [ lazymatch P with
        | _ <= _ < _ => lia
        | _ <= _ <= _ => lia
        | getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | AS0DRVP_dpX4SB_pre.aligned _ _ => exact SAL
        | L5Defs.L5.img_clear _ _ _ => exact IMGC
        | L5Defs.L5.writable _ _ ?a ?n =>
            lazymatch a with
            | context [S] => apply STKW; lia
            | _ => first [ exact (sh_writable LB LK cr A M model a n DI eq_refl)
                         | let k := eval vm_compute in (Z.to_nat n) in
                           exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) ]
            end
        | L5Defs.L5.defined _ ?a ?n =>
            intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
            exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
        | L5Defs.L5.u32_at _ _ 6765656 _ => exact TIDC
        | L5Defs.L5.u32_at _ _ 1293892 _ => exact SO_lk1
        | L5Defs.L5.u32_at _ _ 1293872 _ => exact SOX_fd
        | L5Defs.L5.u64_at _ _ 1293792 _ => exact SO_wpos
        | L5Defs.L5.u64_at _ _ 1293808 _ => exact SO_wbase
        | L5Defs.L5.u64_at _ _ 1293824 _ => exact SOX_wr
        | L5Defs.L5.u64_at _ _ 1293760 _ => exact SOX_z1
        | L5Defs.L5.u64_at _ _ 1293768 _ => exact SOX_z2
        | L5Defs.L5.u64_at _ _ 6896960 _ => exact CAN
        | ?cell =>
            let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
            let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
            let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            first [ solve [ refine (eq_trans (XCV a w v _) _);
                            [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ refine (eq_trans (EXV a w v DI _) _);
                            [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                  | solve [ apply img_cell; [ img_rd | lia | simpl Z.of_nat; lia | intros i RNG; apply CLR; simpl Z.of_nat in RNG; lia ] ] ]
        end
      | specialize (RUN PF); clear PF ]
  end.
  destruct RUN as (
    fx1 & R1 & M1 & GROW1 & FRW1 & FRZ1 & STEPS1 & KEEP1 & _ & Q2 & _ & _ & _ & Q8 & Q9 & Q10 & Q11 & Q12 & _ & _ & _ & _ & Q17 & Q18 & Q19 & Q21 &
    Q22 & _ & C112 & C120 & C128 & C136 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 1180248) M1 model _ LZ STEPS1).
  intros M2 model2 MI2 SBM2 RS2.
  assert (FR1 : forall i : Z, (0 <= i < 1295744 \/ (6896960 <= i /\ i < 6896968) \/ (6898900 <= i /\ i < 6899000)) ->
                 M1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRZ1; lia).
  assert (FR1w : forall x : word, (0 <= bv_unsigned x < 1295744 \/ (6896960 <= bv_unsigned x /\ bv_unsigned x < 6896968) \/ (6898900 <= bv_unsigned x /\ bv_unsigned x < 6899000)) ->
                 M1 x = MV x)
    by (intros x CASE; destruct CASE as [CASE | [CASE | CASE]]; apply FRW1; lia).
  assert (TR1 : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                 rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs).
  { intros a n bs ANN BND RD. apply (rdn_frame_w MV M1 a n bs RD ANN ltac:(destruct BND as [BND|[BND|BND]]; lia)).
    intros x XIN. apply FR1w. destruct BND as [BND | [BND | BND]]; [left | right; left | right; right]; lia. }
  assert (NLQ : forall x : Z, S - 136 <= x < S - 104 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
  { intros x XIN.
    pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 (S - 136)) 32
       (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NL.
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    specialize (NL ltac:(lia) ltac:(intros k KIN; right; left; lia) (x - (S - 136)) ltac:(lia)).
    rewrite Z_to_bv_unsigned, (bv_wrap_small 64 (S - 136)) in NL by (unfold bv_modulus; simpl Z.of_N; lia).
    replace (S - 136 + (x - (S - 136))) with x in NL by lia. exact NL. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A HOFF (m_vm_lazy model) LCOV AWF 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(repeat split; lia) ltac:(split; [lia | split; [left; lia | lia]]) NLQ
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 6%nat) as WV.
  unfold W. apply (WV true R1 M2 model2 (S - 136) 2 6898976 6 0 0 (zero_lines 3) []).
  - reflexivity.
  - apply (sbm_lazy_eq model model2 SBM2).
  - exact MI2.
  - rewrite (sbm_halted_eq model model2 SBM2). exact HALT.
  - rewrite (proj1 (sbm_fds model model2 SBM2)). exact FD1.
  - split; [exact Q17 | split; [exact Q10 | split; [exact Q11 | split; [exact Q12 | split; [exact Q9 | split; [exact Q18 | split; [exact Q22 | exact Q19]]]]]]].
  - rewrite RS2. split; [lia | split; [lia | split; [right; reflexivity | ]]].
    split; [exact C136 | ].
    replace (S - 136 + 8) with (S - 128) by lia. split; [exact C128 | ].
    split.
    { pose proof (L5Defs.L5.writable_grows ASEGS MV M1 (S - 136) 32 GROW1
        (STKW (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(simpl Z.of_nat; lia)) as SW.
      rewrite Z.add_0_r in SW. change (Z.to_nat (16 * 2)) with 32%nat. exact SW. }
    split.
    + split; [lia | split; [lia | split; [lia | split; [right; left; lia | split ]]]].
      * exact (TR1 6898976 6%nat (zero_lines 3) ltac:(lia) ltac:(right; right; split; [lia | simpl Z.of_nat; lia]) BS).
      * intros x XIN.
        pose proof (nolazy_of_inv scfg L ar C IL HI HIok sp0 Hsp DL LB [] LK cr A M model (Z_to_bv 64 6898976) 6
          (di_inv ar HI sp0 M0 LB LK cr A M model DI)) as NLB.
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        specialize (NLB ltac:(lia) ltac:(intros k KIN; left; lia) (x - 6898976) ltac:(lia)).
        rewrite Z_to_bv_unsigned, (bv_wrap_small 64 6898976) in NLB by (unfold bv_modulus; simpl Z.of_N; lia).
        replace (6898976 + (x - 6898976)) with x in NLB by lia. exact NLB.
    + split; [intros CC; discriminate CC | intros _ ].
      replace (S - 136 + 16) with (S - 120) by lia. split; [exact C120 | ].
      replace (S - 136 + 24) with (S - 112) by lia. split; [exact C112 | ].
      split; [ split; [lia | split; [lia | split; [lia | split; [left; reflexivity | split; [reflexivity | intros x XIN; exfalso; lia]]]]] | lia ].
  - lia.
  - rewrite RS2. exact (TR1 1293872 4%nat _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia) SOX_fd).
  - intros R3 M3 model3 MI3 SBM3 KEEP3 FRM3 FRV3 GR3 GRV3.
    assert (SBM13 : same_but_materialized model model3) by (exact (same_but_materialized_trans model model2 model3 SBM2 SBM3)).
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3) by (exact (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3 SBM13)).
    assert (GRW : mem_grows MV (mrestrict (ahid A model) M3)) by (intros x XIN; apply GRV3; rewrite RS2; exact (GROW1 x XIN)).
    assert (FR3w : forall x : word, (bv_unsigned x < S - 136 \/ S - 104 <= bv_unsigned x) -> mrestrict (ahid A model) M3 x = M1 x).
    { intros x CASE. pose proof (u64_range x) as XR. rewrite <- RS2. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      destruct CASE as [CASE|CASE]; apply FRV3; lia. }
    assert (TR3 : forall a (n : nat) bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= S - 136 \/ S - 104 <= a) ->
                    rdn ASEGS M1 (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND SIDE RD. apply (rdn_frame_w M1 _ a n bs RD ANN BND).
      intros x XIN. apply FR3w. destruct SIDE as [SIDE|SIDE]; [left | right]; lia. }
    assert (TRV : forall a (n : nat) bs, 0 <= a -> (a + Z.of_nat n <= 1295744 \/ (6896960 <= a /\ a + Z.of_nat n <= 6896968) \/ (6898900 <= a /\ a + Z.of_nat n <= 6899000)) ->
                    rdn ASEGS MV (Z_to_bv 64 a) n = Some bs -> rdn ASEGS (mrestrict (ahid A model) M3) (Z_to_bv 64 a) n = Some bs).
    { intros a n bs ANN BND RD.
      apply (TR3 a n bs ANN ltac:(destruct BND as [BND|[BND|BND]]; lia) ltac:(left; destruct BND as [BND|[BND|BND]]; lia) (TR1 a n bs ANN BND RD)). }
    change (getr R (Z_to_bv 5 (Z.of_nat 10))) with (getr R 10%bv) in C32. rewrite G10, Z_to_bv_unsigned in C32.
    rewrite (bv_wrap_small 64 st) in C32 by (unfold bv_modulus; simpl Z.of_N; lia).
    pose proof (u64_range (getr R 9%bv)). pose proof (u64_range (getr R 18%bv)). pose proof (u64_range (getr R 19%bv)).
    pose proof (u64_range (getr R 20%bv)). pose proof (u64_range (getr R 21%bv)). pose proof (u64_range (getr R 22%bv)).
    pose proof (u64_range (getr R3 10%bv)). pose proof (u64_range (getr R3 18%bv)). pose proof (u64_range (getr R3 19%bv)).
    pose proof (u64_range (getr R3 20%bv)). pose proof (u64_range (getr R3 22%bv)).
    pose proof (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 (mrestrict (ahid A model) M3)
      (fun k => match k with
                | 2%nat => S - 144 | 9%nat => bv_unsigned (getr R 9%bv) | 10%nat => st
                | 18%nat => bv_unsigned (getr R 18%bv) | 19%nat => bv_unsigned (getr R 19%bv)
                | 20%nat => bv_unsigned (getr R 20%bv) | 21%nat => bv_unsigned (getr R 21%bv)
                | 22%nat => bv_unsigned (getr R 22%bv) | 40%nat => canz
                | 110%nat => bv_unsigned (getr R3 10%bv) | 118%nat => bv_unsigned (getr R3 18%bv)
                | 119%nat => bv_unsigned (getr R3 19%bv) | 120%nat => bv_unsigned (getr R3 20%bv)
                | 122%nat => bv_unsigned (getr R3 22%bv) | _ => 0 end)) as RUN3.
    cbv beta iota in RUN3.
    replace (S - 144 + 40) with (S - 104) in RUN3 by lia.
    replace (S - 144 + 48) with (S - 96) in RUN3 by lia.
    replace (S - 144 + 56) with (S - 88) in RUN3 by lia.
    replace (S - 144 + 64) with (S - 80) in RUN3 by lia.
    replace (S - 144 + 72) with (S - 72) in RUN3 by lia.
    replace (S - 144 + 80) with (S - 64) in RUN3 by lia.
    replace (S - 144 + 88) with (S - 56) in RUN3 by lia.
    replace (S - 144 + 96) with (S - 48) in RUN3 by lia.
    replace (S - 144 + 104) with (S - 40) in RUN3 by lia.
    replace (S - 144 + 112) with (S - 32) in RUN3 by lia.
    replace (S - 144 + 120) with (S - 24) in RUN3 by lia.
    replace (S - 144 - 16) with (S - 160) in RUN3 by lia.
    repeat lazymatch type of RUN3 with
    | ?P -> _ =>
        let PF := fresh "PF" in
        assert (PF : P);
        [ lazymatch P with
          | _ <= _ < _ => lia
          | _ <= _ <= _ => lia
          | getr _ _ = _ =>
              first [ exact (eq_trans (KEEP3 2%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q2)
                    | exact (eq_trans (KEEP3 8%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q8)
                    | exact (eq_trans (KEEP3 9%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q9)
                    | exact (eq_trans (KEEP3 21%bv ltac:(unfold WV_KEEP; repeat first [apply in_eq | apply in_cons])) Q21)
                    | symmetry; apply Z_to_bv_bv_unsigned ]
          | AS0DRVP_dpXd_4.aligned _ _ => unfold AS0DRVP_dpXd_4.aligned; rewrite Zminus_mod, SAL; reflexivity
          | L5Defs.L5.img_clear _ _ _ =>
              intros i RNG;
              rewrite (FR3w (Z_to_bv 64 i) ltac:(left; rewrite Z_to_bv_unsigned, (bv_wrap_small 64 i) by (unfold bv_modulus; simpl Z.of_N; lia); lia));
              rewrite (FR1 i ltac:(left; lia)); apply IMGC; lia
          | L5Defs.L5.writable _ _ ?a ?n =>
              lazymatch a with
              | context [S] => apply (L5Defs.L5.writable_grows ASEGS MV _ a n GRW); apply STKW; lia
              | _ => let k := eval vm_compute in (Z.to_nat n) in
                     exact (wsg_writable (mrestrict (ahid A model) M3) a k ltac:(vm_compute; reflexivity) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity))
              end
          | L5Defs.L5.defined _ ?a ?n =>
              apply (L5Defs.L5.defined_grows MV _ a n GRW);
              intros i RNG; apply (store_ok_defined sp0 MV); [lia|];
              exact (STKW a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(simpl Z.of_nat; lia))
          | ?cell =>
              let a := lazymatch cell with L5Defs.L5.u64_at _ _ ?a _ => a | L5Defs.L5.u32_at _ _ ?a _ => a | L5Defs.L5.u8_at _ _ ?a _ => a end in
              let v := lazymatch cell with L5Defs.L5.u64_at _ _ _ ?v => v | L5Defs.L5.u32_at _ _ _ ?v => v | L5Defs.L5.u8_at _ _ _ ?v => v end in
              let w := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8) | L5Defs.L5.u32_at _ _ _ _ => constr:(4) | L5Defs.L5.u8_at _ _ _ _ => constr:(1) end in
              let wn := lazymatch cell with L5Defs.L5.u64_at _ _ _ _ => constr:(8%nat) | L5Defs.L5.u32_at _ _ _ _ => constr:(4%nat) | L5Defs.L5.u8_at _ _ _ _ => constr:(1%nat) end in
              unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
              lazymatch a with
              | context [S] =>
                  apply (TR3 a wn _ ltac:(lia) ltac:(simpl Z.of_nat; lia) ltac:(right; lia));
                  lazymatch a with
                  | S - 24 => exact C24 | S - 32 => exact C32 | S - 40 => exact C40 | S - 48 => exact C48
                  | S - 56 => exact C56 | S - 64 => exact C64 | S - 72 => exact C72 | S - 80 => exact C80
                  | S - 88 => exact C88 | S - 96 => exact C96 | S - 104 => exact C104
                  end
              | 6896960 =>
                  apply (TRV a wn _ ltac:(lia) ltac:(right; left; split; [lia | simpl Z.of_nat; lia])); exact CAN
              | _ =>
                  apply (TRV a wn _ ltac:(lia) ltac:(left; simpl Z.of_nat; lia));
                  lazymatch a with
                  | 1293752 => exact SO_mode | 1293848 => exact SO_size | 1293784 => exact SO_end
                  | 1293792 => exact SO_wpos | 1293808 => exact SO_wbase | 1293892 => exact SO_lk1 | 1293896 => exact SO_lk2
                  | 1293824 => exact SOX_wr | 1293872 => exact SOX_fd | 1293840 => exact SOX_buf
                  | 1293760 => exact SOX_z1 | 1293768 => exact SOX_z2
                  | _ => first [ solve [ refine (eq_trans (XCV a w v _) _);
                                         [ unfold XC_CELLS_SB; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ]
                               | solve [ refine (eq_trans (EXV a w v DI _) _);
                                         [ unfold EX_CELLS; repeat first [apply in_eq | apply in_cons] | first [reflexivity | img_rd] ] ] ]
                  end
              end
          end
        | specialize (RUN3 PF); clear PF ]
    end.
    destruct RUN3 as (fx4 & R4 & M4 & GROW3 & FRW3 & FRZ3 & STEPS3 & _ & _ & _ & _ & _ & T10 & _ & _ & T17 & _ & _ & _ & _ & _ & _ & _ & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 (Z_to_bv 64 1180260) M3 R4 (Z_to_bv 64 1148296) M4 model3 _ LZ3 STEPS3).
    intros M5 model4 MI4 SBM4 RS4.
    assert (SBM14 : same_but_materialized model model4) by (exact (same_but_materialized_trans model model3 model4 SBM13 SBM4)).
    destruct (lzinv_sbm ASEGS (ahid A model) A model model4 LZ MI4 SBM14) as (_ & _ & _ & _ & HALT4).
    rewrite <- (proj2 (sbm_fds model model4 SBM14)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 1148296) M5 rom model4 ECALLW st fetch_exitA is_ecall_ECALLW HALT4).
    + left. exact T17.
    + exact T10.
    + exact STR.
Qed.
End Exit.
End FPX_1.
