(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA HeapIfaceABx. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import DrvKitA DrvNodesLazyK As0DrvKitA. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b Ba0Drv_defs_b Ba0DrvLib_b Ba0DrvRead_b Ba0DrvPiece_b Ba0DiagLoopK_b Ba0DrvStdio_b Ba0DrvPrintfK_b Ba0DrvPrintf1_b.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require L5Defs L5KnA L5Core ArtMem. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatFsInv_b.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvExit_b Ba0ExitCells_b.
  From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpXB_b Ba0DrvP_dpX2B_pre_b Ba0DrvP_dpX3B_pre_b Ba0DrvP_dpX4B_pre_b Ba0DrvP_dpXd_2_b Ba0DrvP_dpXd_3_b Ba0DrvP_dpXd_4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
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
Definition XC_CELLS_B : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 4); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0); (6897016, 8, 1148964); (6897272, 8, 687916); (6759060, 1, 0); (6897024, 8, 872740); (6897032, 8, 449180); (6897280, 8, 1293304); (6897288, 8, 0)].
Definition exitB (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_B
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

Definition exit_preB (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z))
    (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
  dinvA LB LK cr A M model
  /\ usp - 0x1000 <= S /\ S <= usp /\ S mod 16 = 0
  /\ (forall a n, usp - 0x800000 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n)
  /\ L5Defs.L5.img_clear (mrestrict (ahid A model) M) 0x10000 0x139000
  /\ exitB tid (mrestrict (ahid A model) M).

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0B : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
  intros LB LK cr A M model R S st tid pre MV st_rng ra_r1 sp_r2 tp_r4 a0_r10 outA outX.
  destruct pre as (inv & S_lo & S_hi & S_al & stk & clr & cellsB & tid_rd & tid_rng & gap).
  destruct outA as (o_flags & o_size & o_end & o_wpos & o_wbase & o_lk1 & o_lk2 & _).
  destruct outX as (o_wrfn & o_fd & o_buf & o_rd1 & o_rd2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model inv) as lz.
  pose proof (AS0DRVP_dpXB.dpXB_conc fx R MV (fun k => match k with 2%nat => S | _ => tid end)) as xrun.
  cbv beta iota in xrun.
  repeat lazymatch type of xrun with
  | ?need -> _ =>
      let got := fresh "got" in
      assert (got : need) by (
        lazymatch goal with
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            first [ exact (sh_writable LB LK cr A M model a n inv eq_refl)
                  | (apply stk; lia)
                  | exact (wsg_writable MV a (Z.to_nat n) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
        | |- L5Defs.L5.defined _ ?a ?n =>
            intros i i_rng; apply (store_ok_defined sp0 MV (a + i)); [lia|];
            exact (stk a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(lia))
        | |- L5Defs.L5.img_clear _ _ _ => exact clr
        | |- AS0DRVP_dpXB.aligned _ _ => exact S_al
        | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact ra_r1
        | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact sp_r2
        | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact tp_r4
        | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact tid_rd
        | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact o_lk1
        | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact o_wpos
        | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact o_wbase
        | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact o_rd1
        | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact o_rd2
        | |- ?cell _ _ ?a ?v =>
            let w := lazymatch cell with
                     | L5Defs.L5.u64_at => constr:(8) | L5Defs.L5.u32_at => constr:(4) | L5Defs.L5.u8_at => constr:(1) end in
            lazymatch cell with
            | L5Defs.L5.u64_at => unfold L5Defs.L5.u64_at
            | L5Defs.L5.u32_at => unfold L5Defs.L5.u32_at
            | L5Defs.L5.u8_at =>
                unfold L5Defs.L5.u8_at;
                replace [Z_to_bv 8 v] with (word_to_le_bytes 1 (Z_to_bv 64 v))
                  by (rewrite N_to_le_bytes_1_small; f_equal; apply bv_eq; vm_compute; reflexivity)
            end;
            first [ exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, w, v)
                             ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
                  | exact (ex_cell_vis LB LK cr A M model a w v inv
                             ltac:(unfold EX_CELLS; repeat first [apply in_eq | apply in_cons]))
                  | (apply img_cell; [img_rd | lia | lia | intros i i_rng; apply gap; lia]) ]
        | |- _ => lia
        end);
      specialize (xrun got); clear got
  end.
  destruct xrun as (fx1 & R1 & MV1 & _ & _ & _ & run & kept & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & a7_r17 & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ MV1 model _ lz run).
  intros M2 model2 _ same2 _.
  destruct (sbm_fds _ _ same2) as (_ & fs_same). rewrite <- fs_same.
  apply (rz_exit_at_lit_lz ASEGS scfg R1 _ M2 _ model2 ECALLW st fetch_exitA is_ecall_ECALLW).
  - rewrite (sbm_halted_eq _ _ same2). exact (di_halt _ _ _ _ _ _ _ _ _ _ inv).
  - left. exact a7_r17.
  - etransitivity; [exact (kept 10%nat ltac:(unfold AS0DRVP_dpXB.KS_dpXB; repeat first [apply in_eq | apply in_cons])) | exact a0_r10].
  - exact st_rng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz pre MV st_rng can_rng ra_r1 sp_r2 tp_r4 a0_r10 can_rd outA outX fd1.
  destruct pre as (inv & S_lo & S_hi & S_al & stk & clr & cellsB & tid_rd & tid_rng & gap).
  destruct outA as (o_flags & o_size & o_end & o_wpos & o_wbase & o_lk1 & o_lk2 & o_wfile & o_wbuf & o_lines).
  destruct outX as (o_wrfn & o_fd & o_buf & o_rd1 & o_rd2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model inv) as lz.
  pose proof (AS0DRVP_dpX2B_pre.dpX2B_pre_conc fx R MV
                (fun k => match k with 2%nat => S | 40%nat => canz | _ => tid end)) as xrun.
  cbv beta iota in xrun.
  repeat lazymatch type of xrun with
  | ?need -> _ =>
      let got := fresh "got" in
      assert (got : need) by (
        lazymatch goal with
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            first [ exact (sh_writable LB LK cr A M model a n inv eq_refl)
                  | (apply stk; lia)
                  | exact (wsg_writable MV a (Z.to_nat n) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
        | |- L5Defs.L5.defined _ ?a ?n =>
            intros i i_rng; apply (store_ok_defined sp0 MV (a + i)); [lia|];
            exact (stk a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(lia))
        | |- L5Defs.L5.img_clear _ _ _ => exact clr
        | |- AS0DRVP_dpX2B_pre.aligned _ _ => exact S_al
        | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact ra_r1
        | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact sp_r2
        | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact tp_r4
        | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact tid_rd
        | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact can_rd
        | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact o_lk1
        | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact o_wpos
        | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact o_wbase
        | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact o_wrfn
        | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact o_fd
        | |- ?cell _ _ ?a ?v =>
            let w := lazymatch cell with
                     | L5Defs.L5.u64_at => constr:(8) | L5Defs.L5.u32_at => constr:(4) | L5Defs.L5.u8_at => constr:(1) end in
            lazymatch cell with
            | L5Defs.L5.u64_at => unfold L5Defs.L5.u64_at
            | L5Defs.L5.u32_at => unfold L5Defs.L5.u32_at
            | L5Defs.L5.u8_at =>
                unfold L5Defs.L5.u8_at;
                replace [Z_to_bv 8 v] with (word_to_le_bytes 1 (Z_to_bv 64 v))
                  by (rewrite N_to_le_bytes_1_small; f_equal; apply bv_eq; vm_compute; reflexivity)
            end;
            first [ exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, w, v)
                             ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
                  | exact (ex_cell_vis LB LK cr A M model a w v inv
                             ltac:(unfold EX_CELLS; repeat first [apply in_eq | apply in_cons]))
                  | (apply img_cell; [img_rd | lia | lia | intros i i_rng; apply gap; lia]) ]
        | |- _ => lia
        end);
      specialize (xrun got); clear got
  end.
  destruct xrun as (fx1 & R1 & MV1 & grow1 & _ & keep1 & run1 & kept1 & _ & r2_1 & _ & _ & _ & r8_1 & r9_1
                    & r10_1 & r11_1 & r12_1 & _ & _ & _ & _ & r17_1 & r18_1 & r19_1 & r21_1 & r22_1 & _
                    & m112 & m120 & m128 & m136 & m104 & m96 & m88 & m80 & m72 & m64 & m56 & m48 & m40 & m32 & m24 & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ MV1 model _ lz run1).
  intros M2 model2 minv2 same2 vis2.
  pose proof lz as (h_off & lz_cov & A_good & _ & halt0).
  destruct (same_but_materialized_frame _ _ same2) as (_ & _ & lazy2 & _ & _ & _ & _ & _ & fds2 & _ & _ & fs2 & halt2 & _).
  pose proof (lzinv_sbm _ _ _ _ _ lz minv2 same2) as lz2.
  assert (nolz : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x ->
                 page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x x_rng x_at; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x inv x_rng x_at)).
  assert (old1 : forall i, 0 <= i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897524 <= i < 2147468856 ->
                 MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i i_rng; apply keep1; lia).
  assert (buf0 : rdn ASEGS MV (Z_to_bv 64 6898976) 2 = Some (zero_lines 1)).
  { apply rdn_cons1; [lia | exact (proj1 (o_lines 0 ltac:(lia))) | exact (proj2 (o_lines 0 ltac:(lia)))]. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A h_off (m_vm_lazy model) lz_cov A_good 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(lia) ltac:(lia) ltac:(intros x x_rng; apply nolz; lia)
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 2%nat) as loop.
  apply (loop true R1 M2 model2 (S - 136) 2 6898976 2 0 0 (zero_lines 1) []).
  - cbn. lia.
  - exact lazy2.
  - exact minv2.
  - rewrite halt2. exact halt0.
  - rewrite fds2. exact fd1.
  - exact (conj r17_1 (conj r10_1 (conj r11_1 (conj r12_1 (conj r9_1 (conj r18_1 (conj r22_1 r19_1))))))).
  - rewrite vis2. unfold wv_iov.
    split; [lia|]. split; [lia|]. split; [right; reflexivity|]. split; [exact m136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact m128|].
    split.
    { assert (sk := stk (S - 136) 32 ltac:(lia) ltac:(lia) 0 32%nat ltac:(lia) ltac:(lia)).
      rewrite Z.add_0_r in sk. exact (store_ok_mono _ _ _ _ _ grow1 sk). }
    split.
    { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
      - apply (rdn_tr MV MV1 6898976 2 _ buf0); [lia | lia |]. intros i i_rng. apply old1. lia.
      - intros x x_rng. apply nolz; lia. }
    split; [intros c_one; lia|].
    intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact m120|].
    split; [replace (S - 136 + 24) with (S - 112) by lia; exact m112|].
    split; [|lia].
    unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
    intros x x_rng. lia.
  - lia.
  - rewrite vis2. apply (rdn_tr MV MV1 1293872 4 _ o_fd); [lia | lia |]. intros i i_rng. apply old1. lia.
  - intros R3 M3 model3 minv3 same3 regs3 _ fr3 _ grow3.
    set (MV3 := mrestrict (ahid A model) M3).
    pose proof (lzinv_sbm _ _ _ _ _ lz2 minv3 same3) as lz3.
    assert (wr3 : forall a n, L5Defs.L5.writable ASEGS MV a n -> L5Defs.L5.writable ASEGS MV3 a n).
    { intros a n wr d k d_lo d_hi. apply (store_ok_mono _ _ (mrestrict (ahid A model) M2)); [exact grow3|].
      rewrite vis2. exact (store_ok_mono _ _ _ _ _ grow1 (wr d k d_lo d_hi)). }
    assert (lowc : forall a n bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
                   0 <= a /\ a + Z.of_nat n <= 1295744 \/ 1299704 <= a /\ a + Z.of_nat n <= 6896976 \/
                   6897524 <= a /\ a + Z.of_nat n <= 2147468856 ->
                   rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_rng. apply (rdn_tr MV MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. apply old1. lia. }
    assert (hic : forall a n bs, rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs ->
                  S - 320 <= a -> a + Z.of_nat n <= S -> a + Z.of_nat n <= S - 136 \/ S - 104 <= a ->
                  rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_lo a_hi a_out. apply (rdn_tr MV1 MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. reflexivity. }
    pose proof (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3
                  (fun k => match k with
                            | 2%nat => S - 144 | 40%nat => canz
                            | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                            | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                            | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                            | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                            | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                            | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                            | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                            | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10)))
                            | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
                            | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                            | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
                            | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                            | _ => 0 end)) as drun.
    cbv beta iota in drun.
    repeat lazymatch type of drun with
    | ?need -> _ =>
        let got := fresh "got" in
        assert (got : need) by (
          lazymatch goal with
          | |- 0 <= bv_unsigned _ < 2 ^ 64 => apply u64_range
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = Z_to_bv 64 (bv_unsigned (getr R3 _)) =>
              symmetry; apply Z_to_bv_bv_unsigned
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
              etransitivity;
              [ exact (regs3 (Z_to_bv 5 (Z.of_nat r)) ltac:(unfold WV_KEEP; repeat first [left; apply bv_eq; reflexivity | right]))
              | first [exact r2_1 | exact r8_1 | exact r9_1 | exact r21_1] ]
          | |- AS0DRVP_dpXd_2.aligned _ _ =>
              unfold AS0DRVP_dpXd_2.aligned; rewrite Zminus_mod, S_al; reflexivity
          | |- L5Defs.L5.writable _ _ ?a ?n =>
              apply wr3; first [ (apply stk; lia) | exact (o_wfile a n ltac:(lia) ltac:(lia)) ]
          | |- L5Defs.L5.defined _ ?a ?n =>
              intros i i_rng; apply (store_ok_defined sp0 MV3 (a + i)); [lia|];
              exact (wr3 a n (stk a n ltac:(lia) ltac:(lia)) i 1%nat ltac:(lia) ltac:(lia))
          | |- L5Defs.L5.img_clear _ _ _ =>
              intros i i_rng; unfold MV3; rewrite fr3 by lia; rewrite vis2, old1 by lia; exact (clr i i_rng)
          | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
              let saved := lazymatch k with
                           | 40 => m104 | 48 => m96 | 56 => m88 | 64 => m80 | 72 => m72 | 80 => m64
                           | 88 => m56 | 96 => m48 | 104 => m40 | 112 => m32 | 120 => m24 end in
              let back := eval vm_compute in (144 - k) in
              unfold L5Defs.L5.u64_at; replace (S - 144 + k) with (S - back) by lia;
              apply hic; [exact saved | lia | lia | lia]
          | |- L5Defs.L5.u64_at _ _ ?a ?v =>
              unfold L5Defs.L5.u64_at; apply lowc; [|lia];
              lazymatch a with
              | 1293840 => exact o_buf | 1293848 => exact o_size | 6896960 => exact can_rd
              | 1293760 => exact o_rd1 | 1293768 => exact o_rd2
              | _ => exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 8, v)
                              ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
              end
          | |- L5Defs.L5.u32_at _ _ ?a ?v =>
              unfold L5Defs.L5.u32_at; apply lowc; [|lia];
              exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 4, v)
                       ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
          | |- _ => lia
          end);
        specialize (drun got); clear got
    end.
    destruct drun as (fx4 & R4 & MV4 & _ & _ & _ & run4 & _ & _ & _ & _ & _ & r10_4 & _ & _ & r17_4 & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 _ M3 R4 _ MV4 model3 _ lz3 run4).
    intros M5 model5 _ same5 _.
    destruct (sbm_fds _ _ same5) as (_ & fs5). destruct (sbm_fds _ _ same3) as (_ & fs3).
    rewrite <- fs2, <- fs3, <- fs5.
    apply (rz_exit_at_lit_lz ASEGS scfg R4 _ M5 _ model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    + rewrite (sbm_halted_eq _ _ same5). exact (proj2 (proj2 (proj2 (proj2 lz3)))).
    + left. exact r17_4.
    + etransitivity; [exact r10_4|]. rewrite Z_to_bv_bv_unsigned. exact a0_r10.
    + exact st_rng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz pre MV st_rng can_rng ra_r1 sp_r2 tp_r4 a0_r10 can_rd outA outX fd1.
  destruct pre as (inv & S_lo & S_hi & S_al & stk & clr & cellsB & tid_rd & tid_rng & gap).
  destruct outA as (o_flags & o_size & o_end & o_wpos & o_wbase & o_lk1 & o_lk2 & o_wfile & o_wbuf & o_lines).
  destruct outX as (o_wrfn & o_fd & o_buf & o_rd1 & o_rd2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model inv) as lz.
  pose proof (AS0DRVP_dpX3B_pre.dpX3B_pre_conc fx R MV
                (fun k => match k with 2%nat => S | 40%nat => canz | _ => tid end)) as xrun.
  cbv beta iota in xrun.
  repeat lazymatch type of xrun with
  | ?need -> _ =>
      let got := fresh "got" in
      assert (got : need) by (
        lazymatch goal with
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            first [ exact (sh_writable LB LK cr A M model a n inv eq_refl)
                  | (apply stk; lia)
                  | exact (wsg_writable MV a (Z.to_nat n) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
        | |- L5Defs.L5.defined _ ?a ?n =>
            intros i i_rng; apply (store_ok_defined sp0 MV (a + i)); [lia|];
            exact (stk a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(lia))
        | |- L5Defs.L5.img_clear _ _ _ => exact clr
        | |- AS0DRVP_dpX3B_pre.aligned _ _ => exact S_al
        | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact ra_r1
        | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact sp_r2
        | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact tp_r4
        | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact tid_rd
        | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact can_rd
        | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact o_lk1
        | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact o_wpos
        | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact o_wbase
        | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact o_wrfn
        | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact o_fd
        | |- ?cell _ _ ?a ?v =>
            let w := lazymatch cell with
                     | L5Defs.L5.u64_at => constr:(8) | L5Defs.L5.u32_at => constr:(4) | L5Defs.L5.u8_at => constr:(1) end in
            lazymatch cell with
            | L5Defs.L5.u64_at => unfold L5Defs.L5.u64_at
            | L5Defs.L5.u32_at => unfold L5Defs.L5.u32_at
            | L5Defs.L5.u8_at =>
                unfold L5Defs.L5.u8_at;
                replace [Z_to_bv 8 v] with (word_to_le_bytes 1 (Z_to_bv 64 v))
                  by (rewrite N_to_le_bytes_1_small; f_equal; apply bv_eq; vm_compute; reflexivity)
            end;
            first [ exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, w, v)
                             ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
                  | exact (ex_cell_vis LB LK cr A M model a w v inv
                             ltac:(unfold EX_CELLS; repeat first [apply in_eq | apply in_cons]))
                  | (apply img_cell; [img_rd | lia | lia | intros i i_rng; apply gap; lia]) ]
        | |- _ => lia
        end);
      specialize (xrun got); clear got
  end.
  destruct xrun as (fx1 & R1 & MV1 & grow1 & _ & keep1 & run1 & kept1 & _ & r2_1 & _ & _ & _ & r8_1 & r9_1
                    & r10_1 & r11_1 & r12_1 & _ & _ & _ & _ & r17_1 & r18_1 & r19_1 & r21_1 & r22_1 & _
                    & m112 & m120 & m128 & m136 & m104 & m96 & m88 & m80 & m72 & m64 & m56 & m48 & m40 & m32 & m24 & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ MV1 model _ lz run1).
  intros M2 model2 minv2 same2 vis2.
  pose proof lz as (h_off & lz_cov & A_good & _ & halt0).
  destruct (same_but_materialized_frame _ _ same2) as (_ & _ & lazy2 & _ & _ & _ & _ & _ & fds2 & _ & _ & fs2 & halt2 & _).
  pose proof (lzinv_sbm _ _ _ _ _ lz minv2 same2) as lz2.
  assert (nolz : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x ->
                 page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x x_rng x_at; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x inv x_rng x_at)).
  assert (old1 : forall i, 0 <= i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897524 <= i < 2147468856 ->
                 MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i i_rng; apply keep1; lia).
  assert (buf0 : rdn ASEGS MV (Z_to_bv 64 6898976) 4 = Some (zero_lines 2)).
  { apply rdn_cons1; [lia | exact (proj1 (o_lines 0 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj2 (o_lines 0 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj1 (o_lines 1 ltac:(lia))) | exact (proj2 (o_lines 1 ltac:(lia)))]. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A h_off (m_vm_lazy model) lz_cov A_good 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(lia) ltac:(lia) ltac:(intros x x_rng; apply nolz; lia)
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 4%nat) as loop.
  apply (loop true R1 M2 model2 (S - 136) 2 6898976 4 0 0 (zero_lines 2) []).
  - cbn. lia.
  - exact lazy2.
  - exact minv2.
  - rewrite halt2. exact halt0.
  - rewrite fds2. exact fd1.
  - exact (conj r17_1 (conj r10_1 (conj r11_1 (conj r12_1 (conj r9_1 (conj r18_1 (conj r22_1 r19_1))))))).
  - rewrite vis2. unfold wv_iov.
    split; [lia|]. split; [lia|]. split; [right; reflexivity|]. split; [exact m136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact m128|].
    split.
    { assert (sk := stk (S - 136) 32 ltac:(lia) ltac:(lia) 0 32%nat ltac:(lia) ltac:(lia)).
      rewrite Z.add_0_r in sk. exact (store_ok_mono _ _ _ _ _ grow1 sk). }
    split.
    { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
      - apply (rdn_tr MV MV1 6898976 4 _ buf0); [lia | lia |]. intros i i_rng. apply old1. lia.
      - intros x x_rng. apply nolz; lia. }
    split; [intros c_one; lia|].
    intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact m120|].
    split; [replace (S - 136 + 24) with (S - 112) by lia; exact m112|].
    split; [|lia].
    unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
    intros x x_rng. lia.
  - lia.
  - rewrite vis2. apply (rdn_tr MV MV1 1293872 4 _ o_fd); [lia | lia |]. intros i i_rng. apply old1. lia.
  - intros R3 M3 model3 minv3 same3 regs3 _ fr3 _ grow3.
    set (MV3 := mrestrict (ahid A model) M3).
    pose proof (lzinv_sbm _ _ _ _ _ lz2 minv3 same3) as lz3.
    assert (wr3 : forall a n, L5Defs.L5.writable ASEGS MV a n -> L5Defs.L5.writable ASEGS MV3 a n).
    { intros a n wr d k d_lo d_hi. apply (store_ok_mono _ _ (mrestrict (ahid A model) M2)); [exact grow3|].
      rewrite vis2. exact (store_ok_mono _ _ _ _ _ grow1 (wr d k d_lo d_hi)). }
    assert (lowc : forall a n bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
                   0 <= a /\ a + Z.of_nat n <= 1295744 \/ 1299704 <= a /\ a + Z.of_nat n <= 6896976 \/
                   6897524 <= a /\ a + Z.of_nat n <= 2147468856 ->
                   rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_rng. apply (rdn_tr MV MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. apply old1. lia. }
    assert (hic : forall a n bs, rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs ->
                  S - 320 <= a -> a + Z.of_nat n <= S -> a + Z.of_nat n <= S - 136 \/ S - 104 <= a ->
                  rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_lo a_hi a_out. apply (rdn_tr MV1 MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. reflexivity. }
    pose proof (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3
                  (fun k => match k with
                            | 2%nat => S - 144 | 40%nat => canz
                            | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                            | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                            | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                            | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                            | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                            | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                            | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                            | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10)))
                            | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
                            | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                            | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
                            | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                            | _ => 0 end)) as drun.
    cbv beta iota in drun.
    repeat lazymatch type of drun with
    | ?need -> _ =>
        let got := fresh "got" in
        assert (got : need) by (
          lazymatch goal with
          | |- 0 <= bv_unsigned _ < 2 ^ 64 => apply u64_range
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = Z_to_bv 64 (bv_unsigned (getr R3 _)) =>
              symmetry; apply Z_to_bv_bv_unsigned
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
              etransitivity;
              [ exact (regs3 (Z_to_bv 5 (Z.of_nat r)) ltac:(unfold WV_KEEP; repeat first [left; apply bv_eq; reflexivity | right]))
              | first [exact r2_1 | exact r8_1 | exact r9_1 | exact r21_1] ]
          | |- AS0DRVP_dpXd_3.aligned _ _ =>
              unfold AS0DRVP_dpXd_3.aligned; rewrite Zminus_mod, S_al; reflexivity
          | |- L5Defs.L5.writable _ _ ?a ?n =>
              apply wr3; first [ (apply stk; lia) | exact (o_wfile a n ltac:(lia) ltac:(lia)) ]
          | |- L5Defs.L5.defined _ ?a ?n =>
              intros i i_rng; apply (store_ok_defined sp0 MV3 (a + i)); [lia|];
              exact (wr3 a n (stk a n ltac:(lia) ltac:(lia)) i 1%nat ltac:(lia) ltac:(lia))
          | |- L5Defs.L5.img_clear _ _ _ =>
              intros i i_rng; unfold MV3; rewrite fr3 by lia; rewrite vis2, old1 by lia; exact (clr i i_rng)
          | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
              let saved := lazymatch k with
                           | 40 => m104 | 48 => m96 | 56 => m88 | 64 => m80 | 72 => m72 | 80 => m64
                           | 88 => m56 | 96 => m48 | 104 => m40 | 112 => m32 | 120 => m24 end in
              let back := eval vm_compute in (144 - k) in
              unfold L5Defs.L5.u64_at; replace (S - 144 + k) with (S - back) by lia;
              apply hic; [exact saved | lia | lia | lia]
          | |- L5Defs.L5.u64_at _ _ ?a ?v =>
              unfold L5Defs.L5.u64_at; apply lowc; [|lia];
              lazymatch a with
              | 1293840 => exact o_buf | 1293848 => exact o_size | 6896960 => exact can_rd
              | 1293760 => exact o_rd1 | 1293768 => exact o_rd2
              | _ => exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 8, v)
                              ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
              end
          | |- L5Defs.L5.u32_at _ _ ?a ?v =>
              unfold L5Defs.L5.u32_at; apply lowc; [|lia];
              exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 4, v)
                       ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
          | |- _ => lia
          end);
        specialize (drun got); clear got
    end.
    destruct drun as (fx4 & R4 & MV4 & _ & _ & _ & run4 & _ & _ & _ & _ & _ & r10_4 & _ & _ & r17_4 & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 _ M3 R4 _ MV4 model3 _ lz3 run4).
    intros M5 model5 _ same5 _.
    destruct (sbm_fds _ _ same5) as (_ & fs5). destruct (sbm_fds _ _ same3) as (_ & fs3).
    rewrite <- fs2, <- fs3, <- fs5.
    apply (rz_exit_at_lit_lz ASEGS scfg R4 _ M5 _ model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    + rewrite (sbm_halted_eq _ _ same5). exact (proj2 (proj2 (proj2 (proj2 lz3)))).
    + left. exact r17_4.
    + etransitivity; [exact r10_4|]. rewrite Z_to_bv_bv_unsigned. exact a0_r10.
    + exact st_rng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4B : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preB LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz pre MV st_rng can_rng ra_r1 sp_r2 tp_r4 a0_r10 can_rd outA outX fd1.
  destruct pre as (inv & S_lo & S_hi & S_al & stk & clr & cellsB & tid_rd & tid_rng & gap).
  destruct outA as (o_flags & o_size & o_end & o_wpos & o_wbase & o_lk1 & o_lk2 & o_wfile & o_wbuf & o_lines).
  destruct outX as (o_wrfn & o_fd & o_buf & o_rd1 & o_rd2).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model inv) as lz.
  pose proof (AS0DRVP_dpX4B_pre.dpX4B_pre_conc fx R MV
                (fun k => match k with 2%nat => S | 40%nat => canz | _ => tid end)) as xrun.
  cbv beta iota in xrun.
  repeat lazymatch type of xrun with
  | ?need -> _ =>
      let got := fresh "got" in
      assert (got : need) by (
        lazymatch goal with
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            first [ exact (sh_writable LB LK cr A M model a n inv eq_refl)
                  | (apply stk; lia)
                  | exact (wsg_writable MV a (Z.to_nat n) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
        | |- L5Defs.L5.defined _ ?a ?n =>
            intros i i_rng; apply (store_ok_defined sp0 MV (a + i)); [lia|];
            exact (stk a n ltac:(lia) ltac:(lia) i 1%nat ltac:(lia) ltac:(lia))
        | |- L5Defs.L5.img_clear _ _ _ => exact clr
        | |- AS0DRVP_dpX4B_pre.aligned _ _ => exact S_al
        | |- getr _ (Z_to_bv 5 (Z.of_nat 1)) = _ => exact ra_r1
        | |- getr _ (Z_to_bv 5 (Z.of_nat 2)) = _ => exact sp_r2
        | |- getr _ (Z_to_bv 5 (Z.of_nat 4)) = _ => exact tp_r4
        | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact tid_rd
        | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact can_rd
        | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact o_lk1
        | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact o_wpos
        | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact o_wbase
        | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact o_wrfn
        | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact o_fd
        | |- ?cell _ _ ?a ?v =>
            let w := lazymatch cell with
                     | L5Defs.L5.u64_at => constr:(8) | L5Defs.L5.u32_at => constr:(4) | L5Defs.L5.u8_at => constr:(1) end in
            lazymatch cell with
            | L5Defs.L5.u64_at => unfold L5Defs.L5.u64_at
            | L5Defs.L5.u32_at => unfold L5Defs.L5.u32_at
            | L5Defs.L5.u8_at =>
                unfold L5Defs.L5.u8_at;
                replace [Z_to_bv 8 v] with (word_to_le_bytes 1 (Z_to_bv 64 v))
                  by (rewrite N_to_le_bytes_1_small; f_equal; apply bv_eq; vm_compute; reflexivity)
            end;
            first [ exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, w, v)
                             ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
                  | exact (ex_cell_vis LB LK cr A M model a w v inv
                             ltac:(unfold EX_CELLS; repeat first [apply in_eq | apply in_cons]))
                  | (apply img_cell; [img_rd | lia | lia | intros i i_rng; apply gap; lia]) ]
        | |- _ => lia
        end);
      specialize (xrun got); clear got
  end.
  destruct xrun as (fx1 & R1 & MV1 & grow1 & _ & keep1 & run1 & kept1 & _ & r2_1 & _ & _ & _ & r8_1 & r9_1
                    & r10_1 & r11_1 & r12_1 & _ & _ & _ & _ & r17_1 & r18_1 & r19_1 & r21_1 & r22_1 & _
                    & m112 & m120 & m128 & m136 & m104 & m96 & m88 & m80 & m72 & m64 & m56 & m48 & m40 & m32 & m24 & _).
  apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R _ M R1 _ MV1 model _ lz run1).
  intros M2 model2 minv2 same2 vis2.
  pose proof lz as (h_off & lz_cov & A_good & _ & halt0).
  destruct (same_but_materialized_frame _ _ same2) as (_ & _ & lazy2 & _ & _ & _ & _ & _ & fds2 & _ & _ & fs2 & halt2 & _).
  pose proof (lzinv_sbm _ _ _ _ _ lz minv2 same2) as lz2.
  assert (nolz : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x ->
                 page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x x_rng x_at; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x inv x_rng x_at)).
  assert (old1 : forall i, 0 <= i < 1295744 \/ 1299704 <= i < 6896976 \/ 6897524 <= i < 2147468856 ->
                 MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    by (intros i i_rng; apply keep1; lia).
  assert (buf0 : rdn ASEGS MV (Z_to_bv 64 6898976) 6 = Some (zero_lines 3)).
  { apply rdn_cons1; [lia | exact (proj1 (o_lines 0 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj2 (o_lines 0 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj1 (o_lines 1 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj2 (o_lines 1 ltac:(lia))) |].
    apply rdn_cons1; [lia | exact (proj1 (o_lines 2 ltac:(lia))) | exact (proj2 (o_lines 2 ltac:(lia)))]. }
  pose proof (@wv_loop fx1 scfg (ahid A model) A h_off (m_vm_lazy model) lz_cov A_good 1293752 1 ltac:(lia)
                (S - 136) (S - 104) ltac:(lia) ltac:(lia) ltac:(intros x x_rng; apply nolz; lia)
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 6%nat) as loop.
  apply (loop true R1 M2 model2 (S - 136) 2 6898976 6 0 0 (zero_lines 3) []).
  - cbn. lia.
  - exact lazy2.
  - exact minv2.
  - rewrite halt2. exact halt0.
  - rewrite fds2. exact fd1.
  - exact (conj r17_1 (conj r10_1 (conj r11_1 (conj r12_1 (conj r9_1 (conj r18_1 (conj r22_1 r19_1))))))).
  - rewrite vis2. unfold wv_iov.
    split; [lia|]. split; [lia|]. split; [right; reflexivity|]. split; [exact m136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact m128|].
    split.
    { assert (sk := stk (S - 136) 32 ltac:(lia) ltac:(lia) 0 32%nat ltac:(lia) ltac:(lia)).
      rewrite Z.add_0_r in sk. exact (store_ok_mono _ _ _ _ _ grow1 sk). }
    split.
    { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split.
      - apply (rdn_tr MV MV1 6898976 6 _ buf0); [lia | lia |]. intros i i_rng. apply old1. lia.
      - intros x x_rng. apply nolz; lia. }
    split; [intros c_one; lia|].
    intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact m120|].
    split; [replace (S - 136 + 24) with (S - 112) by lia; exact m112|].
    split; [|lia].
    unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity|].
    intros x x_rng. lia.
  - lia.
  - rewrite vis2. apply (rdn_tr MV MV1 1293872 4 _ o_fd); [lia | lia |]. intros i i_rng. apply old1. lia.
  - intros R3 M3 model3 minv3 same3 regs3 _ fr3 _ grow3.
    set (MV3 := mrestrict (ahid A model) M3).
    pose proof (lzinv_sbm _ _ _ _ _ lz2 minv3 same3) as lz3.
    assert (wr3 : forall a n, L5Defs.L5.writable ASEGS MV a n -> L5Defs.L5.writable ASEGS MV3 a n).
    { intros a n wr d k d_lo d_hi. apply (store_ok_mono _ _ (mrestrict (ahid A model) M2)); [exact grow3|].
      rewrite vis2. exact (store_ok_mono _ _ _ _ _ grow1 (wr d k d_lo d_hi)). }
    assert (lowc : forall a n bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
                   0 <= a /\ a + Z.of_nat n <= 1295744 \/ 1299704 <= a /\ a + Z.of_nat n <= 6896976 \/
                   6897524 <= a /\ a + Z.of_nat n <= 2147468856 ->
                   rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_rng. apply (rdn_tr MV MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. apply old1. lia. }
    assert (hic : forall a n bs, rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs ->
                  S - 320 <= a -> a + Z.of_nat n <= S -> a + Z.of_nat n <= S - 136 \/ S - 104 <= a ->
                  rdn ASEGS MV3 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs src a_lo a_hi a_out. apply (rdn_tr MV1 MV3 a n bs src); [lia | lia |].
      intros i i_rng. unfold MV3. rewrite fr3 by lia. rewrite vis2. reflexivity. }
    pose proof (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3
                  (fun k => match k with
                            | 2%nat => S - 144 | 40%nat => canz
                            | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                            | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                            | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                            | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                            | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                            | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                            | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                            | 110%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 10)))
                            | 118%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 18)))
                            | 119%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))
                            | 120%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 20)))
                            | 122%nat => bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 22)))
                            | _ => 0 end)) as drun.
    cbv beta iota in drun.
    repeat lazymatch type of drun with
    | ?need -> _ =>
        let got := fresh "got" in
        assert (got : need) by (
          lazymatch goal with
          | |- 0 <= bv_unsigned _ < 2 ^ 64 => apply u64_range
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = Z_to_bv 64 (bv_unsigned (getr R3 _)) =>
              symmetry; apply Z_to_bv_bv_unsigned
          | |- getr R3 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
              etransitivity;
              [ exact (regs3 (Z_to_bv 5 (Z.of_nat r)) ltac:(unfold WV_KEEP; repeat first [left; apply bv_eq; reflexivity | right]))
              | first [exact r2_1 | exact r8_1 | exact r9_1 | exact r21_1] ]
          | |- AS0DRVP_dpXd_4.aligned _ _ =>
              unfold AS0DRVP_dpXd_4.aligned; rewrite Zminus_mod, S_al; reflexivity
          | |- L5Defs.L5.writable _ _ ?a ?n =>
              apply wr3; first [ (apply stk; lia) | exact (o_wfile a n ltac:(lia) ltac:(lia)) ]
          | |- L5Defs.L5.defined _ ?a ?n =>
              intros i i_rng; apply (store_ok_defined sp0 MV3 (a + i)); [lia|];
              exact (wr3 a n (stk a n ltac:(lia) ltac:(lia)) i 1%nat ltac:(lia) ltac:(lia))
          | |- L5Defs.L5.img_clear _ _ _ =>
              intros i i_rng; unfold MV3; rewrite fr3 by lia; rewrite vis2, old1 by lia; exact (clr i i_rng)
          | |- L5Defs.L5.u64_at _ _ (S - 144 + ?k) _ =>
              let saved := lazymatch k with
                           | 40 => m104 | 48 => m96 | 56 => m88 | 64 => m80 | 72 => m72 | 80 => m64
                           | 88 => m56 | 96 => m48 | 104 => m40 | 112 => m32 | 120 => m24 end in
              let back := eval vm_compute in (144 - k) in
              unfold L5Defs.L5.u64_at; replace (S - 144 + k) with (S - back) by lia;
              apply hic; [exact saved | lia | lia | lia]
          | |- L5Defs.L5.u64_at _ _ ?a ?v =>
              unfold L5Defs.L5.u64_at; apply lowc; [|lia];
              lazymatch a with
              | 1293840 => exact o_buf | 1293848 => exact o_size | 6896960 => exact can_rd
              | 1293760 => exact o_rd1 | 1293768 => exact o_rd2
              | _ => exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 8, v)
                              ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
              end
          | |- L5Defs.L5.u32_at _ _ ?a ?v =>
              unfold L5Defs.L5.u32_at; apply lowc; [|lia];
              exact (proj1 (Forall_forall _ XC_CELLS_B) cellsB (a, 4, v)
                       ltac:(unfold XC_CELLS_B; repeat first [apply in_eq | apply in_cons]))
          | |- _ => lia
          end);
        specialize (drun got); clear got
    end.
    destruct drun as (fx4 & R4 & MV4 & _ & _ & _ & run4 & _ & _ & _ & _ & _ & r10_4 & _ & _ & r17_4 & _).
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx4 R3 _ M3 R4 _ MV4 model3 _ lz3 run4).
    intros M5 model5 _ same5 _.
    destruct (sbm_fds _ _ same5) as (_ & fs5). destruct (sbm_fds _ _ same3) as (_ & fs3).
    rewrite <- fs2, <- fs3, <- fs5.
    apply (rz_exit_at_lit_lz ASEGS scfg R4 _ M5 _ model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    + rewrite (sbm_halted_eq _ _ same5). exact (proj2 (proj2 (proj2 (proj2 lz3)))).
    + left. exact r17_4.
    + etransitivity; [exact r10_4|]. rewrite Z_to_bv_bv_unsigned. exact a0_r10.
    + exact st_rng.
Qed.
End Exit.
End FPX_1.
