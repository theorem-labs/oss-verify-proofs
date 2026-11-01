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
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpXBS_b Ba0DrvP_dpX2BS_pre_b Ba0DrvP_dpX3BS_pre_b Ba0DrvP_dpX4BS_pre_b Ba0DrvP_dpXd_2_b Ba0DrvP_dpXd_3_b Ba0DrvP_dpXd_4_b.
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
Definition XC_CELLS_BS : list (Z * Z * Z) :=
  [(6897520, 4, 0); (6897555, 1, 0); (6896992, 8, 6897000); (6896984, 4, 8); (6897008, 8, 1148964); (6897264, 8, 619876); (6896980, 4, 0); (6897000, 8, 0); (6898952, 8, 0); (1294224, 8, 1293992); (1294132, 4, 4294967295); (1294032, 8, 0); (1294048, 8, 0); (1294000, 8, 0); (1294008, 8, 0); (1293984, 8, 1293752); (1293744, 8, 1293512); (1293652, 4, 4294967295); (1293552, 8, 0); (1293568, 8, 0); (1293520, 8, 0); (1293528, 8, 0); (6897016, 8, 1148964); (6897272, 8, 687916); (6759060, 1, 0); (6759112, 1, 16); (6759144, 1, 6); (6897024, 8, 872740); (6897032, 8, 449180); (6897040, 8, 874172); (6897048, 8, 449180); (6897056, 8, 874172); (6897064, 8, 449180); (6897280, 8, 1293304); (6897288, 8, 0); (6897296, 8, 6759112); (6897304, 8, 0); (6897312, 8, 6759144); (6897320, 8, 0)].
Definition exitBS (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_BS
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

  Definition exit_preBS (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    dinvA LB LK cr A M model
    /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n : Z, usp - 8388608 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n)
    /\ L5Defs.L5.img_clear (mrestrict (ahid A model) M) 65536 1282048
    /\ exitBS tid (mrestrict (ahid A model) M).

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0BS : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preBS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
Proof.
  intros LB LK cr A M model R S st tid Pre MV StRng RaReg SpReg TpReg StReg Out0 OutX.
  destruct Pre as (Inv & SpLo & SpHi & SpAl & StkW & ImgClr & XBS).
  destruct XBS as (CellsBS & TidAt & TidRng & ImgNone).
  destruct Out0 as (OFlag & OSize & OEnd & OPos & OBase & OLock & OLbf & OFile & OBuf & OLines).
  destruct OutX as (XWrite & XFd & XBufP & XPrev & XNext).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Inv) as Lz.
  pose proof (AS0DRVP_dpXBS.dpXBS_conc fx R MV (fun k => if Nat.eqb k 44 then tid else S)) as Seg.
  cbv beta iota delta [Nat.eqb] in Seg.
  repeat lazymatch type of Seg with
  | ?P -> _ =>
    let Pf := fresh "Pf" in
    assert (Pf : P);
    [ lazymatch goal with
      | |- getr _ _ = _ => first [exact RaReg | exact SpReg | exact TpReg | exact StReg]
      | |- AS0DRVP_dpXBS.aligned _ _ => exact SpAl
      | |- L5Defs.L5.img_clear _ _ _ => exact ImgClr
      | |- L5Defs.L5.writable _ _ (S - _) _ => apply StkW; lia
      | |- L5Defs.L5.defined _ (S - ?k) ?n =>
          intros i Ri; apply (store_ok_defined sp0 MV (S - k + i)); [lia|];
          pose proof (StkW (S - k + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
          rewrite Z.add_0_r in Wr1; exact Wr1
      | |- L5Defs.L5.writable _ _ ?a ?n =>
          first [ exact (sh_writable LB LK cr A M model a n Inv eq_refl)
                | let k := eval vm_compute in (Z.to_nat n) in
                  exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
      | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact TidAt
      | |- L5Defs.L5.u32_at _ _ 1293752 _ => exact OFlag
      | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
      | |- L5Defs.L5.u64_at _ _ 1293784 _ => exact OEnd
      | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact OPos
      | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact OBase
      | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact OLock
      | |- L5Defs.L5.u32_at _ _ 1293896 _ => exact OLbf
      | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact XWrite
      | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact XFd
      | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
      | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
      | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
      | |- _ =>
          first
            [ lazymatch goal with |- ?G =>
              let w := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ _ => constr:(8)
                       | L5Defs.L5.u32_at _ _ _ _ => constr:(4)
                       | L5Defs.L5.u8_at _ _ _ _ => constr:(1)
                       end in
              let a := lazymatch G with
                       | L5Defs.L5.u64_at _ _ ?x _ => x | L5Defs.L5.u32_at _ _ ?x _ => x | L5Defs.L5.u8_at _ _ ?x _ => x end in
              let v := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ ?x => x | L5Defs.L5.u32_at _ _ _ ?x => x | L5Defs.L5.u8_at _ _ _ ?x => x end in
              first
                [ exact (proj1 (Forall_forall _ _) CellsBS (a, w, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
                | exact (ex_cell_vis LB LK cr A M model a w v Inv
                           ltac:(unfold EX_CELLS; cbn [In]; repeat first [left; reflexivity | right]))
                | unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
                  apply img_cell; [img_rd | lia | lia | intros i Ri; apply ImgNone; lia] ]
              end
            | lia ]
      end
    | specialize (Seg Pf); clear Pf ]
  end.
  destruct Seg as (fx' & R' & MV' & Grow & FrameW & FrameZ & Run & Kept & Rest).
  assert (A7 : getr R' (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94) by (decompose [and] Rest; assumption).
  assert (A0 : getr R' (Z_to_bv 5 (Z.of_nat 10)) = getr R (Z_to_bv 5 (Z.of_nat 10)))
    by (apply Kept; unfold AS0DRVP_dpXBS.KS_dpXBS; cbn [In]; repeat first [left; reflexivity | right]).
  clear Rest.
  apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 1149048) M R' (Z_to_bv 64 1148296) MV' model _ Lz Run).
  intros Mx modelx MIx SBMx Vx.
  rewrite <- (proj2 (sbm_fds _ _ SBMx)).
  eapply rz_exit_at_lit_lz.
  - exact fetch_exitA.
  - exact is_ecall_ECALLW.
  - rewrite (sbm_halted_eq _ _ SBMx). exact (di_halt _ _ _ _ _ _ _ _ _ _ Inv).
  - left. exact A7.
  - exact (eq_trans A0 StReg).
  - exact StRng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2BS : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preBS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz Pre MV StRng CanRng RaReg SpReg TpReg StReg CanAt Out0 OutX Fd1.
  destruct Pre as (Inv & SpLo & SpHi & SpAl & StkW & ImgClr & XBS).
  destruct XBS as (CellsBS & TidAt & TidRng & ImgNone).
  destruct Out0 as (OFlag & OSize & OEnd & OPos & OBase & OLock & OLbf & OFile & OBuf & OLines).
  destruct OutX as (XWrite & XFd & XBufP & XPrev & XNext).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Inv) as Lz.
  pose proof (AS0DRVP_dpX2BS_pre.dpX2BS_pre_conc fx R MV (fun k => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Seg.
  cbv beta iota delta [Nat.eqb] in Seg.
  repeat lazymatch type of Seg with
  | ?P -> _ =>
    let Pf := fresh "Pf" in
    assert (Pf : P);
    [ lazymatch goal with
      | |- getr _ _ = _ => first [exact RaReg | exact SpReg | exact TpReg | exact StReg]
      | |- AS0DRVP_dpX2BS_pre.aligned _ _ => exact SpAl
      | |- L5Defs.L5.img_clear _ _ _ => exact ImgClr
      | |- L5Defs.L5.writable _ _ (S - _) _ => apply StkW; lia
      | |- L5Defs.L5.defined _ (S - ?k) ?n =>
          intros i Ri; apply (store_ok_defined sp0 MV (S - k + i)); [lia|];
          pose proof (StkW (S - k + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
          rewrite Z.add_0_r in Wr1; exact Wr1
      | |- L5Defs.L5.writable _ _ ?a ?n =>
          first [ exact (sh_writable LB LK cr A M model a n Inv eq_refl)
                | let k := eval vm_compute in (Z.to_nat n) in
                  exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
      | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact TidAt
      | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
      | |- L5Defs.L5.u32_at _ _ 1293752 _ => exact OFlag
      | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
      | |- L5Defs.L5.u64_at _ _ 1293784 _ => exact OEnd
      | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact OPos
      | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact OBase
      | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact OLock
      | |- L5Defs.L5.u32_at _ _ 1293896 _ => exact OLbf
      | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact XWrite
      | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact XFd
      | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
      | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
      | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
      | |- _ =>
          first
            [ lazymatch goal with |- ?G =>
              let w := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ _ => constr:(8)
                       | L5Defs.L5.u32_at _ _ _ _ => constr:(4)
                       | L5Defs.L5.u8_at _ _ _ _ => constr:(1)
                       end in
              let a := lazymatch G with
                       | L5Defs.L5.u64_at _ _ ?x _ => x | L5Defs.L5.u32_at _ _ ?x _ => x | L5Defs.L5.u8_at _ _ ?x _ => x end in
              let v := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ ?x => x | L5Defs.L5.u32_at _ _ _ ?x => x | L5Defs.L5.u8_at _ _ _ ?x => x end in
              first
                [ exact (proj1 (Forall_forall _ _) CellsBS (a, w, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
                | exact (ex_cell_vis LB LK cr A M model a w v Inv
                           ltac:(unfold EX_CELLS; cbn [In]; repeat first [left; reflexivity | right]))
                | unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
                  apply img_cell; [img_rd | lia | lia | intros i Ri; apply ImgNone; lia] ]
              end
            | lia ]
      end
    | specialize (Seg Pf); clear Pf ]
  end.
  destruct Seg as (fx' & R1 & MV1 & Grow1 & FrameW1 & FrameZ1 & Run1 & Kept1 & Rest1).
  assert (Q2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 144)) by (decompose [and] Rest1; assumption).
  assert (Q8 : getr R1 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (decompose [and] Rest1; assumption).
  assert (Q9 : getr R1 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (decompose [and] Rest1; assumption).
  assert (Q10 : getr R1 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 1) by (decompose [and] Rest1; assumption).
  assert (Q11 : getr R1 (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q12 : getr R1 (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q17 : getr R1 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 66) by (decompose [and] Rest1; assumption).
  assert (Q18 : getr R1 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q19 : getr R1 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q21 : getr R1 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (decompose [and] Rest1; assumption).
  assert (Q22 : getr R1 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (K136 : L5Defs.L5.u64_at ASEGS MV1 (S - 136) 6898976) by (decompose [and] Rest1; assumption).
  assert (K128 : L5Defs.L5.u64_at ASEGS MV1 (S - 128) 2) by (decompose [and] Rest1; assumption).
  assert (K120 : L5Defs.L5.u64_at ASEGS MV1 (S - 120) 0) by (decompose [and] Rest1; assumption).
  assert (K112 : L5Defs.L5.u64_at ASEGS MV1 (S - 112) 0) by (decompose [and] Rest1; assumption).
  assert (K104 : L5Defs.L5.u64_at ASEGS MV1 (S - 104) canz) by (decompose [and] Rest1; assumption).
  assert (K96 : L5Defs.L5.u64_at ASEGS MV1 (S - 96) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))))) by (decompose [and] Rest1; assumption).
  assert (K88 : L5Defs.L5.u64_at ASEGS MV1 (S - 88) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21))))) by (decompose [and] Rest1; assumption).
  assert (K80 : L5Defs.L5.u64_at ASEGS MV1 (S - 80) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))))) by (decompose [and] Rest1; assumption).
  assert (K72 : L5Defs.L5.u64_at ASEGS MV1 (S - 72) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19))))) by (decompose [and] Rest1; assumption).
  assert (K64 : L5Defs.L5.u64_at ASEGS MV1 (S - 64) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))))) by (decompose [and] Rest1; assumption).
  assert (K56 : L5Defs.L5.u64_at ASEGS MV1 (S - 56) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))))) by (decompose [and] Rest1; assumption).
  assert (K48 : L5Defs.L5.u64_at ASEGS MV1 (S - 48) 1293752) by (decompose [and] Rest1; assumption).
  assert (K40 : L5Defs.L5.u64_at ASEGS MV1 (S - 40) 1181792) by (decompose [and] Rest1; assumption).
  assert (K32 : L5Defs.L5.u64_at ASEGS MV1 (S - 32) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))))) by (decompose [and] Rest1; assumption).
  assert (K24 : L5Defs.L5.u64_at ASEGS MV1 (S - 24) 1149156) by (decompose [and] Rest1; assumption).
  clear Rest1 FrameW1.
  assert (Keep1 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
            i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
            i < 2147468856 \/ 2147612852 <= i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Ri OStk O1 O2 O3 O4 O5 OSh. apply FrameZ1; [exact Ri | ..].
    all: intros InR; first [ destruct OSh; lia | destruct OStk; lia | destruct O1; lia | destruct O2; lia
                           | destruct O3; lia | destruct O4; lia | destruct O5; lia ]. }
  clear FrameZ1.
  pose proof (OLines 0 ltac:(lia)) as (Ln0a & Ln0b).
  assert (Buf0 : rdn ASEGS MV (Z_to_bv 64 SOBUF) (Z.to_nat 2) = Some (zero_lines 1)).
  { cbn [zero_lines]. change (Z.to_nat 2) with 2%nat.
    repeat (apply rdn_cons1; [unfold SOBUF; lia | assumption | ]). reflexivity. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 1149048) M R1 (Z_to_bv 64 1180248) MV1 model _ Lz Run1).
  intros M1 model1 MI1 SBM1 Vis1.
  destruct Lz as (HOff & LzCov & AWf & MInv0 & Halt0).
  destruct (same_but_materialized_frame _ _ SBM1) as (_ & _ & Lazy1 & _).
  destruct (sbm_fds _ _ SBM1) as (Fds1 & Fs1).
  assert (Halt1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Halt0).
  assert (PageFree : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x Rx Wx; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Inv Rx Wx)).
  pose proof (@wv_loop fx' scfg (ahid A model) A HOff (m_vm_lazy model) LzCov AWf 1293752 1 ltac:(lia) (S - 136) (S - 104)
                ltac:(lia) ltac:(lia) (fun x Rx => PageFree x ltac:(lia) ltac:(lia))
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 2%nat) as Loop.
  unfold wv_loop_stmt in Loop.
  change (Z_to_bv 64 1180248) with (wv_pc true).
  change (W 1 (zero_lines 1)) with (map (WriteEv (Z_to_bv 64 1)) (zero_lines 1 ++ [])).
  apply (Loop true R1 M1 model1 (S - 136) 2 SOBUF 2 0 0 (zero_lines 1) []).
  - cbn. lia.
  - exact Lazy1.
  - exact MI1.
  - exact Halt1.
  - rewrite Fds1. exact Fd1.
  - unfold wv_regs. repeat split.
    all: first [exact Q17 | exact Q10 | exact Q11 | exact Q12 | exact Q9 | exact Q18 | exact Q22 | exact Q19].
  - unfold wv_iov. rewrite Vis1.
    assert (StkW1 : L5Defs.L5.writable ASEGS MV1 (S - 136) 32) by (apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1); apply StkW; lia).
    split; [lia|]. split; [lia|]. split; [right; reflexivity|].
    split; [exact K136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact K128|].
    split; [pose proof (StkW1 0 32%nat ltac:(lia) ltac:(lia)) as Wq; rewrite Z.add_0_r in Wq; exact Wq|].
    split.
    + unfold wv_buf. split; [unfold SOBUF; lia|]. split; [lia|]. split; [unfold SOBUF; lia|].
      split; [right; left; unfold SOBUF; lia|].
      split; [apply (rdn_tr MV MV1 _ _ _ Buf0); [unfold SOBUF; lia | unfold SOBUF; lia | intros i Ri; unfold SOBUF in Ri; apply Keep1; lia]|].
      intros x Rx. apply PageFree; unfold SOBUF in Rx; lia.
    + split; [intro Bad; lia|].
      intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact K120|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; exact K112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      split; [reflexivity|]. intros x Rx. lia.
  - lia.
  - rewrite Vis1. apply (rdn_tr MV MV1 _ _ _ XFd); [lia | lia | intros i Ri; apply Keep1; lia].
  - intros R2 M2 model2 MI2 SBM2 KeepR2 FrameF2 FrameV2 GrowF2 GrowV2.
    set (MV2 := mrestrict (ahid A model) M2).
    assert (Grow12 : mem_grows MV1 MV2) by (rewrite <- Vis1; exact GrowV2).
    assert (Frame12 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 136 <= a < S - 104) -> MV2 (Z_to_bv 64 a) = MV1 (Z_to_bv 64 a))
      by (rewrite <- Vis1; exact FrameV2).
    assert (Keep02 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
              i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
              i < 2147468856 \/ 2147612852 <= i -> MV2 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Ri OStk O1 O2 O3 O4 O5 OSh. rewrite (Frame12 i Ri ltac:(lia)). exact (Keep1 i Ri OStk O1 O2 O3 O4 O5 OSh). }
    destruct (same_but_materialized_frame _ _ SBM2) as (_ & _ & Lazy2 & _).
    destruct (sbm_fds _ _ SBM2) as (Fds2 & Fs2).
    assert (Halt2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Halt1).
    assert (Lz2 : lzinv ASEGS (ahid A model) A model2) by (split; [exact HOff|]; split; [rewrite Lazy2, Lazy1; exact LzCov|]; split; [exact AWf|]; split; [exact MI2 | exact Halt2]).
    pose proof (Ba0DrvP_dpXd_2_b.AS0DRVP_dpXd_2.dpXd_2_conc fx' R2 MV2
      (fun k => if Nat.eqb k 2 then S - 144
                else if Nat.eqb k 9 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                else if Nat.eqb k 10 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 18 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 19 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 20 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 21 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                else if Nat.eqb k 22 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                else if Nat.eqb k 40 then canz
                else if Nat.eqb k 110 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 118 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 119 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 120 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 122 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
                else 0)) as Seg2.
    cbv beta iota delta [Nat.eqb] in Seg2.
    repeat lazymatch type of Seg2 with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- 0 <= bv_unsigned ?w < 2 ^ 64 => exact (u64_range w)
        | |- getr R2 _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
        | |- getr R2 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
            refine (eq_trans (KeepR2 (Z_to_bv 5 (Z.of_nat r)) _) _);
            [ unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]
            | first [exact Q2 | exact Q8 | exact Q9 | exact Q21] ]
        | |- Ba0DrvP_dpXd_2_b.AS0DRVP_dpXd_2.aligned _ _ => unfold Ba0DrvP_dpXd_2_b.AS0DRVP_dpXd_2.aligned; rewrite Zminus_mod, SpAl; reflexivity
        | |- L5Defs.L5.img_clear _ _ _ =>
            intros i Ri; rewrite (Keep02 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
            exact (ImgClr i Ri)
        | |- L5Defs.L5.writable _ _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            apply StkW; lia
        | |- L5Defs.L5.defined _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.defined_grows MV1 MV2 _ _ Grow12); apply (L5Defs.L5.defined_grows MV MV1 _ _ Grow1);
            intros i Ri; apply (store_ok_defined sp0 MV (S - 144 - 16 + i)); [lia|];
            pose proof (StkW (S - 144 - 16 + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
            rewrite Z.add_0_r in Wr1; exact Wr1
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            intros d k Dlo Dhi; exact (OFile a n ltac:(lia) ltac:(lia) d k Dlo Dhi)
        | |- L5Defs.L5.u64_at _ _ (S - 144 + ?off) _ =>
            let k := eval vm_compute in (144 - off) in
            replace (S - 144 + off) with (S - k) by lia;
            unfold L5Defs.L5.u64_at; apply (rdn_tr MV1 MV2); [assumption | lia | lia | intros i Ri; apply Frame12; lia]
        | |- L5Defs.L5.u64_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u64_at ASEGS MV a v);
            [ lazymatch goal with
              | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
              | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
              | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
              | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
              | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
              | |- _ => exact (proj1 (Forall_forall _ _) CellsBS (a, 8, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
              end
            | unfold L5Defs.L5.u64_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia] ]
        | |- L5Defs.L5.u32_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u32_at ASEGS MV a v)
              by exact (proj1 (Forall_forall _ _) CellsBS (a, 4, v)
                          ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]));
            unfold L5Defs.L5.u32_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia]
        | |- _ => lia
        end
      | specialize (Seg2 Pf); clear Pf ]
    end.
    destruct Seg2 as (fx3 & R3 & MV3 & Grow3 & FrameW3 & FrameZ3 & Run3 & Kept3 & Rest3).
    assert (T17 : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94) by (decompose [and] Rest3; assumption).
    assert (T10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))))
      by (decompose [and] Rest3; assumption).
    rewrite Z_to_bv_bv_unsigned in T10.
    clear Rest3 FrameW3 FrameZ3.
    apply (msteps_vis_fx scfg (ahid A model) A fx' fx3 R2 (Z_to_bv 64 1180260) M2 R3 (Z_to_bv 64 1148296) MV3 model2 _ Lz2 Run3).
    intros M4 model4 MI4 SBM4 Vis4.
    destruct (sbm_fds _ _ SBM4) as (Fds4 & Fs4).
    rewrite <- Fs1, <- Fs2, <- Fs4.
    eapply rz_exit_at_lit_lz.
    + exact fetch_exitA.
    + exact is_ecall_ECALLW.
    + rewrite (sbm_halted_eq _ _ SBM4). exact Halt2.
    + left. exact T17.
    + exact (eq_trans T10 StReg).
    + exact StRng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3BS : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preBS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz Pre MV StRng CanRng RaReg SpReg TpReg StReg CanAt Out0 OutX Fd1.
  destruct Pre as (Inv & SpLo & SpHi & SpAl & StkW & ImgClr & XBS).
  destruct XBS as (CellsBS & TidAt & TidRng & ImgNone).
  destruct Out0 as (OFlag & OSize & OEnd & OPos & OBase & OLock & OLbf & OFile & OBuf & OLines).
  destruct OutX as (XWrite & XFd & XBufP & XPrev & XNext).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Inv) as Lz.
  pose proof (AS0DRVP_dpX3BS_pre.dpX3BS_pre_conc fx R MV (fun k => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Seg.
  cbv beta iota delta [Nat.eqb] in Seg.
  repeat lazymatch type of Seg with
  | ?P -> _ =>
    let Pf := fresh "Pf" in
    assert (Pf : P);
    [ lazymatch goal with
      | |- getr _ _ = _ => first [exact RaReg | exact SpReg | exact TpReg | exact StReg]
      | |- AS0DRVP_dpX3BS_pre.aligned _ _ => exact SpAl
      | |- L5Defs.L5.img_clear _ _ _ => exact ImgClr
      | |- L5Defs.L5.writable _ _ (S - _) _ => apply StkW; lia
      | |- L5Defs.L5.defined _ (S - ?k) ?n =>
          intros i Ri; apply (store_ok_defined sp0 MV (S - k + i)); [lia|];
          pose proof (StkW (S - k + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
          rewrite Z.add_0_r in Wr1; exact Wr1
      | |- L5Defs.L5.writable _ _ ?a ?n =>
          first [ exact (sh_writable LB LK cr A M model a n Inv eq_refl)
                | let k := eval vm_compute in (Z.to_nat n) in
                  exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
      | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact TidAt
      | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
      | |- L5Defs.L5.u32_at _ _ 1293752 _ => exact OFlag
      | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
      | |- L5Defs.L5.u64_at _ _ 1293784 _ => exact OEnd
      | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact OPos
      | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact OBase
      | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact OLock
      | |- L5Defs.L5.u32_at _ _ 1293896 _ => exact OLbf
      | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact XWrite
      | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact XFd
      | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
      | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
      | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
      | |- _ =>
          first
            [ lazymatch goal with |- ?G =>
              let w := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ _ => constr:(8)
                       | L5Defs.L5.u32_at _ _ _ _ => constr:(4)
                       | L5Defs.L5.u8_at _ _ _ _ => constr:(1)
                       end in
              let a := lazymatch G with
                       | L5Defs.L5.u64_at _ _ ?x _ => x | L5Defs.L5.u32_at _ _ ?x _ => x | L5Defs.L5.u8_at _ _ ?x _ => x end in
              let v := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ ?x => x | L5Defs.L5.u32_at _ _ _ ?x => x | L5Defs.L5.u8_at _ _ _ ?x => x end in
              first
                [ exact (proj1 (Forall_forall _ _) CellsBS (a, w, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
                | exact (ex_cell_vis LB LK cr A M model a w v Inv
                           ltac:(unfold EX_CELLS; cbn [In]; repeat first [left; reflexivity | right]))
                | unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
                  apply img_cell; [img_rd | lia | lia | intros i Ri; apply ImgNone; lia] ]
              end
            | lia ]
      end
    | specialize (Seg Pf); clear Pf ]
  end.
  destruct Seg as (fx' & R1 & MV1 & Grow1 & FrameW1 & FrameZ1 & Run1 & Kept1 & Rest1).
  assert (Q2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 144)) by (decompose [and] Rest1; assumption).
  assert (Q8 : getr R1 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (decompose [and] Rest1; assumption).
  assert (Q9 : getr R1 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (decompose [and] Rest1; assumption).
  assert (Q10 : getr R1 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 1) by (decompose [and] Rest1; assumption).
  assert (Q11 : getr R1 (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q12 : getr R1 (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q17 : getr R1 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 66) by (decompose [and] Rest1; assumption).
  assert (Q18 : getr R1 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q19 : getr R1 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q21 : getr R1 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (decompose [and] Rest1; assumption).
  assert (Q22 : getr R1 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 4) by (decompose [and] Rest1; assumption).
  assert (K136 : L5Defs.L5.u64_at ASEGS MV1 (S - 136) 6898976) by (decompose [and] Rest1; assumption).
  assert (K128 : L5Defs.L5.u64_at ASEGS MV1 (S - 128) 4) by (decompose [and] Rest1; assumption).
  assert (K120 : L5Defs.L5.u64_at ASEGS MV1 (S - 120) 0) by (decompose [and] Rest1; assumption).
  assert (K112 : L5Defs.L5.u64_at ASEGS MV1 (S - 112) 0) by (decompose [and] Rest1; assumption).
  assert (K104 : L5Defs.L5.u64_at ASEGS MV1 (S - 104) canz) by (decompose [and] Rest1; assumption).
  assert (K96 : L5Defs.L5.u64_at ASEGS MV1 (S - 96) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))))) by (decompose [and] Rest1; assumption).
  assert (K88 : L5Defs.L5.u64_at ASEGS MV1 (S - 88) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21))))) by (decompose [and] Rest1; assumption).
  assert (K80 : L5Defs.L5.u64_at ASEGS MV1 (S - 80) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))))) by (decompose [and] Rest1; assumption).
  assert (K72 : L5Defs.L5.u64_at ASEGS MV1 (S - 72) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19))))) by (decompose [and] Rest1; assumption).
  assert (K64 : L5Defs.L5.u64_at ASEGS MV1 (S - 64) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))))) by (decompose [and] Rest1; assumption).
  assert (K56 : L5Defs.L5.u64_at ASEGS MV1 (S - 56) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))))) by (decompose [and] Rest1; assumption).
  assert (K48 : L5Defs.L5.u64_at ASEGS MV1 (S - 48) 1293752) by (decompose [and] Rest1; assumption).
  assert (K40 : L5Defs.L5.u64_at ASEGS MV1 (S - 40) 1181792) by (decompose [and] Rest1; assumption).
  assert (K32 : L5Defs.L5.u64_at ASEGS MV1 (S - 32) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))))) by (decompose [and] Rest1; assumption).
  assert (K24 : L5Defs.L5.u64_at ASEGS MV1 (S - 24) 1149156) by (decompose [and] Rest1; assumption).
  clear Rest1 FrameW1.
  assert (Keep1 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
            i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
            i < 2147468856 \/ 2147612852 <= i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Ri OStk O1 O2 O3 O4 O5 OSh. apply FrameZ1; [exact Ri | ..].
    all: intros InR; first [ destruct OSh; lia | destruct OStk; lia | destruct O1; lia | destruct O2; lia
                           | destruct O3; lia | destruct O4; lia | destruct O5; lia ]. }
  clear FrameZ1.
  pose proof (OLines 0 ltac:(lia)) as (Ln0a & Ln0b).
  pose proof (OLines 1 ltac:(lia)) as (Ln1a & Ln1b).
  assert (Buf0 : rdn ASEGS MV (Z_to_bv 64 SOBUF) (Z.to_nat 4) = Some (zero_lines 2)).
  { cbn [zero_lines]. change (Z.to_nat 4) with 4%nat.
    repeat (apply rdn_cons1; [unfold SOBUF; lia | assumption | ]). reflexivity. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 1149048) M R1 (Z_to_bv 64 1180248) MV1 model _ Lz Run1).
  intros M1 model1 MI1 SBM1 Vis1.
  destruct Lz as (HOff & LzCov & AWf & MInv0 & Halt0).
  destruct (same_but_materialized_frame _ _ SBM1) as (_ & _ & Lazy1 & _).
  destruct (sbm_fds _ _ SBM1) as (Fds1 & Fs1).
  assert (Halt1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Halt0).
  assert (PageFree : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x Rx Wx; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Inv Rx Wx)).
  pose proof (@wv_loop fx' scfg (ahid A model) A HOff (m_vm_lazy model) LzCov AWf 1293752 1 ltac:(lia) (S - 136) (S - 104)
                ltac:(lia) ltac:(lia) (fun x Rx => PageFree x ltac:(lia) ltac:(lia))
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 4%nat) as Loop.
  unfold wv_loop_stmt in Loop.
  change (Z_to_bv 64 1180248) with (wv_pc true).
  change (W 1 (zero_lines 2)) with (map (WriteEv (Z_to_bv 64 1)) (zero_lines 2 ++ [])).
  apply (Loop true R1 M1 model1 (S - 136) 2 SOBUF 4 0 0 (zero_lines 2) []).
  - cbn. lia.
  - exact Lazy1.
  - exact MI1.
  - exact Halt1.
  - rewrite Fds1. exact Fd1.
  - unfold wv_regs. repeat split.
    all: first [exact Q17 | exact Q10 | exact Q11 | exact Q12 | exact Q9 | exact Q18 | exact Q22 | exact Q19].
  - unfold wv_iov. rewrite Vis1.
    assert (StkW1 : L5Defs.L5.writable ASEGS MV1 (S - 136) 32) by (apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1); apply StkW; lia).
    split; [lia|]. split; [lia|]. split; [right; reflexivity|].
    split; [exact K136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact K128|].
    split; [pose proof (StkW1 0 32%nat ltac:(lia) ltac:(lia)) as Wq; rewrite Z.add_0_r in Wq; exact Wq|].
    split.
    + unfold wv_buf. split; [unfold SOBUF; lia|]. split; [lia|]. split; [unfold SOBUF; lia|].
      split; [right; left; unfold SOBUF; lia|].
      split; [apply (rdn_tr MV MV1 _ _ _ Buf0); [unfold SOBUF; lia | unfold SOBUF; lia | intros i Ri; unfold SOBUF in Ri; apply Keep1; lia]|].
      intros x Rx. apply PageFree; unfold SOBUF in Rx; lia.
    + split; [intro Bad; lia|].
      intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact K120|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; exact K112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      split; [reflexivity|]. intros x Rx. lia.
  - lia.
  - rewrite Vis1. apply (rdn_tr MV MV1 _ _ _ XFd); [lia | lia | intros i Ri; apply Keep1; lia].
  - intros R2 M2 model2 MI2 SBM2 KeepR2 FrameF2 FrameV2 GrowF2 GrowV2.
    set (MV2 := mrestrict (ahid A model) M2).
    assert (Grow12 : mem_grows MV1 MV2) by (rewrite <- Vis1; exact GrowV2).
    assert (Frame12 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 136 <= a < S - 104) -> MV2 (Z_to_bv 64 a) = MV1 (Z_to_bv 64 a))
      by (rewrite <- Vis1; exact FrameV2).
    assert (Keep02 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
              i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
              i < 2147468856 \/ 2147612852 <= i -> MV2 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Ri OStk O1 O2 O3 O4 O5 OSh. rewrite (Frame12 i Ri ltac:(lia)). exact (Keep1 i Ri OStk O1 O2 O3 O4 O5 OSh). }
    destruct (same_but_materialized_frame _ _ SBM2) as (_ & _ & Lazy2 & _).
    destruct (sbm_fds _ _ SBM2) as (Fds2 & Fs2).
    assert (Halt2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Halt1).
    assert (Lz2 : lzinv ASEGS (ahid A model) A model2) by (split; [exact HOff|]; split; [rewrite Lazy2, Lazy1; exact LzCov|]; split; [exact AWf|]; split; [exact MI2 | exact Halt2]).
    pose proof (Ba0DrvP_dpXd_3_b.AS0DRVP_dpXd_3.dpXd_3_conc fx' R2 MV2
      (fun k => if Nat.eqb k 2 then S - 144
                else if Nat.eqb k 9 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                else if Nat.eqb k 10 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 18 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 19 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 20 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 21 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                else if Nat.eqb k 22 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                else if Nat.eqb k 40 then canz
                else if Nat.eqb k 110 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 118 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 119 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 120 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 122 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
                else 0)) as Seg2.
    cbv beta iota delta [Nat.eqb] in Seg2.
    repeat lazymatch type of Seg2 with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- 0 <= bv_unsigned ?w < 2 ^ 64 => exact (u64_range w)
        | |- getr R2 _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
        | |- getr R2 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
            refine (eq_trans (KeepR2 (Z_to_bv 5 (Z.of_nat r)) _) _);
            [ unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]
            | first [exact Q2 | exact Q8 | exact Q9 | exact Q21] ]
        | |- Ba0DrvP_dpXd_3_b.AS0DRVP_dpXd_3.aligned _ _ => unfold Ba0DrvP_dpXd_3_b.AS0DRVP_dpXd_3.aligned; rewrite Zminus_mod, SpAl; reflexivity
        | |- L5Defs.L5.img_clear _ _ _ =>
            intros i Ri; rewrite (Keep02 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
            exact (ImgClr i Ri)
        | |- L5Defs.L5.writable _ _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            apply StkW; lia
        | |- L5Defs.L5.defined _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.defined_grows MV1 MV2 _ _ Grow12); apply (L5Defs.L5.defined_grows MV MV1 _ _ Grow1);
            intros i Ri; apply (store_ok_defined sp0 MV (S - 144 - 16 + i)); [lia|];
            pose proof (StkW (S - 144 - 16 + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
            rewrite Z.add_0_r in Wr1; exact Wr1
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            intros d k Dlo Dhi; exact (OFile a n ltac:(lia) ltac:(lia) d k Dlo Dhi)
        | |- L5Defs.L5.u64_at _ _ (S - 144 + ?off) _ =>
            let k := eval vm_compute in (144 - off) in
            replace (S - 144 + off) with (S - k) by lia;
            unfold L5Defs.L5.u64_at; apply (rdn_tr MV1 MV2); [assumption | lia | lia | intros i Ri; apply Frame12; lia]
        | |- L5Defs.L5.u64_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u64_at ASEGS MV a v);
            [ lazymatch goal with
              | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
              | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
              | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
              | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
              | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
              | |- _ => exact (proj1 (Forall_forall _ _) CellsBS (a, 8, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
              end
            | unfold L5Defs.L5.u64_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia] ]
        | |- L5Defs.L5.u32_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u32_at ASEGS MV a v)
              by exact (proj1 (Forall_forall _ _) CellsBS (a, 4, v)
                          ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]));
            unfold L5Defs.L5.u32_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia]
        | |- _ => lia
        end
      | specialize (Seg2 Pf); clear Pf ]
    end.
    destruct Seg2 as (fx3 & R3 & MV3 & Grow3 & FrameW3 & FrameZ3 & Run3 & Kept3 & Rest3).
    assert (T17 : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94) by (decompose [and] Rest3; assumption).
    assert (T10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))))
      by (decompose [and] Rest3; assumption).
    rewrite Z_to_bv_bv_unsigned in T10.
    clear Rest3 FrameW3 FrameZ3.
    apply (msteps_vis_fx scfg (ahid A model) A fx' fx3 R2 (Z_to_bv 64 1180260) M2 R3 (Z_to_bv 64 1148296) MV3 model2 _ Lz2 Run3).
    intros M4 model4 MI4 SBM4 Vis4.
    destruct (sbm_fds _ _ SBM4) as (Fds4 & Fs4).
    rewrite <- Fs1, <- Fs2, <- Fs4.
    eapply rz_exit_at_lit_lz.
    + exact fetch_exitA.
    + exact is_ecall_ECALLW.
    + rewrite (sbm_halted_eq _ _ SBM4). exact Halt2.
    + left. exact T17.
    + exact (eq_trans T10 StReg).
    + exact StRng.
Qed.
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4BS : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_preBS LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
Proof.
  intros LB LK cr A M model R S st tid canz Pre MV StRng CanRng RaReg SpReg TpReg StReg CanAt Out0 OutX Fd1.
  destruct Pre as (Inv & SpLo & SpHi & SpAl & StkW & ImgClr & XBS).
  destruct XBS as (CellsBS & TidAt & TidRng & ImgNone).
  destruct Out0 as (OFlag & OSize & OEnd & OPos & OBase & OLock & OLbf & OFile & OBuf & OLines).
  destruct OutX as (XWrite & XFd & XBufP & XPrev & XNext).
  pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Inv) as Lz.
  pose proof (AS0DRVP_dpX4BS_pre.dpX4BS_pre_conc fx R MV (fun k => if Nat.eqb k 44 then tid else if Nat.eqb k 40 then canz else S)) as Seg.
  cbv beta iota delta [Nat.eqb] in Seg.
  repeat lazymatch type of Seg with
  | ?P -> _ =>
    let Pf := fresh "Pf" in
    assert (Pf : P);
    [ lazymatch goal with
      | |- getr _ _ = _ => first [exact RaReg | exact SpReg | exact TpReg | exact StReg]
      | |- AS0DRVP_dpX4BS_pre.aligned _ _ => exact SpAl
      | |- L5Defs.L5.img_clear _ _ _ => exact ImgClr
      | |- L5Defs.L5.writable _ _ (S - _) _ => apply StkW; lia
      | |- L5Defs.L5.defined _ (S - ?k) ?n =>
          intros i Ri; apply (store_ok_defined sp0 MV (S - k + i)); [lia|];
          pose proof (StkW (S - k + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
          rewrite Z.add_0_r in Wr1; exact Wr1
      | |- L5Defs.L5.writable _ _ ?a ?n =>
          first [ exact (sh_writable LB LK cr A M model a n Inv eq_refl)
                | let k := eval vm_compute in (Z.to_nat n) in
                  exact (wsg_writable MV a k ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)) ]
      | |- L5Defs.L5.u32_at _ _ 6765656 _ => exact TidAt
      | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
      | |- L5Defs.L5.u32_at _ _ 1293752 _ => exact OFlag
      | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
      | |- L5Defs.L5.u64_at _ _ 1293784 _ => exact OEnd
      | |- L5Defs.L5.u64_at _ _ 1293792 _ => exact OPos
      | |- L5Defs.L5.u64_at _ _ 1293808 _ => exact OBase
      | |- L5Defs.L5.u32_at _ _ 1293892 _ => exact OLock
      | |- L5Defs.L5.u32_at _ _ 1293896 _ => exact OLbf
      | |- L5Defs.L5.u64_at _ _ 1293824 _ => exact XWrite
      | |- L5Defs.L5.u32_at _ _ 1293872 _ => exact XFd
      | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
      | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
      | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
      | |- _ =>
          first
            [ lazymatch goal with |- ?G =>
              let w := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ _ => constr:(8)
                       | L5Defs.L5.u32_at _ _ _ _ => constr:(4)
                       | L5Defs.L5.u8_at _ _ _ _ => constr:(1)
                       end in
              let a := lazymatch G with
                       | L5Defs.L5.u64_at _ _ ?x _ => x | L5Defs.L5.u32_at _ _ ?x _ => x | L5Defs.L5.u8_at _ _ ?x _ => x end in
              let v := lazymatch G with
                       | L5Defs.L5.u64_at _ _ _ ?x => x | L5Defs.L5.u32_at _ _ _ ?x => x | L5Defs.L5.u8_at _ _ _ ?x => x end in
              first
                [ exact (proj1 (Forall_forall _ _) CellsBS (a, w, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
                | exact (ex_cell_vis LB LK cr A M model a w v Inv
                           ltac:(unfold EX_CELLS; cbn [In]; repeat first [left; reflexivity | right]))
                | unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
                  apply img_cell; [img_rd | lia | lia | intros i Ri; apply ImgNone; lia] ]
              end
            | lia ]
      end
    | specialize (Seg Pf); clear Pf ]
  end.
  destruct Seg as (fx' & R1 & MV1 & Grow1 & FrameW1 & FrameZ1 & Run1 & Kept1 & Rest1).
  assert (Q2 : getr R1 (Z_to_bv 5 (Z.of_nat 2)) = Z_to_bv 64 (S - 144)) by (decompose [and] Rest1; assumption).
  assert (Q8 : getr R1 (Z_to_bv 5 (Z.of_nat 8)) = Z_to_bv 64 0) by (decompose [and] Rest1; assumption).
  assert (Q9 : getr R1 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 1293752) by (decompose [and] Rest1; assumption).
  assert (Q10 : getr R1 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 1) by (decompose [and] Rest1; assumption).
  assert (Q11 : getr R1 (Z_to_bv 5 (Z.of_nat 11)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q12 : getr R1 (Z_to_bv 5 (Z.of_nat 12)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q17 : getr R1 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 66) by (decompose [and] Rest1; assumption).
  assert (Q18 : getr R1 (Z_to_bv 5 (Z.of_nat 18)) = Z_to_bv 64 2) by (decompose [and] Rest1; assumption).
  assert (Q19 : getr R1 (Z_to_bv 5 (Z.of_nat 19)) = Z_to_bv 64 (S - 136)) by (decompose [and] Rest1; assumption).
  assert (Q21 : getr R1 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6896960) by (decompose [and] Rest1; assumption).
  assert (Q22 : getr R1 (Z_to_bv 5 (Z.of_nat 22)) = Z_to_bv 64 6) by (decompose [and] Rest1; assumption).
  assert (K136 : L5Defs.L5.u64_at ASEGS MV1 (S - 136) 6898976) by (decompose [and] Rest1; assumption).
  assert (K128 : L5Defs.L5.u64_at ASEGS MV1 (S - 128) 6) by (decompose [and] Rest1; assumption).
  assert (K120 : L5Defs.L5.u64_at ASEGS MV1 (S - 120) 0) by (decompose [and] Rest1; assumption).
  assert (K112 : L5Defs.L5.u64_at ASEGS MV1 (S - 112) 0) by (decompose [and] Rest1; assumption).
  assert (K104 : L5Defs.L5.u64_at ASEGS MV1 (S - 104) canz) by (decompose [and] Rest1; assumption).
  assert (K96 : L5Defs.L5.u64_at ASEGS MV1 (S - 96) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22))))) by (decompose [and] Rest1; assumption).
  assert (K88 : L5Defs.L5.u64_at ASEGS MV1 (S - 88) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21))))) by (decompose [and] Rest1; assumption).
  assert (K80 : L5Defs.L5.u64_at ASEGS MV1 (S - 80) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20))))) by (decompose [and] Rest1; assumption).
  assert (K72 : L5Defs.L5.u64_at ASEGS MV1 (S - 72) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19))))) by (decompose [and] Rest1; assumption).
  assert (K64 : L5Defs.L5.u64_at ASEGS MV1 (S - 64) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18))))) by (decompose [and] Rest1; assumption).
  assert (K56 : L5Defs.L5.u64_at ASEGS MV1 (S - 56) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9))))) by (decompose [and] Rest1; assumption).
  assert (K48 : L5Defs.L5.u64_at ASEGS MV1 (S - 48) 1293752) by (decompose [and] Rest1; assumption).
  assert (K40 : L5Defs.L5.u64_at ASEGS MV1 (S - 40) 1181792) by (decompose [and] Rest1; assumption).
  assert (K32 : L5Defs.L5.u64_at ASEGS MV1 (S - 32) (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10))))) by (decompose [and] Rest1; assumption).
  assert (K24 : L5Defs.L5.u64_at ASEGS MV1 (S - 24) 1149156) by (decompose [and] Rest1; assumption).
  clear Rest1 FrameW1.
  assert (Keep1 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
            i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
            i < 2147468856 \/ 2147612852 <= i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Ri OStk O1 O2 O3 O4 O5 OSh. apply FrameZ1; [exact Ri | ..].
    all: intros InR; first [ destruct OSh; lia | destruct OStk; lia | destruct O1; lia | destruct O2; lia
                           | destruct O3; lia | destruct O4; lia | destruct O5; lia ]. }
  clear FrameZ1.
  pose proof (OLines 0 ltac:(lia)) as (Ln0a & Ln0b).
  pose proof (OLines 1 ltac:(lia)) as (Ln1a & Ln1b).
  pose proof (OLines 2 ltac:(lia)) as (Ln2a & Ln2b).
  assert (Buf0 : rdn ASEGS MV (Z_to_bv 64 SOBUF) (Z.to_nat 6) = Some (zero_lines 3)).
  { cbn [zero_lines]. change (Z.to_nat 6) with 6%nat.
    repeat (apply rdn_cons1; [unfold SOBUF; lia | assumption | ]). reflexivity. }
  apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 1149048) M R1 (Z_to_bv 64 1180248) MV1 model _ Lz Run1).
  intros M1 model1 MI1 SBM1 Vis1.
  destruct Lz as (HOff & LzCov & AWf & MInv0 & Halt0).
  destruct (same_but_materialized_frame _ _ SBM1) as (_ & _ & Lazy1 & _).
  destruct (sbm_fds _ _ SBM1) as (Fds1 & Fs1).
  assert (Halt1 : m_halted model1 = None) by (rewrite (sbm_halted_eq _ _ SBM1); exact Halt0).
  assert (PageFree : forall x, 0 <= x < 2 ^ 64 -> x < 6905856 \/ usp - 8388608 <= x -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false)
    by (intros x Rx Wx; exact (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Inv Rx Wx)).
  pose proof (@wv_loop fx' scfg (ahid A model) A HOff (m_vm_lazy model) LzCov AWf 1293752 1 ltac:(lia) (S - 136) (S - 104)
                ltac:(lia) ltac:(lia) (fun x Rx => PageFree x ltac:(lia) ltac:(lia))
                (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 6%nat) as Loop.
  unfold wv_loop_stmt in Loop.
  change (Z_to_bv 64 1180248) with (wv_pc true).
  change (W 1 (zero_lines 3)) with (map (WriteEv (Z_to_bv 64 1)) (zero_lines 3 ++ [])).
  apply (Loop true R1 M1 model1 (S - 136) 2 SOBUF 6 0 0 (zero_lines 3) []).
  - cbn. lia.
  - exact Lazy1.
  - exact MI1.
  - exact Halt1.
  - rewrite Fds1. exact Fd1.
  - unfold wv_regs. repeat split.
    all: first [exact Q17 | exact Q10 | exact Q11 | exact Q12 | exact Q9 | exact Q18 | exact Q22 | exact Q19].
  - unfold wv_iov. rewrite Vis1.
    assert (StkW1 : L5Defs.L5.writable ASEGS MV1 (S - 136) 32) by (apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1); apply StkW; lia).
    split; [lia|]. split; [lia|]. split; [right; reflexivity|].
    split; [exact K136|].
    split; [replace (S - 136 + 8) with (S - 128) by lia; exact K128|].
    split; [pose proof (StkW1 0 32%nat ltac:(lia) ltac:(lia)) as Wq; rewrite Z.add_0_r in Wq; exact Wq|].
    split.
    + unfold wv_buf. split; [unfold SOBUF; lia|]. split; [lia|]. split; [unfold SOBUF; lia|].
      split; [right; left; unfold SOBUF; lia|].
      split; [apply (rdn_tr MV MV1 _ _ _ Buf0); [unfold SOBUF; lia | unfold SOBUF; lia | intros i Ri; unfold SOBUF in Ri; apply Keep1; lia]|].
      intros x Rx. apply PageFree; unfold SOBUF in Rx; lia.
    + split; [intro Bad; lia|].
      intros _. split; [replace (S - 136 + 16) with (S - 120) by lia; exact K120|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; exact K112|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
      split; [reflexivity|]. intros x Rx. lia.
  - lia.
  - rewrite Vis1. apply (rdn_tr MV MV1 _ _ _ XFd); [lia | lia | intros i Ri; apply Keep1; lia].
  - intros R2 M2 model2 MI2 SBM2 KeepR2 FrameF2 FrameV2 GrowF2 GrowV2.
    set (MV2 := mrestrict (ahid A model) M2).
    assert (Grow12 : mem_grows MV1 MV2) by (rewrite <- Vis1; exact GrowV2).
    assert (Frame12 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 136 <= a < S - 104) -> MV2 (Z_to_bv 64 a) = MV1 (Z_to_bv 64 a))
      by (rewrite <- Vis1; exact FrameV2).
    assert (Keep02 : forall i, 0 <= i < 2 ^ 64 -> i < S - 320 \/ S <= i -> i < 1295744 \/ 1295752 <= i -> i < 1295824 \/ 1295825 <= i ->
              i < 1299696 \/ 1299704 <= i -> i < 6896976 \/ 6897000 <= i -> i < 6897520 \/ 6897524 <= i ->
              i < 2147468856 \/ 2147612852 <= i -> MV2 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Ri OStk O1 O2 O3 O4 O5 OSh. rewrite (Frame12 i Ri ltac:(lia)). exact (Keep1 i Ri OStk O1 O2 O3 O4 O5 OSh). }
    destruct (same_but_materialized_frame _ _ SBM2) as (_ & _ & Lazy2 & _).
    destruct (sbm_fds _ _ SBM2) as (Fds2 & Fs2).
    assert (Halt2 : m_halted model2 = None) by (rewrite (sbm_halted_eq _ _ SBM2); exact Halt1).
    assert (Lz2 : lzinv ASEGS (ahid A model) A model2) by (split; [exact HOff|]; split; [rewrite Lazy2, Lazy1; exact LzCov|]; split; [exact AWf|]; split; [exact MI2 | exact Halt2]).
    pose proof (Ba0DrvP_dpXd_4_b.AS0DRVP_dpXd_4.dpXd_4_conc fx' R2 MV2
      (fun k => if Nat.eqb k 2 then S - 144
                else if Nat.eqb k 9 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
                else if Nat.eqb k 10 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 18 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 19 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 20 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 21 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
                else if Nat.eqb k 22 then bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
                else if Nat.eqb k 40 then canz
                else if Nat.eqb k 110 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
                else if Nat.eqb k 118 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
                else if Nat.eqb k 119 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
                else if Nat.eqb k 120 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
                else if Nat.eqb k 122 then bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
                else 0)) as Seg2.
    cbv beta iota delta [Nat.eqb] in Seg2.
    repeat lazymatch type of Seg2 with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- 0 <= bv_unsigned ?w < 2 ^ 64 => exact (u64_range w)
        | |- getr R2 _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
        | |- getr R2 (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
            refine (eq_trans (KeepR2 (Z_to_bv 5 (Z.of_nat r)) _) _);
            [ unfold WV_KEEP; cbn [In]; repeat first [left; apply bv_eq; reflexivity | right]
            | first [exact Q2 | exact Q8 | exact Q9 | exact Q21] ]
        | |- Ba0DrvP_dpXd_4_b.AS0DRVP_dpXd_4.aligned _ _ => unfold Ba0DrvP_dpXd_4_b.AS0DRVP_dpXd_4.aligned; rewrite Zminus_mod, SpAl; reflexivity
        | |- L5Defs.L5.img_clear _ _ _ =>
            intros i Ri; rewrite (Keep02 i ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
            exact (ImgClr i Ri)
        | |- L5Defs.L5.writable _ _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            apply StkW; lia
        | |- L5Defs.L5.defined _ (S - 144 - 16) 16 =>
            apply (L5Defs.L5.defined_grows MV1 MV2 _ _ Grow12); apply (L5Defs.L5.defined_grows MV MV1 _ _ Grow1);
            intros i Ri; apply (store_ok_defined sp0 MV (S - 144 - 16 + i)); [lia|];
            pose proof (StkW (S - 144 - 16 + i) 1 ltac:(lia) ltac:(lia) 0 1%nat ltac:(lia) ltac:(lia)) as Wr1;
            rewrite Z.add_0_r in Wr1; exact Wr1
        | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows _ MV1 MV2 _ _ Grow12); apply (L5Defs.L5.writable_grows _ MV MV1 _ _ Grow1);
            intros d k Dlo Dhi; exact (OFile a n ltac:(lia) ltac:(lia) d k Dlo Dhi)
        | |- L5Defs.L5.u64_at _ _ (S - 144 + ?off) _ =>
            let k := eval vm_compute in (144 - off) in
            replace (S - 144 + off) with (S - k) by lia;
            unfold L5Defs.L5.u64_at; apply (rdn_tr MV1 MV2); [assumption | lia | lia | intros i Ri; apply Frame12; lia]
        | |- L5Defs.L5.u64_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u64_at ASEGS MV a v);
            [ lazymatch goal with
              | |- L5Defs.L5.u64_at _ _ 1293840 _ => exact XBufP
              | |- L5Defs.L5.u64_at _ _ 1293848 _ => exact OSize
              | |- L5Defs.L5.u64_at _ _ 6896960 _ => exact CanAt
              | |- L5Defs.L5.u64_at _ _ 1293760 _ => exact XPrev
              | |- L5Defs.L5.u64_at _ _ 1293768 _ => exact XNext
              | |- _ => exact (proj1 (Forall_forall _ _) CellsBS (a, 8, v)
                           ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]))
              end
            | unfold L5Defs.L5.u64_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia] ]
        | |- L5Defs.L5.u32_at _ _ ?a ?v =>
            assert (Src : L5Defs.L5.u32_at ASEGS MV a v)
              by exact (proj1 (Forall_forall _ _) CellsBS (a, 4, v)
                          ltac:(unfold XC_CELLS_BS; cbn [In]; repeat first [left; reflexivity | right]));
            unfold L5Defs.L5.u32_at; apply (rdn_tr MV MV2 _ _ _ Src); [lia | lia | intros i Ri; apply Keep02; lia]
        | |- _ => lia
        end
      | specialize (Seg2 Pf); clear Pf ]
    end.
    destruct Seg2 as (fx3 & R3 & MV3 & Grow3 & FrameW3 & FrameZ3 & Run3 & Kept3 & Rest3).
    assert (T17 : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94) by (decompose [and] Rest3; assumption).
    assert (T10 : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = Z_to_bv 64 (bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))))
      by (decompose [and] Rest3; assumption).
    rewrite Z_to_bv_bv_unsigned in T10.
    clear Rest3 FrameW3 FrameZ3.
    apply (msteps_vis_fx scfg (ahid A model) A fx' fx3 R2 (Z_to_bv 64 1180260) M2 R3 (Z_to_bv 64 1148296) MV3 model2 _ Lz2 Run3).
    intros M4 model4 MI4 SBM4 Vis4.
    destruct (sbm_fds _ _ SBM4) as (Fds4 & Fs4).
    rewrite <- Fs1, <- Fs2, <- Fs4.
    eapply rz_exit_at_lit_lz.
    + exact fetch_exitA.
    + exact is_ecall_ECALLW.
    + rewrite (sbm_halted_eq _ _ SBM4). exact Halt2.
    + left. exact T17.
    + exact (eq_trans T10 StReg).
    + exact StRng.
Qed.
End Exit.
End FPX_1.
