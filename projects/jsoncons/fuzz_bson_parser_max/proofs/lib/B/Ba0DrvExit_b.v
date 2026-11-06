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
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import Ba0DrvP_dpX_b Ba0DrvP_dpX2_pre_b Ba0DrvP_dpX3_pre_b Ba0DrvP_dpX4_pre_b Ba0DrvP_dpXd_2_b Ba0DrvP_dpXd_3_b Ba0DrvP_dpXd_4_b Ba0DrvP_dpXe_b.
  From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0ExitCells_b.
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

  (* [comment removed for export] *)
  #[using="scfg L C IL HIok Hsp DL Hex"] Lemma ex_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) EX_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aiob_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hex _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x696000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.
  #[using="scfg L C IL HIok Hsp DL"] Lemma ax_cells_vis : forall LB LK cr A M (model : Model) (ax : axv), dinvA LB LK cr A M model -> atexit_cellsA M ax ->
    atexit_cellsA (mrestrict (ahid A model) M) ax.
  Proof.
    intros LB LK cr A M model ax D H. unfold atexit_cellsA in *. rewrite Forall_forall in *. intros c Hc.
    pose proof (ax_cells_in ax c Hc) as (BB & B3). specialize (H c Hc). unfold ax_cell in *.
    rewrite rdn_mrestrict_eq; [exact H|].
    intros k Hk. unfold woff. unfold AXLO, AXHI, SSLO, SSHI in *.
    rewrite (u64_lit (fst (fst c))) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="scfg L IL ICok ILY Hsp DL"] Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model ->
    ((2147468856 <=? a) && (a + n <=? 2147469104) || (2147612664 <=? a) && (a + n <=? 2147612852)) = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
  Proof.
    intros LB LK cr A M model a n Dv Win.
    pose proof (di_inv _ _ _ _ _ _ _ _ _ _ Dv) as Inv.
    pose proof (aic_img_shadow _ _ _ _ _ ICok LB [] LK cr A M (vml_of model) Inv) as ImSh.
    rewrite (dla_img_lo _ _ _ _ DL), (dla_img_hi _ _ _ _ DL), (aicl_poison _ ILY) in ImSh.
    destruct (ImSh 145792 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(constructor; [cbn; lia | constructor; [cbn; lia | constructor]])) as (_ & AlLo).
    destruct (ImSh 1295744 8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(constructor; [cbn; lia | constructor; [cbn; lia | constructor]])) as (_ & AlHi).
    assert (PgLo : page_allowedb A (page_base (Z_to_bv 64 2147469104)) = true)
      by (apply AlLo; unfold in_shadow_of; split; apply Z.leb_le; vm_compute; reflexivity).
    assert (PgHi : page_allowedb A (page_base (Z_to_bv 64 2147612848)) = true)
      by (apply AlHi; unfold in_shadow_of; split; apply Z.leb_le; vm_compute; reflexivity).
    assert (SamePg : forall q x y, 0 <= q -> q * 4096 <= x < q * 4096 + 4096 -> q * 4096 <= y < q * 4096 + 4096 -> x < 2 ^ 64 -> y < 2 ^ 64 ->
              page_base (Z_to_bv 64 x) = page_base (Z_to_bv 64 y)).
    { intros q x y Q0 Rx Ry Bx By. unfold page_base, page_base_of, page_size. rewrite !u64_lit by lia.
      rewrite <- (Z.div_unique x 4096 q (x - q * 4096)) by lia. rewrite <- (Z.div_unique y 4096 q (y - q * 4096)) by lia. reflexivity. }
    pose proof (aic_shadow_defined _ _ _ _ _ ICok LB [] LK cr A M (vml_of model) Inv) as ShDef.
    assert (VisX : forall x y, page_base (Z_to_bv 64 x) = page_base (Z_to_bv 64 y) -> page_allowedb A (page_base (Z_to_bv 64 y)) = true ->
              2147450880 <= x < 2415882240 -> mrestrict (ahid A model) M (Z_to_bv 64 x) <> None).
    { intros x y Pxy Ay Rx. unfold mrestrict, ahid, mkH. rewrite Pxy, Ay. cbn [negb]. rewrite andb_false_r.
      apply ShDef. left. unfold LOWSH_LO, LOWSH_HI. exact Rx. }
    destruct (orb_prop _ _ Win) as [Wb|Wb]; apply andb_prop in Wb as (Wa & Wn); apply Z.leb_le in Wa, Wn;
      apply L5Core.L5C.writable_of_defined; try lia; intros i Ri.
    - apply (VisX _ 2147469104); [apply (SamePg 524284); lia | exact PgLo | lia].
    - apply (VisX _ 2147612848); [apply (SamePg 524319); lia | exact PgHi | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="sp0 Hsp M0"] Lemma wsg_writable : forall (MV : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
    L5Defs.L5.writable ASEGS MV a (Z.of_nat n).
  Proof.
    intros MV a n W Ha Hn d k Hd Hk.
    apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) n k a (a + Z.of_nat n)); first [exact W | reflexivity | lia | rewrite u64_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Definition exit_pre (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    dinvA LB LK cr A M model
    /\ usp - 4096 <= S
    /\ S <= usp
    /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n)
    /\ L5Defs.L5.img_clear (mrestrict (ahid A model) M) 65536 1282048
    /\ exitA tid (mrestrict (ahid A model) M).
  Definition exit_preE (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    dinvA LB LK cr A M model
    /\ usp - 4096 <= S
    /\ S <= usp
    /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n)
    /\ L5Defs.L5.img_clear (mrestrict (ahid A model) M) 65536 1282048
    /\ exitE tid (mrestrict (ahid A model) M).

  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid Pre MV Rst G1 G2 G4 G10 SO SX.
    destruct Pre as (Dv & SLo & SHi & S16 & Wstk & Img & (Cells & Tid & TidR & ImgNone)).
    destruct SO as (So1 & So2 & So3 & So4 & So5 & So6 & So7 & SoW1 & SoW2 & SoLn).
    destruct SX as (Sx1 & Sx2 & Sx3 & Sx4 & Sx5).
    pose (V := fun j : nat => match j with 44%nat => tid | _ => S end).
    pose proof (AS0DRVP_dpX.dpX_conc fx R MV V) as Run. unfold V in Run. cbv beta iota in Run. clear V.
    repeat lazymatch type of Run with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | |- _ <= _ < _ => lia
        | |- _ <= _ <= _ => lia
        | |- AS0DRVP_dpX.aligned _ _ => exact S16
        | |- L5Defs.L5.img_clear _ _ _ => exact Img
        | |- L5Defs.L5.defined _ ?a ?n => intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
        | |- L5Defs.L5.writable _ _ ?a ?n =>
          let hi := eval vm_compute in (2147468856 <=? a) in
          lazymatch hi with
          | true => apply (sh_writable LB LK cr A M model a n Dv); vm_compute; reflexivity
          | false => let k := eval vm_compute in (Z.to_nat n) in apply (wsg_writable MV a k); [vm_compute; reflexivity | lia | lia]
          | _ => apply Wstk; lia
          end
        | |- _ =>
          unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
          lazymatch goal with
          | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
            first
              [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
              | let z := eval vm_compute in (Z.of_nat n) in
                let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                first
                  [ exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right]))
                  | exact (ex_cell_vis LB LK cr A M model a z v Dv ltac:(cbn [In EX_CELLS]; repeat first [left; reflexivity | right])) ]
              | apply (img_cell MV a n); [img_rd | lia | cbn; lia | intros i Ri; apply ImgNone; cbn in Ri; lia] ]
          end
        end
      | specialize (Run Pf); clear Pf ]
    end.
    lazymatch type of Run with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
    destruct Run as (fx' & R' & M' & Grow & FrW & FrZ & Steps & Keep & Outs).
    assert (A7 : getr R' (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94).
    { let rec dig T := lazymatch type of T with
        | getr _ (Z_to_bv 5 (Z.of_nat 17)) = _ /\ _ => exact (proj1 T)
        | _ /\ _ => dig constr:(proj2 T)
        end in dig Outs. }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 0x118878) M R' (Z_to_bv 64 0x118588) M' model _
             (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dv) Steps).
    intros M1 model1 MI1 SB1 VE1.
    rewrite <- (proj2 (sbm_fds model model1 SB1)).
    apply (rz_exit_at_lit_lz ASEGS scfg R' _ M1 _ model1 ECALLW st fetch_exitA is_ecall_ECALLW); [| left; exact A7 | | exact Rst].
    - rewrite (sbm_halted_eq _ _ SB1). exact (di_halt _ _ _ _ _ _ _ _ _ _ Dv).
    - exact (eq_trans (Keep 10%nat ltac:(cbn [In AS0DRVP_dpX.KS_dpX]; repeat first [left; reflexivity | right])) G10).
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 1293892) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 1293792) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1293808) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1293760) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 1293768) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preE LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid Pre MV Rst G2 G4 G10 SP.
    destruct Pre as (Dv & SLo & SHi & S16 & Wstk & Img & (Cells & Tid & TidR & ImgNone)).
    destruct SP as (P1 & P2 & P3 & P4 & P5).
    pose (V := fun j : nat => match j with 44%nat => tid | _ => S end).
    pose proof (AS0DRVP_dpXe.dpXe_conc fx R MV V) as Run. unfold V in Run. cbv beta iota in Run. clear V.
    repeat lazymatch type of Run with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- getr _ _ = _ => first [exact G2 | exact G4]
        | |- _ <= _ < _ => lia
        | |- _ <= _ <= _ => lia
        | |- AS0DRVP_dpXe.aligned _ _ => exact S16
        | |- L5Defs.L5.img_clear _ _ _ => exact Img
        | |- L5Defs.L5.defined _ ?a ?n => intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
        | |- L5Defs.L5.writable _ _ ?a ?n =>
          let hi := eval vm_compute in (2147468856 <=? a) in
          lazymatch hi with
          | true => apply (sh_writable LB LK cr A M model a n Dv); vm_compute; reflexivity
          | false => let k := eval vm_compute in (Z.to_nat n) in apply (wsg_writable MV a k); [vm_compute; reflexivity | lia | lia]
          | _ => apply Wstk; lia
          end
        | |- _ =>
          unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
          lazymatch goal with
          | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
            first
              [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
              | let z := eval vm_compute in (Z.of_nat n) in
                let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                first
                  [ exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS_E]; repeat first [left; reflexivity | right]))
                  | exact (ex_cell_vis LB LK cr A M model a z v Dv ltac:(cbn [In EX_CELLS]; repeat first [left; reflexivity | right])) ]
              | apply (img_cell MV a n); [img_rd | lia | cbn; lia | intros i Ri; apply ImgNone; cbn in Ri; lia] ]
          end
        end
      | specialize (Run Pf); clear Pf ]
    end.
    lazymatch type of Run with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
    destruct Run as (fx' & R' & M' & Grow & FrW & FrZ & Steps & Keep & Outs).
    assert (A7 : getr R' (Z_to_bv 5 (Z.of_nat 17)) = Z_to_bv 64 94).
    { let rec dig T := lazymatch type of T with
        | getr _ (Z_to_bv 5 (Z.of_nat 17)) = _ /\ _ => exact (proj1 T)
        | _ /\ _ => dig constr:(proj2 T)
        end in dig Outs. }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx' R (Z_to_bv 64 0x118878) M R' (Z_to_bv 64 0x118588) M' model _
             (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dv) Steps).
    intros M1 model1 MI1 SB1 VE1.
    rewrite <- (proj2 (sbm_fds model model1 SB1)).
    apply (rz_exit_at_lit_lz ASEGS scfg R' _ M1 _ model1 ECALLW st fetch_exitA is_ecall_ECALLW); [| left; exact A7 | | exact Rst].
    - rewrite (sbm_halted_eq _ _ SB1). exact (di_halt _ _ _ _ _ _ _ _ _ _ Dv).
    - exact (eq_trans (Keep 10%nat ltac:(cbn [In AS0DRVP_dpXe.KS_dpXe]; repeat first [left; reflexivity | right])) G10).
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz Pre MV Rst Rcz G1 G2 G4 G10 Cz SO SX FD1.
    destruct Pre as (Dv & SLo & SHi & S16 & Wstk & Img & (Cells & Tid & TidR & ImgNone)).
    destruct SO as (So1 & So2 & So3 & So4 & So5 & So6 & So7 & SoW1 & SoW2 & SoLn).
    destruct SX as (Sx1 & Sx2 & Sx3 & Sx4 & Sx5).
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dv) as LZ.
    pose (V := fun j : nat => match j with 40%nat => canz | 44%nat => tid | _ => S end).
    pose proof (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V) as Run. unfold V in Run. cbv beta iota in Run. clear V.
    repeat lazymatch type of Run with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | |- _ <= _ < _ => lia
        | |- _ <= _ <= _ => lia
        | |- AS0DRVP_dpX2_pre.aligned _ _ => exact S16
        | |- L5Defs.L5.img_clear _ _ _ => exact Img
        | |- L5Defs.L5.defined _ ?a ?n => intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
        | |- L5Defs.L5.writable _ _ ?a ?n =>
          let hi := eval vm_compute in (2147468856 <=? a) in
          lazymatch hi with
          | true => apply (sh_writable LB LK cr A M model a n Dv); vm_compute; reflexivity
          | false => let k := eval vm_compute in (Z.to_nat n) in apply (wsg_writable MV a k); [vm_compute; reflexivity | lia | lia]
          | _ => apply Wstk; lia
          end
        | |- _ =>
          unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
          lazymatch goal with
          | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
            first
              [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
              | let z := eval vm_compute in (Z.of_nat n) in
                let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                first
                  [ exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right]))
                  | exact (ex_cell_vis LB LK cr A M model a z v Dv ltac:(cbn [In EX_CELLS]; repeat first [left; reflexivity | right])) ]
              | apply (img_cell MV a n); [img_rd | lia | cbn; lia | intros i Ri; apply ImgNone; cbn in Ri; lia] ]
          end
        end
      | specialize (Run Pf); clear Pf ]
    end.
    lazymatch type of Run with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
    destruct Run as (fx1 & R1 & M1' & Grow1 & FrW1 & FrZ1 & Steps1 & Keep1 & Outs1).
    repeat lazymatch type of Outs1 with _ /\ _ => let o := fresh "Oc" in destruct Outs1 as [o Outs1] end.
    assert (Safe1 : forall i, 0 <= i < 1295744 \/ 6896960 <= i < 6896976 \/ 6898976 <= i < 6900000 ->
                    M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Zi; apply FrZ1; lia).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) M1' model _ LZ Steps1).
    intros M1 model1 MI1 SB1 VE1.
    pose proof LZ as (HoS & Lcov & Awf & _ & _).
    pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 LZ MI1 SB1) as LZ1.
    change (W 1 (zero_lines 1)) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48; Z_to_bv 8 10] ++ [])).
    apply (@wv_loop fx1 scfg (ahid A model) A HoS (m_vm_lazy model) Lcov Awf 1293752 1 ltac:(lia) (S - 136) (S - 104) ltac:(lia) ltac:(lia)
             (fun x Rx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv ltac:(lia) ltac:(right; lia))
             (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 2%nat true R1 M1 model1 (S - 136) 2 6898976 2 0 0 [Z_to_bv 8 48; Z_to_bv 8 10] []).
    - apply Nat.le_refl.
    - exact (sbm_lazy_eq _ _ SB1).
    - exact MI1.
    - exact (proj2 (proj2 (proj2 (proj2 LZ1)))).
    - rewrite (sbm_fds' _ _ SB1). exact FD1.
    - unfold wv_regs. repeat split; match goal with Oc : getr R1 _ = _ |- _ => exact Oc end.
    - rewrite VE1. unfold wv_iov.
      pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (Wstk (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(cbn; lia)) as W32.
      rewrite Z.add_0_r in W32.
      split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 136) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 8) with (S - 128) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 128) _ |- _ => exact Oc end|].
      split; [exact W32|].
      split.
      { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; lia|]. split.
        - repeat (apply rdn_cons1; [lia | |];
            [ lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ =>
                let off := eval vm_compute in (a - 6898976) in
                let i := eval vm_compute in (off / 2) in
                let p := eval vm_compute in (off mod 2) in
                apply (rdn_tr MV M1' a 1);
                [ lazymatch p with 0 => exact (proj1 (SoLn i ltac:(lia))) | _ => exact (proj2 (SoLn i ltac:(lia))) end
                | lia | cbn; lia | intros x Rx; apply Safe1; cbn in Rx; lia ]
              end | ]).
          reflexivity.
        - intros x Rx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv); lia. }
      split; [intros C1; discriminate C1|].
      intros _.
      split; [replace (S - 136 + 16) with (S - 120) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 120) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 112) _ |- _ => exact Oc end|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity | intros x Rx; lia].
    - lia.
    - rewrite VE1. apply (rdn_tr MV M1' 1293872 4); [exact Sx2 | lia | cbn; lia | intros i Ri; apply Safe1; cbn in Ri; lia].
    - intros R2 M2 model2 MI2 SB2 KR2 FrM2 FrV2 GrM2 GrV2.
      rewrite VE1 in FrV2, GrV2.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 LZ1 MI2 SB2) as LZ2.
      pose proof (mem_grows_trans _ _ _ Grow1 GrV2) as GrowV.
      pose (Vd := fun j : nat => match j with
        | 2%nat => S - 144
        | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
        | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
        | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
        | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
        | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
        | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
        | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
        | 40%nat => canz
        | 110%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
        | 118%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
        | 119%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
        | 120%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
        | 122%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
        | _ => 0 end).
      pose proof (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R2 (mrestrict (ahid A model) M2) Vd) as Run2. unfold Vd in Run2. cbv beta iota in Run2. clear Vd.
      repeat lazymatch type of Run2 with
      | ?P -> _ =>
        let Pf := fresh "Pf" in
        assert (Pf : P);
        [ lazymatch goal with
          | |- 0 <= bv_unsigned _ < _ => apply u64_range
          | |- _ <= _ < _ => lia
          | |- _ <= _ <= _ => lia
          | |- getr _ _ = _ =>
            first
              [ rewrite Z_to_bv_bv_unsigned; reflexivity
              | etransitivity; [apply KR2; cbn [In WV_KEEP]; repeat first [left; apply bv_eq; reflexivity | right] |];
                match goal with Oc : getr R1 _ = _ |- _ => exact Oc end ]
          | |- AS0DRVP_dpXd_2.aligned _ _ => unfold AS0DRVP_dpXd_2.aligned; rewrite Zminus_mod, S16; reflexivity
          | |- L5Defs.L5.img_clear _ _ _ => intros i Ri; rewrite FrV2, Safe1 by lia; exact (Img i Ri)
          | |- L5Defs.L5.defined _ ?a ?n =>
            apply (L5Defs.L5.defined_grows MV _ _ _ GrowV); intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
          | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ GrowV); first [apply Wstk; lia | intros d k Rd Rk; apply (SoW1 a n); lia]
          | |- _ =>
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            lazymatch goal with
            | |- rdn _ _ (Z_to_bv 64 (S - 144 + ?k)) _ = _ =>
              let k' := eval vm_compute in (144 - k) in
              replace (S - 144 + k) with (S - k') by lia;
              apply rdn_tr with (M := M1');
              [ match goal with Oc : L5Defs.L5.u64_at _ M1' (S - k') _ |- _ => exact Oc end
              | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | intros i Ri; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ri; apply FrV2; lia ]
            | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
              apply rdn_tr with (M := M1'); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply FrV2; lia];
              apply rdn_tr with (M := MV); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply Safe1; lia];
              first
                [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
                | let z := eval vm_compute in (Z.of_nat n) in
                  let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                  exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right])) ]
            end
          end
        | specialize (Run2 Pf); clear Pf ]
      end.
      lazymatch type of Run2 with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
      destruct Run2 as (fx3 & R3 & M3' & Grow3 & FrW3 & FrZ3 & (Steps3 & Keep3 & Outs3)).
      repeat lazymatch type of Outs3 with _ /\ _ => let o := fresh "Od" in destruct Outs3 as [o Outs3] end.
      apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 (Z_to_bv 64 0x120264) M2 R3 (Z_to_bv 64 0x118588) M3' model2 _ LZ2 Steps3).
      intros M3 model3 MI3 SB3 VE3.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 LZ2 MI3 SB3) as LZ3.
      rewrite <- (proj2 (sbm_fds _ _ SB1)), <- (proj2 (sbm_fds _ _ SB2)), <- (proj2 (sbm_fds _ _ SB3)).
      apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW); [| left | | exact Rst].
      + exact (proj2 (proj2 (proj2 (proj2 LZ3)))).
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = _ |- _ => exact Od end.
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = _ |- _ => rewrite Z_to_bv_bv_unsigned in Od; exact (eq_trans Od G10) end.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz Pre MV Rst Rcz G1 G2 G4 G10 Cz SO SX FD1.
    destruct Pre as (Dv & SLo & SHi & S16 & Wstk & Img & (Cells & Tid & TidR & ImgNone)).
    destruct SO as (So1 & So2 & So3 & So4 & So5 & So6 & So7 & SoW1 & SoW2 & SoLn).
    destruct SX as (Sx1 & Sx2 & Sx3 & Sx4 & Sx5).
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dv) as LZ.
    pose (V := fun j : nat => match j with 40%nat => canz | 44%nat => tid | _ => S end).
    pose proof (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V) as Run. unfold V in Run. cbv beta iota in Run. clear V.
    repeat lazymatch type of Run with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | |- _ <= _ < _ => lia
        | |- _ <= _ <= _ => lia
        | |- AS0DRVP_dpX3_pre.aligned _ _ => exact S16
        | |- L5Defs.L5.img_clear _ _ _ => exact Img
        | |- L5Defs.L5.defined _ ?a ?n => intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
        | |- L5Defs.L5.writable _ _ ?a ?n =>
          let hi := eval vm_compute in (2147468856 <=? a) in
          lazymatch hi with
          | true => apply (sh_writable LB LK cr A M model a n Dv); vm_compute; reflexivity
          | false => let k := eval vm_compute in (Z.to_nat n) in apply (wsg_writable MV a k); [vm_compute; reflexivity | lia | lia]
          | _ => apply Wstk; lia
          end
        | |- _ =>
          unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
          lazymatch goal with
          | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
            first
              [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
              | let z := eval vm_compute in (Z.of_nat n) in
                let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                first
                  [ exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right]))
                  | exact (ex_cell_vis LB LK cr A M model a z v Dv ltac:(cbn [In EX_CELLS]; repeat first [left; reflexivity | right])) ]
              | apply (img_cell MV a n); [img_rd | lia | cbn; lia | intros i Ri; apply ImgNone; cbn in Ri; lia] ]
          end
        end
      | specialize (Run Pf); clear Pf ]
    end.
    lazymatch type of Run with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
    destruct Run as (fx1 & R1 & M1' & Grow1 & FrW1 & FrZ1 & Steps1 & Keep1 & Outs1).
    repeat lazymatch type of Outs1 with _ /\ _ => let o := fresh "Oc" in destruct Outs1 as [o Outs1] end.
    assert (Safe1 : forall i, 0 <= i < 1295744 \/ 6896960 <= i < 6896976 \/ 6898976 <= i < 6900000 ->
                    M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Zi; apply FrZ1; lia).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) M1' model _ LZ Steps1).
    intros M1 model1 MI1 SB1 VE1.
    pose proof LZ as (HoS & Lcov & Awf & _ & _).
    pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 LZ MI1 SB1) as LZ1.
    change (W 1 (zero_lines 2)) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ++ [])).
    apply (@wv_loop fx1 scfg (ahid A model) A HoS (m_vm_lazy model) Lcov Awf 1293752 1 ltac:(lia) (S - 136) (S - 104) ltac:(lia) ltac:(lia)
             (fun x Rx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv ltac:(lia) ltac:(right; lia))
             (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 4%nat true R1 M1 model1 (S - 136) 2 6898976 4 0 0 [Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] []).
    - apply Nat.le_refl.
    - exact (sbm_lazy_eq _ _ SB1).
    - exact MI1.
    - exact (proj2 (proj2 (proj2 (proj2 LZ1)))).
    - rewrite (sbm_fds' _ _ SB1). exact FD1.
    - unfold wv_regs. repeat split; match goal with Oc : getr R1 _ = _ |- _ => exact Oc end.
    - rewrite VE1. unfold wv_iov.
      pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (Wstk (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(cbn; lia)) as W32.
      rewrite Z.add_0_r in W32.
      split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 136) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 8) with (S - 128) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 128) _ |- _ => exact Oc end|].
      split; [exact W32|].
      split.
      { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; lia|]. split.
        - repeat (apply rdn_cons1; [lia | |];
            [ lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ =>
                let off := eval vm_compute in (a - 6898976) in
                let i := eval vm_compute in (off / 2) in
                let p := eval vm_compute in (off mod 2) in
                apply (rdn_tr MV M1' a 1);
                [ lazymatch p with 0 => exact (proj1 (SoLn i ltac:(lia))) | _ => exact (proj2 (SoLn i ltac:(lia))) end
                | lia | cbn; lia | intros x Rx; apply Safe1; cbn in Rx; lia ]
              end | ]).
          reflexivity.
        - intros x Rx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv); lia. }
      split; [intros C1; discriminate C1|].
      intros _.
      split; [replace (S - 136 + 16) with (S - 120) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 120) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 112) _ |- _ => exact Oc end|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity | intros x Rx; lia].
    - lia.
    - rewrite VE1. apply (rdn_tr MV M1' 1293872 4); [exact Sx2 | lia | cbn; lia | intros i Ri; apply Safe1; cbn in Ri; lia].
    - intros R2 M2 model2 MI2 SB2 KR2 FrM2 FrV2 GrM2 GrV2.
      rewrite VE1 in FrV2, GrV2.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 LZ1 MI2 SB2) as LZ2.
      pose proof (mem_grows_trans _ _ _ Grow1 GrV2) as GrowV.
      pose (Vd := fun j : nat => match j with
        | 2%nat => S - 144
        | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
        | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
        | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
        | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
        | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
        | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
        | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
        | 40%nat => canz
        | 110%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
        | 118%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
        | 119%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
        | 120%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
        | 122%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
        | _ => 0 end).
      pose proof (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R2 (mrestrict (ahid A model) M2) Vd) as Run2. unfold Vd in Run2. cbv beta iota in Run2. clear Vd.
      repeat lazymatch type of Run2 with
      | ?P -> _ =>
        let Pf := fresh "Pf" in
        assert (Pf : P);
        [ lazymatch goal with
          | |- 0 <= bv_unsigned _ < _ => apply u64_range
          | |- _ <= _ < _ => lia
          | |- _ <= _ <= _ => lia
          | |- getr _ _ = _ =>
            first
              [ rewrite Z_to_bv_bv_unsigned; reflexivity
              | etransitivity; [apply KR2; cbn [In WV_KEEP]; repeat first [left; apply bv_eq; reflexivity | right] |];
                match goal with Oc : getr R1 _ = _ |- _ => exact Oc end ]
          | |- AS0DRVP_dpXd_3.aligned _ _ => unfold AS0DRVP_dpXd_3.aligned; rewrite Zminus_mod, S16; reflexivity
          | |- L5Defs.L5.img_clear _ _ _ => intros i Ri; rewrite FrV2, Safe1 by lia; exact (Img i Ri)
          | |- L5Defs.L5.defined _ ?a ?n =>
            apply (L5Defs.L5.defined_grows MV _ _ _ GrowV); intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
          | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ GrowV); first [apply Wstk; lia | intros d k Rd Rk; apply (SoW1 a n); lia]
          | |- _ =>
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            lazymatch goal with
            | |- rdn _ _ (Z_to_bv 64 (S - 144 + ?k)) _ = _ =>
              let k' := eval vm_compute in (144 - k) in
              replace (S - 144 + k) with (S - k') by lia;
              apply rdn_tr with (M := M1');
              [ match goal with Oc : L5Defs.L5.u64_at _ M1' (S - k') _ |- _ => exact Oc end
              | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | intros i Ri; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ri; apply FrV2; lia ]
            | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
              apply rdn_tr with (M := M1'); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply FrV2; lia];
              apply rdn_tr with (M := MV); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply Safe1; lia];
              first
                [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
                | let z := eval vm_compute in (Z.of_nat n) in
                  let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                  exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right])) ]
            end
          end
        | specialize (Run2 Pf); clear Pf ]
      end.
      lazymatch type of Run2 with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
      destruct Run2 as (fx3 & R3 & M3' & Grow3 & FrW3 & FrZ3 & (Steps3 & Keep3 & Outs3)).
      repeat lazymatch type of Outs3 with _ /\ _ => let o := fresh "Od" in destruct Outs3 as [o Outs3] end.
      apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 (Z_to_bv 64 0x120264) M2 R3 (Z_to_bv 64 0x118588) M3' model2 _ LZ2 Steps3).
      intros M3 model3 MI3 SB3 VE3.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 LZ2 MI3 SB3) as LZ3.
      rewrite <- (proj2 (sbm_fds _ _ SB1)), <- (proj2 (sbm_fds _ _ SB2)), <- (proj2 (sbm_fds _ _ SB3)).
      apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW); [| left | | exact Rst].
      + exact (proj2 (proj2 (proj2 (proj2 LZ3)))).
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = _ |- _ => exact Od end.
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = _ |- _ => rewrite Z_to_bv_bv_unsigned in Od; exact (eq_trans Od G10) end.
  Qed.


  #[using="L C IL HIok ICok ILY Hsp DL Hex"] Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 1147060 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6765824 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6896960) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x118878) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz Pre MV Rst Rcz G1 G2 G4 G10 Cz SO SX FD1.
    destruct Pre as (Dv & SLo & SHi & S16 & Wstk & Img & (Cells & Tid & TidR & ImgNone)).
    destruct SO as (So1 & So2 & So3 & So4 & So5 & So6 & So7 & SoW1 & SoW2 & SoLn).
    destruct SX as (Sx1 & Sx2 & Sx3 & Sx4 & Sx5).
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 LB LK cr A M model Dv) as LZ.
    pose (V := fun j : nat => match j with 40%nat => canz | 44%nat => tid | _ => S end).
    pose proof (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V) as Run. unfold V in Run. cbv beta iota in Run. clear V.
    repeat lazymatch type of Run with
    | ?P -> _ =>
      let Pf := fresh "Pf" in
      assert (Pf : P);
      [ lazymatch goal with
        | |- getr _ _ = _ => first [exact G1 | exact G2 | exact G4]
        | |- _ <= _ < _ => lia
        | |- _ <= _ <= _ => lia
        | |- AS0DRVP_dpX4_pre.aligned _ _ => exact S16
        | |- L5Defs.L5.img_clear _ _ _ => exact Img
        | |- L5Defs.L5.defined _ ?a ?n => intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
        | |- L5Defs.L5.writable _ _ ?a ?n =>
          let hi := eval vm_compute in (2147468856 <=? a) in
          lazymatch hi with
          | true => apply (sh_writable LB LK cr A M model a n Dv); vm_compute; reflexivity
          | false => let k := eval vm_compute in (Z.to_nat n) in apply (wsg_writable MV a k); [vm_compute; reflexivity | lia | lia]
          | _ => apply Wstk; lia
          end
        | |- _ =>
          unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
          lazymatch goal with
          | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
            first
              [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
              | let z := eval vm_compute in (Z.of_nat n) in
                let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                first
                  [ exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right]))
                  | exact (ex_cell_vis LB LK cr A M model a z v Dv ltac:(cbn [In EX_CELLS]; repeat first [left; reflexivity | right])) ]
              | apply (img_cell MV a n); [img_rd | lia | cbn; lia | intros i Ri; apply ImgNone; cbn in Ri; lia] ]
          end
        end
      | specialize (Run Pf); clear Pf ]
    end.
    lazymatch type of Run with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
    destruct Run as (fx1 & R1 & M1' & Grow1 & FrW1 & FrZ1 & Steps1 & Keep1 & Outs1).
    repeat lazymatch type of Outs1 with _ /\ _ => let o := fresh "Oc" in destruct Outs1 as [o Outs1] end.
    assert (Safe1 : forall i, 0 <= i < 1295744 \/ 6896960 <= i < 6896976 \/ 6898976 <= i < 6900000 ->
                    M1' (Z_to_bv 64 i) = MV (Z_to_bv 64 i)) by (intros i Zi; apply FrZ1; lia).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0x118878) M R1 (Z_to_bv 64 0x120258) M1' model _ LZ Steps1).
    intros M1 model1 MI1 SB1 VE1.
    pose proof LZ as (HoS & Lcov & Awf & _ & _).
    pose proof (lzinv_sbm ASEGS (ahid A model) A model model1 LZ MI1 SB1) as LZ1.
    change (W 1 (zero_lines 3)) with (map (WriteEv (Z_to_bv 64 1)) ([Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] ++ [])).
    apply (@wv_loop fx1 scfg (ahid A model) A HoS (m_vm_lazy model) Lcov Awf 1293752 1 ltac:(lia) (S - 136) (S - 104) ltac:(lia) ltac:(lia)
             (fun x Rx => nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv ltac:(lia) ltac:(right; lia))
             (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _) 6%nat true R1 M1 model1 (S - 136) 2 6898976 6 0 0
             [Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10; Z_to_bv 8 48; Z_to_bv 8 10] []).
    - apply Nat.le_refl.
    - exact (sbm_lazy_eq _ _ SB1).
    - exact MI1.
    - exact (proj2 (proj2 (proj2 (proj2 LZ1)))).
    - rewrite (sbm_fds' _ _ SB1). exact FD1.
    - unfold wv_regs. repeat split; match goal with Oc : getr R1 _ = _ |- _ => exact Oc end.
    - rewrite VE1. unfold wv_iov.
      pose proof (L5Defs.L5.writable_grows ASEGS MV M1' (S - 136) 32 Grow1 (Wstk (S - 136) 32 ltac:(lia) ltac:(lia)) 0 32%nat ltac:(lia) ltac:(cbn; lia)) as W32.
      rewrite Z.add_0_r in W32.
      split; [lia|]. split; [lia|]. split; [right; reflexivity|].
      split; [match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 136) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 8) with (S - 128) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 128) _ |- _ => exact Oc end|].
      split; [exact W32|].
      split.
      { unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; lia|]. split.
        - repeat (apply rdn_cons1; [lia | |];
            [ lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 1 = _ =>
                let off := eval vm_compute in (a - 6898976) in
                let i := eval vm_compute in (off / 2) in
                let p := eval vm_compute in (off mod 2) in
                apply (rdn_tr MV M1' a 1);
                [ lazymatch p with 0 => exact (proj1 (SoLn i ltac:(lia))) | _ => exact (proj2 (SoLn i ltac:(lia))) end
                | lia | cbn; lia | intros x Rx; apply Safe1; cbn in Rx; lia ]
              end | ]).
          reflexivity.
        - intros x Rx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 LB LK cr A M model x Dv); lia. }
      split; [intros C1; discriminate C1|].
      intros _.
      split; [replace (S - 136 + 16) with (S - 120) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 120) _ |- _ => exact Oc end|].
      split; [replace (S - 136 + 24) with (S - 112) by lia; match goal with Oc : L5Defs.L5.u64_at _ M1' (S - 112) _ |- _ => exact Oc end|].
      split; [|lia].
      unfold wv_buf. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [reflexivity | intros x Rx; lia].
    - lia.
    - rewrite VE1. apply (rdn_tr MV M1' 1293872 4); [exact Sx2 | lia | cbn; lia | intros i Ri; apply Safe1; cbn in Ri; lia].
    - intros R2 M2 model2 MI2 SB2 KR2 FrM2 FrV2 GrM2 GrV2.
      rewrite VE1 in FrV2, GrV2.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model1 model2 LZ1 MI2 SB2) as LZ2.
      pose proof (mem_grows_trans _ _ _ Grow1 GrV2) as GrowV.
      pose (Vd := fun j : nat => match j with
        | 2%nat => S - 144
        | 9%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 9)))
        | 10%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 10)))
        | 18%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 18)))
        | 19%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 19)))
        | 20%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 20)))
        | 21%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 21)))
        | 22%nat => bv_unsigned (getr R (Z_to_bv 5 (Z.of_nat 22)))
        | 40%nat => canz
        | 110%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 10)))
        | 118%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 18)))
        | 119%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 19)))
        | 120%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 20)))
        | 122%nat => bv_unsigned (getr R2 (Z_to_bv 5 (Z.of_nat 22)))
        | _ => 0 end).
      pose proof (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R2 (mrestrict (ahid A model) M2) Vd) as Run2. unfold Vd in Run2. cbv beta iota in Run2. clear Vd.
      repeat lazymatch type of Run2 with
      | ?P -> _ =>
        let Pf := fresh "Pf" in
        assert (Pf : P);
        [ lazymatch goal with
          | |- 0 <= bv_unsigned _ < _ => apply u64_range
          | |- _ <= _ < _ => lia
          | |- _ <= _ <= _ => lia
          | |- getr _ _ = _ =>
            first
              [ rewrite Z_to_bv_bv_unsigned; reflexivity
              | etransitivity; [apply KR2; cbn [In WV_KEEP]; repeat first [left; apply bv_eq; reflexivity | right] |];
                match goal with Oc : getr R1 _ = _ |- _ => exact Oc end ]
          | |- AS0DRVP_dpXd_4.aligned _ _ => unfold AS0DRVP_dpXd_4.aligned; rewrite Zminus_mod, S16; reflexivity
          | |- L5Defs.L5.img_clear _ _ _ => intros i Ri; rewrite FrV2, Safe1 by lia; exact (Img i Ri)
          | |- L5Defs.L5.defined _ ?a ?n =>
            apply (L5Defs.L5.defined_grows MV _ _ _ GrowV); intros i Ri; refine (store_ok_defined sp0 _ _ _ (Wstk a n _ _ i 1%nat _ _)); lia
          | |- L5Defs.L5.writable _ _ ?a ?n =>
            apply (L5Defs.L5.writable_grows ASEGS MV _ _ _ GrowV); first [apply Wstk; lia | intros d k Rd Rk; apply (SoW1 a n); lia]
          | |- _ =>
            unfold L5Defs.L5.u64_at, L5Defs.L5.u32_at, L5Defs.L5.u8_at;
            lazymatch goal with
            | |- rdn _ _ (Z_to_bv 64 (S - 144 + ?k)) _ = _ =>
              let k' := eval vm_compute in (144 - k) in
              replace (S - 144 + k) with (S - k') by lia;
              apply rdn_tr with (M := M1');
              [ match goal with Oc : L5Defs.L5.u64_at _ M1' (S - k') _ |- _ => exact Oc end
              | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
              | intros i Ri; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ri; apply FrV2; lia ]
            | |- rdn _ _ (Z_to_bv 64 ?a) ?n = Some ?bs =>
              apply rdn_tr with (M := M1'); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply FrV2; lia];
              apply rdn_tr with (M := MV); [| lia | cbn; lia | intros i Ri; cbn in Ri; apply Safe1; lia];
              first
                [ match goal with Hc : rdn _ _ (Z_to_bv 64 a) _ = _ |- _ => exact Hc end
                | let z := eval vm_compute in (Z.of_nat n) in
                  let v := lazymatch bs with word_to_le_bytes _ (Z_to_bv 64 ?w) => w | [Z_to_bv 8 ?w] => w end in
                  exact (proj1 (Forall_forall _ _) Cells (a, z, v) ltac:(cbn [In XC_CELLS]; repeat first [left; reflexivity | right])) ]
            end
          end
        | specialize (Run2 Pf); clear Pf ]
      end.
      lazymatch type of Run2 with ?P -> _ => fail 0 "premise left:" P | _ => idtac end.
      destruct Run2 as (fx3 & R3 & M3' & Grow3 & FrW3 & FrZ3 & (Steps3 & Keep3 & Outs3)).
      repeat lazymatch type of Outs3 with _ /\ _ => let o := fresh "Od" in destruct Outs3 as [o Outs3] end.
      apply (msteps_vis_fx scfg (ahid A model) A fx1 fx3 R2 (Z_to_bv 64 0x120264) M2 R3 (Z_to_bv 64 0x118588) M3' model2 _ LZ2 Steps3).
      intros M3 model3 MI3 SB3 VE3.
      pose proof (lzinv_sbm ASEGS (ahid A model) A model2 model3 LZ2 MI3 SB3) as LZ3.
      rewrite <- (proj2 (sbm_fds _ _ SB1)), <- (proj2 (sbm_fds _ _ SB2)), <- (proj2 (sbm_fds _ _ SB3)).
      apply (rz_exit_at_lit_lz ASEGS scfg R3 _ M3 _ model3 ECALLW st fetch_exitA is_ecall_ECALLW); [| left | | exact Rst].
      + exact (proj2 (proj2 (proj2 (proj2 LZ3)))).
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 17)) = _ |- _ => exact Od end.
      + match goal with Od : getr R3 (Z_to_bv 5 (Z.of_nat 10)) = _ |- _ => rewrite Z_to_bv_bv_unsigned in Od; exact (eq_trans Od G10) end.
  Qed.

End Exit.
End FPX_1.
