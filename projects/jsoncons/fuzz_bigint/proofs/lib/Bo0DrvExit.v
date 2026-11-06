(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Bo0DrvEntry Bo0Drv_defs Bo0DrvLib Bo0DrvRead Bo0DrvPiece Bo0DiagLoopK Bo0DrvStdio Bo0DrvPrintfK Bo0DrvPrintf1.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require L5Defs L5KnA L5Core ArtMem BrtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0DrvP_dpX Bo0DrvP_dpX2_pre Bo0DrvP_dpX3_pre Bo0DrvP_dpX4_pre Bo0DrvP_dpXd_2 Bo0DrvP_dpXd_3 Bo0DrvP_dpXd_4 Bo0DrvP_dpXe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XC_CELLS : list (Z * Z * Z) :=
  [(6495096, 4, 0); (6495131, 1, 0); (6494568, 8, 6494576); (6494560, 4, 2); (6494584, 8, 778276); (6494840, 8, 513736); (6494556, 4, 0); (6494576, 8, 0); (6496256, 8, 0); (896632, 8, 896400); (896540, 4, 4294967295); (896440, 8, 0); (896456, 8, 0); (896408, 8, 0); (896416, 8, 0); (896392, 8, 896160); (896152, 8, 895920); (896060, 4, 4294967295); (895960, 8, 0); (895976, 8, 0); (895928, 8, 0); (895936, 8, 0); (6494592, 8, 778276); (6494848, 8, 581776); (6360468, 1, 0)].
Definition XC_CELLS_E : list (Z * Z * Z) :=
  [(6495096, 4, 0); (6495131, 1, 0); (6494568, 8, 6494576); (6494560, 4, 1); (6494584, 8, 778276); (6494840, 8, 513736); (6494556, 4, 0); (6494576, 8, 0); (6496256, 8, 0); (896632, 8, 896400); (896540, 4, 4294967295); (896440, 8, 0); (896456, 8, 0); (896408, 8, 0); (896416, 8, 0); (896392, 8, 896160); (896152, 8, 895920); (896060, 4, 4294967295); (895960, 8, 0); (895976, 8, 0); (895928, 8, 0); (895936, 8, 0)].

Definition cells_at (MV : word -> option byte) (l : list (Z * Z * Z)) : Prop :=
  Forall (fun c => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (Z.to_nat (snd (fst c))) = Some (word_to_le_bytes (Z.to_nat (snd (fst c))) (Z_to_bv 64 (snd c)))) l.
Lemma cells_at_nth : forall MV l (i : nat) a n v, cells_at MV l -> nth_error l i = Some (a, n, v) ->
  rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
Proof. intros MV l i a n v HC Hn. exact (proj1 (Forall_forall _ _) HC (a, n, v) (nth_error_In _ _ Hn)). Qed.

(* [comment removed for export] *)
Definition exitA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6363232) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0xdaeb0 <= i < 0xdb070 -> MV (Z_to_bv 64 i) = None).
Definition exitE (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XC_CELLS_E
  /\ rdn ASEGS MV (Z_to_bv 64 6363232) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0xdaeb0 <= i < 0xdb070 -> MV (Z_to_bv 64 i) = None).

Lemma rdn_cons1 : forall (MV : word -> option byte) a b (n : nat) bs, 0 <= a ->
  rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn ASEGS MV (Z_to_bv 64 (a + 1)) n = Some bs -> rdn ASEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs Ha H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs). apply (SeqExec.rdn_app ASEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Ltac img_rd := vm_compute; apply f_equal; repeat (apply f_equal2; [apply bv_eq; reflexivity|]); reflexivity.

Lemma fetch_exitA : fetch_word ASEGS (Z_to_bv 64 0xbde50) = Some ECALLW.
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
  Hypothesis HIok : asan_iface_ok L ar C scfg HI.
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
  Lemma ex_cell_vis : forall LB LK cr A M (model : Model) a n v, dinvA LB LK cr A M model -> In (a, n, v) EX_CELLS ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)).
  Proof.
    intros LB LK cr A M model a n v D Hin. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    destruct (aio_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (dla_segs _ _ _ _ DL) in CS.
    pose proof (proj1 (Forall_forall _ _) CS (a, n, v) (Hex _ Hin)) as X. unfold cell_is in X. cbn [fst snd] in X.
    rewrite rdn_mrestrict_eq; [exact X|].
    intros k Hk. unfold woff.
    assert (B : 0 <= a /\ a + Z.of_nat (Z.to_nat n) <= 0x634000).
    { unfold EX_CELLS in Hin. cbn [In] in Hin. repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn; lia|]). destruct Hin. }
    rewrite (u64_lit a) by lia. apply (vis_low scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ _ D). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sh_writable : forall LB LK cr A M (model : Model) a n, dinvA LB LK cr A M model ->
    ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true ->
    L5Defs.L5.writable ASEGS (mrestrict (ahid A model) M) a n.
  Proof.
    intros LB LK cr A M model a n D Hb. pose proof (di_inv _ _ _ _ _ _ _ _ _ _ D) as HH.
    apply L5Core.L5C.writable_of_defined; [|apply orb_prop in Hb; rewrite !andb_true_iff, !Z.leb_le in Hb; lia | apply orb_prop in Hb; rewrite !andb_true_iff, !Z.leb_le in Hb; lia].
    intros i Hi. set (x := a + i).
    assert (Hx : 2147468588 <= x < 2147468700 \/ 2147562966 <= x < 2147563022) by (unfold x; apply orb_prop in Hb; rewrite !andb_true_iff, !Z.leb_le in Hb; lia).
    assert (DEF : M (Z_to_bv 64 x) <> None).
    { apply (aic_shadow_defined _ _ _ _ _ ICok _ _ _ _ _ _ _ HH x). left. unfold LOWSH_LO, LOWSH_HI. lia. }
    assert (VIS : ahid A model (Z_to_bv 64 x) = false).
    { unfold ahid, mkH. apply andb_false_intro2. apply negb_false_iff.
      destruct Hx as [Hx|Hx].
      - pose proof (aic_globals _ _ _ _ _ ICok _ _ _ _ _ _ _ HH) as G. rewrite (aicl_globals IL ILY) in G.
        pose proof (proj2 (Forall_inv G)) as SA. cbn [fst snd] in SA.
        specialize (SA 2147468588 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
        replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147468588)); [exact SA|].
        unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size. 
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      - destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0xdb070 16) as (_ & SA);
          [rewrite (dla_img_lo _ _ _ _ DL); lia | rewrite (dla_img_hi _ _ _ _ DL); lia | lia
          | rewrite (aicl_poison IL ILY); repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil |].
        specialize (SA 2147563022 ltac:(unfold in_shadow_of, S, SB; cbn; lia)).
        replace (page_base (Z_to_bv 64 x)) with (page_base (Z_to_bv 64 2147563022)); [exact SA|].
        unfold page_base, page_base_of. rewrite !u64_lit by lia. f_equal. unfold page_size. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold mrestrict. rewrite VIS. exact DEF.
  Qed.

  (* [comment removed for export] *)
  Lemma wsg_writable : forall (MV : word -> option byte) a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> 0 <= a -> a + Z.of_nat n <= 2 ^ 63 ->
    L5Defs.L5.writable ASEGS MV a (Z.of_nat n).
  Proof.
    intros MV a n W Ha Hn d k Hd Hk.
    apply (store_ok_window ASEGS MV (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) n k a (a + Z.of_nat n)); first [exact W | reflexivity | lia | rewrite u64_lit by lia; lia].
  Qed.

  (* [comment removed for export] *)
  Definition exit_pre (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 884736 -> MV (Z_to_bv 64 i) = None)
    /\ exitA tid MV.
  Definition exit_preE (LB : list (Z * Z)) (LK : list fframe) (cr : credit) (A : list (Z * Z)) (M : word -> option byte) (model : Model) (S tid : Z) : Prop :=
    let MV := mrestrict (ahid A model) M in
    dinvA LB LK cr A M model /\ usp - 4096 <= S /\ S <= usp /\ S mod 16 = 0
    /\ (forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV (Z_to_bv 64 (a + d)) k = true)
    /\ (forall i, 65536 <= i < 884736 -> MV (Z_to_bv 64 i) = None)
    /\ exitE tid MV.

  Lemma exit_run_0 : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 1%bv = Z_to_bv 64 776572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6363400 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutA 0 MV -> stdoutXA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbe078) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G1 G2 G4 G10 SO SOX.
    pose proof Hsp as Hsp'. destruct SO as (_ & _ & _ & SOwpos & SOwbase & SOlock & _). destruct SOX as (_ & _ & _ & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpX.dpX_conc fx R MV V
           HS64 HT64 G1 G2 G4 HSr HSa CWR CDF IMGc (WSG 897152 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 897232 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 901104 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494552 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6494560 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494568 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6495096 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl) (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl) (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl) (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl) (SHW 2147468655 1 eq_refl) (SHW 2147468660 1 eq_refl) (SHW 2147468660 4 eq_refl) (SHW 2147468661 1 eq_refl) (SHW 2147468662 1 eq_refl) (SHW 2147468663 1 eq_refl) (SHW 2147468664 4 eq_refl) (SHW 2147468668 1 eq_refl) (SHW 2147468668 4 eq_refl) (SHW 2147468669 1 eq_refl) (SHW 2147468670 1 eq_refl) (SHW 2147468671 1 eq_refl) (SHW 2147468672 1 eq_refl) (SHW 2147468672 4 eq_refl) (SHW 2147468673 1 eq_refl) (SHW 2147468674 1 eq_refl) (SHW 2147468675 1 eq_refl) (SHW 2147468676 4 eq_refl) (SHW 2147468680 1 eq_refl) (SHW 2147468680 4 eq_refl) (SHW 2147468681 1 eq_refl) (SHW 2147468682 1 eq_refl) (SHW 2147468683 1 eq_refl) (SHW 2147468684 1 eq_refl) (SHW 2147468684 4 eq_refl) (SHW 2147468685 1 eq_refl) (SHW 2147468686 1 eq_refl) (SHW 2147468687 1 eq_refl) (SHW 2147468688 4 eq_refl) (SHW 2147468692 1 eq_refl) (SHW 2147468692 4 eq_refl) (SHW 2147468693 1 eq_refl) (SHW 2147468694 1 eq_refl) (SHW 2147468695 1 eq_refl) (SHW 2147468696 1 eq_refl) (SHW 2147468697 1 eq_refl) (SHW 2147468698 1 eq_refl) (SHW 2147468699 1 eq_refl) (SHW 2147562966 1 eq_refl) (SHW 2147562967 1 eq_refl) (SHW 2147562968 1 eq_refl) (SHW 2147562968 4 eq_refl) (SHW 2147562969 1 eq_refl) (SHW 2147562972 4 eq_refl) (SHW 2147562976 4 eq_refl) (SHW 2147562980 4 eq_refl) (SHW 2147562984 4 eq_refl) (SHW 2147562988 4 eq_refl) (SHW 2147562992 4 eq_refl) (SHW 2147562996 4 eq_refl) (SHW 2147563000 4 eq_refl) (SHW 2147563004 4 eq_refl) (SHW 2147563008 4 eq_refl) (SHW 2147563012 4 eq_refl) (SHW 2147563016 4 eq_refl) (SHW 2147563018 1 eq_refl) (SHW 2147563019 1 eq_refl) (SHW 2147563020 1 eq_refl) (SHW 2147563021 1 eq_refl) TIDC HTr (XCC 0%nat 6495096 4 0 eq_refl) (XCC1 1%nat 6495131 0 eq_refl eq_refl)
           (XCC 2%nat 6494568 8 6494576 eq_refl) (XCC 3%nat 6494560 4 2 eq_refl) (XCC 4%nat 6494584 8 778276 eq_refl) (XCC 5%nat 6494840 8 513736 eq_refl)
           (XCC 6%nat 6494556 4 0 eq_refl) (STC1 10%nat 1508832 0 eq_refl eq_refl) (XCC 7%nat 6494576 8 0 eq_refl) (STC1 3%nat 897232 0 eq_refl eq_refl)
           (STC 0%nat 885400 8 885400 eq_refl) (STC 2%nat 897152 8 1 eq_refl) (STC 4%nat 900944 4 1 eq_refl) (STC 5%nat 901104 8 0 eq_refl) (STC1 8%nat 914456 1 eq_refl eq_refl)
           (STC 7%nat 911160 8 2147450880 eq_refl) (DSC 896688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 896704 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 909212 1 eq_refl eq_refl)
           (DSC 896704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1508064 8 18446744073709551615 eq_refl) (STC 1%nat 885800 8 837440 eq_refl)
           (DSC 896744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 896768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 896768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 896808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 896832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142240)) ltac:(img_rd) eq_refl) (DSC 896896 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142336)) ltac:(img_rd) eq_refl) (DSC 896960 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142432)) ltac:(img_rd) eq_refl) (DSC 897024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 897024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142528)) ltac:(img_rd) eq_refl) (DSC 897088 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 897088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 897128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6496256 8 0 eq_refl) (XCC 9%nat 896632 8 896400 eq_refl)
           (XCC 10%nat 896540 4 4294967295 eq_refl) (XCC 11%nat 896440 8 0 eq_refl) (XCC 12%nat 896456 8 0 eq_refl) (XCC 13%nat 896408 8 0 eq_refl) (XCC 14%nat 896416 8 0 eq_refl)
           (XCC 15%nat 896392 8 896160 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 896152 8 895920 eq_refl) (XCC 17%nat 896060 4 4294967295 eq_refl)
           (XCC 18%nat 895960 8 0 eq_refl) (XCC 19%nat 895976 8 0 eq_refl) (XCC 20%nat 895928 8 0 eq_refl) (XCC 21%nat 895936 8 0 eq_refl) (XCC 22%nat 6494592 8 778276 eq_refl) (XCC 23%nat 6494848 8 581776 eq_refl) (XCC1 24%nat 6360468 0 eq_refl eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xbde50) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0xbde50) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpX.KS_dpX; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.

  (* [comment removed for export] *)
  Definition stdoutPA (MV : word -> option byte) : Prop :=
    rdn ASEGS MV (Z_to_bv 64 896300) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
    /\ rdn ASEGS MV (Z_to_bv 64 896200) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 896216) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 896168) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn ASEGS MV (Z_to_bv 64 896176) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Lemma exit_run_e : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preE LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6363400 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbe078) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
  Proof.
    intros LB LK cr A M model R S st tid (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst G2 G4 G10 SOP.
    pose proof Hsp as Hsp'. destruct SOP as (SOlock & SOwpos & SOwbase & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpXe.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS_E i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS_E i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS_E i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXe.dpXe_conc fx R MV V
           HS64 HT64 G2 G4 HSr HSa CWR CDF IMGc (WSG 897152 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 897232 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 901104 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494552 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6494560 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494568 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6495096 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl) (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl) (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl) (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl) (SHW 2147468655 1 eq_refl) (SHW 2147468660 1 eq_refl) (SHW 2147468660 4 eq_refl) (SHW 2147468661 1 eq_refl) (SHW 2147468662 1 eq_refl) (SHW 2147468663 1 eq_refl) (SHW 2147468664 4 eq_refl) (SHW 2147468668 1 eq_refl) (SHW 2147468668 4 eq_refl) (SHW 2147468669 1 eq_refl) (SHW 2147468670 1 eq_refl) (SHW 2147468671 1 eq_refl) (SHW 2147468672 1 eq_refl) (SHW 2147468672 4 eq_refl) (SHW 2147468673 1 eq_refl) (SHW 2147468674 1 eq_refl) (SHW 2147468675 1 eq_refl) (SHW 2147468676 4 eq_refl) (SHW 2147468680 1 eq_refl) (SHW 2147468680 4 eq_refl) (SHW 2147468681 1 eq_refl) (SHW 2147468682 1 eq_refl) (SHW 2147468683 1 eq_refl) (SHW 2147468684 1 eq_refl) (SHW 2147468684 4 eq_refl) (SHW 2147468685 1 eq_refl) (SHW 2147468686 1 eq_refl) (SHW 2147468687 1 eq_refl) (SHW 2147468688 4 eq_refl) (SHW 2147468692 1 eq_refl) (SHW 2147468692 4 eq_refl) (SHW 2147468693 1 eq_refl) (SHW 2147468694 1 eq_refl) (SHW 2147468695 1 eq_refl) (SHW 2147468696 1 eq_refl) (SHW 2147468697 1 eq_refl) (SHW 2147468698 1 eq_refl) (SHW 2147468699 1 eq_refl) (SHW 2147562966 1 eq_refl) (SHW 2147562967 1 eq_refl) (SHW 2147562968 1 eq_refl) (SHW 2147562968 4 eq_refl) (SHW 2147562969 1 eq_refl) (SHW 2147562972 4 eq_refl) (SHW 2147562976 4 eq_refl) (SHW 2147562980 4 eq_refl) (SHW 2147562984 4 eq_refl) (SHW 2147562988 4 eq_refl) (SHW 2147562992 4 eq_refl) (SHW 2147562996 4 eq_refl) (SHW 2147563000 4 eq_refl) (SHW 2147563004 4 eq_refl) (SHW 2147563008 4 eq_refl) (SHW 2147563012 4 eq_refl) (SHW 2147563016 4 eq_refl) (SHW 2147563018 1 eq_refl) (SHW 2147563019 1 eq_refl) (SHW 2147563020 1 eq_refl) (SHW 2147563021 1 eq_refl) TIDC HTr (XCC 0%nat 6495096 4 0 eq_refl) (XCC1 1%nat 6495131 0 eq_refl eq_refl)
           (XCC 2%nat 6494568 8 6494576 eq_refl) (XCC 3%nat 6494560 4 1 eq_refl) (XCC 4%nat 6494584 8 778276 eq_refl) (XCC 5%nat 6494840 8 513736 eq_refl)
           (XCC 6%nat 6494556 4 0 eq_refl) (STC1 10%nat 1508832 0 eq_refl eq_refl) (XCC 7%nat 6494576 8 0 eq_refl) (STC1 3%nat 897232 0 eq_refl eq_refl)
           (STC 0%nat 885400 8 885400 eq_refl) (STC 2%nat 897152 8 1 eq_refl) (STC 4%nat 900944 4 1 eq_refl) (STC 5%nat 901104 8 0 eq_refl) (STC1 8%nat 914456 1 eq_refl eq_refl)
           (STC 7%nat 911160 8 2147450880 eq_refl) (DSC 896688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 896704 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 909212 1 eq_refl eq_refl)
           (DSC 896704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1508064 8 18446744073709551615 eq_refl) (STC 1%nat 885800 8 837440 eq_refl)
           (DSC 896744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 896768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 896768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 896808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 896832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142240)) ltac:(img_rd) eq_refl) (DSC 896896 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142336)) ltac:(img_rd) eq_refl) (DSC 896960 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142432)) ltac:(img_rd) eq_refl) (DSC 897024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 897024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142528)) ltac:(img_rd) eq_refl) (DSC 897088 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 897088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 897128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6496256 8 0 eq_refl) (XCC 9%nat 896632 8 896400 eq_refl)
           (XCC 10%nat 896540 4 4294967295 eq_refl) (XCC 11%nat 896440 8 0 eq_refl) (XCC 12%nat 896456 8 0 eq_refl) (XCC 13%nat 896408 8 0 eq_refl) (XCC 14%nat 896416 8 0 eq_refl)
           (XCC 15%nat 896392 8 896160 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 896152 8 895920 eq_refl) (XCC 17%nat 896060 4 4294967295 eq_refl)
           (XCC 18%nat 895960 8 0 eq_refl) (XCC 19%nat 895976 8 0 eq_refl) (XCC 20%nat 895928 8 0 eq_refl) (XCC 21%nat 895936 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xbde50) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0xbde50) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXe.KS_dpXe; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.


  Lemma exit_run_2 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 776572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6363400 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6494536) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 1 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbe078) M rom) model) (t_emit (W 1 (zero_lines 1%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX2_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX2_pre.dpX2_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4 HSr HSa CWR CDF IMGc (WSG 897152 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 897232 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 901104 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494552 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6494560 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494568 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6495096 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl) (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl) (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl) (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl) (SHW 2147468655 1 eq_refl) (SHW 2147468660 1 eq_refl) (SHW 2147468660 4 eq_refl) (SHW 2147468661 1 eq_refl) (SHW 2147468662 1 eq_refl) (SHW 2147468663 1 eq_refl) (SHW 2147468664 4 eq_refl) (SHW 2147468668 1 eq_refl) (SHW 2147468668 4 eq_refl) (SHW 2147468669 1 eq_refl) (SHW 2147468670 1 eq_refl) (SHW 2147468671 1 eq_refl) (SHW 2147468672 1 eq_refl) (SHW 2147468672 4 eq_refl) (SHW 2147468673 1 eq_refl) (SHW 2147468674 1 eq_refl) (SHW 2147468675 1 eq_refl) (SHW 2147468676 4 eq_refl) (SHW 2147468680 1 eq_refl) (SHW 2147468680 4 eq_refl) (SHW 2147468681 1 eq_refl) (SHW 2147468682 1 eq_refl) (SHW 2147468683 1 eq_refl) (SHW 2147468684 1 eq_refl) (SHW 2147468684 4 eq_refl) (SHW 2147468685 1 eq_refl) (SHW 2147468686 1 eq_refl) (SHW 2147468687 1 eq_refl) (SHW 2147468688 4 eq_refl) (SHW 2147468692 1 eq_refl) (SHW 2147468692 4 eq_refl) (SHW 2147468693 1 eq_refl) (SHW 2147468694 1 eq_refl) (SHW 2147468695 1 eq_refl) (SHW 2147468696 1 eq_refl) (SHW 2147468697 1 eq_refl) (SHW 2147468698 1 eq_refl) (SHW 2147468699 1 eq_refl) (SHW 2147562966 1 eq_refl) (SHW 2147562967 1 eq_refl) (SHW 2147562968 1 eq_refl) (SHW 2147562968 4 eq_refl) (SHW 2147562969 1 eq_refl) (SHW 2147562972 4 eq_refl) (SHW 2147562976 4 eq_refl) (SHW 2147562980 4 eq_refl) (SHW 2147562984 4 eq_refl) (SHW 2147562988 4 eq_refl) (SHW 2147562992 4 eq_refl) (SHW 2147562996 4 eq_refl) (SHW 2147563000 4 eq_refl) (SHW 2147563004 4 eq_refl) (SHW 2147563008 4 eq_refl) (SHW 2147563012 4 eq_refl) (SHW 2147563016 4 eq_refl) (SHW 2147563018 1 eq_refl) (SHW 2147563019 1 eq_refl) (SHW 2147563020 1 eq_refl) (SHW 2147563021 1 eq_refl) TIDC HTr (XCC 0%nat 6495096 4 0 eq_refl) (XCC1 1%nat 6495131 0 eq_refl eq_refl)
           (XCC 2%nat 6494568 8 6494576 eq_refl) (XCC 3%nat 6494560 4 2 eq_refl) (XCC 4%nat 6494584 8 778276 eq_refl) (XCC 5%nat 6494840 8 513736 eq_refl)
           (XCC 6%nat 6494556 4 0 eq_refl) (STC1 10%nat 1508832 0 eq_refl eq_refl) (XCC 7%nat 6494576 8 0 eq_refl) (STC1 3%nat 897232 0 eq_refl eq_refl)
           (STC 0%nat 885400 8 885400 eq_refl) (STC 2%nat 897152 8 1 eq_refl) (STC 4%nat 900944 4 1 eq_refl) (STC 5%nat 901104 8 0 eq_refl) (STC1 8%nat 914456 1 eq_refl eq_refl)
           (STC 7%nat 911160 8 2147450880 eq_refl) (DSC 896688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 896704 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 909212 1 eq_refl eq_refl)
           (DSC 896704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1508064 8 18446744073709551615 eq_refl) (STC 1%nat 885800 8 837440 eq_refl)
           (DSC 896744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 896768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 896768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 896808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 896832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142240)) ltac:(img_rd) eq_refl) (DSC 896896 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142336)) ltac:(img_rd) eq_refl) (DSC 896960 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142432)) ltac:(img_rd) eq_refl) (DSC 897024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 897024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142528)) ltac:(img_rd) eq_refl) (DSC 897088 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 897088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 897128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6496256 8 0 eq_refl) (XCC 9%nat 896632 8 896400 eq_refl)
           (XCC 10%nat 896540 4 4294967295 eq_refl) (XCC 11%nat 896440 8 0 eq_refl) (XCC 12%nat 896456 8 0 eq_refl) (XCC 13%nat 896408 8 0 eq_refl) (XCC 14%nat 896416 8 0 eq_refl)
           (XCC 15%nat 896392 8 896160 eq_refl) SOlock SOwpos SOwbase SOwrite CANc SOfd (XCC 22%nat 6494592 8 778276 eq_refl) (XCC 23%nat 6494848 8 581776 eq_refl) (XCC1 24%nat 6360468 0 eq_refl eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 897152 \/ 901112 <= i < 6494552 \/ 6494576 <= i < 6495096 \/ 6495100 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xc3a48) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6496280) (Z.to_nat (2 * 1)) = Some (zero_lines 1%nat)).
    { apply (LITX 6496280 (Z.to_nat (2 * 1))); [|reflexivity]. change (Z.to_nat (2 * 1)) with (2 * 1%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 896160 /\ (896160 + 124 <= q \/ q + 32 + 16 <= 896160 + 120) /\ 896160 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 1%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 896160 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 1%nat)%nat true R1 M1 model1 q 2 6496280 (2 * 1) 0 0 (zero_lines 1%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 896160 <= a -> a + n <= 896160 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 884736 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 896160) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6494536) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
    destruct (AS0DRVP_dpXd_2.dpXd_2_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 896192 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 896200 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 896216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 896248 8%nat _ SObuf eq_refl)
           (LIT3 896256 8%nat _ SObufsz eq_refl) (LIT3 6494536 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 896168 8%nat _ SOrpos eq_refl) (LIT3 896176 8%nat _ SOrend eq_refl)
           (LIT3 896152 8%nat _ (XCC 16%nat 896152 8 895920 eq_refl) eq_refl) (LIT3 896060 4%nat _ (XCC 17%nat 896060 4 4294967295 eq_refl) eq_refl)
           (LIT3 895960 8%nat _ (XCC 18%nat 895960 8 0 eq_refl) eq_refl) (LIT3 895976 8%nat _ (XCC 19%nat 895976 8 0 eq_refl) eq_refl)
           (LIT3 895928 8%nat _ (XCC 20%nat 895928 8 0 eq_refl) eq_refl) (LIT3 895936 8%nat _ (XCC 21%nat 895936 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0xc3a54) M3 R4 (Z_to_bv 64 0xbde50) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0xbde50) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  Lemma exit_run_3 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 776572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6363400 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6494536) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 2 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbe078) M rom) model) (t_emit (W 1 (zero_lines 2%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX3_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX3_pre.dpX3_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4 HSr HSa CWR CDF IMGc (WSG 897152 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 897232 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 901104 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494552 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6494560 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494568 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6495096 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl) (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl) (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl) (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl) (SHW 2147468655 1 eq_refl) (SHW 2147468660 1 eq_refl) (SHW 2147468660 4 eq_refl) (SHW 2147468661 1 eq_refl) (SHW 2147468662 1 eq_refl) (SHW 2147468663 1 eq_refl) (SHW 2147468664 4 eq_refl) (SHW 2147468668 1 eq_refl) (SHW 2147468668 4 eq_refl) (SHW 2147468669 1 eq_refl) (SHW 2147468670 1 eq_refl) (SHW 2147468671 1 eq_refl) (SHW 2147468672 1 eq_refl) (SHW 2147468672 4 eq_refl) (SHW 2147468673 1 eq_refl) (SHW 2147468674 1 eq_refl) (SHW 2147468675 1 eq_refl) (SHW 2147468676 4 eq_refl) (SHW 2147468680 1 eq_refl) (SHW 2147468680 4 eq_refl) (SHW 2147468681 1 eq_refl) (SHW 2147468682 1 eq_refl) (SHW 2147468683 1 eq_refl) (SHW 2147468684 1 eq_refl) (SHW 2147468684 4 eq_refl) (SHW 2147468685 1 eq_refl) (SHW 2147468686 1 eq_refl) (SHW 2147468687 1 eq_refl) (SHW 2147468688 4 eq_refl) (SHW 2147468692 1 eq_refl) (SHW 2147468692 4 eq_refl) (SHW 2147468693 1 eq_refl) (SHW 2147468694 1 eq_refl) (SHW 2147468695 1 eq_refl) (SHW 2147468696 1 eq_refl) (SHW 2147468697 1 eq_refl) (SHW 2147468698 1 eq_refl) (SHW 2147468699 1 eq_refl) (SHW 2147562966 1 eq_refl) (SHW 2147562967 1 eq_refl) (SHW 2147562968 1 eq_refl) (SHW 2147562968 4 eq_refl) (SHW 2147562969 1 eq_refl) (SHW 2147562972 4 eq_refl) (SHW 2147562976 4 eq_refl) (SHW 2147562980 4 eq_refl) (SHW 2147562984 4 eq_refl) (SHW 2147562988 4 eq_refl) (SHW 2147562992 4 eq_refl) (SHW 2147562996 4 eq_refl) (SHW 2147563000 4 eq_refl) (SHW 2147563004 4 eq_refl) (SHW 2147563008 4 eq_refl) (SHW 2147563012 4 eq_refl) (SHW 2147563016 4 eq_refl) (SHW 2147563018 1 eq_refl) (SHW 2147563019 1 eq_refl) (SHW 2147563020 1 eq_refl) (SHW 2147563021 1 eq_refl) TIDC HTr (XCC 0%nat 6495096 4 0 eq_refl) (XCC1 1%nat 6495131 0 eq_refl eq_refl)
           (XCC 2%nat 6494568 8 6494576 eq_refl) (XCC 3%nat 6494560 4 2 eq_refl) (XCC 4%nat 6494584 8 778276 eq_refl) (XCC 5%nat 6494840 8 513736 eq_refl)
           (XCC 6%nat 6494556 4 0 eq_refl) (STC1 10%nat 1508832 0 eq_refl eq_refl) (XCC 7%nat 6494576 8 0 eq_refl) (STC1 3%nat 897232 0 eq_refl eq_refl)
           (STC 0%nat 885400 8 885400 eq_refl) (STC 2%nat 897152 8 1 eq_refl) (STC 4%nat 900944 4 1 eq_refl) (STC 5%nat 901104 8 0 eq_refl) (STC1 8%nat 914456 1 eq_refl eq_refl)
           (STC 7%nat 911160 8 2147450880 eq_refl) (DSC 896688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 896704 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 909212 1 eq_refl eq_refl)
           (DSC 896704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1508064 8 18446744073709551615 eq_refl) (STC 1%nat 885800 8 837440 eq_refl)
           (DSC 896744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 896768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 896768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 896808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 896832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142240)) ltac:(img_rd) eq_refl) (DSC 896896 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142336)) ltac:(img_rd) eq_refl) (DSC 896960 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142432)) ltac:(img_rd) eq_refl) (DSC 897024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 897024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142528)) ltac:(img_rd) eq_refl) (DSC 897088 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 897088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 897128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6496256 8 0 eq_refl) (XCC 9%nat 896632 8 896400 eq_refl)
           (XCC 10%nat 896540 4 4294967295 eq_refl) (XCC 11%nat 896440 8 0 eq_refl) (XCC 12%nat 896456 8 0 eq_refl) (XCC 13%nat 896408 8 0 eq_refl) (XCC 14%nat 896416 8 0 eq_refl)
           (XCC 15%nat 896392 8 896160 eq_refl) SOlock SOwpos SOwbase SOwrite CANc SOfd (XCC 22%nat 6494592 8 778276 eq_refl) (XCC 23%nat 6494848 8 581776 eq_refl) (XCC1 24%nat 6360468 0 eq_refl eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 897152 \/ 901112 <= i < 6494552 \/ 6494576 <= i < 6495096 \/ 6495100 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xc3a48) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6496280) (Z.to_nat (2 * 2)) = Some (zero_lines 2%nat)).
    { apply (LITX 6496280 (Z.to_nat (2 * 2))); [|reflexivity]. change (Z.to_nat (2 * 2)) with (2 * 2%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 896160 /\ (896160 + 124 <= q \/ q + 32 + 16 <= 896160 + 120) /\ 896160 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 2%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 896160 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 2%nat)%nat true R1 M1 model1 q 2 6496280 (2 * 2) 0 0 (zero_lines 2%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 896160 <= a -> a + n <= 896160 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 884736 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 896160) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6494536) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
    destruct (AS0DRVP_dpXd_3.dpXd_3_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 896192 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 896200 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 896216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 896248 8%nat _ SObuf eq_refl)
           (LIT3 896256 8%nat _ SObufsz eq_refl) (LIT3 6494536 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 896168 8%nat _ SOrpos eq_refl) (LIT3 896176 8%nat _ SOrend eq_refl)
           (LIT3 896152 8%nat _ (XCC 16%nat 896152 8 895920 eq_refl) eq_refl) (LIT3 896060 4%nat _ (XCC 17%nat 896060 4 4294967295 eq_refl) eq_refl)
           (LIT3 895960 8%nat _ (XCC 18%nat 895960 8 0 eq_refl) eq_refl) (LIT3 895976 8%nat _ (XCC 19%nat 895976 8 0 eq_refl) eq_refl)
           (LIT3 895928 8%nat _ (XCC 20%nat 895928 8 0 eq_refl) eq_refl) (LIT3 895936 8%nat _ (XCC 21%nat 895936 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0xc3a54) M3 R4 (Z_to_bv 64 0xbde50) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0xbde50) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.


  Lemma exit_run_4 : forall LB LK cr A M (model : Model) R (S st tid canz : Z),
    exit_pre LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 -> 0 <= canz < 2 ^ 64 ->
    getr R 1%bv = Z_to_bv 64 776572 -> getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6363400 -> getr R 10%bv = Z_to_bv 64 st ->
    rdn ASEGS MV (Z_to_bv 64 6494536) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 canz)) ->
    stdoutA 3 MV -> stdoutXA MV ->
    fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbe078) M rom) model) (t_emit (W 1 (zero_lines 3%nat)) (t_exit (Z_to_bv 64 st) (m_fs model))).
  Proof.
    intros LB LK cr A M model R S st tid canz (D & HS1 & HS2 & HS16 & WIN & IMGc & (XC & TIDC & HTr & DESC)) MV Hst Hcan G1 G2 G4 G10 CANc SO SOX FD1.
    pose proof Hsp as Hsp'. destruct SO as (_ & SObufsz & _ & SOwpos & SOwbase & SOlock & _ & FW & BW & BC). destruct SOX as (SOwrite & SOfd & SObuf & SOrpos & SOrend).
    set (V := fun n : nat => match n with 2%nat => S | 44%nat => tid | 40%nat => canz | _ => 0 end).
    assert (HS64 : 0 <= V 2%nat < 2 ^ 64) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HT64 : 0 <= V 44%nat < 2 ^ 64) by (cbn [V]; clear - HTr; lia).
    assert (HSr : 140735332552704 <= V 2%nat <= 140737488355328) by (cbn [V]; clear - Hsp' HS1 HS2; lia).
    assert (HSa : AS0DRVP_dpX4_pre.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XC_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XC_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XC_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    (* [comment removed for export] *)
    destruct (AS0DRVP_dpX4_pre.dpX4_pre_conc fx R MV V
           HS64 Hcan HT64 G1 G2 G4 HSr HSa CWR CDF IMGc (WSG 897152 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 897232 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 901104 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494552 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6494560 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6494568 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6495096 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl) (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl) (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl) (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl) (SHW 2147468655 1 eq_refl) (SHW 2147468660 1 eq_refl) (SHW 2147468660 4 eq_refl) (SHW 2147468661 1 eq_refl) (SHW 2147468662 1 eq_refl) (SHW 2147468663 1 eq_refl) (SHW 2147468664 4 eq_refl) (SHW 2147468668 1 eq_refl) (SHW 2147468668 4 eq_refl) (SHW 2147468669 1 eq_refl) (SHW 2147468670 1 eq_refl) (SHW 2147468671 1 eq_refl) (SHW 2147468672 1 eq_refl) (SHW 2147468672 4 eq_refl) (SHW 2147468673 1 eq_refl) (SHW 2147468674 1 eq_refl) (SHW 2147468675 1 eq_refl) (SHW 2147468676 4 eq_refl) (SHW 2147468680 1 eq_refl) (SHW 2147468680 4 eq_refl) (SHW 2147468681 1 eq_refl) (SHW 2147468682 1 eq_refl) (SHW 2147468683 1 eq_refl) (SHW 2147468684 1 eq_refl) (SHW 2147468684 4 eq_refl) (SHW 2147468685 1 eq_refl) (SHW 2147468686 1 eq_refl) (SHW 2147468687 1 eq_refl) (SHW 2147468688 4 eq_refl) (SHW 2147468692 1 eq_refl) (SHW 2147468692 4 eq_refl) (SHW 2147468693 1 eq_refl) (SHW 2147468694 1 eq_refl) (SHW 2147468695 1 eq_refl) (SHW 2147468696 1 eq_refl) (SHW 2147468697 1 eq_refl) (SHW 2147468698 1 eq_refl) (SHW 2147468699 1 eq_refl) (SHW 2147562966 1 eq_refl) (SHW 2147562967 1 eq_refl) (SHW 2147562968 1 eq_refl) (SHW 2147562968 4 eq_refl) (SHW 2147562969 1 eq_refl) (SHW 2147562972 4 eq_refl) (SHW 2147562976 4 eq_refl) (SHW 2147562980 4 eq_refl) (SHW 2147562984 4 eq_refl) (SHW 2147562988 4 eq_refl) (SHW 2147562992 4 eq_refl) (SHW 2147562996 4 eq_refl) (SHW 2147563000 4 eq_refl) (SHW 2147563004 4 eq_refl) (SHW 2147563008 4 eq_refl) (SHW 2147563012 4 eq_refl) (SHW 2147563016 4 eq_refl) (SHW 2147563018 1 eq_refl) (SHW 2147563019 1 eq_refl) (SHW 2147563020 1 eq_refl) (SHW 2147563021 1 eq_refl) TIDC HTr (XCC 0%nat 6495096 4 0 eq_refl) (XCC1 1%nat 6495131 0 eq_refl eq_refl)
           (XCC 2%nat 6494568 8 6494576 eq_refl) (XCC 3%nat 6494560 4 2 eq_refl) (XCC 4%nat 6494584 8 778276 eq_refl) (XCC 5%nat 6494840 8 513736 eq_refl)
           (XCC 6%nat 6494556 4 0 eq_refl) (STC1 10%nat 1508832 0 eq_refl eq_refl) (XCC 7%nat 6494576 8 0 eq_refl) (STC1 3%nat 897232 0 eq_refl eq_refl)
           (STC 0%nat 885400 8 885400 eq_refl) (STC 2%nat 897152 8 1 eq_refl) (STC 4%nat 900944 4 1 eq_refl) (STC 5%nat 901104 8 0 eq_refl) (STC1 8%nat 914456 1 eq_refl eq_refl)
           (STC 7%nat 911160 8 2147450880 eq_refl) (DSC 896688 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 896704 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 909212 1 eq_refl eq_refl)
           (DSC 896704 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1508064 8 18446744073709551615 eq_refl) (STC 1%nat 885800 8 837440 eq_refl)
           (DSC 896744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896752 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 896768 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 896768 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 896808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896816 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 896832 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896832 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896880 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142240)) ltac:(img_rd) eq_refl) (DSC 896896 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896896 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 896936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 896944 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142336)) ltac:(img_rd) eq_refl) (DSC 896960 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 896960 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897008 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142432)) ltac:(img_rd) eq_refl) (DSC 897024 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 897024 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 897064 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 897072 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142528)) ltac:(img_rd) eq_refl) (DSC 897088 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 897088 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 897128 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6496256 8 0 eq_refl) (XCC 9%nat 896632 8 896400 eq_refl)
           (XCC 10%nat 896540 4 4294967295 eq_refl) (XCC 11%nat 896440 8 0 eq_refl) (XCC 12%nat 896456 8 0 eq_refl) (XCC 13%nat 896408 8 0 eq_refl) (XCC 14%nat 896416 8 0 eq_refl)
           (XCC 15%nat 896392 8 896160 eq_refl) SOlock SOwpos SOwbase SOwrite CANc SOfd (XCC 22%nat 6494592 8 778276 eq_refl) (XCC 23%nat 6494848 8 581776 eq_refl) (XCC1 24%nat 6360468 0 eq_refl eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & XFRZ & XMS & _ & _ & Xr2 & _ & _ & _ & Xr8 & Xr9 & Xr10 & Xr11 & Xr12 & _ & _ & _ & _ & Xr17 & Xr18 & Xr19 & Xr21 & Xr22 & _ & Xm112 & Xm120 & Xm128 & Xm136 & Xm104 & Xm96 & Xm88 & Xm80 & Xm72 & Xm64 & Xm56 & Xm48 & Xm40 & Xm32 & Xm24 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    unfold V in XFRZ, XMS; cbn beta iota in XFRZ, XMS. cbn [V] in *.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (HH & HL & HA & HM & Hh).
    (* [comment removed for export] *)
    set (good := fun i : Z => i < 897152 \/ 901112 <= i < 6494552 \/ 6494576 <= i < 6495096 \/ 6495100 <= i < 2147450880).
    assert (FRX : forall i, 0 <= i -> good i -> MV1 (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
    { intros i Hi Hg. apply XFRZ; [unfold good in Hg; clear - Hi Hg; lia | ..]; (intros X; unfold good in Hg; clear - Hsp' HS1 HS2 Hi Hg X; lia). }
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xc3a48) MV1 model _ LZ XMS).
    intros M1 model1 MI1 SBM1 VIS1.
    assert (LITX : forall a (n : nat) bs, rdn ASEGS MV (Z_to_bv 64 a) n = Some bs ->
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
              rdn ASEGS MV1 (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le in B2.
      apply (rdn_tr MV MV1 a n bs Hr B1); [lia|]. intros i Hi. apply FRX; [lia|]. unfold good. clear - B1 B2 Hi. lia. }
    (* [comment removed for export] *)
    assert (DATA : rdn ASEGS MV1 (Z_to_bv 64 6496280) (Z.to_nat (2 * 3)) = Some (zero_lines 3%nat)).
    { apply (LITX 6496280 (Z.to_nat (2 * 3))); [|reflexivity]. change (Z.to_nat (2 * 3)) with (2 * 3%nat)%nat.
            destruct (BC 0 ltac:(lia)) as (B0a & B0b). destruct (BC 1 ltac:(lia)) as (B1a & B1b). destruct (BC 2 ltac:(lia)) as (B2a & B2b). cbn [zero_lines].
      apply rdn_cons1; [lia | exact B0a|]. apply rdn_cons1; [lia | exact B0b|]. apply rdn_cons1; [lia | exact B1a|]. apply rdn_cons1; [lia | exact B1b|]. apply rdn_cons1; [lia | exact B2a|]. apply rdn_cons1; [lia | exact B2b|]. reflexivity. }
    (* [comment removed for export] *)
    set (q := S - 136) in *.
    assert (Hq : 0 <= q /\ q <= q + 32 /\ q + 32 + 16 <= 2 ^ 47) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (Hf : 0 <= 896160 /\ (896160 + 124 <= q \/ q + 32 + 16 <= 896160 + 120) /\ 896160 + 124 < 2 ^ 63) by (unfold q; clear - Hsp' HS1 HS2; lia).
    assert (NLq : forall x, q <= x < q + 32 -> page_in_ranges (page_base_of x) (m_vm_lazy model) = false).
    { intros x Hx. apply (nl_pt scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ x D); unfold q in Hx; clear - Hsp' HS1 HS2 Hx; lia. }
    assert (WIN1 : forall a n, usp - 8388608 <= a -> a + n <= usp -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV1 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (WIN a n); assumption).
    unfold W. rewrite <- (app_nil_r (zero_lines 3%nat)).
    apply (wv_loop scfg (ahid A model) A HH (m_vm_lazy model) HL HA 896160 1 ltac:(lia) q (q + 32) Hq Hf NLq (t_exit (Z_to_bv 64 st) (m_fs model)) (t_exit_has_nil _ _)
             (2 * 3%nat)%nat true R1 M1 model1 q 2 6496280 (2 * 3) 0 0 (zero_lines 3%nat) []).
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
              (0 <=? a) && ((a + Z.of_nat n <=? 897152) || ((901112 <=? a) && (a + Z.of_nat n <=? 6494552)) || ((6495100 <=? a) && (a + Z.of_nat n <=? 2147450880))) = true ->
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
    assert (FW3 : forall a n, 896160 <= a -> a + n <= 896160 + 232 -> forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS MV3 (Z_to_bv 64 (a + d)) k = true)
      by (intros a n H1 H2 d k Hd Hk; apply (store_ok_mono ASEGS k MV1 MV3 _ GRV3); apply (store_ok_mono ASEGS k MV MV1 _ XGR); apply (FW a n); assumption).
    assert (IMG3 : forall i, 65536 <= i < 884736 -> MV3 (Z_to_bv 64 i) = None).
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
    assert (Dg9 : getr R3 (Z_to_bv 5 (Z.of_nat 9)) = Z_to_bv 64 896160) by (eapply eq_trans; [exact (KR3 9%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr9]).
    assert (Dg21 : getr R3 (Z_to_bv 5 (Z.of_nat 21)) = Z_to_bv 64 6494536) by (eapply eq_trans; [exact (KR3 21%bv ltac:(unfold WV_KEEP; cbn [In]; tauto)) | exact Xr21]).
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
    destruct (AS0DRVP_dpXd_4.dpXd_4_conc fx1 R3 MV3 VD
           HD64 (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) Hcan (u64_range _) (u64_range _) (u64_range _) (u64_range _)
           (u64_range _) Dg2 Dg8 Dg9 Dg10 Dg18 Dg19 Dg20 Dg21 Dg22 HDr HDa DWR DDF IMG3 (fun d k Hd Hk => FW3 896192 8 ltac:(lia) ltac:(lia) d k Hd Hk)
           (fun d k Hd Hk => FW3 896200 8 ltac:(lia) ltac:(lia) d k Hd Hk) (fun d k Hd Hk => FW3 896216 8 ltac:(lia) ltac:(lia) d k Hd Hk) (LIT3 896248 8%nat _ SObuf eq_refl)
           (LIT3 896256 8%nat _ SObufsz eq_refl) (LIT3 6494536 8%nat _ CANc eq_refl) (cellS 40 104 _ _ Xm104 eq_refl) (cellS 104 40 _ _ Xm40 eq_refl) (cellS 96 48 _ _ Xm48 eq_refl)
           (cellS 88 56 _ _ Xm56 eq_refl) (cellS 80 64 _ _ Xm64 eq_refl) (cellS 72 72 _ _ Xm72 eq_refl) (cellS 64 80 _ _ Xm80 eq_refl) (cellS 56 88 _ _ Xm88 eq_refl)
           (cellS 48 96 _ _ Xm96 eq_refl) (LIT3 896168 8%nat _ SOrpos eq_refl) (LIT3 896176 8%nat _ SOrend eq_refl)
           (LIT3 896152 8%nat _ (XCC 16%nat 896152 8 895920 eq_refl) eq_refl) (LIT3 896060 4%nat _ (XCC 17%nat 896060 4 4294967295 eq_refl) eq_refl)
           (LIT3 895960 8%nat _ (XCC 18%nat 895960 8 0 eq_refl) eq_refl) (LIT3 895976 8%nat _ (XCC 19%nat 895976 8 0 eq_refl) eq_refl)
           (LIT3 895928 8%nat _ (XCC 20%nat 895928 8 0 eq_refl) eq_refl) (LIT3 895936 8%nat _ (XCC 21%nat 895936 8 0 eq_refl) eq_refl) (cellS 120 24 _ _ Xm24 eq_refl)
           (cellS 112 32 _ _ Xm32 eq_refl)) as
      (fx2 & R4 & MV4 & _ & _ & _ & DMS & _ & _ & _ & _ & _ & Dr10 & _ & _ & Dr17 & _).
    unfold VD in DMS; cbn beta iota in DMS.
    assert (LZ3 : lzinv ASEGS (ahid A model) A model3).
    { apply (lzinv_sbm ASEGS (ahid A model) A model model3 LZ MI3). exact (same_but_materialized_trans _ _ _ SBM1 SBM3). }
    apply (msteps_vis_fx scfg (ahid A model) A fx1 fx2 R3 (Z_to_bv 64 0xc3a54) M3 R4 (Z_to_bv 64 0xbde50) MV4 model3 _ LZ3 DMS).
    intros M5 model5 MI5 SBM5 _.
    pose proof (same_but_materialized_trans _ _ _ (same_but_materialized_trans _ _ _ SBM1 SBM3) SBM5) as SBMT.
    rewrite <- (proj2 (sbm_fds model model5 SBMT)).
    apply (rz_exit_at_lit_lz ASEGS scfg R4 (Z_to_bv 64 0xbde50) M5 rom model5 ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBMT). exact Hh.
    - left. exact Dr17.
    - eapply eq_trans; [exact Dr10|]. cbn [VD]. rewrite Z_to_bv_bv_unsigned. exact G10.
    - exact Hst.
  Qed.

End Exit.
End FPX_1.
