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
  HeapIface HeapIfaceA IcptIfaceAB0 DrvKitA DrvNodesLazyK As0DrvKitA Bo0DrvEntry Bo0Drv_defs Bo0DrvLib Bo0DrvRead Bo0DrvPiece Bo0DiagLoopK Bo0DrvStdio Bo0DrvPrintfK Bo0DrvPrintf1 Bo0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require L5Defs L5KnA L5Core ArtMem BrtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0DrvP_dpXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6495096, 4, 0); (6495131, 1, 0); (6494568, 8, 6494576); (6494560, 4, 1); (6494584, 8, 778276); (6494840, 8, 513736); (6494556, 4, 0); (6494576, 8, 0); (6496256, 8, 0); (896632, 8, 896400); (896540, 4, 4294967295); (896440, 8, 0); (896456, 8, 0); (896408, 8, 0); (896416, 8, 0); (896392, 8, 896160); (896152, 8, 895920); (896060, 4, 4294967295); (895960, 8, 6496272); (895976, 8, 6496272); (895928, 8, 0); (895936, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6363232) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0xdaeb0 <= i < 0xdb070 -> MV (Z_to_bv 64 i) = None).

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section ExitM.
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
    /\ (forall i, 65536 <= i < 884736 -> MV (Z_to_bv 64 i) = None)
    /\ exitMA tid MV.

  Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
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
    assert (HSa : AS0DRVP_dpXm.aligned (V 2%nat) 16) by (cbn [V]; exact HS16).
    assert (CWR : L5Defs.L5.writable ASEGS MV (V 2%nat - 320) 320).
    { cbn [V]. intros d k Hd Hk. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hd Hk; lia. }
    assert (CDF : L5Defs.L5.defined MV (V 2%nat - 320) 320).
    { cbn [V]. intros i Hi. apply (store_ok_defined sp0); [clear - Hsp' HS1 HS2 Hi; lia|]. apply (WIN (S - 320) 320); clear - Hsp' HS1 HS2 Hi; lia. }
    assert (WSG : forall a (n : nat), wseg_ok ASEGS (Z_to_bv 64 a) n = true -> (0 <=? a) && (a + Z.of_nat n <=? 2 ^ 63) = true -> L5Defs.L5.writable ASEGS MV a (Z.of_nat n)).
    { intros a n W Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. exact (wsg_writable sp0 Hsp M0 MV a n W B1 B2). }
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468700) || (2147562966 <=? a) && (a + n <=? 2147563022)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xdaeb0 <=? a) && (a + Z.of_nat n <=? 0xdb070) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V
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
           (XCC 18%nat 895960 8 6496272 eq_refl) (XCC 19%nat 895976 8 6496272 eq_refl) (XCC 20%nat 895928 8 0 eq_refl) (XCC 21%nat 895936 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbe078) M R1 (Z_to_bv 64 0xbde50) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0xbde50) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
