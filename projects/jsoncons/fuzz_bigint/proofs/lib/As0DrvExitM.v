(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim ShapeAlg ShapeLaws SpinAlg Hoare AgentLib Spec AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  HeapIface HeapIfaceA IcptIfaceA DrvKitA DrvNodesLazyK As0DrvKitA As0DrvEntry As0Drv_defs As0DrvLib As0DrvRead As0DrvPiece As0DiagLoopK As0DrvStdio As0DrvPrintfK As0DrvPrintf1 As0DrvExit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require L5Defs L5KnA L5Core ArtMem ArtFsInv.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import As0DrvP_dpXm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XCM_CELLS : list (Z * Z * Z) :=
  [(6492024, 4, 0); (6492059, 1, 0); (6491496, 8, 6491504); (6491488, 4, 1); (6491512, 8, 775184); (6491768, 8, 513096); (6491484, 4, 0); (6491504, 8, 0); (6493184, 8, 0); (893544, 8, 893312); (893452, 4, 4294967295); (893352, 8, 0); (893368, 8, 0); (893320, 8, 0); (893328, 8, 0); (893304, 8, 893072); (893064, 8, 892832); (892972, 4, 4294967295); (892872, 8, 6493200); (892888, 8, 6493200); (892840, 8, 0); (892848, 8, 0)].
Definition exitMA (tid : Z) (MV : word -> option byte) : Prop :=
  cells_at MV XCM_CELLS
  /\ rdn ASEGS MV (Z_to_bv 64 6360160) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) /\ 1 <= tid <= 4194303
  /\ (forall i, 0xda298 <= i < 0xda480 -> MV (Z_to_bv 64 i) = None).

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
    /\ (forall i, 65536 <= i < 880640 -> MV (Z_to_bv 64 i) = None)
    /\ exitMA tid MV.

  Lemma exit_run_m : forall LB LK cr A M (model : Model) R (S st tid : Z),
    exit_preM LB LK cr A M model S tid ->
    let MV := mrestrict (ahid A model) M in
    0 <= st < 256 ->
    getr R 2%bv = Z_to_bv 64 S -> getr R 4%bv = Z_to_bv 64 6360328 -> getr R 10%bv = Z_to_bv 64 st ->
    stdoutPA MV ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xbd464) M rom) model) (t_exit (Z_to_bv 64 st) (m_fs model)).
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
    assert (SHW : forall a n, ((2147468588 <=? a) && (a + n <=? 2147468660) || (2147562580 <=? a) && (a + n <=? 2147562636)) = true -> L5Defs.L5.writable ASEGS MV a n)
      by (intros a n Hb; exact (sh_writable scfg L ar IL HI ICok ILY sp0 Hsp DL M0 _ _ _ _ _ _ a n D Hb)).
    assert (STC : forall (i : nat) a n v, nth_error EX_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (ex_cell_vis scfg L ar C IL HI HIok sp0 Hsp DL Hex M0 _ _ _ _ _ _ a n v D (nth_error_In _ _ Hn))).
    assert (STC1 : forall (i : nat) a v, nth_error EX_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (STC i a 1 v Hn). }
    assert (XCC : forall (i : nat) a n v, nth_error XCM_CELLS i = Some (a, n, v) -> rdn ASEGS MV (Z_to_bv 64 a) (Z.to_nat n) = Some (word_to_le_bytes (Z.to_nat n) (Z_to_bv 64 v)))
      by (intros i a n v Hn; exact (cells_at_nth MV XCM_CELLS i a n v XC Hn)).
    assert (XCC1 : forall (i : nat) a v, nth_error XCM_CELLS i = Some (a, 1, v) -> (0 <=? v) && (v <? 2 ^ 64) = true -> rdn ASEGS MV (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v]).
    { intros i a v Hn Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1. apply Z.ltb_lt in B2. rewrite <- (ArtMem.art_bytes1 v (conj B1 B2)). exact (XCC i a 1 v Hn). }
    assert (DSC : forall a (n : nat) bs, rdn ASEGS (fun _ => None) (Z_to_bv 64 a) n = Some bs -> (0xda298 <=? a) && (a + Z.of_nat n <=? 0xda480) = true -> rdn ASEGS MV (Z_to_bv 64 a) n = Some bs).
    { intros a n bs Hr Hb. apply andb_prop in Hb as (B1 & B2). apply Z.leb_le in B1, B2. apply (img_cell MV a n bs Hr); [lia | lia|]. intros i Hi. apply DESC. lia. }
    destruct (AS0DRVP_dpXm.dpXm_conc fx R MV V
           HS64 HT64 G2 G4 HSr HSa CWR CDF IMGc (WSG 894080 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 894160 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 898032 8%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6491480 1%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6491488 4%nat ltac:(vm_compute; reflexivity) eq_refl) (WSG 6491496 8%nat ltac:(vm_compute; reflexivity) eq_refl)
           (WSG 6492024 4%nat ltac:(vm_compute; reflexivity) eq_refl) (SHW 2147468588 1 eq_refl) (SHW 2147468588 4 eq_refl) (SHW 2147468589 1 eq_refl) (SHW 2147468590 1 eq_refl)
           (SHW 2147468591 1 eq_refl) (SHW 2147468592 4 eq_refl) (SHW 2147468596 1 eq_refl) (SHW 2147468596 4 eq_refl) (SHW 2147468597 1 eq_refl) (SHW 2147468598 1 eq_refl)
           (SHW 2147468599 1 eq_refl) (SHW 2147468600 1 eq_refl) (SHW 2147468601 1 eq_refl) (SHW 2147468602 1 eq_refl) (SHW 2147468603 1 eq_refl) (SHW 2147468604 1 eq_refl)
           (SHW 2147468604 4 eq_refl) (SHW 2147468605 1 eq_refl) (SHW 2147468606 1 eq_refl) (SHW 2147468607 1 eq_refl) (SHW 2147468608 4 eq_refl) (SHW 2147468612 1 eq_refl)
           (SHW 2147468612 4 eq_refl) (SHW 2147468613 1 eq_refl) (SHW 2147468614 1 eq_refl) (SHW 2147468615 1 eq_refl) (SHW 2147468620 1 eq_refl) (SHW 2147468620 4 eq_refl)
           (SHW 2147468621 1 eq_refl) (SHW 2147468622 1 eq_refl) (SHW 2147468623 1 eq_refl) (SHW 2147468624 4 eq_refl) (SHW 2147468628 1 eq_refl) (SHW 2147468628 4 eq_refl)
           (SHW 2147468629 1 eq_refl) (SHW 2147468630 1 eq_refl) (SHW 2147468631 1 eq_refl) (SHW 2147468632 1 eq_refl) (SHW 2147468632 4 eq_refl) (SHW 2147468633 1 eq_refl)
           (SHW 2147468634 1 eq_refl) (SHW 2147468635 1 eq_refl) (SHW 2147468636 4 eq_refl) (SHW 2147468640 1 eq_refl) (SHW 2147468640 4 eq_refl) (SHW 2147468641 1 eq_refl)
           (SHW 2147468642 1 eq_refl) (SHW 2147468643 1 eq_refl) (SHW 2147468644 1 eq_refl) (SHW 2147468644 4 eq_refl) (SHW 2147468645 1 eq_refl) (SHW 2147468646 1 eq_refl)
           (SHW 2147468647 1 eq_refl) (SHW 2147468648 4 eq_refl) (SHW 2147468652 1 eq_refl) (SHW 2147468652 4 eq_refl) (SHW 2147468653 1 eq_refl) (SHW 2147468654 1 eq_refl)
           (SHW 2147468655 1 eq_refl) (SHW 2147468656 1 eq_refl) (SHW 2147468657 1 eq_refl) (SHW 2147468658 1 eq_refl) (SHW 2147468659 1 eq_refl) (SHW 2147562580 1 eq_refl)
           (SHW 2147562580 4 eq_refl) (SHW 2147562581 1 eq_refl) (SHW 2147562582 1 eq_refl) (SHW 2147562583 1 eq_refl) (SHW 2147562584 4 eq_refl) (SHW 2147562588 4 eq_refl)
           (SHW 2147562592 4 eq_refl) (SHW 2147562596 4 eq_refl) (SHW 2147562600 4 eq_refl) (SHW 2147562604 4 eq_refl) (SHW 2147562608 4 eq_refl) (SHW 2147562612 4 eq_refl)
           (SHW 2147562616 4 eq_refl) (SHW 2147562620 4 eq_refl) (SHW 2147562624 4 eq_refl) (SHW 2147562628 4 eq_refl) (SHW 2147562632 1 eq_refl) (SHW 2147562632 4 eq_refl)
           (SHW 2147562633 1 eq_refl) (SHW 2147562634 1 eq_refl) (SHW 2147562635 1 eq_refl) TIDC HTr (XCC 0%nat 6492024 4 0 eq_refl) (XCC1 1%nat 6492059 0 eq_refl eq_refl)
           (XCC 2%nat 6491496 8 6491504 eq_refl) (XCC 3%nat 6491488 4 1 eq_refl) (XCC 4%nat 6491512 8 775184 eq_refl) (XCC 5%nat 6491768 8 513096 eq_refl)
           (XCC 6%nat 6491484 4 0 eq_refl) (STC1 10%nat 1505760 0 eq_refl eq_refl) (XCC 7%nat 6491504 8 0 eq_refl) (STC1 3%nat 894160 0 eq_refl eq_refl)
           (STC 0%nat 882312 8 882312 eq_refl) (STC 2%nat 894080 8 1 eq_refl) (STC 4%nat 897872 4 1 eq_refl) (STC 5%nat 898032 8 0 eq_refl) (STC1 8%nat 911384 1 eq_refl eq_refl)
           (STC 7%nat 908088 8 2147450880 eq_refl) (DSC 893600 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141664)) ltac:(img_rd) eq_refl)
           (DSC 893616 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl) (STC1 6%nat 906140 1 eq_refl eq_refl)
           (DSC 893616 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl) (STC 9%nat 1504992 8 18446744073709551615 eq_refl) (STC 1%nat 882712 8 834348 eq_refl)
           (DSC 893656 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893664 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141760)) ltac:(img_rd) eq_refl) (DSC 893680 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 893680 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 893720 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893728 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141792)) ltac:(img_rd) eq_refl) (DSC 893744 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 893744 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 893784 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893792 8%nat (word_to_le_bytes 8 (Z_to_bv 64 141920)) ltac:(img_rd) eq_refl) (DSC 893808 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 893808 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 893848 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893856 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142016)) ltac:(img_rd) eq_refl) (DSC 893872 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 893872 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 893912 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893920 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142112)) ltac:(img_rd) eq_refl) (DSC 893936 1%nat [Z_to_bv 8 96] ltac:(img_rd) eq_refl)
           (DSC 893936 8%nat (word_to_le_bytes 8 (Z_to_bv 64 96)) ltac:(img_rd) eq_refl)
           (DSC 893976 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl)
           (DSC 893984 8%nat (word_to_le_bytes 8 (Z_to_bv 64 142208)) ltac:(img_rd) eq_refl) (DSC 894000 1%nat [Z_to_bv 8 32] ltac:(img_rd) eq_refl)
           (DSC 894000 8%nat (word_to_le_bytes 8 (Z_to_bv 64 32)) ltac:(img_rd) eq_refl)
           (DSC 894040 8%nat (word_to_le_bytes 8 (Z_to_bv 64 18446744073709551615)) ltac:(img_rd) eq_refl) (XCC 8%nat 6493184 8 0 eq_refl) (XCC 9%nat 893544 8 893312 eq_refl)
           (XCC 10%nat 893452 4 4294967295 eq_refl) (XCC 11%nat 893352 8 0 eq_refl) (XCC 12%nat 893368 8 0 eq_refl) (XCC 13%nat 893320 8 0 eq_refl) (XCC 14%nat 893328 8 0 eq_refl)
           (XCC 15%nat 893304 8 893072 eq_refl) SOlock SOwpos SOwbase SOrpos SOrend (XCC 16%nat 893064 8 892832 eq_refl) (XCC 17%nat 892972 4 4294967295 eq_refl)
           (XCC 18%nat 892872 8 6493200 eq_refl) (XCC 19%nat 892888 8 6493200 eq_refl) (XCC 20%nat 892840 8 0 eq_refl) (XCC 21%nat 892848 8 0 eq_refl)) as
      (fx1 & R1 & MV1 & XGR & _ & _ & XMS & XKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Xr17 & _).
    unfold V in XMS; cbn beta iota in XMS.
    pose proof (dinv_lzinv scfg L ar C IL HI HIok sp0 DL M0 _ _ _ _ _ _ D) as LZ. pose proof LZ as (_ & _ & _ & _ & Hh).
    apply (msteps_vis_fx scfg (ahid A model) A fx fx1 R (Z_to_bv 64 0xbd464) M R1 (Z_to_bv 64 0xbd23c) MV1 model _ LZ XMS).
    intros M' model' MI' SBM' _.
    rewrite <- (proj2 (sbm_fds model model' SBM')).
    apply (rz_exit_at_lit_lz ASEGS scfg R1 (Z_to_bv 64 0xbd23c) M' rom model' ECALLW st fetch_exitA is_ecall_ECALLW).
    - rewrite (sbm_halted_eq _ _ SBM'). exact Hh.
    - left. exact Xr17.
    - eapply eq_trans; [exact (XKS 10%nat ltac:(unfold AS0DRVP_dpXm.KS_dpXm; cbn [In]; repeat first [left; reflexivity | right]))|]. exact G10.
    - exact Hst.
  Qed.
End ExitM.
End FPX_1.
