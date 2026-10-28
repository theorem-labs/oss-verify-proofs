(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_libc_iface AZ_kx AZ_xxh_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

(* [comment removed for export] *)
Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      match goal with
      | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
      | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
      | H : rw_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
      | H : ro_cells segs m ?A0 ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
      | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
      | _ => (* [comment removed for export] *)
          let A' := eval lazy in A in
          lazymatch A' with
          | Z0 => idtac | Zpos _ => idtac
          | _ => fail 0 "kx_rd_at: no chunk hypothesis justifies the region at" A
          end;
          apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
      end
  end.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma xu_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
Qed.
Lemma xu_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) A B. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.

(* [comment removed for export] *)
Definition xu_held (P : Prop) : Prop := P.

Section XU.
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.
  Variables (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : amem) (SPV S8 IN lo : Z) (inb : list byte).
  Notation len := (zlen inb).
  Notation STA := (8 * S8).
  Notation W := [(STA, STA + 88); (SPV - 2352, SPV)].
  Hypothesis R0 : 0x625000 <= STA.
  Hypothesis R1 : STA + 88 <= 2^47.
  Hypothesis SA : STA + 88 <= 0x7fff7000 \/ 0x10007fff8000 <= STA.
  Hypothesis KLO : 17594333495296 <= lo.
  Hypothesis LOS : lo <= SPV - 2352.
  Hypothesis SPV47 : SPV < 2^47.
  Hypothesis SS : STA + 88 <= lo \/ SPV <= STA.
  Hypothesis RS : rng RNG STA 88.
  Hypothesis RSS : rng RNG (2147450880 + S8) 11.
  Hypothesis RSTK : rng RNG lo (SPV - lo).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis AHS : ahull RNG m STA 88.
  Hypothesis US : unpoisoned m STA (STA + 88).

  Notation POST := (zd_xxh_update_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m).
  (* [comment removed for export] *)
  Notation STpc pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  (* [comment removed for export] *)
  Definition FIN (m1 : amem) (w8 w16 : word) : Prop :=
    (exists j0, rw_cells bsegs m1 (SPV + -128) [CB 8 j0; C8 w8; C8 w16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ stk bsegs m1 lo (SPV + -128) /\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ art m1.

  (* [comment removed for export] *)
  Lemma US_of : forall m1, munch W m m1 -> unpoisoned m1 STA (STA + 88).
  Proof.
    intros m1 MU1. eapply unpoisoned_munch; [exact US| exact MU1|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
    clear - SA KLO LOS SPV47 R0 R1. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma ZW_of : forall m1, munch W m m1 -> forall i, 0 <= i < 11 -> m1 (wa (2147450880 + S8 + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros m1 MU1. pose proof (unp_zero_win m1 S8 88 (US_of m1 MU1)) as ZW. unfold ASHOFF in ZW. change (88 / 8) with 11 in ZW. exact ZW.
  Qed.

  (* [comment removed for export] *)
  Lemma xu_epi : forall m1 w8 w16 csh jm msz' j2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FIN m1 w8 w16 -> rw_cells bsegs m1 STA csh -> cells_size csh = 40%nat ->
    rw_cells bsegs m1 (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 msz'); CB 12 j2] -> 0 <= msz' < 32 ->
    evtF bsegs RNG POST (STpc 0xafad0 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros ([j0 FR1] & ST1 & MU1 & WM1 & MI1 & (GOT & RIC & SHB & INI & LAY & REAL)) HC HSZ MTC RM.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    change (xu_held (rw_cells bsegs m1 STA csh)) in HC.
    lazymatch type of MTC with ?T => change (xu_held T) in MTC end.
    kx_autoFLAx [KAApp (SPV - 128) 128] [] 30%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZWr (SPV - 128) 128]
      [(SPV - 128, 128)] [(SPV - 128, 128)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: kx_mem.
    all: kx_abs.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -128) _, STc : stk _ ?mc ?l (?S + -128) |- _ => release_frame FRc STc S end.
    all: kx_mkR_fold.
    all: apply evtF_done; unfold zd_xxh_update_postA.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => do 14 eexists; exists mc, msz' end.
    all: split; [reflexivity|].
    all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
    all: split; [| exact RM].
    all: unfold xu_held in HC, MTC.
    all: assert (ALL : rw_cells bsegs m1 STA (csh ++ [CB 32 jm; C4 (Z_to_bv 64 msz'); CB 12 j2]))
      by (apply (proj2 (ZdWalkKit.rw_cells_app _ _ _ _ _)); split; [exact HC|]; rewrite HSZ; exact MTC).
    all: change (csh ++ [CB 32 jm; C4 (Z_to_bv 64 msz'); CB 12 j2]) with (csh ++ [CB 32 jm] ++ [C4 (Z_to_bv 64 msz'); CB 12 j2]) in ALL.
    all: rewrite app_assoc in ALL.
    all: apply (rw_cells_merge bsegs m1 STA [] (csh ++ [CB 32 jm]) _) in ALL; cbn [app] in ALL.
    all: rewrite cells_size_app, HSZ in ALL; change (40 + cells_size [CB 32 jm])%nat with 72%nat in ALL.
    all: unfold xxh_state, xxh_cells; do 2 eexists; exact ALL.
  Qed.

  (* [comment removed for export] *)
  Lemma mtc_split : forall mm jm v j2, rw_cells bsegs mm (STA + 40) [CB 32 jm; C4 v; CB 12 j2] ->
    rw_cells bsegs mm (STA + 40) [CB 32 jm] /\ rw_cells bsegs mm (STA + 72) [C4 v; CB 12 j2].
  Proof.
    intros mm jm v j2 H. apply (proj1 (ZdWalkKit.rw_cells_app _ _ _ [CB 32 _] _)) in H. destruct H as [H1 H2].
    cbn [cells_size csize Nat.add] in H2. replace (STA + 40 + Z.of_nat 32) with (STA + 72) in H2 by lia. split; assumption.
  Qed.
  Lemma mtc_join : forall mm jm v j2, rw_cells bsegs mm (STA + 40) [CB 32 jm] -> rw_cells bsegs mm (STA + 72) [C4 v; CB 12 j2] ->
    rw_cells bsegs mm (STA + 40) [CB 32 jm; C4 v; CB 12 j2].
  Proof.
    intros mm jm v j2 H1 H2. apply (proj2 (ZdWalkKit.rw_cells_app _ _ _ [CB 32 _] _)). split; [exact H1|].
    cbn [cells_size csize Nat.add]. replace (STA + 40 + Z.of_nat 32) with (STA + 72) by lia. exact H2.
  Qed.

  Section NONNULL.
  Hypothesis INB : bytes_at bsegs m IN inb.
  Hypothesis RIN : 4096 <= IN.
  Hypothesis RIN2 : IN + len <= 2^47.
  Hypothesis DSI : STA + 88 <= IN \/ IN + len <= STA.
  Hypothesis DIS : IN + len <= lo \/ SPV <= IN.
  Hypothesis ABI : ablk IN (IN + len).
  Hypothesis UI : unpoisoned m IN (IN + len).
  Hypothesis RGI : rng RNG IN len.
  Hypothesis RGIS : rng RNG (shad IN) (shspan IN len).
  Hypothesis AHI : ahull RNG m IN len.
  Lemma BI0 : IN + len <= 0x7fff7000 \/ 0x10007fff8000 <= IN. Proof. unfold ablk, AIMG_HI, KLS in ABI; lia. Qed.
  Lemma BIL0 : 0x625000 <= IN. Proof. pose proof ABI as H. unfold ablk, AIMG_HI, KLS in H; lia. Qed.

  Lemma inb_suffix : forall mm p, bytes_at bsegs mm IN inb -> 0 <= p <= len ->
    bytes_at bsegs mm (IN + p) (skipn (Z.to_nat p) inb) /\ length (skipn (Z.to_nat p) inb) = Z.to_nat (len - p).
  Proof.
    intros mm p H Hp. rewrite <- (firstn_skipn (Z.to_nat p) inb) in H.
    apply (proj1 (bytes_at_app bsegs mm IN _ _)) in H. destruct H as [_ H].
    rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia. split; [exact H|]. rewrite length_skipn. lia.
  Qed.
  Lemma inb_prefix : forall mm k, bytes_at bsegs mm IN inb -> 0 <= k <= len ->
    bytes_at bsegs mm IN (firstn (Z.to_nat k) inb) /\ length (firstn (Z.to_nat k) inb) = Z.to_nat k.
  Proof.
    intros mm k H Hk. rewrite <- (firstn_skipn (Z.to_nat k) inb) in H.
    apply (proj1 (bytes_at_app bsegs mm IN _ _)) in H. destruct H as [H _]. split; [exact H|]. apply firstn_length_le. lia.
  Qed.
  Lemma inb_sub : forall mm p k, bytes_at bsegs mm IN inb -> 0 <= p -> 0 <= k -> p + k <= len ->
    exists bs, bytes_at bsegs mm (IN + p) bs /\ zlen bs = k.
  Proof.
    intros mm p k H Hp Hk Hpk. destruct (inb_suffix mm p H ltac:(lia)) as [S SL].
    rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat p) inb)) in S.
    apply (proj1 (bytes_at_app bsegs mm (IN + p) _ _)) in S. destruct S as [S _].
    eexists. split; [exact S|]. rewrite firstn_length_le by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Definition INF (m1 : amem) : Prop := bytes_at bsegs m1 IN inb /\ unpoisoned m1 IN (IN + len) /\ ahull RNG m1 IN len.
  Lemma INF_of : forall m1, munch W m m1 -> wmono bsegs m m1 -> INF m1.
  Proof.
    intros m1 MU1 WM1. split; [| split].
    - eapply bytes_at_transport; [exact INB| exact MU1|]. cbn [disjoint_from]. assert (Z.of_nat (length inb) = len) by reflexivity. lia.
    - pose proof BI0 as BI. pose proof BIL0 as BIL.
      eapply unpoisoned_munch; [exact UI| exact MU1|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
      clear - SA KLO LOS SPV47 R0 R1 BI BIL RIN RIN2. repeat split; Z.div_mod_to_equations; lia.
    - eapply xu_ahull_wmono; [exact AHI| exact WM1].
  Qed.

  (* [comment removed for export] *)
  Lemma xu_tail : forall m1 w8 w16 wt w0 w1 w2 w3 jm j2 p x1 x5 x7 x9 x10 x12 x13 x15 x16 x17 x22 x25 x26 x27 x28 x29 x30 x31,
    FIN m1 w8 w16 ->
    rw_cells bsegs m1 STA [C8 wt; C8 w0; C8 w1; C8 w2; C8 w3] ->
    rw_cells bsegs m1 (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 0); CB 12 j2] ->
    0 <= p <= len -> len - p < 32 ->
    evtF bsegs RNG POST (STpc 0xafab0 m1 x1 x5 (Z_to_bv 64 (STA + 40)) x7 (Z_to_bv 64 (STA + 72)) x9 x10 (Z_to_bv 64 (IN + p)) x12 x13 (Z_to_bv 64 (IN + len))
                           x15 x16 x17 (Z_to_bv 64 (STA + 8)) (Z_to_bv 64 (STA + 16)) (Z_to_bv 64 (STA + 24)) (Z_to_bv 64 (STA + 32)) x22 (Z_to_bv 64 (S8 + 2147450889)) (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros FI HC MTC RP RL.
    pose proof FI as ([j0 FR1] & ST1 & MU1 & WM1 & MI1 & (GOT & RIC & SHB & INI & LAY & REAL)).
    destruct (INF_of m1 MU1 WM1) as (INB1 & UI1 & AHI1). pose proof (US_of m1 MU1) as US1. pose proof (ZW_of m1 MU1) as ZW.
    pose proof BI0 as BI. pose proof BIL0 as BIL.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xafad0] 40%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange p 0 (2^47); KZRange (IN + p) 4096 (2^47);
       KZWr (SPV - 128) 128; KZWr STA 40; KZWr (STA + 40) 48; KZZero (2147450880 + S8) 11;
       KZDisj (SPV - 128) 128 STA 88]
      [(SPV - 128, 128); (STA, 40); (STA + 40, 48)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    { eapply (xu_epi m1); [exact FI| exact HC| reflexivity| exact MTC| lia]. }
    destruct (inb_suffix m1 p INB1 ltac:(lia)) as [SUF SUFL].
    destruct (mtc_split _ _ _ _ MTC) as [MC TC]. clear MTC.
    destruct (cb_carve bsegs m1 (STA + 40) 32 jm 0 (len - p) MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
    replace (STA + 40 + 0) with (STA + 40) in * by lia.
    replace (-1 * p + len) with (len - p) by lia.
    call (MEMCPY RNG (STA + 40) (IN + p) (len - p) (SPV + -128)).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- bytes_at _ _ (IN + _) _ => exact SUF
         | |- length _ = _ => exact SUFL
         | |- rw_cells _ _ (STA + 40) _ => exact M2
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => exact ST1
         | |- app_blk (IN + _) _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABI| lia| lia]| lia]
         | |- app_blk (STA + 40) _ => unfold app_blk, KLOW, KHIGH, KEND; clear - SA R0 R1 RP RL; lia
         | |- aro _ _ (IN + _) _ => split; [eapply unpoisoned_sub; [exact UI1| lia| lia]| split; [eapply rng_sub'; [exact RGI| lia]| eapply rng_sub'; [exact RGIS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RP RL RIN; Z.div_mod_to_equations; lia]]]
         | |- aro _ _ (STA + 40) _ => split; [eapply unpoisoned_sub; [exact US1| lia| lia]| split; [eapply rng_sub'; [exact RS| lia]| eapply rng_sub'; [exact RSS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RP RL; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ (IN + _) _ => eapply xu_ahull_sub; [exact AHI1| lia| lia]
         | |- ahull _ _ (STA + 40) _ => eapply xu_ahull_sub; [eapply xu_ahull_wmono; [exact AHS| exact WM1]| lia| lia]
         | |- art _ => split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]]
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LOS; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => clear - DSI DIS SS LOS KLO RP RL R0 R1 RIN RIN2 SPV47; lia
         | |- _ => clear - LOS KLO RP RL R0 R1 RIN RIN2 SPV47 SA; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    clear KXE KXA KXRD KXK ZW US1 UI1 AHI1 SUF.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end. rename PC into ST2. rename PC0 into M2'.
    replace (STA + 40) with (STA + 40 + 0) in M2' by lia.
    replace (STA + 40 + (len - p)) with (STA + 40 + 0 + (len - p)) in M3 by lia.
    destruct (cb_uncarve bsegs _ (STA + 40) 32 0 (len - p) _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
    pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2. clear M1 M2' M3 MC2 TC.
    pose proof (ZW_of m2 MU1) as ZW. pose proof (US_of m2 MU1) as US2.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xafad0] 40%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange p 0 (2^47); KZRange len 0 (2^47);
       KZWr (SPV - 128) 128; KZWr (STA + 72) 16; KZZero (2147450880 + S8) 11;
       KZDisj (SPV - 128) 128 STA 88]
      [(SPV - 128, 128)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: kx_mem.
    replace (-1 * p + len) with (len - p) in MTC2 by lia.
    eapply (xu_epi m0 w8 w16); [| exact HC| reflexivity| exact MTC2| lia].
    split; [eexists; exact FR1|]. split; [exact ST2|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact KXMI|].
    split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
  Qed.

  (* [comment removed for export] *)
  Lemma xu_loop : forall (n : nat) m1 P0 Q wt w0 w1 w2 w3 jm j2 x1 x7 x10 x12 x14 x22 x23 x25 x26 x27 x28 x30 x31,
    IN + len - Q <= Z.of_nat n ->
    FIN m1 (Z_to_bv 64 (STA + 40)) (Z_to_bv 64 (S8 + 2147450889)) ->
    rw_cells bsegs m1 STA [C8 wt; C8 w0; C8 w1; C8 w2; C8 w3] ->
    rw_cells bsegs m1 (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 0); CB 12 j2] ->
    IN <= P0 -> P0 <= Q -> Q + 32 <= IN + len ->
    evtF bsegs RNG POST (STpc 0xaf79c m1 x1 (Z_to_bv 64 (Q - P0)) (Z_to_bv 64 (IN + len - 32)) x7 (Z_to_bv 64 (STA + 72)) (Z_to_bv 64 (IN + len)) x10
                           (Z_to_bv 64 P0) x12 (Z_to_bv 64 (S8 + 2147450881)) x14 (Z_to_bv 64 (S8 + 2147450882)) (Z_to_bv 64 (S8 + 2147450883)) (Z_to_bv 64 (S8 + 2147450884))
                           (Z_to_bv 64 (STA + 8)) (Z_to_bv 64 (STA + 16)) (Z_to_bv 64 (STA + 24)) (Z_to_bv 64 (STA + 32))
                           x22 x23 (Z_to_bv 64 2147450880) x25 x26 x27 x28 (Z_to_bv 64 (2147450880 + Q / 8)) x30 x31).
  Proof.
    induction n as [|n IH]; intros until x31; intros RN FI HC MTC RP0 RPQ RQL; [exfalso; lia|].
    pose proof FI as ([j0 FR1] & ST1 & MU1 & WM1 & MI1 & (GOT & RIC & SHB & INI & LAY & REAL)).
    destruct (INF_of m1 MU1 WM1) as (INB1 & UI1 & AHI1). pose proof (US_of m1 MU1) as US1. pose proof (ZW_of m1 MU1) as ZW.
    pose proof BI0 as BI. pose proof BIL0 as BIL.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    destruct (inb_sub m1 (Q - IN) 32 INB1 ltac:(lia) ltac:(lia) ltac:(lia)) as (qb & QB & QBL).
    replace (IN + (Q - IN)) with Q in QB by lia.
    assert (QBL' : Z.of_nat (length qb) = 32) by exact QBL.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88; KAUnp Q 32; KAShp (2147450880 + Q / 8) Q] [0xaf79c; 0xafab0] 300%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange P0 4096 (2^47); KZRange Q 4096 (2^47 - 32); KZRange (Q - P0) 0 (2^47);
       KZWr (SPV - 128) 128; KZWr STA 40; KZZero (2147450880 + S8) 11;
       KZDisj (SPV - 128) 128 STA 88; KZDisj STA 88 Q 32; KZDisj (SPV - 128) 128 Q 32]
      [(SPV - 128, 128); (STA, 40); (STA + 40, 48); (Q, 32)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11); (Q, 32)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: kx_mem.
    (* [comment removed for export] *)
    all: repeat match goal with
         | |- context [Z_to_bv 64 ?e] =>
             lazymatch e with context [_ * bv_unsigned _] => let w := fresh "hv" in set (w := Z_to_bv 64 e) in *; clearbody w end
         end.
    (* [comment removed for export] *)
    all: repeat match goal with
         | H : context [Z_to_bv 64 ?e] |- _ =>
             lazymatch e with context [_ * bv_unsigned _] => let w := fresh "hv" in set (w := Z_to_bv 64 e) in *; clearbody w end
         end.
    all: clear KXE KXA KXRD KXK.
    - (* [comment removed for export] *)
      replace (Q + -1 * P0 + 32) with (Q + 32 - P0) by lia.
      replace (Q / 8 + 2147450884) with (2147450880 + (Q + 32) / 8) by (Z.div_mod_to_equations; lia).
      eapply (IH m0 P0 (Q + 32)); [lia| | exact HC| exact MTC| lia| lia| lia].
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact KXMI|].
      split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
    - (* [comment removed for export] *)
      replace (Q + 32) with (IN + (Q + 32 - IN)) by lia.
      eapply (xu_tail m0 (Z_to_bv 64 (STA + 40)) (Z_to_bv 64 (S8 + 2147450889))); [| exact HC| exact MTC| lia| lia].
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact KXMI|].
      split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
  Qed.

  (* [comment removed for export] *)
  Lemma xu_mid : forall m1 w8 p wt w0 w1 w2 w3 jm j2 x1 x5 x7 x9 x10 x12 x13 x15 x16 x17 x25 x26 x27 x28 x29 x30 x31,
    FIN m1 w8 (Z_to_bv 64 (S8 + 2147450889)) ->
    rw_cells bsegs m1 STA [C8 wt; C8 w0; C8 w1; C8 w2; C8 w3] ->
    rw_cells bsegs m1 (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 0); CB 12 j2] ->
    0 <= p <= len ->
    evtF bsegs RNG POST (STpc 0xaf728 m1 x1 x5 (Z_to_bv 64 (STA + 40)) x7 (Z_to_bv 64 (STA + 72)) x9 x10
                           (Z_to_bv 64 (IN + p)) x12 x13 (Z_to_bv 64 IN) x15 x16 x17 (Z_to_bv 64 (STA + 8)) (Z_to_bv 64 (STA + 16)) (Z_to_bv 64 (STA + 24))
                           (Z_to_bv 64 (STA + 32)) (Z_to_bv 64 len) (Z_to_bv 64 (S8 + 2147450889)) (Z_to_bv 64 2147450880) x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31. intros FI HC MTC RP.
    pose proof FI as ([j0 FR1] & ST1 & MU1 & WM1 & MI1 & (GOT & RIC & SHB & INI & LAY & REAL)).
    destruct (INF_of m1 MU1 WM1) as (INB1 & UI1 & AHI1). pose proof (US_of m1 MU1) as US1. pose proof (ZW_of m1 MU1) as ZW.
    pose proof BI0 as BI. pose proof BIL0 as BIL.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xaf79c; 0xafab0] 80%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange p 0 (2^47); KZRange (IN + p) 4096 (2^47);
       KZWr (SPV - 128) 128; KZWr (STA + 72) 16; KZZero (2147450880 + S8) 11;
       KZDisj (SPV - 128) 128 STA 88]
      [(SPV - 128, 128); (STA, 40); (STA + 40, 48)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: kx_mem.
    all: clear KXE KXA KXRD KXK.
    - (* [comment removed for export] *)
      eapply (xu_tail m1 w8 (Z_to_bv 64 (S8 + 2147450889))); [exact FI| exact HC| exact MTC| lia| lia].
    - (* [comment removed for export] *)
      rewrite (Z.mod_small (IN + p) (2^64)) by lia.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 ((IN + p) - (IN + p))) by (f_equal; lia).
      replace (IN + len + -32) with (IN + len - 32) by lia.
      replace ((IN + p) / 8 + 2147450880) with (2147450880 + (IN + p) / 8) by lia.
      (* [comment removed for export] *)
      eapply (xu_loop (Z.to_nat (len - p)) m0 (IN + p) (IN + p)); [lia| | exact HC| exact MTC| lia| lia| lia].
      split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact KXMI|].
      split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
  Qed.


  (* [comment removed for export] *)
  Lemma xu_fill : forall m2 wt jv jm j2 msz w8 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    FIN m2 w8 (Z_to_bv 64 (S8 + 2147450889)) ->
    rw_cells bsegs m2 STA [C8 wt; CB 32 jv] ->
    rw_cells bsegs m2 (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 msz); CB 12 j2] ->
    0 < msz < 32 -> 32 - msz <= len ->
    evtF bsegs RNG POST (STpc 0xaf414 m2 x1 x5 x6 x7 (Z_to_bv 64 (STA + 40)) (Z_to_bv 64 (STA + 72)) x10 x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 (STA + 8)) (Z_to_bv 64 (STA + 16)) (Z_to_bv 64 (STA + 24)) (Z_to_bv 64 (STA + 32))
                           (Z_to_bv 64 len) (Z_to_bv 64 IN) (Z_to_bv 64 2147450880) (Z_to_bv 64 14029467366897019727) (Z_to_bv 64 11400714785074694791) (Z_to_bv 64 STA) x28 x29 x30 x31).
  Proof.
    intros until x31. intros FI HC MTC RM RML.
    pose proof FI as ([j0 FR1] & ST1 & MU1 & WM1 & MI1 & (GOT & RIC & SHB & INI & LAY & REAL)).
    pose proof (US_of m2 MU1) as US2. pose proof (ZW_of m2 MU1) as ZW.
    pose proof BI0 as BI. pose proof BIL0 as BIL.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xaf728] 250%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange msz 1 31;
       KZWr (SPV - 128) 128; KZWr STA 40; KZWr (STA + 40) 48; KZZero (2147450880 + S8) 11;
       KZDisj (SPV - 128) 128 STA 88]
      [(SPV - 128, 128); (STA, 40); (STA + 40, 48)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: kx_mem.
    all: clear KXA KXRD KXK.
    all: repeat match goal with
         | H : context [Z_to_bv 64 ?e] |- _ =>
             lazymatch e with context [_ * bv_unsigned _] => let w := fresh "hv" in set (w := Z_to_bv 64 e) in *; clearbody w end
         end.
    all: repeat match goal with
         | |- context [ev ?E ?j] => let w := fresh "rv" in set (w := ev E j) in *; clearbody w
         | H : context [ev ?E ?j] |- _ => let w := fresh "rv" in set (w := ev E j) in *; clearbody w
         end.
    all: clear KXE.
    replace (IN + -1 * msz + 32) with (IN + (32 - msz)) by lia.
    eapply (xu_mid m0 w8 (32 - msz)); [| exact HC| exact MTC| lia].
    split; [eexists; exact FR1|]. split; [exact ST1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact KXMI|].
    split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xu_nonnull : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msz jt jv jm j2,
    rw_cells bsegs m STA [CB 8 jt; CB 32 jv] -> rw_cells bsegs m (STA + 40) [CB 32 jm; C4 (Z_to_bv 64 msz); CB 12 j2] -> 0 <= msz < 32 ->
    stk bsegs m lo SPV -> mem_inv bsegs m -> art m ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STA) (Z_to_bv 64 IN) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_XXH_UPDATE) fc None m (seg_rom bsegs)).
  Proof.
    intros until j2. intros HC MTC RM ST MI (GOT & RIC & SHB & INI & LAY & REAL).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof BI0 as BI. pose proof BIL0 as BIL.
    pose proof (ZW_of m (munch_refl W m)) as ZW.
    assert (MU : munch W m m) by apply munch_refl.
    assert (WM : wmono bsegs m m) by apply wmono_refl.
    carve_frame 128%nat ST.
    unfold APZD_XXH_UPDATE.
    (* [comment removed for export] *)
    change (xu_held (bytes_at bsegs m IN inb)) in INB.
    kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xaf728] 140%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange IN 4096 (2^47); KZRange len 0 (2^47);
       KZRange (IN + len) 4096 (2^47); KZRange msz 0 31; KZAlign STA 8;
       KZWr (SPV - 128) 128; KZWr STA 40; KZWr (STA + 40) 48; KZZero (2147450880 + S8) 11; KZImg 0x10338 0x10340; KZImg 0x103e0 0x103e8;
       KZDisj (SPV - 128) 128 STA 88]
      [(SPV - 128, 128); (STA, 40); (STA + 40, 48)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: try (split; [lia|]; split; [lia| exact ZW]).
    all: kx_mem.
    all: clear KXA KXRD KXK.
    all: repeat match goal with
         | |- context [ev ?E ?j] => let w := fresh "rv" in set (w := ev E j) in *; clearbody w
         | H : context [ev ?E ?j] |- _ => let w := fresh "rv" in set (w := ev E j) in *; clearbody w
         end.
    all: clear KXE.
    all: unfold xu_held in INB.
    (* [comment removed for export] *)
    all: match type of FR with rw_cells _ _ _ (CB ?k ?jj :: _) => set (j00 := jj) in FR; clearbody j00 end.
    3: apply (rw_cells_split_CB bsegs _ _ [] 24 j00 _ [8; 8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR;
         destruct (cb8_as_c8 bsegs _ _ [CB 8 _] _ _ FR) as [w8 FR2]; cbn [app] in FR2; clear FR;
         destruct (cb8_as_c8 bsegs _ _ [CB 8 _; C8 w8] _ _ FR2) as [w16 FR']; cbn [app] in FR'; clear FR2.
    1,2: apply (rw_cells_split_CB bsegs _ _ [] 16 j00 _ [8; 8]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR; destruct (cb8_as_c8 bsegs _ _ [CB 8 _] _ _ FR) as [w8 FR']; cbn [app] in FR'; clear FR.   (* [comment removed for export] *)
    all: match type of FR' with rw_cells _ _ _ [_; C8 ?a; C8 ?b; _; _; _; _; _; _; _; _; _; _; _; _; _] =>
           assert (FI : FIN m0 a b) by
            (split; [eexists; exact FR'|]; split; [exact ST|]; split; [exact MU|]; split; [exact WM|]; split; [exact KXMI|];
             split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]]) end.
    all: destruct (INF_of m0 MU WM) as (INB1 & UI1 & AHI1); pose proof (US_of m0 MU) as US1.
    3: { (* [comment removed for export] *)
      assert (PREL : length inb = Z.to_nat len) by (rewrite Nat2Z.id; reflexivity).
      destruct (mtc_split _ _ _ _ MTC) as [MC TC]. clear MTC.
      destruct (cb_carve bsegs _ (STA + 40) 32 jm msz len MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
      replace (STA + msz + 40) with (STA + 40 + msz) by lia.
      call (MEMCPY RNG (STA + 40 + msz) IN len (SPV + -128)).
      all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- bytes_at _ _ IN _ => exact INB1
         | |- length _ = _ => exact PREL
         | |- rw_cells _ _ (STA + 40 + _) _ => exact M2
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => exact ST
         | |- app_blk IN _ => apply ablk_app_blk; [exact ABI| lia]
         | |- app_blk (STA + 40 + _) _ => unfold app_blk, KLOW, KHIGH, KEND; clear - SA R0 R1 RM KXBR; lia
         | |- aro _ _ IN _ => split; [exact UI1| split; [exact RGI| exact RGIS]]
         | |- aro _ _ (STA + 40 + _) _ => split; [eapply unpoisoned_sub; [exact US1| lia| lia]| split; [eapply rng_sub'; [exact RS| lia]| eapply rng_sub'; [exact RSS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RM KXBR; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ IN _ => exact AHI1
         | |- ahull _ _ (STA + 40 + _) _ => eapply xu_ahull_sub; [eapply xu_ahull_wmono; [exact AHS| exact WM]| lia| lia]
         | |- art _ => split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]]
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LOS; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => clear - DSI DIS SS LOS KLO RM KXBR R0 R1 RIN RIN2 SPV47; lia
         | |- _ => clear - LOS KLO RM KXBR R0 R1 RIN RIN2 SPV47 SA; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
      clear ZW UI1 AHI1 INB1.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end. rename PC into ST2. rename PC0 into M2'.
      destruct (cb_uncarve bsegs _ (STA + 40) 32 msz len _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
      pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2. clear M1 M2' M3 MC2 TC.
      pose proof (ZW_of m2 MU) as ZW. pose proof (US_of m2 MU) as US2.
      kx_autoFLAx [KAApp (SPV - 128) 128; KAApp STA 88; KAUnp STA 88] [0xafad0] 40%nat
        [KZRange SPV 0x10007fff8000 (2^47); KZRange S8 788992 (2^44 - 11); KZRange msz 0 31; KZRange len 0 31;
         KZWr (SPV - 128) 128; KZWr (STA + 72) 16; KZZero (2147450880 + S8) 11;
         KZDisj (SPV - 128) 128 STA 88]
        [(SPV - 128, 128)] [(SPV - 128, 128); (STA, 88); (2147450880 + S8, 11)].
      all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
      all: try (split; [lia|]; split; [lia| exact ZW]).
      all: kx_mem.
      clear KXA KXRD KXK KXE.
      eapply (xu_epi m1 w8 w16); [| exact HC| reflexivity| exact MTC2| lia].
      split; [eexists; exact FR'|]. split; [exact ST2|]. split; [exact MU|]. split; [exact WM|]. split; [exact KXMI|].
      split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]]. }
    - (* [comment removed for export] *)
      rewrite KXBR0 in MTC.
      destruct (cb32_as_c8s bsegs _ STA _ _ HC) as (w0 & w1 & w2 & w3 & HC5).
      rewrite <- (Z.add_0_r IN) at 1.
      eapply (xu_mid m0 w8 0); [exact FI| exact HC5| exact MTC| lia].
    - (* [comment removed for export] *)
      replace (STA + msz + 40) with (STA + 40 + msz) by lia. replace (-1 * msz + 32) with (32 - msz) by lia.
      destruct (inb_prefix m0 (32 - msz) INB1 ltac:(lia)) as [PRE PREL].
      destruct (mtc_split _ _ _ _ MTC) as [MC TC]. clear MTC.
      destruct (cb_carve bsegs _ (STA + 40) 32 jm msz (32 - msz) MC ltac:(lia) ltac:(lia) ltac:(lia)) as (k1 & k2 & k3 & M1 & M2 & M3).
      call (MEMCPY RNG (STA + 40 + msz) IN (32 - msz) (SPV + -128)).
      all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- bytes_at _ _ IN _ => exact PRE
         | |- length _ = _ => exact PREL
         | |- rw_cells _ _ (STA + 40 + _) _ => exact M2
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => exact ST
         | |- app_blk IN _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABI| lia| lia]| lia]
         | |- app_blk (STA + 40 + _) _ => unfold app_blk, KLOW, KHIGH, KEND; clear - SA R0 R1 RM KXBR; lia
         | |- aro _ _ IN _ => split; [eapply unpoisoned_sub; [exact UI1| lia| lia]| split; [eapply rng_sub'; [exact RGI| lia]| eapply rng_sub'; [exact RGIS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RM RIN KXBR; Z.div_mod_to_equations; lia]]]
         | |- aro _ _ (STA + 40 + _) _ => split; [eapply unpoisoned_sub; [exact US1| lia| lia]| split; [eapply rng_sub'; [exact RS| lia]| eapply rng_sub'; [exact RSS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - RM KXBR; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ IN _ => eapply xu_ahull_sub; [exact AHI1| lia| lia]
         | |- ahull _ _ (STA + 40 + _) _ => eapply xu_ahull_sub; [eapply xu_ahull_wmono; [exact AHS| exact WM]| lia| lia]
         | |- art _ => split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]]
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LOS; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => clear - DSI DIS SS LOS KLO RM KXBR R0 R1 RIN RIN2 SPV47; lia
         | |- _ => clear - LOS KLO RM KXBR R0 R1 RIN RIN2 SPV47 SA; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
      clear ZW UI1 AHI1 INB1 PRE.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end. rename PC into ST2. rename PC0 into M2'.
      destruct (cb_uncarve bsegs _ (STA + 40) 32 msz (32 - msz) _ _ _ _ _ _ M1 M2' M3 ltac:(lia) ltac:(lia) ltac:(lia)) as [jm2 MC2].
      pose proof (mtc_join _ _ _ _ MC2 TC) as MTC2. clear M1 M2' M3 MC2 TC.
      eapply (xu_fill m2); [| exact HC| exact MTC2| lia| lia].
      split; [eexists; exact FR'|]. split; [exact ST2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
      split; [exact GOT| split; [exact RIC| split; [exact SHB| split; [exact INI| split; [exact LAY| exact REAL]]]]].
  Qed.
  End NONNULL.

  (* [comment removed for export] *)
  Lemma xu_null : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msz j1 j2,
    rw_cells bsegs m STA [CB 72 j1; C4 (Z_to_bv 64 msz); CB 12 j2] -> 0 <= msz < 32 ->
    stk bsegs m lo SPV -> mem_inv bsegs m -> art m ->
    evtF bsegs RNG POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STA) (Z_to_bv 64 0) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_XXH_UPDATE) fc None m (seg_rom bsegs)).
  Proof.
    intros until j2. intros XC RM ST MI (GOT & RIC & SHB & INI & LAY & REAL).
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (MU : munch W m m) by apply munch_refl.
    assert (WM : wmono bsegs m m) by apply wmono_refl.
    carve_frame 128%nat ST.
    unfold APZD_XXH_UPDATE.
    kx_autoFLAx [KAApp (SPV - 128) 128] [] 60%nat
      [KZRange SPV 0x10007fff8000 (2^47); KZWr (SPV - 128) 128]
      [(SPV - 128, 128)] [(SPV - 128, 128)].
    all: try kx_cell_lit. all: try kx_z. all: try kx_acc RI.
    all: kx_mem.
    all: kx_abs.
    all: zstep.
    all: lazymatch goal with FRc : rw_cells _ ?mc (?S + -128) _, STc : stk _ ?mc ?l (?S + -128) |- _ => release_frame FRc STc S end.
    all: kx_mkR_fold.
    all: apply evtF_done; unfold zd_xxh_update_postA.
    all: lazymatch goal with |- context [MS _ _ _ _ _ ?mc _] => do 14 eexists; exists mc, msz end.
    all: split; [reflexivity|].
    all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
    all: split; [| exact RM].
    all: exists j1, j2; exact XC.
  Qed.
End XU.

Theorem zd_xxh_update_proofA2 : zd_memcpyZ_stmtA -> zd_xxh_update_stmtA2.
Proof.
  intros MEMCPY. intros until lo. intros XS RMS RSTA ST8 RSTA2 INCASE ST RLO LOS SPV47 SS ARS AHS ART AST MI -> ->.
  assert (E8 : exists S8, STA = 8 * S8) by (exists (STA / 8); Z.div_mod_to_equations; lia).
  destruct E8 as [S8 E8]. subst STA.
  destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
  destruct (ARS ltac:(lia)) as (ABS & US & RS & RSS).
  assert (R0 : 0x625000 <= 8 * S8) by (unfold ablk, AIMG_HI, KLS in ABS; lia).
  assert (SA : 8 * S8 + 88 <= 0x7fff7000 \/ 0x10007fff8000 <= 8 * S8) by (pose proof ATOP_range as ATR; unfold ATOP_MIN, ATOP_MAX in ATR; unfold ablk, AIMG_HI, KLS in ABS; lia).
  rewrite shad_div in RSS. unfold shspan, ASHOFF in RSS.
  replace (8 * S8 / 8) with S8 in RSS by (Z.div_mod_to_equations; lia).
  replace ((8 * S8 + 88 + 7) / 8 - S8) with 11 in RSS by (Z.div_mod_to_equations; lia).
  destruct XS as (j1 & j2 & XC). unfold xxh_cells in XC.
  destruct INCASE as [[-> ->] | (INB & -> & RIN & RIN2 & DSI & DIS & (ABI & UI & RGI & RGIS) & AHI)].
  - eapply xu_null; try eassumption; lia.
  - apply (rw_cells_split_CB bsegs _ _ [] _ _ _ [8; 32; 32]%nat) in XC; [| reflexivity]. cbn [mk_CB_cells app] in XC.
    apply (proj1 (ZdWalkKit.rw_cells_app _ _ _ [CB 8 _; CB 32 _] _)) in XC. destruct XC as [HEADC MTC]. cbn [cells_size csize Nat.add] in MTC.
    replace (8 * S8 + Z.of_nat 40) with (8 * S8 + 40) in MTC by lia.
    eapply xu_nonnull; try eassumption; lia.
Qed.
End CANSEC1.
