(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXLean KXLeanAll.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_frame_iface AZ_dframe_iface AZ_libc_iface AZ_kx.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma db_rep_ro : forall m, mem_inv bsegs m -> bytes_at bsegs m 0x21640 (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)).
Proof.
  intros m MI.
  pose proof (ro_cells_image bsegs m 0x21640 (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)) MI
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ B].
  cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma db_zero16 : forall (m : amem) s, rw_cells bsegs m s [CB 16 (repeat (Z_to_bv 8 0) 16)] -> rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
Lemma db_zero32 : forall (m : amem) s, rw_cells bsegs m s [CB 32 (repeat (Z_to_bv 8 0) 32)] ->
  rw_cells bsegs m s [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m s H. eapply rw_cells_recast; [exact H| cbn; repeat split; exact I| vm_compute; reflexivity| reflexivity]. Qed.
Lemma db_rep12 : forall (m : amem) s, rw_cells bsegs m s [CB 12 (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8))] ->
  bytes_at bsegs m s (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)).
Proof. intros m s H. pose proof (proj2 (proj1 H)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.
Lemma db_huf4 : forall (m : amem) s, rw_cells bsegs m s [C4 (Z_to_bv 64 201326604)] -> bytes_at bsegs m s (le4 (Z_to_bv 64 201326604)).
Proof. intros m s H. pose proof (proj2 (proj1 H)) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. Qed.
Lemma db_cells_split : forall (m : amem) A B cs1 cs2, rw_cells bsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells bsegs m A cs1 /\ rw_cells bsegs m B cs2.
Proof. intros m A B cs1 cs2 H E. subst B. exact (proj1 (rw_cells_app bsegs m A cs1 cs2) H). Qed.
Lemma db_cells_join : forall (m : amem) A B cs1 cs2, rw_cells bsegs m A cs1 -> rw_cells bsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells bsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 E. subst B. exact (proj2 (rw_cells_app bsegs m A cs1 cs2) (conj H1 H2)). Qed.

(* [comment removed for export] *)
Lemma db_ahull_wmono : forall RNG m m' X n, ahull RNG m X n -> wmono bsegs m m' -> ahull RNG m' X n.
Proof.
  intros RNG m m' X n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) WM. exists RLO, RHI.
  repeat (split; [assumption|]). split; [eapply wr_at_transport; [exact W| exact WM]| exact R].
Qed.
Lemma db_ahull_sub : forall RNG m X n X' n', ahull RNG m X n -> X <= X' -> X' + n' <= X + n -> ahull RNG m X' n'.
Proof.
  intros RNG m X n X' n' (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & W & R) A B. exists RLO, RHI.
  split; [lia|]. split; [lia|]. repeat (split; [assumption|]). exact R.
Qed.
(* [comment removed for export] *)
Definition db_held (P : Prop) : Prop := P.

(* [comment removed for export] *)
Local Ltac kx_wr_at ::=
  lazymatch goal with
  | |- wr_at ?segs ?m ?A ?N =>
      first
      [ lazymatch goal with
        | H : rw_cells segs m A ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (wr_at_sub segs m A n A N (proj2 H)); kx_lia
        end
      | match goal with
        | H : wr_at segs m ?A0 ?N0 |- _ => apply (wr_at_sub segs m A0 N0 A N H); kx_lia
        | H : u8arr segs m ?A0 ?bs |- _ => apply (wr_at_sub segs m A0 (Z.of_nat (length bs)) A N (proj2 H)); kx_lia
        | H : rw_cells segs m ?A0 ?cs |- _ =>
            let n := eval lazy in (Z.of_nat (cells_size cs)) in
            apply (wr_at_sub segs m A0 n A N (proj2 H)); kx_lia
        | H : stk segs m ?lo ?hi |- _ => apply (wr_at_sub segs m lo (hi - lo) A N); [apply (wr_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
        end ]
  end.
Local Ltac kx_rd_at ::=
  lazymatch goal with
  | |- rd_at ?segs ?m ?A ?N =>
      first
      [ lazymatch goal with
        | H : rw_cells segs m A ?cs |- _ =>
          let n := eval lazy in (Z.of_nat (cells_size cs)) in
          apply (rd_at_sub segs m A n A N (rd_at_rw_cells segs m A cs H)); kx_lia
        end
      | match goal with
        | H : bytes_at segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_bytes_at segs m A0 bs H)); kx_lia
        | H : u8arr segs m ?A0 ?bs |- _ => apply (rd_at_sub segs m A0 (Z.of_nat (length bs)) A N (rd_at_u8arr segs m A0 bs H)); kx_lia
        | H : rw_cells segs m ?A0 ?cs |- _ =>
            let n := eval lazy in (Z.of_nat (cells_size cs)) in
            apply (rd_at_sub segs m A0 n A N (rd_at_rw_cells segs m A0 cs H)); kx_lia
        | H : ro_cells segs m ?A0 ?cs |- _ =>
            let n := eval lazy in (Z.of_nat (cells_size cs)) in
            apply (rd_at_sub segs m A0 n A N (rd_at_ro_cells segs m A0 cs H)); kx_lia
        | H : stk segs m ?lo ?hi |- _ => apply (rd_at_sub segs m lo (hi - lo) A N); [apply (rd_at_stk segs m lo hi H); kx_lia | kx_lia | kx_lia]
        | _ => apply (rd_at_imgZ segs m A N); [lia | lia | lia | vm_compute; reflexivity]
        end ]
  end.
(* [comment removed for export] *)
Local Ltac db_kxclear := repeat match goal with
  | H : reads_ok _ _ _ _ _ |- _ => clear H
  | H : know_ok _ _ _ _ |- _ => clear H
  | H : log_flat _ _ |- _ => clear H
  | H : atoms_ok _ _ |- _ => clear H
  | E : env |- _ => clear E
  end.
(* [comment removed for export] *)
Local Ltac db_run SPV DCTX :=
  kx_autoFLAx [KAUnp DCTX 95992; KAApp (SPV + -112) 112; KAApp DCTX 32; KAApp (DCTX + 10296) 4; KAApp (DCTX + 29888) 40; KAApp (DCTX + 29976) 32;
             KAApp (DCTX + 30096) 276; KAApp (DCTX + 95940) 52] (@nil Z) 400%nat
    [KZRange SPV 0x10007fff8000 (2^47); KZRange DCTX 0x625000 (2^47 - 95992); KZAlign DCTX 8;
     KZWr (SPV + -112) 112; KZWr DCTX 32; KZWr (DCTX + 10296) 4; KZWr (DCTX + 29888) 40; KZWr (DCTX + 29976) 32; KZWr (DCTX + 30096) 276; KZWr (DCTX + 95940) 52;
     KZDisj DCTX 95992 (SPV + -112) 112]
    [(SPV + -112, 112); (DCTX + 30096, 276)] [(SPV + -112, 112); (DCTX, 95992)].
Local Ltac db_hold_dj := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with ?T => change (db_held T) in H end end.

Section Thm.
  Hypothesis MEMCPY : zd_memcpyZ_stmtA.
  Hypothesis MEMSET : zd_memsetZ_stmtA.

  Theorem zd_dbegin_proofA : zd_dbegin_stmtA.
  Proof.
    intros RNG ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DCTX
           llt mlt oft huf pde pfx vst dend expd pcs dsz bt stg le fe ws jhb ovd dcb dce trace gend lo.
    intros PTRC H1C H3C H5C H5OK TXC OWN GOT RD0 RD1 ST LO RSP SP47 DS GS GD D8 ARD AHD ART AST ARO MI -> -> ->.
    unfold wz0 in *.
    destruct ART as (RTG & RIC & SHBc & INI & LAY & REAL).
    destruct AST as (KLO & RSTK & RI). unfold KHIGH in KLO.
    destruct (ARD ltac:(lia)) as (ABD & UD0 & RDc & RDS). clear ARD.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (DA : DCTX + 95992 <= 0x7fff7000 \/ 0x10007fff8000 <= DCTX) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
    assert (DAL : 0x625000 <= DCTX) by (unfold ablk, AIMG_HI, KLS in ABD; lia).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct H5C as [H5C' H5L]. destruct OWN as [OWE OWX].
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_tx in *.
    destruct H5OK as (K_FMT & K_REST).
    h5_open ws H5L. lazymatch type of K_FMT with ?x = _ => subst x end. clear K_REST.
    destruct (stk_open bsegs m (DCTX + 32) (DCTX + 29888) (DCTX + 10296) 4 OWE ltac:(lia) ltac:(lia)) as (jh & HUF0 & OWE1 & OWE2).
    destruct (stk_open bsegs m (DCTX + 10296 + Z.of_nat 4) (DCTX + 29888) (DCTX + 26684) 12 OWE2 ltac:(lia) ltac:(lia)) as (jr & REP & OWE3 & OWE4).
    clear OWE OWE2. change (Z.of_nat 4) with 4 in OWE1, OWE3. change (Z.of_nat 12) with 12 in OWE4.
    replace (DCTX + 10296 + 4) with (DCTX + 10300) in OWE3 by lia. replace (DCTX + 26684 + 12) with (DCTX + 26696) in OWE4 by lia.
    pose proof (munch_refl [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                 (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPV - 2400, SPV)] m) as MU.
    pose proof (wmono_refl bsegs m) as WM.
    assert (DSH : forall m', munch [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                 (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPV - 2400, SPV)] m m' ->
                 unpoisoned m' DCTX (DCTX + 95992)).
    { intros m' MU'. eapply unpoisoned_munch; [exact UD0| exact MU'|]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *.
      clear - DA DAL RD1 KLO LO SP47. repeat split; Z.div_mod_to_equations; lia. }
    assert (AW : aappW [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
                 (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPV - 2400, SPV)]).
    { unfold aappW, KLOW, KHIGH. clear - DA KLO LO. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    carve_frame 112%nat ST.
    unfold APZD_DBEGIN.
    (* [comment removed for export] *)
    unfold wz0 in H5C'.
    apply (rw_cells_merge bsegs _ _ [C8 b; C4 (Z_to_bv 64 0)] [C4 b1; C4 b2; C4 b3; C8 b4; C8 b5; C8 b6; C8 b7; C8 b8; C8 b9; C8 b10] _) in H5C'.
    cbn [app cells_size csize Nat.add] in H5C'.
    apply (rw_cells_merge bsegs _ _ [C8 b; C4 (Z_to_bv 64 0); CB 68 _; C4 b11] [C4 b12; C8 b13; C8 b14] _) in H5C'.
    cbn [app cells_size csize Nat.add] in H5C'.
    apply (rw_cells_merge bsegs _ _ [C8 b; C4 (Z_to_bv 64 0); CB 68 _; C4 b11; CB 20 _; C4 b15] [C4 b16; C4 b17; C4 b18; C8 b19; C4 b20; C4 b21; C4 b22; C4 b23; C8 b24; C8 b25; C8 b26; C8 b27; C8 b28; C8 b29; C8 b30; C8 b31; C8 b32; C4 b33; C4 b34; C4 b35; C4 b36; C8 b37; C8 b38; C8 b39; C8 b40; C8 b41; C4 b42] []) in H5C'.
    cbn [app cells_size csize Nat.add] in H5C'.
    change (db_held (DCTX + 95992 <= lo \/ SPV <= DCTX)) in DS.
    lazymatch type of GS with ?T => change (db_held T) in GS end.
    lazymatch type of GD with ?T => change (db_held T) in GD end.
    lazymatch type of ATR with ?T => change (db_held T) in ATR end.
    lazymatch type of RD0 with ?T => change (db_held T) in RD0 end.
    lazymatch type of RSP with ?T => change (db_held T) in RSP end.
    clear LO0.
    (* [comment removed for export] *)
    db_run SPV DCTX.
    all: try kx_cell_lit.
    all: try kx_acc RI.
    all: kx_mem.
    all: try (unfold db_held in *; lia).
    db_kxclear.
    destruct (db_cells_split _ _ (DCTX + 29920) [_; _; _; _] [_] H1C ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as [H1Z H1B].
    clear H1C. destruct (rw_cells_forget _ _ _ _ H1Z) as (j1 & H1J). clear H1Z. cbn [cells_size csize Nat.add] in H1J.
    pose proof (DSH m0 MU) as UD3.
    assert (ART3 : art m0) by (split; [exact RTG| split; [exact RIC| split; [exact SHBc| split; [exact INI| split; [exact LAY| exact REAL]]]]]).
    assert (AH3 : ahull RNG m0 DCTX 95992) by (eapply db_ahull_wmono; [exact AHD| exact WM]).
    assert (ARO3 : aro_client RNG m0) by (eapply aro_client_transport; [exact ARO| exact MU| exact WM| exact AW]).
    unfold db_held in DS, GS, GD.
    call (MEMSET RNG (DCTX + 29888) 32 0 (SPV + -112)).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- rw_cells _ _ _ _ => eassumption
         | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| lia| lia]| lia]
         | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact UD3| lia| lia]| split; [eapply rng_sub'; [exact RDc| lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ _ _ => eapply db_ahull_sub; [exact AH3| lia| lia]
         | |- art _ => exact ART3
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LO; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => unfold db_held in *; lia
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    clear UD3 ART3 AH3 ARO3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS1 end.
    lazymatch goal with H : rw_cells bsegs mS1 (DCTX + 29888) _ |- _ => apply db_zero32 in H; rename H into H1Z end.
    pose proof (db_cells_join _ _ _ _ _ H1Z H1B ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as H1C.
    cbn [app] in H1C. clear H1Z H1B.
    pose proof (DSH mS1 MU) as UD4.
    lazymatch type of DS with ?T => change (db_held T) in DS end.
    lazymatch type of GS with ?T => change (db_held T) in GS end.
    lazymatch type of GD with ?T => change (db_held T) in GD end.
    db_run SPV DCTX.
    all: try kx_cell_lit.
    all: try kx_acc RI.
    all: kx_mem.
    all: try (unfold db_held in *; lia).
    db_kxclear. clear UD4.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mW2 end.
    destruct (db_cells_split _ _ (DCTX + 29992) [_; _] [_; _; _; _] H3C ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as [H3Z H3B].
    clear H3C. destruct (rw_cells_forget _ _ _ _ H3Z) as (j3 & H3J). clear H3Z. cbn [cells_size csize Nat.add] in H3J.
    pose proof (DSH mW2 MU) as UD3.
    assert (ART3 : art mW2) by (split; [exact RTG| split; [exact RIC| split; [exact SHBc| split; [exact INI| split; [exact LAY| exact REAL]]]]]).
    assert (AH3 : ahull RNG mW2 DCTX 95992) by (eapply db_ahull_wmono; [exact AHD| exact WM]).
    assert (ARO3 : aro_client RNG mW2) by (eapply aro_client_transport; [exact ARO| exact MU| exact WM| exact AW]).
    unfold db_held in DS, GS, GD.
    call (MEMSET RNG (DCTX + 29976) 16 0 (SPV + -112)).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- rw_cells _ _ _ _ => eassumption
         | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| lia| lia]| lia]
         | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact UD3| lia| lia]| split; [eapply rng_sub'; [exact RDc| lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ _ _ => eapply db_ahull_sub; [exact AH3| lia| lia]
         | |- art _ => exact ART3
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LO; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => unfold db_held in *; lia
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    clear UD3 ART3 AH3 ARO3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mS2 end.
    lazymatch goal with H : rw_cells bsegs mS2 (DCTX + 29976) _ |- _ => apply db_zero16 in H; rename H into H3Z end.
    pose proof (db_cells_join _ _ _ _ _ H3Z H3B ltac:(cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as H3C.
    cbn [app] in H3C. clear H3Z H3B.
    pose proof (DSH mS2 MU) as UD4.
    lazymatch type of DS with ?T => change (db_held T) in DS end.
    lazymatch type of GS with ?T => change (db_held T) in GS end.
    lazymatch type of GD with ?T => change (db_held T) in GD end.
    db_run SPV DCTX.
    all: try kx_cell_lit.
    all: try kx_acc RI.
    all: kx_mem.
    all: try (unfold db_held in *; lia).
    db_kxclear. clear UD4.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mW3 end.
    (* [comment removed for export] *)
    pose proof (DSH mW3 MU) as UD3.
    assert (ART3 : art mW3) by (split; [exact RTG| split; [exact RIC| split; [exact SHBc| split; [exact INI| split; [exact LAY| exact REAL]]]]]).
    assert (AH3 : ahull RNG mW3 DCTX 95992) by (eapply db_ahull_wmono; [exact AHD| exact WM]).
    assert (ARO3 : aro_client RNG mW3) by (eapply aro_client_transport; [exact ARO| exact MU| exact WM| exact AW]).
    pose proof (db_rep_ro mW3 KXMI) as REPB.
    unfold db_held in DS, GS, GD.
    call (MEMCPY RNG (DCTX + 26684) 0x21640 12 (SPV + -112)).
    all: first [ lazymatch goal with
         | |- evtF _ _ _ _ => idtac
         | |- mem_inv _ _ => assumption
         | |- stk _ _ _ _ => eassumption
         | |- bytes_at _ _ _ _ => exact REPB
         | |- length _ = _ => reflexivity
         | |- rw_cells _ _ _ _ => eassumption
         | |- app_blk 136768 _ => unfold app_blk, KLOW; clear; lia
         | |- aro _ _ 136768 _ => aro_cl ARO3
         | |- ahull _ _ 136768 _ => apply (aro_client_hull _ _ _ _ ARO3); clear; lia
         | |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact ABD| lia| lia]| lia]
         | |- aro _ _ _ _ => split; [eapply unpoisoned_sub; [exact UD3| lia| lia]| split; [eapply rng_sub'; [exact RDc| lia]| eapply rng_sub'; [exact RDS| unfold shspan; rewrite !shad_div; unfold ASHOFF; clear - D8; Z.div_mod_to_equations; lia]]]
         | |- ahull _ _ _ _ => eapply db_ahull_sub; [exact AH3| lia| lia]
         | |- art _ => exact ART3
         | |- astk _ _ _ => split; [unfold KHIGH; clear -KLO; lia| split; [eapply rng_sub'; [exact RSTK| clear -LO; lia]| exact RI]]
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ \/ _ => unfold db_held in *; lia
         | |- _ => unfold KHIGH, KEND in *; lia
         end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
    clear UD3 ART3 AH3 ARO3.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    lazymatch goal with H : rw_cells bsegs m4 (DCTX + 26684) _ |- _ => rename H into REPZ end.
    (* [comment removed for export] *)
    pose proof (DSH m4 MU) as UD4.
    lazymatch type of DS with ?T => change (db_held T) in DS end.
    lazymatch type of GS with ?T => change (db_held T) in GS end.
    lazymatch type of GD with ?T => change (db_held T) in GD end.
    db_run SPV DCTX.
    all: try kx_cell_lit.
    all: try kx_acc RI.
    all: kx_mem.
    all: try (unfold db_held in *; lia).
    db_kxclear. clear UD4.
    zstep.                                      (* [comment removed for export] *)
    release_frame FR PC SPV.
    kx_mkR_fold.
    apply evtF_done. unfold zd_dbegin_postA.
    do 15 eexists.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact KXMI|]. split; [exact PC|].
    unfold dctx_ptrs, dctx_h1, dctx_h3, dctx_h5, dctx_tx, dctx_owned, wz0.
    split; [exact PTRC|].
    split; [exact H1C|].
    split; [exact H3C|].
    split.
    { split; [| reflexivity].
      cbv beta iota delta [h5_cells h5_sizes mk_wcells wupd H5_isFrameDecompression H5_dictID].
      eapply rw_cells_recell; [exact H5C'| cbn; repeat split; exact I| cbn [cells_bytes cbytes app]; reflexivity]. }
    split; [exact TXC|].
    split.
    { split; [| exact OWX].
      eapply (stk_close bsegs _ (DCTX + 32) (DCTX + 29888) (DCTX + 10296) _ OWE1 HUF0); [| clear; lia | cbn [cells_size csize Nat.add]; clear; lia].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      match goal with |- stk _ _ ?a _ => replace a with (DCTX + 10300) by (clear; lia) end.
      eapply (stk_close bsegs _ _ (DCTX + 29888) (DCTX + 26684) _ OWE3 REPZ); [| clear; lia | cbn [cells_size csize Nat.add Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; clear; lia].
      cbn [cells_size csize Nat.add Z.to_nat Z.of_nat Pos.to_nat Pos.iter_op Pos.of_succ_nat Pos.succ Pos.add Pos.mul].
      match goal with |- stk _ _ ?a _ => replace a with (DCTX + 26696) by (clear; lia) end. exact OWE4. }
    split; [apply db_huf4; exact HUF0| apply db_rep12; exact REPZ].
  Qed.
End Thm.
End CANSEC1.
Print Assumptions zd_dbegin_proofA.
