(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 ZdWalkKit ZdCellKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface
     FsKit AZ_kit AZ_globals AZ_globalsR AZ_fkit AZ_huf_iface AZ_kx AZ_hufkit AZ_huf_disp AZ_huf_wkit AZ_huf_wksp.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac kx_lia ::= kx_lia_fast.
Ltac kxa_norm ::= unfold shspan in *.

Notation zlen l := (Z.of_nat (length l)).
Notation ALGOTIME := 0x22460 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition algotime_bytes : list byte := Eval vm_compute in match image_bytes bsegs ALGOTIME 256 with Some bs => bs | None => [] end.
Lemma algotime_at : forall m, mem_inv bsegs m -> bytes_at bsegs m ALGOTIME algotime_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image bsegs m ALGOTIME algotime_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma algotime_len : zlen algotime_bytes = 256.
Proof. vm_compute. reflexivity. Qed.

Section W.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FHL : fake_heap_law AI.
Hypothesis RDX1 : huf_rdx1_stmtA AI rng_fs.
Hypothesis RDX2 : huf_rdx2_stmtA AI rng_fs.
Hypothesis H4X1 : huf_4x1_stmtA.
Hypothesis H4X2 : huf_4x2_stmtA.

Theorem huf_4x_wksp_proofA : huf_4x_wksp_stmtA AI rng_fs.
Proof.
  unfold huf_4x_wksp_stmtA, huf_wksp_stmtA_at, APHUF_4X_WKSP.
  intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV DST dcap SRC n DT WK wksz lo src dtb.
  intros PRE UT HDR T0 T1 TA WKS W0 W1 W2 WA OSD OSW DJD DJW DJTW DJTS DJWS AFP TP AROc ADT HDT IND AWK HWK INW INDST INS HSRC.
  pose proof PRE as (MI & STK & LO0 & LO & SPB & OUT & D0 & D1 & D2 & SRCB & SL & S0 & S1 & S2 & OS1 & OS2 & DJ1 & AD & AS & ART & ASTK & AZ & _ & SP16).
  pose proof AFP as (AH & ASH & _ & _ & RFS & BOT & SPT & _ & RSTK2 & LBH).
  pose proof ASTK as (KLO & RSTK & RI).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _ & _ & LY7 & LY8).
  pose proof HDR as [LTB DT0]. unfold HUF_DTABLE_BYTES in *.
  pose proof ART as (GOT & _ & SHB & _ & _ & _).
  pose proof (algotime_at m MI) as ALG. pose proof algotime_len as ALGL.
  destruct (aro_client_at RNG m ALGOTIME 256 AROc ltac:(cbn; do 28 right; left; reflexivity)) as (UALG & RALG & RSALG).
  (* [comment removed for export] *)
  pose proof STK as STK2. carve_frame 64%nat STK2.
  assert (RSTKf : rng RNG (SPV - 64) 64) by (eapply rng_sub; [exact RSTK | lia | lia]).
  assert (MU0 : munch [(SPV - 64, SPV)] m m) by apply munch_refl.
  assert (WM0 : wmono bsegs m m) by apply wmono_refl.
  (* [comment removed for export] *)
  repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with ?T => change (fk_held T) in H end end.
  kx_autoFLA (GOT, SHB) (@nil kza) [0xa9924; 0xa9ac0] 40%nat
    [KZRange SPV (0x10007fff8000 + 6000) (2^47); KZAlign SPV 16; KZWr (SPV - 64) 64; KZRange n 0 (2^32 - 1); KZRange dcap 0 (2^32 - 1)]
    (@nil (Z * Z)) [(SPV - 64, 64)].
  all: try kx_cell_lit.
  all: try match goal with H : rng _ 65536 _ |- accP _ _ _ => kx_acc H end.
  all: unfold fk_held in OS1, OS2, OSD, OSW.
  all: kx_mem.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  (* [comment removed for export] *)
  all: pose proof FR as FRs; apply stk_of_rw_cells in FRs; cbn [cells_size csize Nat.add length firstn] in FRs;
       match type of FRs with stk _ _ ?a ?h => replace h with SPV in FRs by (clear; lia) end;
       pose proof (stk_merge bsegs m0 lo (SPV + -64) SPV STK2 FRs ltac:(clear - LO; lia)) as STK0; clear FRs.
  all: assert (FFR00 : ffr_pres [] LB m m0) by (eapply (fk_ffr_stack AI); [exact AH| exact MU0| exact WM0| apply Forall_cons; [cbn [fst]; clear - BOT LO; lia| apply Forall_nil]]).
  all: assert (AH0 : AHEAP AI L RNG st LB m0)
    by (eapply (AI_frame AI); [exact AH | exact MU0 | exact WM0 |]; apply Forall_cons; [cbn [fst snd]; apply (fk_acr_stack AI LB lo); [exact BOT | clear - LO; lia | clear - SPB; lia]| apply Forall_nil]).
  (* [comment removed for export] *)
  1-2: kx_autoFLA FR (@nil kza) (@nil Z) 20%nat [KZRange SPV (0x10007fff8000 + 6000) (2^47); KZAlign SPV 16] [(SPV - 64, 64)] (@nil (Z * Z));
       try (kx_acc RSTKf).
  1-2: zstep.
  1-2: unfold fk_held in *; apply evtF_done; unfold huf_dec_postF; do 16 eexists;
       (split; [reflexivity|]); (split; [eapply munch_weaken; [| exact MU0]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|]);
       (split; [exact WM0|]); (split; [exact KXMI|]); (split; [exact STK0|]); (split; [exact OUT|]);
       (split; [apply ffr_pres_mono_nil1; exact FFR00|]); (split; [exact AH0|]); (split; [right; reflexivity|]); (split; [clear; cbn; lia|]);
       (split; [| exact WKS]); exists dtb; (split; [exact UT|]); (split; [exact HDR|]); intros NE; cbv in NE; discriminate NE.
  (* [comment removed for export] *)
  assert (K64 : KHIGH <= SPV - 64) by (clear - KLO LO; lia).
  assert (AW : aappW [(SPV - 64, SPV)]) by (constructor; [cbn [fst snd]; right; exact K64 | constructor]).
  assert (UF : forall A B, unpoisoned m A B -> 0 <= A -> B <= KEND -> unpoisoned m0 A B).
  { intros A B U HA HB. eapply unpoisoned_munch; [exact U | exact MU0 |]. cbn [disjoint_from fst snd]. split; [|exact I].
    rewrite !shad_div. unfold ASHOFF, KHIGH, KEND in *. left. clear - K64 HA HB. Z.div_mod_to_equations. lia. }
  pose proof (UF _ _ UALG ltac:(clear; lia) ltac:(unfold KEND; clear; lia)) as UALG0.
  assert (KQ : forall (Q : Z) (x6 : word), 0 <= Q <= 15 -> 0 < n -> 0 < dcap ->
    evtF bsegs RNG
      (huf_dec_postF AI L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST dcap lo 6000 [(DT, DT + 16388); (WK, WK + wksz)] m
         (fun (m' : amem) (r : Z) => huf_built DT m' r /\ stk bsegs m' WK (WK + wksz)))
      (MS (mkR ra (Z_to_bv 64 (SPV + -64)) gp tp (Z_to_bv 64 Q) x6 (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 DST) (Z_to_bv 64 dcap) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 WK) (Z_to_bv 64 wksz) flags s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa9950) fc None m0 (seg_rom bsegs))).
  2: { (* [comment removed for export] *)
       lazymatch type of KQ with ?T => change (fk_held T) in KQ end.
       zstep. if_cases KI; zify_cond KI.
       - zstep. unfold fk_held in KQ. apply KQ; [clear; lia| clear - KXBR0 S1 SL; lia| clear - KXBR D1; lia].
       - zstep. zstep. zstep. zstep. zstep.
         (* [comment removed for export] *)
         kx_mkR_fold. unfold fk_held in KQ.
         rewrite (u_divu64 (Z_to_bv 64 (Z.shiftl n 4)) (Z_to_bv 64 dcap)) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; rewrite Z.mod_small; clear - KXBR D1; lia).
         rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. rewrite Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 4) with 16.
         rewrite (Z.mod_small (n * 16)) by (clear - S1 SL; lia). rewrite (Z.mod_small dcap) by (clear - D1; lia).
         assert (QR : 0 <= n * 16 / dcap <= 15).
         { clear - KXBR KI D1 S1 SL KXBR0. assert (Q16 : n * 16 / dcap < 16) by (apply Z.div_lt_upper_bound; lia). split; [Z.div_mod_to_equations; nia| lia]. }
         try rewrite (Z.mod_small (n * 16 / dcap)) by (clear - QR; lia).
         apply KQ; [exact QR| clear - KXBR0 S1 SL; lia| clear - KXBR D1; lia]. }
  clear FFR00 STK0. intros Q x6 QR NPOS DPOS. unfold fk_held in D1, S1. try clear KXBR; try clear KXBR0.
  (* [comment removed for export] *)
  repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with ?T => change (fk_held T) in H end end.
  kx_autoFLA (GOT, SHB) [KAUnp 0x22460 256] [0x97374; 0x96138] 60%nat
    [KZRange SPV (0x10007fff8000 + 6000) (2^47); KZAlign SPV 16; KZRange Q 0 15; KZRange n 1 (2^32 - 1); KZRange dcap 1 (2^32 - 1)]
    [(0x22460, 256)] (@nil (Z * Z)).
  all: try (kx_acc RALG).
  all: unfold fk_held in *.
  (* [comment removed for export] *)
  all: assert (AF : forall A k, areg RNG m A k -> areg RNG m0 A k)
    by (intros A k H Hn; destruct (H Hn) as (AB & U & R & RS); split; [exact AB | split; [| split; [exact R | exact RS]]];
        pose proof (ablk_lin _ _ AB) as (? & ? & ? & ?); apply UF; [exact U | lia | unfold KEND; lia]).
  all: assert (ART0 : art m0) by (eapply art_frameW; [exact ART | exact MU0 | exact WM0 | exact K64]).
  all: assert (AZ0 : azstk RNG m0 lo (SPV + -64))
    by (eapply azstk_sub; [eapply azstk_transport; [exact AZ | exact MU0 | exact WM0 | exact AW | clear - LO; lia]| apply Z.le_refl| clear - LO; lia| clear; lia]).
  all: assert (ARO0 : aro_client RNG m0) by (eapply aro_client_transport; [exact AROc | exact MU0 | exact WM0 | exact AW]).
  (* [comment removed for export] *)
  - pose proof RDX1 as R1. unfold huf_rdx1_stmtA, huf_rd_stmtA_at, APHUF_RDX1 in R1.
    eapply evtF_cut.
    { eapply (R1 L RNG st LB) with (lo := lo) (src := src) (dtb := dtb); clear R1;
        first [ exact KXMI0| exact STK2| exact SRCB| exact SL| exact UT| exact HDR| exact WKS| exact DJTW| exact DJTS| exact DJWS| exact TP| exact AZ0| exact ARO0| exact IND| exact INW| exact INS
              | apply AF; assumption
              | eapply fk_ahull_pres; [exact WM0| assumption]
              | intros NP; eapply fk_ahull_pres; [exact WM0| exact (HSRC NP)]
              | unfold afpre; split; [exact AH0| split; [exact ASH| split; [exact ART0| split; [split; [exact KLO| split; [eapply rng_sub; [exact RSTK| clear; lia| clear - LO; lia]| exact RI]]|
                  split; [exact RFS| split; [exact BOT| split; [clear - SPT; lia| split; [clear - SP16; Z.div_mod_to_equations; lia| split; [exact RSTK2| exact LBH]]]]]]]]]
              | unfold HUF_DTABLE_BYTES; clear - LO0 LO SPB S0 S1 S2 OSD OSW OS2 T0 T1 TA W0 W1 W2 WA; lia
              | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    clear R1. cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & r & dtb' & -> & MU1 & WM1 & MI1 & STK1 & WKS1 & FFR1 & AH1 & UT1 & HDR1 & RR & RES).
    replace (ret_pc (Z_to_bv 64 0xa9a74)) with (Z_to_bv 64 0xa9a74) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (DSTK : forall X kk, SPV - 64 <= X -> 0 <= kk -> X + kk <= SPV -> disjoint_from ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV + -64 - 5936, SPV + -64)] ++ fake_area L) X kk).
    { intros X kk H1 Hk H2. unfold HUF_DTABLE_BYTES, fake_area, FAKESZ. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF in *. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      unfold KHIGH in KLO. clear - H1 Hk H2 OSD OSW LO LY7 LY8 BOT KLO ATR. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FR MU1 WM1 ltac:(apply DSTK; cbn; clear; lia)) as FR1. clear DSTK.
    destruct (FHL _ _ _ _ _ AH) as [FAB FHB]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    destruct (fk_inblk_ablk _ _ _ LBH IND ltac:(unfold HUF_DTABLE_BYTES; clear; lia)) as (AdT & NdT & BdT & BdT1 & BdT2). pose proof (fk_ablk_lits _ _ BdT) as BDT.
    destruct (fk_inblk_ablk _ _ _ LBH INW ltac:(clear - W1; lia)) as (AwK & NwK & BwK & BwK1 & BwK2). pose proof (fk_ablk_lits _ _ BwK) as BWK.
    destruct (fk_inblk_ablk _ _ _ LBH INDST ltac:(clear - D1; lia)) as (AdS & NdS & BdS & BdS1 & BdS2). pose proof (fk_ablk_lits _ _ BdS) as BDS.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold HUF_DTABLE_BYTES in *.
    set (Wc := [(DT, DT + 16388); (WK, WK + wksz); (SPV + -64 - 5936, SPV + -64)]) in MU1.
    assert (AW1 : aappW Wc).
    { subst Wc. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - BDT BdT1 BdT2 ATR; lia|]. apply Forall_cons; [cbn [fst snd]; clear - BWK BwK1 BwK2 ATR; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - KLO LO; lia|]. apply Forall_nil. }
    assert (FFR1' : ffr_pres Wc LB m0 m1).
    { eapply magree_mono; [exact FFR1|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      subst Wc; cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & _). exact (conj O1 (conj O2 I)). }
    destruct (ADT ltac:(clear; lia)) as (ABD & UD & RDT & RSDT).
    assert (DJX : disjoint_from Wc DST (DST + dcap - DST)) by (subst Wc; cbn [disjoint_from]; clear - DJD DJW OS1 LO D1; repeat split; try exact I; lia).
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ Wc DST (DST + dcap) AH0 ltac:(replace (DST + dcap - DST) with dcap by (clear; lia); exact INDST) DJX MU1 WM1 FFR1' OUT) as OUT1.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc _ _ AH0 IND ltac:(clear; lia) ltac:(unfold KEND; clear - T1; lia) AW1 MU1 FFR1' (UF _ _ UD ltac:(clear - T0; lia) ltac:(unfold KEND; clear - T1; lia))) as UD1.
    assert (ADST1 : areg RNG m1 DST dcap).
    { intros Hn. destruct (AD Hn) as (AB & U & R & RS). split; [exact AB | split; [| split; [exact R | exact RS]]].
      eapply (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| exact INDST| exact Hn| unfold KEND; clear - D2; lia| exact AW1| exact MU1| exact FFR1'|].
      apply UF; [exact U| clear - D0; lia| unfold KEND; clear - D2; lia]. }
    assert (DIMG : forall X nn, 0 <= X -> X + nn <= AIMG_HI -> 0 <= nn ->
              disjoint_from (Wc ++ fake_area L) X nn /\ disjoint_from (Wc ++ fake_area L) (shad X) (shad (X + nn - 1) + 1 - shad X)).
    { intros X nn X0 XH Hn. subst Wc. unfold AIMG_HI in XH. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF, AIMG_HI, KHIGH in *.
      clear - X0 XH Hn FABL BDT BdT1 BdT2 BWK BwK1 BwK2 LY7 ATR KLO LO. split; repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (ASRC1 : areg RNG m1 SRC n).
    { intros Hn. destruct (AS Hn) as (AB & U & R & RS). split; [exact AB | split; [| split; [exact R | exact RS]]].
      destruct (INS Hn) as [IB|[I0 I1]].
      - eapply (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| exact IB| exact Hn| unfold KEND; clear - S2; lia| exact AW1| exact MU1| exact FFR1'|].
        apply UF; [exact U| clear - S0; lia| unfold KEND; clear - S2; lia].
      - eapply unpoisoned_munch; [apply UF; [exact U| exact I0| unfold KEND, AIMG_HI in *; clear - I1; lia]| exact MU1|].
        exact (proj2 (DIMG SRC n I0 I1 ltac:(clear - Hn; lia))). }
    assert (SRCB1 : bytes_at bsegs m1 SRC src).
    { destruct (INS NPOS) as [IB|[I0 I1]].
      - eapply (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| rewrite SL; exact IB| | exact MU1| exact FFR1'| exact SRCB].
        rewrite SL. subst Wc. cbn [disjoint_from]. clear - DJTS DJWS OS2 LO NPOS S1 SL; repeat split; try exact I; lia.
      - eapply bytes_at_transport; [exact SRCB| exact MU1|]. rewrite SL. exact (proj1 (DIMG SRC n I0 I1 ltac:(clear - NPOS; lia))). }
    assert (ART1 : art m1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (? & GOT' & RIC' & REAL' & SHB' & SUA' & INI' & LAY' & _). unfold art.
      split; [exact GOT'|]. split; [exact RIC'|]. split; [exact SHB'|]. split; [exact INI'|]. split; [exact LAY'| exact REAL']. }
    assert (AZ1 : azstk RNG m1 lo SPV).
    { eapply azstk_transport_F; [| exact MU1| exact WM1| exact AW1| exact FAB| exact FA8| clear - LY8 BOT; unfold FAKESZ; lia| clear - LO; lia].
      eapply azstk_transport; [exact AZ | exact MU0 | exact WM0 | exact AW | clear - LO; lia]. }
    assert (ARO1 : aro_client RNG m1) by (eapply aro_client_transport_F; [exact ARO0| exact MU1| exact WM1| exact AW1| exact FAB]).
    pose proof FR1 as FR1s. apply stk_of_rw_cells in FR1s. cbn [cells_size csize Nat.add length firstn] in FR1s.
    match type of FR1s with stk _ _ ?a ?h => replace h with SPV in FR1s by (clear; lia) end.
    pose proof (stk_merge bsegs m1 lo (SPV + -64) SPV STK1 FR1s ltac:(clear - LO; lia)) as STKF. clear FR1s.
    assert (FFR00 : ffr_pres [] LB m m0) by (eapply (fk_ffr_stack AI); [exact AH| exact MU0| exact WM0| apply Forall_cons; [cbn [fst]; clear - BOT LO; lia| apply Forall_nil]]).
    assert (FFR01 : ffr_pres ((DST, DST + dcap) :: [(DT, DT + 16388); (WK, WK + wksz)]) LB m m1).
    { eapply ffr_pres_trans; [apply ffr_pres_mono_nil1; exact FFR00|].
      eapply magree_mono; [exact FFR1|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & O3 & _). exact (conj O2 (conj O3 I)). }
    assert (MU01 : munch ((((DST, DST + dcap) :: [(DT, DT + 16388); (WK, WK + wksz)]) ++ [(SPV - 6000, SPV)]) ++ fake_area L) m m1).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU0]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
      eapply munch_weaken; [| exact MU1]. intros x Hx. subst Wc. cbn [outside app fake_area] in *. clear - Hx. lia. }
    (* [comment removed for export] *)
    clear DIMG UF AF DJX FFR00.
    repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with ?T => change (fk_held T) in H end end.
    kx_autoFLA FR1 (@nil kza) [0xa4cbc] 40%nat
      [KZRange SPV (0x10007fff8000 + 6000) (2^47); KZAlign SPV 16; KZRange r 0 (2^64 - 1); KZRange n 1 (2^32 - 1); KZRange SRC 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32 - 1)]
      [(SPV - 64, 64)] (@nil (Z * Z)).
    all: try (kx_acc RSTKf).
    all: unfold fk_held in *.
    + (* [comment removed for export] *)
      match goal with H : _ < r |- _ => rename H into RERR end. zstep.
      assert (ERR : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; clear - RERR RR; lia).
      apply evtF_done. unfold huf_dec_postF. do 16 eexists.
      split; [reflexivity|]. split; [exact MU01|]. split; [exact (wmono_trans _ _ _ _ WM0 WM1)|]. split; [exact MI1|]. split; [exact STKF|]. split; [exact OUT1|].
      split; [exact FFR01|]. split; [exact AH1|]. split; [right; exact ERR|]. split; [exact RR|].
      split; [| exact WKS1]. exists dtb'. split; [exact UT1|]. split; [exact HDR1|]. intros NE; rewrite ERR in NE; discriminate NE.
    + (* [comment removed for export] *)
      zstep.
      apply evtF_done. unfold huf_dec_postF. do 16 eexists.
      split; [reflexivity|]. split; [exact MU01|]. split; [exact (wmono_trans _ _ _ _ WM0 WM1)|]. split; [exact MI1|]. split; [exact STKF|]. split; [exact OUT1|].
      split; [exact FFR01|]. split; [exact AH1|]. split; [right; reflexivity|]. split; [clear; cbn; lia|].
      split; [| exact WKS1]. exists dtb'. split; [exact UT1|]. split; [exact HDR1|]. intros NE; cbv in NE; discriminate NE.
    + (* [comment removed for export] *)
      match goal with H : r <= _ |- _ => rename H into ROK end. match goal with H : r < n |- _ => rename H into RLTN end.
      assert (NE : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; clear - ROK RR; lia).
      pose proof (proj1 (RES NE)) as TOK.
      destruct (RES NE) as ((_ & ty & tl & TY & TLB & TLR & X2 & NB) & ty' & TY' & TYZ).
      rewrite TY in TY'. injection TY' as <-.
      assert (TY0 : bv_unsigned ty = 0) by (destruct (Z.eq_dec (bv_unsigned ty) 0) as [Z0|NZ]; [exact Z0 | apply TYZ in NZ; discriminate NZ]).
      rewrite TY0 in NB. change (negb (0 =? 0)) with false in NB.
      assert (SRC' : bytes_at bsegs m1 (r + SRC) (skipn (Z.to_nat r) src)).
      { pose proof SRCB1 as SB. rewrite <- (firstn_skipn (Z.to_nat r) src) in SB. apply bytes_at_app in SB as [_ SB].
        rewrite length_firstn, Nat.min_l in SB by (clear - RLTN RR SL; lia). rewrite Z2Nat.id in SB by (clear - RR; lia). replace (r + SRC) with (SRC + r) by (clear; lia). exact SB. }
      assert (SL' : zlen (skipn (Z.to_nat r) src) = -1 * r + n) by (rewrite length_skipn; clear - RLTN RR SL; lia).
      pose proof H4X1 as H1. unfold huf_4x1_stmtA, huf_int_stmtA_at, APHUF_4X1 in H1.
      eapply evtF_mono.
      { eapply (H1 RNG ra gp tp) with (m := m1) (SPV := SPV) (DST := DST) (dcap := dcap) (SRC := r + SRC) (n := -1 * r + n) (DT := DT) (tl := tl) (lo := lo) (src := skipn (Z.to_nat r) src) (dtb := dtb'); clear H1.
        - unfold huf_dec_preA.
          repeat match goal with |- _ /\ _ => split end;
          first [ exact MI1| exact STKF| exact OUT1| exact SRC'| exact SL'| exact ADST1| exact ART1| exact ASTK| exact AZ1| exact ARO1| exact SP16
                | eapply areg_sub; [exact ASRC1| clear - RR; lia| clear - RLTN RR; lia| clear; lia]
                | clear - LO0 LO SPB D0 D1 D2 S0 S1 S2 OS1 OS2 DJ1 RLTN RR; lia
                | lazymatch goal with |- ?G => idtac "LEFT1:" G end ].
        - unfold huf_dt_preA. unfold HUF_DTABLE_BYTES. pose proof HDR1 as [DL1 _]. unfold HUF_DTABLE_BYTES in DL1.
          repeat match goal with |- _ /\ _ => split end;
          first [ exact (proj1 UT1)| exact DL1| exact TA| split; [exact UD1| split; [exact RDT| exact RSDT]]
                | clear - T0 T1 OSD DJD; lia
                | lazymatch goal with |- ?G => idtac "LEFT2:" G end ].
        - exact TLB.
        - exact TLR.
        - intro X; discriminate X.
        - exact NB. }
      clear H1. cbv beta. intros ms' PO. unfold huf_dec_postA in PO.
      destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & r2 & E & MU2 & WM2 & MI2 & STL2 & OUT2 & R2 & RG2 & _).
      unfold huf_dec_postF. do 16 eexists. split; [exact E|].
      split. { eapply munch_trans; [exact MU01|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia. }
      split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM0 WM1) WM2)|]. split; [exact MI2|]. split; [exact STL2|]. split; [exact OUT2|].
      split.
      { eapply ffr_pres_trans; [exact FFR01|]. unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU2| exact WM2]|].
        intros a [((c & A & k & Hb & Ha) & HO)|(a' & (c & A & k & Hb & Ha') & ->)];
          pose proof (AI_block_bounds AI _ _ _ _ _ _ AH1 Hb) as (B1 & B2 & B3); cbn [ab_addr ab_size] in B1, B2, B3; unfold AIMG_HI in B1; cbn [outside app] in *.
        - destruct HO as (O1 & _). split; [exact O1|]. split; [clear - Ha B3 BOT LO; lia| exact I].
        - rewrite shad_div. unfold ASHOFF. unfold KHIGH in KLO. split; [clear - Ha' B1 B3 ATR BDS BdS1 BdS2; Z.div_mod_to_equations; lia|]. split; [clear - Ha' B1 B3 ATR KLO LO; Z.div_mod_to_equations; lia| exact I]. }
      split.
      { eapply (AI_frame AI); [exact AH1| exact MU2| exact WM2|]. cbn [app].
        apply Forall_cons; [cbn [fst snd]; replace (DST + dcap - DST) with dcap by (clear; lia); apply fk_acr_inblk; exact INDST|].
        apply Forall_cons; [cbn [fst snd]; apply (fk_acr_stack AI LB lo); [exact BOT| clear - LO; lia| clear - SPB; lia]| apply Forall_nil]. }
      split; [exact R2|]. split; [exact RG2|].
      split.
      * exists dtb'. split; [| split; [exact HDR1| intros _; exact TOK]].
        eapply u8arr_transport; [exact UT1| exact MU2| exact WM2|]. pose proof HDR1 as [DL1 _]. unfold HUF_DTABLE_BYTES in DL1. rewrite DL1. cbn [disjoint_from app]. clear - DJD OSD LO. repeat split; try exact I; lia.
      * eapply stk_transport_disjoint; [exact WKS1| exact MU2| exact WM2|]. cbn [disjoint_from app]. clear - DJW OSW LO. repeat split; try exact I; lia.
  (* [comment removed for export] *)
  - pose proof RDX2 as R1. unfold huf_rdx2_stmtA, huf_rd_stmtA_at, APHUF_RDX2 in R1.
    eapply evtF_cut.
    { eapply (R1 L RNG st LB) with (lo := lo) (src := src) (dtb := dtb); clear R1;
        first [ exact KXMI0| exact STK2| exact SRCB| exact SL| exact UT| exact HDR| exact WKS| exact DJTW| exact DJTS| exact DJWS| exact TP| exact AZ0| exact ARO0| exact IND| exact INW| exact INS
              | apply AF; assumption
              | eapply fk_ahull_pres; [exact WM0| assumption]
              | intros NP; eapply fk_ahull_pres; [exact WM0| exact (HSRC NP)]
              | unfold afpre; split; [exact AH0| split; [exact ASH| split; [exact ART0| split; [split; [exact KLO| split; [eapply rng_sub; [exact RSTK| clear; lia| clear - LO; lia]| exact RI]]|
                  split; [exact RFS| split; [exact BOT| split; [clear - SPT; lia| split; [clear - SP16; Z.div_mod_to_equations; lia| split; [exact RSTK2| exact LBH]]]]]]]]]
              | unfold HUF_DTABLE_BYTES; clear - LO0 LO SPB S0 S1 S2 OSD OSW OS2 T0 T1 TA W0 W1 W2 WA; lia
              | lazymatch goal with |- ?G => idtac "LEFT:" G end ]. }
    clear R1. cbv beta. intros ms' PO.
    destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & r & dtb' & -> & MU1 & WM1 & MI1 & STK1 & WKS1 & FFR1 & AH1 & UT1 & HDR1 & RR & RES).
    replace (ret_pc (Z_to_bv 64 0xa9a0c)) with (Z_to_bv 64 0xa9a0c) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    (* [comment removed for export] *)
    assert (DSTK : forall X kk, SPV - 64 <= X -> 0 <= kk -> X + kk <= SPV -> disjoint_from ([(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV + -64 - 5936, SPV + -64)] ++ fake_area L) X kk).
    { intros X kk H1 Hk H2. unfold HUF_DTABLE_BYTES, fake_area, FAKESZ. cbn [disjoint_from app]. rewrite !shad_div. unfold ASHOFF in *. pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
      unfold KHIGH in KLO. clear - H1 Hk H2 OSD OSW LO LY7 LY8 BOT KLO ATR. repeat split; try exact I; Z.div_mod_to_equations; lia. }
    pose proof (rw_cells_transport _ _ _ _ _ _ FR MU1 WM1 ltac:(apply DSTK; cbn; clear; lia)) as FR1. clear DSTK.
    destruct (FHL _ _ _ _ _ AH) as [FAB FHB]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    destruct (fk_inblk_ablk _ _ _ LBH IND ltac:(unfold HUF_DTABLE_BYTES; clear; lia)) as (AdT & NdT & BdT & BdT1 & BdT2). pose proof (fk_ablk_lits _ _ BdT) as BDT.
    destruct (fk_inblk_ablk _ _ _ LBH INW ltac:(clear - W1; lia)) as (AwK & NwK & BwK & BwK1 & BwK2). pose proof (fk_ablk_lits _ _ BwK) as BWK.
    destruct (fk_inblk_ablk _ _ _ LBH INDST ltac:(clear - D1; lia)) as (AdS & NdS & BdS & BdS1 & BdS2). pose proof (fk_ablk_lits _ _ BdS) as BDS.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold HUF_DTABLE_BYTES in *.
    set (Wc := [(DT, DT + 16388); (WK, WK + wksz); (SPV + -64 - 5936, SPV + -64)]) in MU1.
    assert (AW1 : aappW Wc).
    { subst Wc. unfold aappW, KLS, KLOW, KHIGH in *.
      apply Forall_cons; [cbn [fst snd]; clear - BDT BdT1 BdT2 ATR; lia|]. apply Forall_cons; [cbn [fst snd]; clear - BWK BwK1 BwK2 ATR; lia|].
      apply Forall_cons; [cbn [fst snd]; clear - KLO LO; lia|]. apply Forall_nil. }
    assert (FFR1' : ffr_pres Wc LB m0 m1).
    { eapply magree_mono; [exact FFR1|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      subst Wc; cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & _). exact (conj O1 (conj O2 I)). }
    destruct (ADT ltac:(clear; lia)) as (ABD & UD & RDT & RSDT).
    assert (DJX : disjoint_from Wc DST (DST + dcap - DST)) by (subst Wc; cbn [disjoint_from]; clear - DJD DJW OS1 LO D1; repeat split; try exact I; lia).
    pose proof (fcall_stk_pres AI FHL _ _ _ _ _ _ _ Wc DST (DST + dcap) AH0 ltac:(replace (DST + dcap - DST) with dcap by (clear; lia); exact INDST) DJX MU1 WM1 FFR1' OUT) as OUT1.
    pose proof (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc _ _ AH0 IND ltac:(clear; lia) ltac:(unfold KEND; clear - T1; lia) AW1 MU1 FFR1' (UF _ _ UD ltac:(clear - T0; lia) ltac:(unfold KEND; clear - T1; lia))) as UD1.
    assert (ADST1 : areg RNG m1 DST dcap).
    { intros Hn. destruct (AD Hn) as (AB & U & R & RS). split; [exact AB | split; [| split; [exact R | exact RS]]].
      eapply (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| exact INDST| exact Hn| unfold KEND; clear - D2; lia| exact AW1| exact MU1| exact FFR1'|].
      apply UF; [exact U| clear - D0; lia| unfold KEND; clear - D2; lia]. }
    assert (DIMG : forall X nn, 0 <= X -> X + nn <= AIMG_HI -> 0 <= nn ->
              disjoint_from (Wc ++ fake_area L) X nn /\ disjoint_from (Wc ++ fake_area L) (shad X) (shad (X + nn - 1) + 1 - shad X)).
    { intros X nn X0 XH Hn. subst Wc. unfold AIMG_HI in XH. cbn [disjoint_from app fake_area]. rewrite !shad_div. unfold FAKESZ, ASHOFF, AIMG_HI, KHIGH in *.
      clear - X0 XH Hn FABL BDT BdT1 BdT2 BWK BwK1 BwK2 LY7 ATR KLO LO. split; repeat split; try exact I; Z.div_mod_to_equations; lia. }
    assert (ASRC1 : areg RNG m1 SRC n).
    { intros Hn. destruct (AS Hn) as (AB & U & R & RS). split; [exact AB | split; [| split; [exact R | exact RS]]].
      destruct (INS Hn) as [IB|[I0 I1]].
      - eapply (fcall_unp_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| exact IB| exact Hn| unfold KEND; clear - S2; lia| exact AW1| exact MU1| exact FFR1'|].
        apply UF; [exact U| clear - S0; lia| unfold KEND; clear - S2; lia].
      - eapply unpoisoned_munch; [apply UF; [exact U| exact I0| unfold KEND, AIMG_HI in *; clear - I1; lia]| exact MU1|].
        exact (proj2 (DIMG SRC n I0 I1 ltac:(clear - Hn; lia))). }
    assert (SRCB1 : bytes_at bsegs m1 SRC src).
    { destruct (INS NPOS) as [IB|[I0 I1]].
      - eapply (fcall_bytes_pres AI FHL _ _ _ _ _ _ _ Wc); [exact AH0| rewrite SL; exact IB| | exact MU1| exact FFR1'| exact SRCB].
        rewrite SL. subst Wc. cbn [disjoint_from]. clear - DJTS DJWS OS2 LO NPOS S1 SL; repeat split; try exact I; lia.
      - eapply bytes_at_transport; [exact SRCB| exact MU1|]. rewrite SL. exact (proj1 (DIMG SRC n I0 I1 ltac:(clear - NPOS; lia))). }
    assert (ART1 : art m1).
    { pose proof (AI_rtcells AI _ _ _ _ _ AH1) as (? & GOT' & RIC' & REAL' & SHB' & SUA' & INI' & LAY' & _). unfold art.
      split; [exact GOT'|]. split; [exact RIC'|]. split; [exact SHB'|]. split; [exact INI'|]. split; [exact LAY'| exact REAL']. }
    assert (AZ1 : azstk RNG m1 lo SPV).
    { eapply azstk_transport_F; [| exact MU1| exact WM1| exact AW1| exact FAB| exact FA8| clear - LY8 BOT; unfold FAKESZ; lia| clear - LO; lia].
      eapply azstk_transport; [exact AZ | exact MU0 | exact WM0 | exact AW | clear - LO; lia]. }
    assert (ARO1 : aro_client RNG m1) by (eapply aro_client_transport_F; [exact ARO0| exact MU1| exact WM1| exact AW1| exact FAB]).
    pose proof FR1 as FR1s. apply stk_of_rw_cells in FR1s. cbn [cells_size csize Nat.add length firstn] in FR1s.
    match type of FR1s with stk _ _ ?a ?h => replace h with SPV in FR1s by (clear; lia) end.
    pose proof (stk_merge bsegs m1 lo (SPV + -64) SPV STK1 FR1s ltac:(clear - LO; lia)) as STKF. clear FR1s.
    assert (FFR00 : ffr_pres [] LB m m0) by (eapply (fk_ffr_stack AI); [exact AH| exact MU0| exact WM0| apply Forall_cons; [cbn [fst]; clear - BOT LO; lia| apply Forall_nil]]).
    assert (FFR01 : ffr_pres ((DST, DST + dcap) :: [(DT, DT + 16388); (WK, WK + wksz)]) LB m m1).
    { eapply ffr_pres_trans; [apply ffr_pres_mono_nil1; exact FFR00|].
      eapply magree_mono; [exact FFR1|]. intros a [[HF HO]|HS]; [| right; exact HS]. left; split; [exact HF|].
      cbn [outside app] in HO |- *. destruct HO as (O1 & O2 & O3 & _). exact (conj O2 (conj O3 I)). }
    assert (MU01 : munch ((((DST, DST + dcap) :: [(DT, DT + 16388); (WK, WK + wksz)]) ++ [(SPV - 6000, SPV)]) ++ fake_area L) m m1).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU0]; intros x Hx; cbn [outside app fake_area] in *; clear - Hx; lia|].
      eapply munch_weaken; [| exact MU1]. intros x Hx. subst Wc. cbn [outside app fake_area] in *. clear - Hx. lia. }
    (* [comment removed for export] *)
    clear DIMG UF AF DJX FFR00.
    repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with ?T => change (fk_held T) in H end end.
    kx_autoFLA FR1 (@nil kza) [0x9bb00] 40%nat
      [KZRange SPV (0x10007fff8000 + 6000) (2^47); KZAlign SPV 16; KZRange r 0 (2^64 - 1); KZRange n 1 (2^32 - 1); KZRange SRC 4096 (2^47);
       KZRange DT 4096 (2^47); KZRange DST 4096 (2^47); KZRange dcap 1 (2^32 - 1)]
      [(SPV - 64, 64)] (@nil (Z * Z)).
    all: try (kx_acc RSTKf).
    all: unfold fk_held in *.
    + (* [comment removed for export] *)
      match goal with H : _ < r |- _ => rename H into RERR end. zstep.
      assert (ERR : zd_is_error r = true) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_lt; clear - RERR RR; lia).
      apply evtF_done. unfold huf_dec_postF. do 16 eexists.
      split; [reflexivity|]. split; [exact MU01|]. split; [exact (wmono_trans _ _ _ _ WM0 WM1)|]. split; [exact MI1|]. split; [exact STKF|]. split; [exact OUT1|].
      split; [exact FFR01|]. split; [exact AH1|]. split; [right; exact ERR|]. split; [exact RR|].
      split; [| exact WKS1]. exists dtb'. split; [exact UT1|]. split; [exact HDR1|]. intros NE; rewrite ERR in NE; discriminate NE.
    + (* [comment removed for export] *)
      zstep.
      apply evtF_done. unfold huf_dec_postF. do 16 eexists.
      split; [reflexivity|]. split; [exact MU01|]. split; [exact (wmono_trans _ _ _ _ WM0 WM1)|]. split; [exact MI1|]. split; [exact STKF|]. split; [exact OUT1|].
      split; [exact FFR01|]. split; [exact AH1|]. split; [right; reflexivity|]. split; [clear; cbn; lia|].
      split; [| exact WKS1]. exists dtb'. split; [exact UT1|]. split; [exact HDR1|]. intros NE; cbv in NE; discriminate NE.
    + (* [comment removed for export] *)
      match goal with H : r <= _ |- _ => rename H into ROK end. match goal with H : r < n |- _ => rename H into RLTN end.
      assert (NE : zd_is_error r = false) by (unfold zd_is_error, ZE_maxCode; apply Z.ltb_ge; clear - ROK RR; lia).
      pose proof (proj1 (RES NE)) as TOK.
      destruct (RES NE) as ((_ & ty & tl & TY & TLB & TLR & X2 & NB) & ty' & TY' & TYZ).
      rewrite TY in TY'. injection TY' as <-.
      assert (TZ : (bv_unsigned ty =? 0) = false) by (apply Z.eqb_neq; apply (proj2 TYZ); reflexivity).
      rewrite TZ in NB. change (negb false) with true in NB.
      assert (SRC' : bytes_at bsegs m1 (r + SRC) (skipn (Z.to_nat r) src)).
      { pose proof SRCB1 as SB. rewrite <- (firstn_skipn (Z.to_nat r) src) in SB. apply bytes_at_app in SB as [_ SB].
        rewrite length_firstn, Nat.min_l in SB by (clear - RLTN RR SL; lia). rewrite Z2Nat.id in SB by (clear - RR; lia). replace (r + SRC) with (SRC + r) by (clear; lia). exact SB. }
      assert (SL' : zlen (skipn (Z.to_nat r) src) = -1 * r + n) by (rewrite length_skipn; clear - RLTN RR SL; lia).
      pose proof H4X2 as H1. unfold huf_4x2_stmtA, huf_int_stmtA_at, APHUF_4X2 in H1.
      eapply evtF_mono.
      { eapply (H1 RNG ra gp tp) with (m := m1) (SPV := SPV) (DST := DST) (dcap := dcap) (SRC := r + SRC) (n := -1 * r + n) (DT := DT) (tl := tl) (lo := lo) (src := skipn (Z.to_nat r) src) (dtb := dtb'); clear H1.
        - unfold huf_dec_preA.
          repeat match goal with |- _ /\ _ => split end;
          first [ exact MI1| exact STKF| exact OUT1| exact SRC'| exact SL'| exact ADST1| exact ART1| exact ASTK| exact AZ1| exact ARO1| exact SP16
                | eapply areg_sub; [exact ASRC1| clear - RR; lia| clear - RLTN RR; lia| clear; lia]
                | clear - LO0 LO SPB D0 D1 D2 S0 S1 S2 OS1 OS2 DJ1 RLTN RR; lia
                | lazymatch goal with |- ?G => idtac "LEFT1:" G end ].
        - unfold huf_dt_preA. unfold HUF_DTABLE_BYTES. pose proof HDR1 as [DL1 _]. unfold HUF_DTABLE_BYTES in DL1.
          repeat match goal with |- _ /\ _ => split end;
          first [ exact (proj1 UT1)| exact DL1| exact TA| split; [exact UD1| split; [exact RDT| exact RSDT]]
                | clear - T0 T1 OSD DJD; lia
                | lazymatch goal with |- ?G => idtac "LEFT2:" G end ].
        - exact TLB.
        - exact TLR.
        - intros _; apply X2; apply (proj2 TYZ); reflexivity.
        - exact NB. }
      clear H1. cbv beta. intros ms' PO. unfold huf_dec_postA in PO.
      destruct PO as (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & r2 & E & MU2 & WM2 & MI2 & STL2 & OUT2 & R2 & RG2 & _).
      unfold huf_dec_postF. do 16 eexists. split; [exact E|].
      split. { eapply munch_trans; [exact MU01|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn [outside app fake_area] in *. clear - Hx. lia. }
      split; [exact (wmono_trans _ _ _ _ (wmono_trans _ _ _ _ WM0 WM1) WM2)|]. split; [exact MI2|]. split; [exact STL2|]. split; [exact OUT2|].
      split.
      { eapply ffr_pres_trans; [exact FFR01|]. unfold ffr_pres. eapply magree_mono; [eapply magree_of_munch; [exact MU2| exact WM2]|].
        intros a [((c & A & k & Hb & Ha) & HO)|(a' & (c & A & k & Hb & Ha') & ->)];
          pose proof (AI_block_bounds AI _ _ _ _ _ _ AH1 Hb) as (B1 & B2 & B3); cbn [ab_addr ab_size] in B1, B2, B3; unfold AIMG_HI in B1; cbn [outside app] in *.
        - destruct HO as (O1 & _). split; [exact O1|]. split; [clear - Ha B3 BOT LO; lia| exact I].
        - rewrite shad_div. unfold ASHOFF. unfold KHIGH in KLO. split; [clear - Ha' B1 B3 ATR BDS BdS1 BdS2; Z.div_mod_to_equations; lia|]. split; [clear - Ha' B1 B3 ATR KLO LO; Z.div_mod_to_equations; lia| exact I]. }
      split.
      { eapply (AI_frame AI); [exact AH1| exact MU2| exact WM2|]. cbn [app].
        apply Forall_cons; [cbn [fst snd]; replace (DST + dcap - DST) with dcap by (clear; lia); apply fk_acr_inblk; exact INDST|].
        apply Forall_cons; [cbn [fst snd]; apply (fk_acr_stack AI LB lo); [exact BOT| clear - LO; lia| clear - SPB; lia]| apply Forall_nil]. }
      split; [exact R2|]. split; [exact RG2|].
      split.
      * exists dtb'. split; [| split; [exact HDR1| intros _; exact TOK]].
        eapply u8arr_transport; [exact UT1| exact MU2| exact WM2|]. pose proof HDR1 as [DL1 _]. unfold HUF_DTABLE_BYTES in DL1. rewrite DL1. cbn [disjoint_from app]. clear - DJD OSD LO. repeat split; try exact I; lia.
      * eapply stk_transport_disjoint; [exact WKS1| exact MU2| exact WM2|]. cbn [disjoint_from app]. clear - DJW OSW LO. repeat split; try exact I; lia.
Qed.
End W.
End CANSEC1.
