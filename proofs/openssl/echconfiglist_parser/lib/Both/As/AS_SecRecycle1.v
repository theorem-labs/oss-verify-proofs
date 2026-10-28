(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel AllocSim MmapSim SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_AllocBase AW_LargeAlloc1 AW_SysconfPg AW_PoisonRemap1
     SecLazy AW_GetBlockBegin AW_SecRecycle1 AW_LargeDealloc1 AW_LargeDealloc2 AW_LargeDealloc3 AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition rs_W (lo : Z) (sp : word) (a msz pa nch lst TH : Z) : list ivl :=
  [(lo, bv_unsigned sp); (6976264, 6976880); (pa, pa + 8 * nch); (a, a + msz); (lst + 24, lst + 32); (sh a, sh a + msz / 8); (TH + 2800, TH + 3168)]%Z.

(* [comment removed for export] *)
Definition rs_chunks (chunks : list Z) (idx nch lst : Z) : list Z :=
  if idx =? nch - 1 then chunks else firstn (Z.to_nat idx) chunks ++ lst :: skipn (S (Z.to_nat idx)) chunks.

(* [comment removed for export] *)
Definition recycle_sec_mid (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo a msz nres nch idx pa lst TSD CTX TH : Z) (chunks : list Z) (sbs : list byte) (g : word) (b244 : byte)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       lzok asegs L S Zr (mkCfg msF' mo')
    /\ restrict L S msF'
       = MS (mkR (wz 0x1998d4) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a) (wz a) (wz msz) (wz 0) a3 a4 a5 a6 a7
                 (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1c06e0) fc None m' (seg_rom asegs)
    /\ same_but_materialized mo mo'
    /\ munch (rs_W lo sp a msz pa nch lst TH) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ SENV tp TSD CTX TH m' /\ RENV g b244 m'
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' 6976264 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]
    /\ stk asegs m' 6976288 6976832 /\ rw_cells asegs m' 6976832 [C8 (wz 0)] /\ stk asegs m' 6976840 6976880
    /\ u64arr asegs m' pa (wlist (rs_chunks chunks idx nch lst))
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz)]
    /\ rw_cells asegs m' (lst + 24) [C8 (wz idx)]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ u8arr asegs m' (sh a) sbs.
End HCW.

Section SecRecycle.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz sz idx pa nres nch lst lidx TSD CTX TH sb n actx : Z) (chunks : list Z) (ob0 ob1 : byte) (sbs : list byte) (g : word) (b244 : byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40.
  Hypothesis SBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil).
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= TH \/ TH + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch <= nres <= 2^20.
  Hypothesis IDX : nth_error chunks (Z.to_nat idx) = Some a.
  Hypothesis LNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis PLCL : idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= TH \/ TH + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst)).
  Hypothesis LSTA : idx = nch - 1 -> lst = a.
  (* [comment removed for export] *)
  Hypothesis DISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks.
  Hypothesis NR : 0 <= n < 2^32.
  (* [comment removed for export] *)
  Hypothesis SEN : SENV tp TSD CTX TH m.
  Hypothesis REN : RENV g b244 m.
  Hypothesis SB32 : rw_cells asegs m 6976184 [C8 (wz sb)].
  Hypothesis INST64 : rw_cells asegs m 6976216 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m 6976264 [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis SST : stk asegs m 6976288 6976832.
  Hypothesis MTX : rw_cells asegs m 6976832 [C8 (wz 0)].
  Hypothesis GST : stk asegs m 6976840 6976880.
  Hypothesis PA : u64arr asegs m pa (wlist chunks).
  Hypothesis HDR : rw_cells asegs m a [C8 (wz a); C8 (wz msz); C8 (wz sz); C8 (wz idx)].
  Hypothesis LSTC : idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz lidx)].
  Hypothesis CHDR : rw_cells asegs m (a + 6128) [C1 ob0; C1 ob1; C2 (wz 0); C4 (wz n); C8 (wz actx)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SHD : u8arr asegs m (sh a) sbs. Hypothesis SHDL : Z.of_nat (length sbs) = msz / 8.
  Hypothesis OK : lzok asegs L S Zr (mkCfg msF mo).
  Hypothesis VISE : restrict L S msF
    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x199214) fc None m (seg_rom asegs).

  Let ARE : 12599296 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Let PAE : 12599296 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; lia)). Qed.   (* [comment removed for export] *)
  Let LRE : 12599296 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Let MID := recycle_sec_mid L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks sbs g b244.

  Lemma recycle_sec_head :
    (forall msF' mo', MID msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SBR as R; destruct R as [SBR'].
    pose proof AR as R; destruct R as (AHI & CE & AL & MAL & MSZ). pose proof PAR as R; destruct R as (PLO & PHI & PAL). pose proof NCH as R; destruct R as (LEN & IDR & NHI).
    pose proof LR as R; destruct R as [LLO LHI].
    unfold AHI_LO, AIMG_TOP, kSpaceSize, kPtrArrayReserve in *. acb.
    (* [comment removed for export] *)
    pose proof PLC as R; destruct R as [(P1 & P2 & P3 & P4 & P5 & P6)].
    assert (PLC1 : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX))).
    { constructor. split; [exact P1|]. split; [clear - P4; try acb; lia| clear - P5; try acb; lia]. }
    assert (PLC2 : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (pa + 8 * nch <= a \/ a + msz <= pa) /\ (pa + 8 * nch <= TH \/ TH + 4096 <= pa))).
    { constructor. split; [clear - P4; try acb; lia|]. split; [clear - P6 NHI IDR; try acb; lia| clear - P2 NHI IDR; try acb; lia]. }
    (* [comment removed for export] *)
    assert (RNG2 : hidden (akobj TH 4096 /\ TH + 4096 <= aceil)) by (constructor; clear - RNG'; tauto).
    assert (PAR' : aapp pa (8 * nch) /\ pa + 8 * nch <= aceil).
    { split; [| clear - PHI NHI IDR; try acb; lia]. apply (aapp_sub _ _ _ _ PLO); clear - NHI IDR; try acb; lia. }
    assert (NCH1 : zlen chunks = nch /\ 1 <= nch) by (clear - LEN IDR; try acb; lia).
    assert (NCH2 : zlen chunks = nch /\ 0 <= idx < nch /\ nch < 2^40) by (clear - LEN IDR NHI; try acb; lia).
    assert (AR2 : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ 0x2000 <= msz) by (split; [exact AHI| clear - CE AL MSZ; try acb; lia]).
    assert (HI2 : lo + 80 <= bv_unsigned sp) by (clear - HI; try acb; lia).
    clear P1 P2 P3 P4 P5 P6.
    assert (SHB : 2148314624 <= sh a /\ sh a + msz / 8 <= 17594333495296) by (clear - AHI CE; try acb; aunf; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; lia).
    assert (LENW : Z.of_nat (length (wlist chunks)) = nch) by (unfold wlist; rewrite length_map; unfold zlen in LEN; lia).
    (* [comment removed for export] *)
    assert (PLL : hidden ((TH + 4096 <= lst \/ lst + 32 <= TH) /\ (CTX + 160 <= lst \/ lst + 32 <= CTX) /\ (pa + 8 * nch <= lst \/ lst + 32 <= pa))).
    { destruct (Z.eq_dec idx (nch - 1)) as [IL|INE].
      - rewrite (LSTA IL). destruct PLC2 as [(Q1 & Q2 & Q3)]. destruct PLC1 as [(Q4 & Q5 & Q6)]. constructor.
        split; [clear - Q1 MSZ; try acb; lia|]. split; [clear - Q6 MSZ; try acb; lia| clear - Q2 MSZ; try acb; lia].
      - pose proof (PLCL ltac:(hci; clear - INE IDR; try acb; lia)) as R; destruct R as [(Q1 & Q2 & Q3 & Q4)]. constructor.
        split; [clear - Q3; try acb; lia|]. split; [clear - Q4; try acb; lia| clear - Q2 NHI IDR; try acb; lia]. }
    region_table.
    (* [comment removed for export] *)
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF _ mo Q OK VISE).
    { eapply (recycle_sec1 ra sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo a msz sz idx pa nres nch 0 TSD CTX TH sb n actx chunks ob0 ob1);
        try eassumption; try reflexivity.
      eapply nth_error_In. exact IDX. }
    cbv beta. intros msF1 mo1 OK1 SBM1 HS1 P1.
    destruct P1 as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & MTX1 & TST1).
    unfold AINST in VIS1. change (6976152 + 64) with 6976216 in VIS1. change (6976152 + 688) with 6976840 in VIS1.
    (* [comment removed for export] *)
    assert (MU : munch (rs_W lo sp a msz pa nch lst TH) m m1).
    { unfold rs_W. eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. intros; (first [clear - H HI2; lia | lia]). }
    pose proof WM1 as WM. unfold rs_W in MU.
    senv_at SEN MU1 WM1 SEN1. renv_at REN MU1 WM1 REN1.
    assert (LSTC1 : idx < nch - 1 -> rw_cells asegs m1 (lst + 24) [C8 (wz lidx)]).
    { intros Hi. pose proof (PLCL Hi) as R; destruct R as [PL]. eapply rw_cells_transport; [exact (LSTC Hi)| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize length Nat.add]. clear - PL LLO LHI SPR LO HI RNG'; try acb. aunf; (first [clear - ACEILB0 PL LLO HI LO; lia | lia]). }
    clear SEN REN ST MTX TST LSTC CHDR.
    transport_after_call asegs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    assert (DONE : forall msF2 mo2 chunks',
      chunks' = rs_chunks chunks idx nch lst ->
      lzok asegs L S Zr (mkCfg msF2 mo2) -> same_but_materialized mo1 mo2 ->
      dealloc1_post ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 F fc m1
         [(lo, bv_unsigned sp); (6976264, 6976880); (pa, pa + 8 * nch); (a + 16, a + 32); (lst + 24, lst + 32); (TH + 2800, TH + 3168)]%Z
         lo a msz nres nch pa TH chunks' (fun m' => rw_cells asegs m' (lst + 24) [C8 (wz idx)]) (restrict L S msF2) ->
      sreach asegs Q (mkCfg msF2 mo2)).
    { intros msF2 mo2 chunks' EC OK2 SBM2 P2.
      destruct P2 as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & m2 & VIS2 & MU2 & WM2 & MI2 & ST2 & FR2 & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & HDR2 & TST2 & LST2).
      senv_at SEN1 MU2 WM2 SEN2. renv_at REN1 MU2 WM2 REN2.
      clear ST1 MTX1 TST1 INST64 NRES SST GST PA HDR LSTC1 SEN1 REN1.
      transport_after_call asegs m1 m2 MU2 WM2. clear MU2 WM2.
      apply K. unfold MID, recycle_sec_mid. rewrite <- EC.
      exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, m2.
      split; [exact OK2|]. split; [exact VIS2|]. split; [exact (same_but_materialized_trans _ _ _ SBM1 SBM2)|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI2|].
      repeat match goal with |- _ /\ _ => split end; try assumption. }
    destruct (Z.eq_dec idx (nch - 1)) as [IL|INE].
    - eapply (evt_sreach_lazy_at asegs L S Zr _ msF1 _ mo1 Q OK1 VIS1).
      { eapply (dealloc1_last ra sp gp tp F fc lo a msz sz idx pa nres nch TH lst chunks s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); try eassumption.
        clear - HI; try acb; lia. }
      cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2. apply (DONE msF2 mo2 chunks); [| exact OK2| exact SBM2| exact P2].
      unfold rs_chunks. replace (idx =? nch - 1) with true by (symmetry; apply Z.eqb_eq; exact IL). reflexivity.
    - eapply (evt_sreach_lazy_at asegs L S Zr _ msF1 _ mo1 Q OK1 VIS1).
      { eapply (dealloc1_mid ra sp gp tp F fc lo a msz sz idx pa nres nch TH lst chunks s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); try eassumption.
        all: try (clear - HI; try acb; lia). all: try (clear - INE IDR; try acb; lia). all: try exact (LSTC1 ltac:(hci; clear - INE IDR; try acb; lia)).
        pose proof (PLCL ltac:(hci; clear - INE IDR; try acb; lia)) as R; destruct R as [(Q1 & Q2 & Q3 & Q4)]; constructor.
        split; [clear - Q1; try acb; lia|]. split; [clear - Q2 IDR NHI; try acb; lia| clear - Q3; try acb; lia]. }
      cbv beta. intros msF2 mo2 OK2 SBM2 HS2 P2. eapply (DONE msF2 mo2); [| exact OK2| exact SBM2| exact P2].
      unfold rs_chunks. replace (idx =? nch - 1) with false by (symmetry; apply Z.eqb_neq; exact INE). reflexivity.
  Qed.
End SecRecycle.

