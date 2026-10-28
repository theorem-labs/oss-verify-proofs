(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BAllocSim BMmapSim BReach BazyRestrict BazyLedger BazySR BazyNodes BazyMadvise.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics BsDepotInv BllocWalkKit B_memset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BW_Leaves BW_PoisonShadow BW_AllocBase BW_LargeAlloc1 BW_SysconfPg BW_PoisonRemap1 BecLazy BecLazy2 BecLazyMadvise BW_LargeDealloc1 BW_LargeDealloc2 BW_LargeDealloc3 BS_SecRecycle1 BllocTacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocPerfKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BerfLia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition rs_L (L : list (word * word)) (a msz : Z) : list (word * word) := maps_subtract L a (a + msz).

Definition ps0_model (mo : Model) (a msz : Z) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
     nonvm_same mo mo'
  /\ vm_maps h' = vm_maps h
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = vm_noaccess h
  /\ eager_used mo' <= eager_used mo.

Definition rs_model (mo : Model) (a msz : Z) (mo' : Model) : Prop :=
  let h := m_vmmaps mo in let h' := m_vmmaps mo' in
     nonvm_same mo mo'
  /\ vm_maps h' = map_remove (vm_maps h) (wz a)
  /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h /\ vm_mmap_base h' = vm_mmap_base h
  /\ vm_brk h' = vm_brk h /\ vm_start_brk h' = vm_start_brk h
  /\ vm_noaccess h' = maps_subtract (vm_noaccess h) a (a + msz)
  /\ eager_used mo' + msz <= eager_used mo.

Lemma ps0_model_mat : forall mo a msz mo1 mo2, ps0_model mo a msz mo1 -> same_but_materialized mo1 mo2 -> ps0_model mo a msz mo2.
Proof.
  intros mo a msz mo1 mo2 (NV & REST) SB. unfold ps0_model.
  rewrite (same_but_materialized_vmmaps _ _ SB), (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [exact NV| apply nonvm_same_mat; exact SB].
Qed.
Lemma rs_model_mat : forall mo a msz mo1 mo2, rs_model mo a msz mo1 -> same_but_materialized mo1 mo2 -> rs_model mo a msz mo2.
Proof.
  intros mo a msz mo1 mo2 (NV & REST) SB. unfold rs_model.
  rewrite (same_but_materialized_vmmaps _ _ SB), (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [exact NV| apply nonvm_same_mat; exact SB].
Qed.
Lemma ps0_model_pre : forall mo0 mo a msz mo1, same_but_materialized mo0 mo -> ps0_model mo a msz mo1 -> ps0_model mo0 a msz mo1.
Proof.
  intros mo0 mo a msz mo1 SB (NV & REST). unfold ps0_model in *.
  rewrite <- (same_but_materialized_vmmaps _ _ SB), <- (same_but_materialized_eager _ _ SB).
  split; [| exact REST]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SB| exact NV].
Qed.

Lemma rs_chunks_length : forall chunks idx nch lst,
  zlen chunks = nch -> 0 <= idx < nch -> Z.of_nat (length (wlist (rs_chunks chunks idx nch lst))) = nch.
Proof.
  intros chunks idx nch lst LEN IDR. unfold wlist, zlen in *. rewrite length_map. unfold rs_chunks.
  destruct (idx =? nch - 1); [tlia|]. rewrite length_app, length_firstn. cbn [length]. rewrite length_skipn. tlia.
Qed.

Definition recycle_sec_mid2 (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo a msz nres nch idx pa lst TSD CTX TH : Z) (chunks : list Z) (g : word) (b244 : byte)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       lzok asegs L S Zr (mkCfg msF' mo')
    /\ restrict L S msF'
       = MS (mkR (wz 0x94e6c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz a) (wz a) a0 a1 a2 a3 a4 a5 a6 a7
                 (wz msz) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x94e6c) fc None m' (seg_rom asegs)
    /\ ps0_model mo a msz mo'
    /\ munch (rs_W lo sp a msz pa nch lst TH) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ SENV tp TSD CTX TH m' /\ RENV g b244 m'
    /\ stk asegs m' lo (bv_unsigned sp + -32)
    /\ rw_cells asegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' 1628696 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' 1628744 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]
    /\ stk asegs m' 1628768 1629312 /\ rw_cells asegs m' 1629312 [C8 (wz 0)] /\ stk asegs m' 1629320 1629360
    /\ u64arr asegs m' pa (wlist (rs_chunks chunks idx nch lst))
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz)]
    /\ rw_cells asegs m' (lst + 24) [C8 (wz idx)]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ u8arr asegs m' (sh a) (repeat (b8 0) (Z.to_nat (msz / 8))).

Definition recycle_sec_post (L S Zr : list (word * word)) (mo : Model) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo a msz nres nch idx pa lst TSD CTX TH : Z) (chunks : list Z) (g : word) (b244 : byte)
    (msF' : machine_state) (mo' : Model) : Prop :=
  exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
       lzok asegs (rs_L L a msz) S Zr (mkCfg msF' mo')
    /\ restrict (rs_L L a msz) S msF'
       = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ rs_model mo a msz mo'
    /\ munch (rs_W lo sp a msz pa nch lst TH) m m' /\ wmono_out [(a, a + msz)] m m' /\ mem_inv asegs m'
    /\ SENV tp TSD CTX TH m' /\ RENV g b244 m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 1628696 [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]
    /\ rw_cells asegs m' 1628744 [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]
    /\ stk asegs m' 1628768 1629312 /\ rw_cells asegs m' 1629312 [C8 (wz 0)] /\ stk asegs m' 1629320 1629360
    /\ u64arr asegs m' pa (wlist (rs_chunks chunks idx nch lst))
    /\ (idx < nch - 1 -> rw_cells asegs m' (lst + 24) [C8 (wz idx)])
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ u8arr asegs m' (sh a) (repeat (b8 0) (Z.to_nat (msz / 8)))
    /\ (forall x : word, a <= bv_unsigned x < a + msz -> m' x = None).

Section SecRecycle2.
  Variables (L S Zr : list (word * word)) (mo : Model) (Q : config -> Prop).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo a msz idx pa nres nch lst TSD CTX TH sb : Z) (chunks : list Z) (g : word) (b244 : byte).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40.
  Hypothesis TPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (6762288 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= TH \/ TH + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= TH \/ TH + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a)).
  Hypothesis PAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0.
  Hypothesis NCH : zlen chunks = nch /\ 0 <= idx < nch /\ nch <= nres <= 2^20.
  Hypothesis LR : aapp lst 4096 /\ lst + 4096 <= aceil.
  Hypothesis PLCL : idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= TH \/ TH + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst)).
  Hypothesis LSTA : idx = nch - 1 -> lst = a.

  Hypothesis NW : entries_nowrap (vm_maps (m_vmmaps mo)). Hypothesis NWA : entries_nowrap (vm_noaccess (m_vmmaps mo)).
  Hypothesis NOV : nooverlap (vm_maps (m_vmmaps mo)).
  Hypothesis NWL : entries_nowrap L.

  Hypothesis ZRSH : forall x : word, (sh AHI_LO <= bv_unsigned x < sh aceil \/ sh AIMG_TOP <= bv_unsigned x < sh ALOWSH_LO) -> in_rangesb x Zr = true.
  Hypothesis HSRF : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_reserved (m_vmmaps mo)) a n = true.
  Hypothesis HSMC : forall a n : word, 0 < bv_unsigned n -> (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      map_contains (vm_maps (m_vmmaps mo)) a n = true.

  Hypothesis HSNA : forall a n : word, (sh AHI_LO <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh aceil) \/ (sh AIMG_TOP <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= sh ALOWSH_LO) ->
                      region_free (vm_noaccess (m_vmmaps mo)) a n = true.

  Hypothesis WIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x S = true.
  Hypothesis HAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true.
  Hypothesis NOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x L = false.
  Hypothesis NOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false.

  Hypothesis ATOP : alloc_top (m_vmmaps mo) = hceil.

  Let ARE : 7241728 <= a /\ a + msz <= aceil. Proof. exact (aapp_env _ _ (proj1 AR) ltac:(tlia)). Qed.
  Let PAE : 7241728 <= pa /\ pa + kPtrArrayReserve <= aceil. Proof. exact (aapp_env _ _ (proj1 PAR) ltac:(clear; hci; unfold kPtrArrayReserve; tlia)). Qed.
  Let LRE : 7241728 <= lst /\ lst + 4096 <= aceil. Proof. exact (aapp_env _ _ (proj1 LR) ltac:(clear; tlia)). Qed.
  Let MID := recycle_sec_mid L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks.
  Let MID2 := recycle_sec_mid2 L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.
  Let POST := recycle_sec_post L S Zr mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo a msz nres nch idx pa lst TSD CTX TH chunks g b244.

  Lemma recycle_sec_poison : forall (sbs : list byte) msF3 mo3,
    MID sbs g b244 msF3 mo3 -> Z.of_nat (length sbs) = msz / 8 ->
    (forall msF' mo', MID2 msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF3 mo3).
  Proof.
    intros sbs msF3 mo3 M SHDL K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR'].
    pose proof AR as R; destruct R as (AHI & CE & AL & MAL & MSZ). pose proof PAR as R; destruct R as (PLO & PHI & PAL). pose proof NCH as R; destruct R as (LEN & IDR & NHI).
    pose proof LR as R; destruct R as [LLO LHI].
    unfold AHI_LO, AIMG_TOP, kSpaceSize, kPtrArrayReserve in *. acb.
    assert (MQ : exists mq, msz = 4096 * mq) by (exists (msz / 4096); clear - MAL; try acb; Z.div_mod_to_equations; tlia). destruct MQ as [mq MQ].
    assert (SHB : 2148356096 <= sh a /\ sh a + msz / 8 <= 17594333495296 /\ msz / 8 = 512 * mq) by (clear - AHI CE MQ; try acb; aunf; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; tlia).
    destruct SHB as (SHB1 & SHB2 & SHB3).
    destruct M as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m3 & OK3 & VIS3 & SBM3 & MU & WM & MI3 & SEN3 & REN3 & ST3 & FR3 & INST3 & NRES3
                   & SST3 & MTX3 & GST3 & PA3 & HDR3 & LST3 & TST3 & SHD3).
    unfold rs_W in MU.
    assert (LENW : Z.of_nat (length (wlist (rs_chunks chunks idx nch lst))) = nch) by (apply rs_chunks_length; [exact LEN| exact IDR]).
    assert (PLL : hidden ((TH + 4096 <= lst \/ lst + 32 <= TH) /\ (CTX + 160 <= lst \/ lst + 32 <= CTX) /\ (pa + 8 * nch <= lst \/ lst + 32 <= pa))).
    { pose proof PLC as R; destruct R as [(P1 & P2 & P3 & P4 & P5 & P6)].
      destruct (Z.eq_dec idx (nch - 1)) as [IL|INE].
      - rewrite (LSTA IL). constructor. split; [clear - P4 MSZ; try acb; tlia|]. split; [clear - P5 MSZ; try acb; tlia| clear - P6 MSZ NHI IDR; try acb; tlia].
      - pose proof (PLCL ltac:(hci; clear - INE IDR; try acb; tlia)) as R; destruct R as [(Q1 & Q2 & Q3 & Q4)]. constructor.
        split; [clear - Q3; try acb; tlia|]. split; [clear - Q4; try acb; tlia| clear - Q2 NHI IDR; try acb; tlia]. }
    region_table.
    pose proof SEN3 as E3. open_senv E3.
    assert (HI3 : lo + 64 <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32))) by (rewrite unsigned_lit by tlia; tlia).
    assert (ST3' : stk asegs m3 lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)))) by (rewrite unsigned_lit by tlia; exact ST3).
    assert (ARK : (AHI_LO <= a \/ 0 <= a /\ a + 8 * (msz / 8) <= ALOWSH_LO) /\ 1 <= msz / 8 /\ a + 8 * (msz / 8) <= aceil /\ a mod 8 = 0)
      by (unfold AHI_LO, ALOWSH_LO; acb; clear - AHI CE AL MQ SHB3 MSZ; try acb; aunf; tlia).
    assert (A1 : wz msz = wz (8 * (msz / 8))) by (f_equal; clear - MQ SHB3; try acb; tlia).
    eapply (evt_sreach_lazy_at asegs L S Zr _ msF3 _ mo3 Q OK3 VIS3).
    { apply (poison_shadow_specK _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 lo a (sh a) (msz / 8) 0 sbs
               MI3 ST3' LO HI3 eq_refl A1 eq_refl eq_refl ARK ltac:(hci; clear; tlia) SHD3 SHDL Ecan Egot Eshb Ehme Ethresh Erms). }
    cbv beta. intros msF4 mo4 OK4 SBM4 HS4 P4.
    destruct P4 as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & m4 & VIS4 & MU4 & WM4 & MI4 & ST4 & ZER4).
    rewrite unsigned_lit in MU4, ST4 by tlia.
    replace (ret_pc (wz 609900)) with (Z_to_bv 64 609900) in VIS4 by (symmetry; apply ret_pc_even; [tlia|reflexivity]).
    clear Etsdi Etp Etsd Ectx Ecan Egot Eshb Ehme Ethresh Emlim Edpm Erms Epsc Ename.
    senv_img_at SEN3 MU4 WM4 SEN4. renv_img_at REN3 MU4 WM4 REN4. clear SEN3 REN3 ST3 SHD3.
    transport_after_call asegs m3 m4 MU4 WM4. clear MU4 WM4.
    apply K. unfold MID2, recycle_sec_mid2.
    exists z0, z1, z2, z10, z11, z12, z13, z14, z15, z16, z17, z3, z4, z5, z6, m4.
    split; [exact OK4|]. split; [exact VIS4|].
    split.
    {
      apply (ps0_model_mat _ _ _ mo3); [| exact SBM4]. apply (ps0_model_pre mo mo3); [exact SBM3|].
      unfold ps0_model.
      split; [apply nonvm_same_refl|]. repeat split; try reflexivity; tlia. }
    split; [unfold rs_W; exact MU|]. split; [exact WM|]. split; [exact MI4|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
  Local Ltac tr_mu MUX H := first
    [ apply (rw_cells_transport_mu _ _ _ MUX) in H; [| cbn [disjoint_from]; simpl_sizes; region_decide]
    | apply (stk_transport_mu _ _ _ MUX) in H; [| cbn [disjoint_from]; region_decide]
    | apply (u8arr_transport_mu _ _ _ MUX) in H; [| cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide]
    | apply (u64arr_transport_mu _ _ _ MUX) in H; [| cbn [disjoint_from]; simpl_sizes; rx_arr_sizes; region_decide] ].

  Lemma recycle_sec_unmap : forall msF4 mo4,
    MID2 msF4 mo4 -> (forall msF' mo', POST msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF4 mo4).
  Proof.
    intros msF4 mo4 M K.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RNG as R; destruct R as [RNG']. pose proof TPR as R; destruct R as [TPR']. pose proof SPA as R; destruct R as [SPA'].
    pose proof AR as R; destruct R as (AHI & CE & AL & MAL & MSZ). pose proof PAR as R; destruct R as (PLO & PHI & PAL). pose proof NCH as R; destruct R as (LEN & IDR & NHI).
    pose proof LR as R; destruct R as [LLO LHI].
    unfold AHI_LO, AIMG_TOP, kSpaceSize, kPtrArrayReserve in *. acb.
    assert (MQ : exists mq, msz = 4096 * mq) by (exists (msz / 4096); clear - MAL; try acb; Z.div_mod_to_equations; tlia). destruct MQ as [mq MQ].
    assert (SHB : 2148356096 <= sh a /\ sh a + msz / 8 <= 17594333495296 /\ msz / 8 = 512 * mq) by (clear - AHI CE MQ; try acb; aunf; unfold sh, ASHADOW_BASE in *; Z.div_mod_to_equations; tlia).
    destruct SHB as (SHB1 & SHB2 & SHB3).
    destruct M as (u0 & u1 & u2 & v0 & v1 & v2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m4 & OK4 & VIS4 & PM4 & MU & WM & MI4 & SEN4 & REN4 & ST4 & FR4 & INST4 & NRES4
                   & SST4 & MTX4 & GST4 & PA4 & HDR4 & LST4 & TST4 & ZER4).
    unfold rs_W in MU.
    set (L1 := L) in *.
    assert (LENW : Z.of_nat (length (wlist (rs_chunks chunks idx nch lst))) = nch) by (apply rs_chunks_length; [exact LEN| exact IDR]).
    assert (PLL : hidden ((TH + 4096 <= lst \/ lst + 32 <= TH) /\ (CTX + 160 <= lst \/ lst + 32 <= CTX) /\ (pa + 8 * nch <= lst \/ lst + 32 <= pa))).
    { pose proof PLC as R; destruct R as [(P1 & P2 & P3 & P4 & P5 & P6)].
      destruct (Z.eq_dec idx (nch - 1)) as [IL|INE].
      - rewrite (LSTA IL). constructor. split; [clear - P4 MSZ; try acb; tlia|]. split; [clear - P5 MSZ; try acb; tlia| clear - P6 MSZ NHI IDR; try acb; tlia].
      - pose proof (PLCL ltac:(hci; clear - INE IDR; try acb; tlia)) as R; destruct R as [(Q1 & Q2 & Q3 & Q4)]. constructor.
        split; [clear - Q3; try acb; tlia|]. split; [clear - Q4; try acb; tlia| clear - Q2 NHI IDR; try acb; tlia]. }
    assert (PLC2 : hidden ((TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))).
    { pose proof PLC as R; destruct R as [(P1 & _ & _ & P4 & _ & _)]. constructor. split; [clear - P4; try acb; tlia| exact P1]. }
    assert (AR2 : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ 0x10000 <= msz) by (split; [exact AHI| clear - CE AL MSZ; try acb; tlia]).
    assert (HI2 : lo + 80 <= bv_unsigned sp) by (clear - HI; try acb; tlia).

    assert (LSTC4 : idx < nch - 1 -> rw_cells asegs m4 (lst + 24) [C8 (wz idx)]) by (intros _; exact LST4). clear LST4.
    region_table.

    eapply (evt_sreach_lazy_at asegs L1 S Zr _ msF4 _ mo4 Q OK4 VIS4).
    { eapply (dealloc2a ra sp gp tp F fc m4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo a msz TSD CTX TH); try eassumption. }
    cbv beta. intros msFa moa OKa SBMa HSa Pa.
    destruct Pa as (p0 & p1 & p2 & pa4 & pa5 & pa6 & p3 & p4 & p5 & p6 & ma & VISa & MUa & WMa & MIa & STa).
    senv_img_at SEN4 MUa WMa SENa. renv_img_at REN4 MUa WMa RENa. clear SEN4 REN4 ST4.
    assert (LSTCa : idx < nch - 1 -> rw_cells asegs ma (lst + 24) [C8 (wz idx)]).
    { intros Hi. pose proof (PLCL Hi) as R; destruct R as [PL]. eapply rw_cells_transport; [exact (LSTC4 Hi)| exact MUa| exact WMa|]. cbn [disjoint_from cells_size csize length Nat.add]. clear - PL LLO LHI SPR LO HI RNG'; try acb. aunf; tlia. }
    clear LSTC4.
    transport_after_call asegs m4 ma MUa WMa. clear MUa WMa.

    eapply (sr_ecall_MS L1 S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0xcc5b4 fc None ma msFa moa Q OKa VISa ecall_aa3ac).
    intros msFb OKb VISb HSb.

    pose proof PM4 as PM; unfold ps0_model in PM; cbv beta iota zeta in PM. destruct PM as (NV4 & VM4 & VR4 & VL4 & VB4 & VK4 & VS4 & VA4 & EAG4).
    destruct (fl_pbe a msz ltac:(clear - ARE; tlia) AL ltac:(clear - MSZ; tlia)) as (FB1 & FE1 & FBE & FBA & FEA).
    set (pb := fl_pb a) in *. set (pe := fl_pe a msz) in *.
    assert (PBR : 2148356096 <= pb /\ pb + 4096 <= pe /\ pe <= 17594333495296 /\ sh a <= pb /\ pe <= sh a + msz / 8)
      by (clear - FB1 FE1 FBE SHB1 SHB2; tlia).
    assert (NZf : page_round_up_Z (bv_unsigned (wz (pe - pb))) = pe - pb).
    { unfold wz. rewrite unsigned_lit by (clear - PBR; tlia). apply page_round_up_Z_aligned; [clear - FBE; tlia|]. unfold page_size.
      clear - FBA FEA. Z.div_mod_to_equations; tlia. }
    assert (SHBAND : (sh AHI_LO <= pb /\ pb + (pe - pb) <= sh aceil) \/ (sh AIMG_TOP <= pb /\ pb + (pe - pb) <= sh ALOWSH_LO)).
    { clear - AHI CE MQ SHB3 FB1 FE1 FBE MSZ. unfold sh, ASHADOW_BASE, AHI_LO, AIMG_TOP, ALOWSH_LO in *. try acb. aunf. Z.div_mod_to_equations; tlia. }

    eapply (sr_madvise_MS L1 S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0xcc5b4 fc None ma msFb moa Q OKb VISb eq_refl);
      rewrite ?NZf; rewrite ?(same_but_materialized_vmmaps _ _ SBMa), ?VM4, ?VR4, ?VA4; unfold wz; rewrite ?(unsigned_lit pb) by (clear - PBR; tlia).
    { unfold page_size. exact FBA. }
    { reflexivity. }
    { apply wz_ne0. clear - PBR; tlia. }
    { clear - PBR; tlia. }
    { apply HSRF. rewrite !unsigned_lit by (clear - PBR; tlia). exact SHBAND. }
    { apply HSMC; rewrite !unsigned_lit by (clear - PBR; tlia); [clear - FBE; tlia| exact SHBAND]. }
    { apply HSNA. rewrite !unsigned_lit by (clear - PBR; tlia). exact SHBAND. }
    { intros x Hx _. apply ZRSH. clear - Hx SHBAND. unfold AHI_LO, AIMG_TOP in SHBAND. tlia. }
    intros msFc. cbv zeta. rewrite ?NZf. intros OKc VISc HSc SBMc.
    change (837044 + 4) with 837048 in VISc.
    rewrite (mzero_zfill_S L1 S) in VISc
      by (unfold wz; rewrite !unsigned_lit by (clear - PBR; tlia); intros x Hx; apply WIN; clear - Hx PBR; tlia).
    rewrite (zfill_zero_id _ _ ma (sh a) (Z.to_nat (msz / 8)) ZER4) in VISc
      by (unfold wz; rewrite ?unsigned_lit by (clear - PBR; tlia); clear - PBR SHB1; tlia).
    set (moc := madvise_dontneed_next moa (wz pb) (Z_to_bv 64 (pe - pb))) in *.

    eapply (evt_sreach_lazy_at asegs L1 S Zr _ msFc _ moc Q OKc VISc).
    { eapply (dealloc2b ra sp gp tp F fc ma _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo a msz TSD CTX TH); try eassumption. }
    cbv beta. intros msF5 mo5 OK5 SBMd HS5 P5.
    assert (SBM5 : same_but_materialized mo4 mo5).
    { eapply same_but_materialized_trans; [exact SBMa|]. eapply same_but_materialized_trans; [exact SBMc| exact SBMd]. }
    destruct P5 as (w0 & w1 & w2 & wa2 & wa3 & wa4 & wa5 & wa6 & w3 & w4 & w5 & w6 & j16 & m5 & VIS5 & MU5 & WM5 & MI5 & ST5 & FR5 & TST5).
    senv_img_at SENa MU5 WM5 SEN5. renv_img_at RENa MU5 WM5 REN5. clear SENa RENa STa FR4 TST4 HDR4.
    assert (LSTC5 : idx < nch - 1 -> rw_cells asegs m5 (lst + 24) [C8 (wz idx)]).
    { intros Hi. pose proof (PLCL Hi) as R; destruct R as [PL]. eapply rw_cells_transport; [exact (LSTCa Hi)| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize length Nat.add]. clear - PL LLO LHI SPR LO HI RNG'; try acb. aunf; tlia. }
    clear LSTCa.
    transport_after_call asegs ma m5 MU5 WM5. clear MU5 WM5.

    eapply (sr_ecall_MS L1 S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0xcc57c fc None m5 msF5 mo5 Q OK5 VIS5 ecall_aa374).
    intros msF6 OK6 VIS6 HS6.
    assert (NZ : page_round_up_Z (bv_unsigned (wz msz)) = msz).
    { unfold wz. rewrite unsigned_lit by tlia. apply page_round_up_Z_aligned; [tlia|]. unfold page_size. rewrite MQ, Z.mul_comm. apply Z_mod_mult. }
    assert (NWA4 : entries_nowrap (vm_noaccess (m_vmmaps mo4))) by (rewrite VA4; exact NWA).

    assert (RL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x L1 = false) by exact NOL.

    eapply (sr_munmap_MS L1 S Zr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F 0xcc57c fc None m5 msF6 mo5 Q OK6 VIS6 eq_refl);
      rewrite ?NZ; rewrite ?(same_but_materialized_vmmaps _ _ SBM5), ?VM4.
    { unfold wz, page_size. rewrite unsigned_lit by tlia. clear - AL; try acb; Z.div_mod_to_equations; tlia. }
    { apply wz_ne0. tlia. }
    {   unfold wz, TASK_SIZE. rewrite unsigned_lit by tlia. acb. tlia. }
    { exact HAS. }
    { exact NOV. }
    { exact NW. }
    { exact NWA4. }
    { intros x. unfold wz. rewrite unsigned_lit by tlia. exact (RL x). }
    intros msF7. cbv zeta. rewrite ?NZ. unfold wz at 1 2 3 4 5 6. rewrite ?(unsigned_lit a) by tlia.
    intros OK7 VIS7 HS7 HID7 EAG7.
    change (836988 + 4) with 836992 in VIS7.
    set (mo7 := munmap_model (wz a) (Z_to_bv 64 msz) mo5) in *.
    set (m7 := unfill (wz a) (Z_to_bv 64 msz) m5) in *.
    assert (MU7 : munch [(a, a + msz)] m5 m7).
    { subst m7. pose proof (unfill_munch (wz a) (Z_to_bv 64 msz) m5) as X. unfold wz in X. rewrite !unsigned_lit in X by tlia. exact X. }
    assert (MI7 : mem_inv asegs m7) by (subst m7; apply unfill_mem_inv; exact MI5).
    assert (WMO7 : wmono_out [(a, a + msz)] m m7).
    { eapply wmono_out_wmono_l; [exact WM|]. subst m7. pose proof (unfill_wmono_out (wz a) (Z_to_bv 64 msz) m5) as X. unfold wz in X. rewrite !unsigned_lit in X by tlia. exact X. }
    assert (NONE7 : forall x : word, a <= bv_unsigned x < a + msz -> m7 x = None).
    { intros x Hx. subst m7. apply unfill_none. unfold wz. rewrite !unsigned_lit by tlia. exact Hx. }

    assert (REM : rem (wz a, Z_to_bv 64 msz) (cuts mo5) = msz).
    { rewrite rem_uncovered. { cbn [snd]. apply unsigned_lit. tlia. }
      intros x Hx. unfold BazyLedger.lo, BazyLedger.hi in Hx. cbn [fst snd] in Hx. unfold wz in Hx. rewrite !unsigned_lit in Hx by tlia.
      unfold cuts. pose proof (li_lazy _ _ _ (lzok_inv OK6)) as LZ5. cbn [cfg_model] in LZ5. rewrite LZ5.
      apply zcovb_app_false.
      - rewrite (same_but_materialized_vmmaps _ _ SBM5), VA4. apply in_rangesb_false_zcovb; [tlia|]. apply NOACC. unfold wz. rewrite unsigned_lit by tlia. tlia.
      - apply in_rangesb_false_zcovb; [tlia|]. apply RL. unfold wz. rewrite unsigned_lit by tlia. tlia. }

    tr_mu MU7 ST5. tr_mu MU7 FR5. tr_mu MU7 TST5. tr_mu MU7 INST4. tr_mu MU7 NRES4. tr_mu MU7 SST4. tr_mu MU7 MTX4. tr_mu MU7 GST4. tr_mu MU7 PA4. tr_mu MU7 ZER4.
    assert (LSTC7 : idx < nch - 1 -> rw_cells asegs m7 (lst + 24) [C8 (wz idx)]).
    { intros Hi. pose proof (PLCL Hi) as R; destruct R as [PL]. pose proof (LSTC5 Hi) as X. apply (rw_cells_transport_mu _ _ _ MU7) in X; [exact X|]. cbn [disjoint_from cells_size csize length Nat.add]. clear - PL; try acb. tlia. }
    clear LSTC5.
    assert (SEN7 : SENV tp TSD CTX TH m7) by (apply (senv_transport_mu _ _ _ MU7 _ _ _ _ SEN5); cbn [disjoint_from]; region_decide).
    assert (REN7 : RENV g b244 m7) by (apply (renv_transport_mu _ _ _ MU7 _ _ REN5); cbn [disjoint_from]; region_decide).
    clear SEN5 REN5.

    assert (MUA : munch [(lo, bv_unsigned sp); (1628744, 1629360); (pa, pa + 8 * nch); (a, a + msz); (lst + 24, lst + 32); (sh a, sh a + msz / 8); (TH + 2800, TH + 3168)] m m7).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU7]. unfold sub_fp; cbn [outside]. intros; tauto. }
    clear MU WM MI5 MU7.

    eapply (evt_sreach_lazy_at asegs (maps_subtract L1 a (a + msz)) S Zr _ msF7 _ mo7 Q OK7 VIS7).
    { eapply (dealloc3 ra sp gp tp F fc m7 _ _ _ _ _ _ _ _ _ _ _ _ s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j16 lo a msz TSD CTX TH); try eassumption.
      all: clear - MSZ; try acb; tlia. }
    cbv beta. intros msF8 mo8 OK8 SBM8 HS8 P8.
    destruct P8 as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m8 & VIS8 & MU8 & WM8 & MI8 & ST8).
    senv_img_at SEN7 MU8 WM8 SEN8. renv_img_at REN7 MU8 WM8 REN8. clear SEN7 REN7 ST5 FR5.
    assert (NONE8 : forall x : word, a <= bv_unsigned x < a + msz -> m8 x = None).
    { eapply (none_range_munch _ m7 m8 a (a + msz) NONE7 MU8). cbn [disjoint_from]. clear - LO CE SPR HI; try acb; tlia. }
    assert (WMO8 : wmono_out [(a, a + msz)] m m8) by (eapply wmono_out_wmono_r; [exact WMO7| exact WM8]).
    assert (LSTC8 : idx < nch - 1 -> rw_cells asegs m8 (lst + 24) [C8 (wz idx)]).
    { intros Hi. pose proof (LSTC7 Hi) as X. eapply rw_cells_transport; [exact X| exact MU8| exact WM8|]. cbn [disjoint_from cells_size csize length Nat.add]. clear - LO LHI SPR HI; try acb; tlia. }
    clear NONE7 WMO7 LSTC7.
    transport_after_call asegs m7 m8 MU8 WM8. clear MU8 WM8.

    apply K. unfold POST, recycle_sec_post, rs_L. fold L1.
    exists y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m8.
    split; [exact OK8|]. split; [exact VIS8|].
    split.
    {
      apply (rs_model_mat _ _ _ mo7); [| exact SBM8]. subst mo7. unfold rs_model.
      rewrite munmap_model_eqL, munmap_modelL_vmmaps. unfold munmap_vmmaps. cbn [vm_maps vm_reserved vm_limit vm_mmap_base vm_brk vm_start_brk vm_noaccess].
      rewrite (same_but_materialized_vmmaps _ _ SBM5), VM4, VR4, VL4, VB4, VK4, VS4, VA4.
      unfold wz. rewrite !unsigned_lit by tlia.
      split. { eapply nonvm_same_trans; [exact NV4|]. eapply nonvm_same_trans; [apply nonvm_same_mat; exact SBM5|]. rewrite <- munmap_model_eqL. apply nonvm_same_munmap. }
      repeat match goal with |- _ /\ _ => split end; try reflexivity.
      rewrite <- munmap_model_eqL. pose proof (same_but_materialized_eager _ _ SBM5) as E5. unfold wz in EAG7, REM. rewrite REM in EAG7. clear - EAG7 E5 EAG4; try acb. tlia. }
    split; [exact MUA|]. split; [exact WMO8|]. split; [exact MI8|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
  Qed.
End SecRecycle2.

End HCW.

