(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocKit_B MallocKit_B2 MallocFacts_Bpres.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require F_free F_free_spec.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.MallocFacts_Bpres OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_free.F_ntf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_free.F_free_K OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc.F_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require RF_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require RF_free.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require RF_free RF_get_meta RF_allzerop.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RMallocRep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RMallocTree OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RMallocKit_B OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RMallocKit_B2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RMalloc_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RF_free.RF_ntf OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RF_free.RF_free_K OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RF_free OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RF_get_meta OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU.RF_allzerop.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import HdrGuards MallocTree.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_inv.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma rallzerop_live : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list block) (st : mstate) (blk : block) (off : Z),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  hdr_ok pans_mem pupd_mem st (aadd (blk_slot blk) (UNIT * off)) (blk_slot blk) ->
  rmrep st m -> mem_inv usegs m ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  c_init_done (ctx st) <> 0 ->
  evt usegs (rallzerop_postZ ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc m st (blk_slot blk))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until off. intros C Hin Hoff HA HOK MR MI A0 INI.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (pose proof (round_up_pg_ge (r_len r)); lia).
  clear SIM SM B16 RBAL AL.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  destruct HOK as (st1 & g' & idx' & RUN & _). specialize (RUN m).
  destruct (free_hdr_guards pans_mem pupd_mem m st pf st1 g' idx' v3 lo8 hi (mkGhdr (Some g) ai) g RUN) as (G12 & G13 & G14 & (ar & AR1 & G15) & G16 & G16b & G17).
  { unfold pf; cbn [aadd fst snd]. replace (snd c0 + UNIT * off + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). exact OK. }
  { unfold pf; cbn [aadd fst snd]. replace (snd c0 + UNIT * off + -3) with (snd c0 + UNIT * off - 3) by lia. exact C3. }
  { unfold pf; cbn [aadd fst snd]. replace (snd c0 + UNIT * off + -2) with (snd c0 + UNIT * off - 2) by lia. exact C2. }
  { unfold pf; cbn [aadd fst snd]. replace (snd c0 + UNIT * off + -2 + 1) with (snd c0 + UNIT * off - 1) by lia. exact C1. }
  { rewrite EB. exact Hgh. }
  { reflexivity. }
  rewrite V31 in G12, G13, G14, G16.
  eapply (rallzerop_specZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi (blk_slot blk) i);
    first [exact MR | exact MI | exact Kr | idtac].
  all: rewrite ?EB, ?V31.
  - rewrite Fp. exact Hr.
  - rewrite A0, HAp. apply unsigned_lit. lia.
  - exact P16m.
  - rewrite Sp, Sc. lia.
  - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
  - exact PHI.
  - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
  - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
  - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
  - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
  - exact Hgh.
  - reflexivity.
  - exact (go_slot _ _ _ GO).
  - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
  - exact (go_mem _ _ _ GO).
  - exact AR1.
  - exact G15.
  - exact INI.
  - exact (go_avail _ _ _ GO).
  - exact (go_freed _ _ _ GO).
  - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
  - lia.
  - rewrite (go_freeable _ _ _ GO). lia.
  - pose proof (go_sc _ _ _ GO). lia.
  - pose proof (go_maplen _ _ _ GO). lia.
  - exact G12.
  - exact G13.
  - exact G14.
  - exact G16.
  - exact G16b.
  - intros Hml. specialize (G17 Hml). unfold UNIT in G17.
    replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
    rewrite Z.div_mul in G17 by lia. lia.
  - exact SL.
Qed.

Lemma rallzerop_heap : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A n : Z),
  RHEAP s LB m -> In (p, A, n) LB -> mem_inv usegs m ->
  a0 = Z_to_bv 64 A ->
  evt usegs (rallzerop_postZ ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 F fc m (ps_m s) (fst p))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rallzerop_entry) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until n. intros HP Hin MI A0.
  destruct HP as (st & LB0 & PERM & Hst & MR & [BL AR]).
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  pose proof (MallocFacts_inv.areach_hdr_ok_proof st LB0 (p, A, n) off AR Hin0 O0 OA) as HOK.
  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL' & (IR & IA & _) & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. pose proof (go_slot _ _ _ (ci_gmetas _ _ C b g HBg)) as (a & ar & k & Ha & _).
    rewrite E0 in Ha. rewrite lookup_empty in Ha. discriminate. }
  rewrite <- Hst.
  exact (rallzerop_live ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m LB0 st (p, A, n) off
           C Hin0 O0 OA HOK MR MI A0 INI).
Qed.
End WithCeiling0.
