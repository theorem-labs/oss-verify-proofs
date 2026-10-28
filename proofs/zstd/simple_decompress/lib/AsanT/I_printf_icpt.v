(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ShadowTac F_irt F_rip F_tryinit I_printf_lib I_printf_common I_printf_formats.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac addr_eq_tac ::= addr_eq_tac_fast.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.

(* [comment removed for export] *)
Notation rt_ckpf m := (rw_cells bsegs m 0x161878 [C8 (Z_to_bv 64 4294967296)]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma vfprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j16 : list byte) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 16 j16; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x475f8) fc None m (seg_rom bsegs)).
Proof.
  intros until s2v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma vprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j24 : list byte) (rav s0v s1v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 24 j24; C8 s1v; C8 s0v; C8 rav] ->
  rng RNG (bv_unsigned sp) 48 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46a88) fc None m (seg_rom bsegs)).
Proof.
  intros until s1v. intros MI FR RR. pose proof (rw_cells_bound _ _ _ _ FR) as B. cbn in B.
  do 5 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fprintf_i_post : forall RNG x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (j32 : list byte) (va : list cell) (rav s0v s1v s2v : word),
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) ([CB 32 j32; C8 s2v; C8 s1v; C8 s0v; C8 rav] ++ va) -> cells_size va = 48%nat ->
  rng RNG (bv_unsigned sp) 112 ->
  evtF bsegs RNG (fun ms' => ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 112)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (ret_pc rav) fc None m (seg_rom bsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47a14) fc None m (seg_rom bsegs)).
Proof.
  intros until s2v. intros MI FR SZ RR. pose proof (rw_cells_bound _ _ _ _ FR) as B.
  rewrite cells_size_app, SZ in B. cbn in B.
  apply (proj1 (rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FR FRV].
  do 6 zstep. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
End CANSEC1.
Ltac iprem :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- mem_inv _ _ => first [assumption | eassumption]
  | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; iprem
  | |- stk _ _ _ _ => first [assumption | eassumption]
  | |- rw_cells _ _ _ _ => rewrite ?Z_to_bv_bv_unsigned; first [assumption | eassumption]
  | |- shadow_bytes _ _ _ _ => first [assumption | eassumption]
  | |- bytes_at _ _ _ _ => first [assumption | eassumption]
  | |- unpoisoned _ _ _ => first [assumption | eassumption]
  | |- wr_at _ _ _ _ => first [assumption | eassumption]
  | |- app_blk _ _ => first [assumption | eassumption]
  | |- Forall _ _ => first [assumption | eassumption]
  | |- _ = Z_to_bv 64 _ => first [reflexivity | assumption | symmetry; assumption]
  | |- rng _ _ _ => first [ assumption | match goal with H : rng _ _ _ |- _ => eapply rng_sub'; [exact H | unfold KHIGH, sf_hide in *; lia] end]
  | |- ?g => unfold KHIGH, sf_hide in *; first [assumption | lia]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition fprintf_i_mid (ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j32,
    ms' = MS (mkR (Z_to_bv 64 0x47a14) (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2
                  a1 a0 a0 a1 (Z_to_bv 64 (bv_unsigned sp - 48)) x13 x14 x15 x16 x17
                  (Z_to_bv 64 (bv_unsigned sp - 48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbce78) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2432, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 112)
    /\ rw_cells bsegs m' (bv_unsigned sp - 112)
         [CB 32 j32; C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]
    /\ rt_inited m'.

Section FPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2432)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A1 : a1 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).

  Notation MID := (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  (* [comment removed for export] *)
  Lemma fprintf_i_A : forall Q,
    (forall m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
       munch [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       stk bsegs m1 lo (bv_unsigned sp + -112) ->
       rw_cells bsegs m1 (bv_unsigned sp + -112)
         [CB 8 j8; C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48)); C8 (Z_to_bv 64 (bv_unsigned sp + -48));
          C8 s2; C8 s1; C8 s0; C8 ra; C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
       rt_got m1 -> rt_shbase m1 -> rt_inited m1 -> rt_real_printf m1 ->
       evtF bsegs RNG Q (MS (mkR (Z_to_bv 64 0x479d4) (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp x5 x6 x7 a1 a0
                              (Z_to_bv 64 0x1ed3c) a1 (Z_to_bv 64 (bv_unsigned sp + -48)) x13 x14 x15 x16 x17
                              (Z_to_bv 64 (bv_unsigned sp + -48)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                            F (Z_to_bv 64 0x46ac0) fc None m1 (seg_rom bsegs))) ->
    evtF bsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).
  Proof.
    intros Q K.
    pose proof (munch_refl [(bv_unsigned sp + -2432, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 112%nat ST0.
    do 15 zstep. zstep.
    call_sp tryinit_spec. all: match goal with |- ?g => idtac "=="; idtac g end. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    zstep. zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 4 zstep. zstep.
    eapply K; try assumption; eassumption.
  Qed.

  Hypothesis PCI : printf_common_int_stmt A n.

  Lemma fprintf_i_pre_int :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed.

  (* [comment removed for export] *)
  Variables (sstr : list byte) (RLO RHI : Z).
  Notation Sa := (bv_unsigned a2).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis LAY : rt_layout m.
  Hypothesis SSTR : bytes_at bsegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis APPS : app_blk Sa (Sa + NS).
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis USTR : unpoisoned m Sa (Sa + NS).
  Hypothesis NSZ : (NS <= 2^40)%Z.
  Hypothesis R1 : (RLO <= Sa /\ Sa + NS <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z.
  Hypothesis WR1 : wr_at bsegs m (shad RLO) (shad RHI - shad RLO).
  Hypothesis RS : rng RNG Sa NS.
  Hypothesis RSH1 : rng RNG (shad RLO) (shad RHI - shad RLO).
  Hypothesis PCS : printf_common_s_stmt A n.

  Lemma fprintf_i_pre_s :
    evtF bsegs RNG MID (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).
  Proof.
    apply fprintf_i_A. intros m1 j8 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU1 WM1 MI1 ST1 FR1 GOT1 SHB1 INI1 RPF1.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2432) 2432) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof APPS as APPS'. destruct APPS' as [LES AS']. unfold KLOW, KHIGH, KEND in AS'.
    assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z)).
    { eapply shadow_bytes_munch; [exact FZ | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
    assert (LAY1 : rt_layout m1).
    { eapply rw_cells_transport; [exact LAY | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
    assert (SSTR1 : bytes_at bsegs m1 Sa (sstr ++ [Z_to_bv 8 0])).
    { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    assert (USTR1 : unpoisoned m1 Sa (Sa + NS)).
    { eapply unpoisoned_munch; [exact USTR | exact MU1 |]. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Z.div_mod_to_equations; lia. }
    assert (WR11 : wr_at bsegs m1 (shad RLO) (shad RHI - shad RLO)) by (eapply wr_at_transport; eassumption).
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF; change (?P) with (sf_hide P) in FZ; change (?P) with (sf_hide P) in LAY;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in USTR; change (?P) with (sf_hide P) in WR1.
    chunk_split FR1 8%nat FRV. chunk_split FRV 1%nat FRW.
    call_sp PCS. all: iprem.
    chunk_join FRV FRW. chunk_join FR1 FRV.
    do 4 zstep. do 3 zstep. zstep.
    apply evtF_done. unfold fprintf_i_mid.
    replace (bv_unsigned sp - 112)%Z with (bv_unsigned sp + -112)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2432)%Z with (bv_unsigned sp + -2432)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FR : rw_cells bsegs mf (bv_unsigned sp + -112) (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3; c4] rest FR) as FRm; cbn [app cells_size csize Nat.add] in FRm end end.
    do 14 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm.
  Qed.
End FPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vprintf_i_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 x13 x14 x15 x16 x17 t3 t4 t5 t6 m' j24 j16,
    ms' = MS (mkR (Z_to_bv 64 0x475f8) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2
                  a0 (Z_to_bv 64 0xcb9f8) (Z_to_bv 64 0xcb9f8) a0 a1 x13 x14 x15 x16 x17
                  a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbce78) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2416, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 96)
    /\ rw_cells bsegs m' (bv_unsigned sp - 48) [CB 24 j24; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' (bv_unsigned sp - 96) [CB 16 j16; C8 s2; C8 a1; C8 a0; C8 (Z_to_bv 64 0x46a88)]
    /\ rt_inited m'.

Section VPRINTF.
  Variables (RNG : footprint)
            (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (A n : Z).
  Hypothesis MI : mem_inv bsegs m.
  Hypothesis ST : stk bsegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2416)%Z.
  Hypothesis KLO : (KHIGH <= lo)%Z.
  Hypothesis GOT : rt_got m.
  Hypothesis SHB : rt_shbase m.
  Hypothesis INI : rt_inited m.
  Hypothesis CKP : rt_ckpf m.
  Hypothesis RPF : rt_real_printf m.
  Hypothesis A0 : a0 = Z_to_bv 64 A.
  Hypothesis NA : (0 <= n /\ 65536 <= A - 64 /\ A + n + 64 < 2^47)%Z.
  Hypothesis FZ : shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RSHF : rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)).
  Hypothesis PCI : printf_common_int_stmt A n.

  Lemma vprintf_i_pre :
    evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x46a24) fc None m (seg_rom bsegs)).
  Proof.
    pose proof (munch_refl [(bv_unsigned sp + -2416, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption). unfold KHIGH in KLO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in SPR.
    assert (RSTK' : rng RNG (bv_unsigned sp + -2416) 2416) by (eapply rng_sub'; [exact RSTK| lia]).
    pose proof MI as MIc. pose proof ST as ST0. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof INI as INIc.
    pose proof CKP as CKPc. pose proof RPF as RPFc.
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in INI; change (?P) with (sf_hide P) in CKP;
    change (?P) with (sf_hide P) in RPF.
    recell CKPc 0%nat 1%nat [C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 1); CB 3 (repeat (Z_to_bv 8 0) 3)].
    carve_frame 48%nat ST0.
    do 7 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1. cbv in K1. lia. } clear K1.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. } clear K2.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ1 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)
    end end.
    change (?P) with (sf_hide P) in FZ.
    call_sp PCI. all: iprem.
    clear FZ1.
    (* [comment removed for export] *)
    do 4 zstep. zstep.
    do 7 zstep. zstep.
    (* [comment removed for export] *)
    match goal with H : stk bsegs _ lo (bv_unsigned sp + -48) |- _ => carve_frame 48%nat H end.
    do 9 zstep. zstep.
    call_sp tryinit_spec. all: iprem.
    zstep. if_cases K3; zify_cond K3. { exfalso. clear -K3. cbv in K3. lia. } clear K3.
    do 3 zstep. zstep. cbv beta. rewrite unsigned_lit8 by lia. zstep. zstep. if_cases K4; zify_cond K4. { exfalso. clear -K4. cbv in K4. lia. } clear K4.
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) => lazymatch goal with MU1 : munch _ m m1 |- _ =>
      assert (FZ2 : shadow_bytes m1 (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z))
        by (unfold sf_hide in FZ; eapply shadow_bytes_munch; [exact FZ | exact MU1 |]; cbn [disjoint_from]; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia)
    end end.
    call_sp PCI. all: iprem.
    clear FZ2.
    do 5 zstep. zstep.
    apply evtF_done. unfold vprintf_i_mid.
    replace (bv_unsigned sp - 96)%Z with (bv_unsigned sp + -96)%Z by lia.
    replace (bv_unsigned sp - 48)%Z with (bv_unsigned sp + -48)%Z by lia.
    replace (bv_unsigned sp - 2416)%Z with (bv_unsigned sp + -2416)%Z by lia.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
      lazymatch goal with FRa : rw_cells bsegs mf (bv_unsigned sp + -48) (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2; c3] rest FRa) as FRm1; cbn [app cells_size csize Nat.add] in FRm1 end;
      lazymatch goal with FRb : rw_cells bsegs mf (bv_unsigned sp + -96) (?c1 :: ?c2 :: ?rest) |- _ =>
        pose proof (rw_cells_merge bsegs mf _ [] [c1; c2] rest FRb) as FRm2; cbn [app cells_size csize Nat.add] in FRm2 end end.
    do 15 eexists. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split end; try assumption. exact FRm1. exact FRm2.
  Qed.
End VPRINTF.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Corollary vprintf_i_pre_d : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2416)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a0 = Z_to_bv 64 FMT_D ->
  shadow_bytes m (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_D - 64)) (shad (FMT_D + 3 + 64) - shad (FMT_D - 64)) ->
  evtF bsegs RNG (vprintf_i_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46a24) fc None m (seg_rom bsegs)).
Proof. intros. eapply vprintf_i_pre; try eassumption. { unfold FMT_D. lia. } exact printf_common_d_stmt. Qed.

Corollary fprintf_i_pre_toobig : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m ->
  a1 = Z_to_bv 64 FMT_TOOBIG ->
  shadow_bytes m (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64)) (fun _ => 0%Z) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (FMT_TOOBIG - 64)) (shad (FMT_TOOBIG + 32 + 64) - shad (FMT_TOOBIG - 64)) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).
Proof. intros. eapply fprintf_i_pre_int; try eassumption. { unfold FMT_TOOBIG. lia. } exact printf_common_toobig_stmt. Qed.

(* [comment removed for export] *)
Definition fprintf_i_pre_s_stmt (A n : Z) : Prop :=
  forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (sstr : list byte) (RLO RHI : Z),
  mem_inv bsegs m -> stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2432)%Z -> (KHIGH <= lo)%Z ->
  rt_got m -> rt_shbase m -> rt_inited m -> rt_ckpf m -> rt_real_printf m -> rt_layout m ->
  a1 = Z_to_bv 64 A ->
  shadow_bytes m (shad (A - 64)) (shad (A + n + 64)) (fun _ => 0%Z) ->
  bytes_at bsegs m (bv_unsigned a2) (sstr ++ [Z_to_bv 8 0]) -> Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr ->
  (bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= bv_unsigned sp - 2432 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  app_blk (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (0 < bv_unsigned a2)%Z ->
  unpoisoned m (bv_unsigned a2) (bv_unsigned a2 + (Z.of_nat (length sstr) + 1)) -> (Z.of_nat (length sstr) + 1 <= 2^40)%Z ->
  (RLO <= bv_unsigned a2 /\ bv_unsigned a2 + (Z.of_nat (length sstr) + 1) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND)%Z ->
  wr_at bsegs m (shad RLO) (shad RHI - shad RLO) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (shad (A - 64)) (shad (A + n + 64) - shad (A - 64)) ->
  rng RNG (bv_unsigned a2) (Z.of_nat (length sstr) + 1) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
  evtF bsegs RNG (fprintf_i_mid ra sp gp tp s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x47954) fc None m (seg_rom bsegs)).

End CANSEC2.
Ltac fis PC A := unfold fprintf_i_pre_s_stmt; intros; eapply fprintf_i_pre_s; try eassumption; [unfold A; lia | exact PC].
Section CANSEC3. Context {rc : runConstT}.
Corollary fprintf_i_pre_usage : fprintf_i_pre_s_stmt FMT_USAGE 16. Proof. fis printf_common_usage_spec FMT_USAGE. Qed.
Corollary fprintf_i_pre_cantopen : fprintf_i_pre_s_stmt FMT_CANTOPEN 20. Proof. fis printf_common_cantopen_spec FMT_CANTOPEN. Qed.
Corollary fprintf_i_pre_readerr : fprintf_i_pre_s_stmt FMT_READERR 22. Proof. fis printf_common_readerr_spec FMT_READERR. Qed.
End CANSEC3.
