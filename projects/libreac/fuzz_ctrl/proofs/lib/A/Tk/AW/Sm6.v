(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/SmLeaf.v, with its module paths, module names and numbers changed; 359 of its 393 lines of code are new or changed and 353 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Tac Image ZBridge Arr SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AK Require Import StepFast StoreFast LiaFix.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLeaf SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.asan_stack_malloc_c_on.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_ul.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step_core segs R F pc fc rv m ro ::= step_core_fast segs R F pc fc rv m ro.
Local Ltac zsimp ::= zsimp_fast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_guard | solve_load_image ].

Section Loop.
  Variables (sp gp tp t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (FS hZ : Z) (flags : list byte) (Q : machine_state -> Prop).
  Hypothesis FS0 : 0 < FS.
  Hypothesis FSB : FS + 11571200 <= 2 ^ 64.
  Hypothesis HR : 0 <= hZ < 2 ^ 64.
  Hypothesis FLB : bytes_at rsegs m (FS + 36352) flags.
  Hypothesis FLEN : Z.of_nat (length flags) = 256.
  Hypothesis F01 : Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags.
  Abbreviation LS pc x5 x10 x12 x14 x17 :=
    (MS (mkR (Z_to_bv 64 0x3da7c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 t1 t2 sp (Z_to_bv 64 FS)
             x10 (Z_to_bv 64 (FS + 4096)) x12 (Z_to_bv 64 (FS + 36352)) x14 (Z_to_bv 64 255) (Z_to_bv 64 (hZ + 256)) x17
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Hypothesis KF : forall j (x5 : word), 0 <= j < 256 ->
    (forall i', 0 <= i' < j -> nth_error flags (Z.to_nat ((hZ + i') mod 256)) = Some (Z_to_bv 8 1)) ->
    nth_error flags (Z.to_nat ((hZ + j) mod 256)) = Some (Z_to_bv 8 0) ->
    evt rsegs Q (LS 0x3db64 x5 (Z_to_bv 64 (256 - j)) (Z_to_bv 64 (hZ + j))
                   (Z_to_bv 64 (FS + 36352 + (hZ + j) mod 256)) (Z_to_bv 64 ((hZ + j) mod 256))).
  Hypothesis KE : forall (x5 x12 x14 x17 : word),
    (forall i', 0 <= i' < 256 -> nth_error flags (Z.to_nat ((hZ + i') mod 256)) = Some (Z_to_bv 8 1)) ->
    evt rsegs Q (LS 0x3db08 x5 (Z_to_bv 64 0) x12 x14 x17).

  Lemma probe (k : nat) : forall i (x5 x14 x17 : word),
    Z.to_nat (256 - i) = k -> 0 <= i < 256 ->
    (forall i', 0 <= i' < i -> nth_error flags (Z.to_nat ((hZ + i') mod 256)) = Some (Z_to_bv 8 1)) ->
    evt rsegs Q (LS 0x3daec x5 (Z_to_bv 64 (256 - i)) (Z_to_bv 64 (hZ + i)) x14 x17).
  Proof using FS0 FSB HR FLB FLEN F01 KF KE.
    induction k as [|k IH]; intros i x5 x14 x17 Hk Hi ONES; [lia|].
    assert (PR : 0 <= (hZ + i) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    destruct (flag_read m (FS + 36352) flags ((hZ + i) mod 256) FLB ltac:(lia) F01) as (b & NTH & B01 & RD).
    zstep. rewrite (land_mod_low _ 8 255 256) by first [reflexivity | lia].
    zstep.
    destruct B01 as [-> | ->].
    - zstep. try change (bv_unsigned (Z_to_bv 8 0)) with 0.
      zstep. if_true.
      apply KF; [lia| exact ONES| exact NTH].
    - zstep. try change (bv_unsigned (Z_to_bv 8 1)) with 1.
      zstep. if_false.
      zstep. rewrite swrap32_small by lia.
      zstep. zstep. if_cases K; zify_cond K.
      + assert (Hi1 : i + 1 < 256) by (first [lia | rewrite Z.mod_small in K by lia; lia]).
        replace (256 - i + -1) with (256 - (i + 1)) by lia. replace (hZ + i + 1) with (hZ + (i + 1)) by lia.
        apply IH; [lia| lia|]. intros i' Hi'. destruct (Z.eq_dec i' i) as [->|NE]; [exact NTH| apply ONES; lia].
      + assert (Hi1 : i = 255) by (first [lia | rewrite Z.mod_small in K by lia; lia]).
        replace (256 - i + -1) with 0 by lia.
        apply KE. intros i' Hi'. destruct (Z.eq_dec i' i) as [->|NE]; [exact NTH| apply ONES; lia].
  Qed.
End Loop.

Theorem stack_malloc_6 : asan_stack_malloc_6_contract.
Proof.
  unfold asan_stack_malloc_6_contract, asan_stack_malloc_contract, ASAN_STACK_MALLOC_6, ASAN_STACK_MALLOC_K. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags.
  intros HL HL8 AC SRW MI0 TLS _ FSP PL SSL0 GC0 HINT0 FLG0 FLEN F01 ST0 LOK ROOM APS DISJ.
  apply ul_entry. rewrite mkR_ul.
  destruct (tls_leaf m (bv_unsigned tp) DT TS C T DB k AC TLS) as (tb & te & LC).
  pose proof (m2s_of_asan m AC) as M2. clear AC TLS.
  destruct PL as (FS0 & FS4K & FSGT & FAPP & FSTK0).
  assert (STF : stk rsegs m FS (FS + FS_SIZE)) by exact FSTK0. clear FSTK0.
  assert (ST : stk rsegs m lo (bv_unsigned sp)) by exact ST0. clear ST0.
  assert (MI : mem_inv rsegs m) by exact MI0. clear MI0.
  assert (TPE : tp = Z_to_bv 64 (bv_unsigned tp)) by (symmetry; apply Z_to_bv_lit_self).
  assert (AP : leaf_apart (bv_unsigned tp) (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T) (bv_unsigned DB) k
                 (bv_unsigned sp - 208) (bv_unsigned sp)).
  { split; [unfold FS_SIZE, ASAN_GT in *; lia|]. split; [lia|]. split; [pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R; cbn in R; lia|].
    replace (bv_unsigned sp - (bv_unsigned sp - 208)) with 208 by lia. exact DISJ. }
  clear DISJ.
  pose proof AP as (_ & _ & _ & DJ). unfold leaf_ivs in DJ. cbn [disjoint_from] in DJ.
  destruct DJ as (DJ1 & DJ2 & DJ3 & DJ4 & DJ5 & DJ6 & DJ7 & _).
  assert (TPC : ro_cells rsegs m (bv_unsigned tp) [C8 (Z_to_bv 64 FS)]) by (apply ro8; exact FSP). clear FSP.
  assert (SSL : ro_cells rsegs m (FS + 88) [C8 (Z_to_bv 64 20)]) by (apply ro8; exact SSL0). clear SSL0.
  assert (GCC : ro_cells rsegs m (FS + 96) [C1 (Z_to_bv 8 0)]) by (apply ro1; exact GC0). clear GC0.
  replace (fs_hint FS 6) with (FS + 48) in HINT0 by (unfold fs_hint; simpl; lia).
  rewrite <- (Z_to_bv_lit_self h) in HINT0.
  assert (HN : rw_cells rsegs m (FS + 48) [C8 (Z_to_bv 64 (bv_unsigned h))]).
  { apply (stk_rw m FS (FS + FS_SIZE)); [exact STF| apply ro8; exact HINT0| lia| cbn; unfold FS_SIZE; lia]. }
  clear HINT0.
  replace (fs_flag FS 6 0) with (FS + 36352) in FLG0 by (unfold fs_flag; simpl; lia).
  assert (FLB : bytes_at rsegs m (FS + 36352) flags) by exact FLG0. clear FLG0.
  change (fs_M 6) with 256 in FLEN.
  remember (shadow_addr (FS + 6328320)) as SB eqn:ESB.
  assert (SHS : stk rsegs m SB (SB + 131072)).
  { subst SB. apply shadow_stk; [exact SRW| lia| unfold FS_SIZE in *; lia| lia|].
    intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (SHI : forall y, SB <= y < SB + 131072 -> in_shadow y).
  { subst SB. apply shadow_range_in; [lia| lia| lia|]. intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (DSH : bv_unsigned sp <= SB \/ SB + 131072 <= bv_unsigned sp - 208).
  { apply (app_shadow_apart (bv_unsigned sp - 208) (bv_unsigned sp) SB 131072); [exact APS| lia| exact SHI| lia]. }
  pose proof (bv_unsigned_in_range 64 h) as HR. unfold bv_modulus in HR. cbn in HR.
  remember (bv_unsigned h) as hZ eqn:EhZ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold FS_SIZE, ASAN_GT in *.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep.
  do 2 zstep.
  freshLC LC0.
  zstep. call_sp icpt_spec; [exact ST| lia| reflexivity| exact TPE| exact LC0| eapply leaf_apart_sub; [exact AP| lia ..]| assumption|].
  rename POST into ST. clear LC0.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; first [lia | rewrite Z.mod_small in K0 by lia; lia]|].
  zstep. zstep. zstep. if_true.
  zstep. zstep. zstep. zstep.
  zstep. if_false.
  do 15 zstep.
  replace (Z_to_bv 64 hZ) with (Z_to_bv 64 (hZ + 0)) by (rewrite Z.add_0_r; reflexivity).
  assert (DFS : FS + 11571200 <= SB \/ SB + 131072 <= FS)
    by (apply (app_shadow_apart FS (FS + 11571200) SB 131072); [exact FAPP| lia| exact SHI| lia]).
  clear DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ7 TPC K0.
  refine (probe sp gp tp t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA FS hZ flags _ ltac:(lia) ltac:(lia)
            HR FLB FLEN F01 _ _ _ 0 _ _ _ eq_refl ltac:(lia) ltac:(intros; lia)).
  - intros j x5 Hj ONES ZERO.
    assert (HP : 0 <= (hZ + j) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    remember ((hZ + j) mod 256) as pos eqn:Epos.
    pose proof (bytes_at_one mA _ _ _ _ FLB ZERO) as FB. rewrite Z2Nat.id in FB by lia.
    assert (FC : rw_cells rsegs mA (FS + 36352 + pos) [C1 (Z_to_bv 8 0)])
      by (apply (stk_rw mA FS (FS + 11571200)); [exact STF| apply ro1; exact FB| lia| cbn; lia]).
    clear FB.
    remember (FS + 36352 + pos) as FLG eqn:EFLG.
    remember (FS + 6328320 + pos * 4096) as Fa eqn:EFa.
    destruct (stk_junk mA FS (FS + 11571200) (Fa + 24) 8 STF ltac:(lia) ltac:(lia)) as (j1 & FA1).
    destruct (stk_junk mA FS (FS + 11571200) (Fa + 4088) 8 STF ltac:(lia) ltac:(lia)) as (j2 & FA2).
    assert (ESA : shadow_addr Fa = SB + 512 * pos).
    { rewrite EFa, ESB. replace (FS + 6328320 + pos * 4096) with (FS + 6328320 + 8 * (512 * pos)) by lia. apply shadow_addr_add. }
    remember (shadow_addr Fa) as SA eqn:ESA'.
    destruct (stk_junk mA SB (SB + 131072) SA 512 SHS ltac:(lia) ltac:(lia)) as (j3 & SHC).
    assert (SAL : 0x5fe000 <= SA).
    { pose proof (SHI SA ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
    assert (SAU : SA + 512 <= 0x10007fff8000).
    { pose proof (SHI (SA + 511) ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
    apply (munch_weaken _ [(FS + 48, FS + 48 + 8); (FLG, FLG + 1); (Fa + 24, Fa + 32); (Fa + 4088, Fa + 4096); (SA, SA + 512);
                           (bv_unsigned sp - 208, bv_unsigned sp)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto].
    do 3 zstep.
    zstep.
    zstep.
    do 7 zstep.
    match goal with |- context [Z_to_bv 64 ?e] => lazymatch e with context [Z.shiftl pos 12] =>
      replace e with Fa by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 12) with 4096; lia) end end.
    zstep.
    zstep.
    zstep.
    zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (m2s_cells_munch m mx _ M2 MU ltac:(repeat constructor; cbn [fst]; lia)) as M2c end.
    zstep. call m2s_spec; [reflexivity| pose proof (FAPP Fa ltac:(lia)) as AF; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF; exact AF
                          | exact M2c| assumption|].
    clear M2c.
    replace (Fa / 8 + 2147450880) with SA by (rewrite ESA'; reflexivity).
    do 2 zstep.
    do 63 (zstep; zstep; zstep; if_cases K; zify_cond K;
           [clear K| exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]]).
    zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]| clear K].
    zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. subst hZ.
    assert (EFR : fs_frame FS 6 pos = Fa).
    { rewrite EFa. unfold fs_frame, fs_B.
      change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + pos * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + pos * (64 * 64)).
      lia. }
    assert (EFG : fs_flag FS 6 pos = FLG).
    { rewrite EFLG. unfold fs_flag. change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + pos) with (FS + 4096 + 32768 - 512 + pos).
      lia. }
    eapply (post_found 6 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF j);
      [exact WM| exact MI| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 6) with 256; lia| change (fs_M 6) with 256; exact ONES
      | change (fs_M 6) with 256; rewrite <- Epos; exact ZERO| ].
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). apply rw_c8_bytes. exact HN.
    + change (fs_M 6) with 256. rewrite <- Epos, <- EFR.
      apply frame_ok; [lia| change (fs_M 6) with 256; lia| exact HL| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
                     | unfold FS_SIZE; exact STF| unfold FS_SIZE; lia| | | | | ];
        rewrite ?EFR, ?EFG; try change (fs_B 6) with 4096.
      * apply rw_c1_bytes. exact FC.
      * apply rw_c8_bytes. exact FA1.
      * replace (Fa + 4096 - 8) with (Fa + 4088) by lia. apply rw_c8_bytes. exact FA2.
      * rewrite <- ESA'. change (Z.to_nat (4096 / 8)) with (8 * 64)%nat. apply rw_zero_cells. exact SHC.
      * rewrite <- ESA'. change (4096 / 8) with 512. replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia).
        replace (Fa + 4096 - 8) with (Fa + 4088) by lia. exact MU.
  - intros x5 x12 x14 x17 ONES.
    apply (munch_weaken _ [(FS + 48, FS + 48 + 8); (bv_unsigned sp - 208, bv_unsigned sp)]) in MU;
      [| unfold sub_fp; cbn [outside]; intros; tauto].
    zstep. zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. subst hZ.
    eapply (post_full 6 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF);
      [exact WM| assumption| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 6) with 256; lia| change (fs_M 6) with 256; exact FLEN
      | change (fs_M 6) with 256; exact ONES| ].
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). apply rw_c8_bytes. exact HN.
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). exact MU.
Qed.

(* route (C) (a Theorem Labs lane 10:19Z; wave lead a Theorem Labs lane, form ASSIGN.md:8-15 (a working note, not in this delivery), amended 10:33Z): stack_malloc_6's walk
   re-run with its shadow premise narrowed; stack_malloc_6 above is unchanged.  R = shadow_stk_shadow_R (FS + 6328320)
   131072, the shadow of class 6's frame region [FS + 6328320, FS + 6328320 + 2^20).  The run reads no shadow byte; it
   stores the chosen frame's 512 shadow bytes, inside R.  The proof's one use of the premise is shadow_stk_on over R: the
   bytes it stores into are present.  POST unchanged: asan_stack_malloc_post states no shadow fact. *)
(* R is the class-c block only because the premise `bytes_at m (FS + 96) [Z_to_bv 8 0]` makes the guard skip
   FakeStack::GC, which would store shadow over every class block (frames area
   [shadow_addr (FS + 36864), shadow_addr (FS + FS_SIZE))). *)
Theorem stack_malloc_6_on :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B 6 -> L mod 8 = 0 ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (shadow_stk_shadow_R (FS + 6328320) 131072) m -> lib.Lib.Mem.mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= 6)%nat -> lib.Lib.Mem.bytes_at rsegs m (CF + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  lib.Lib.Mem.bytes_at rsegs m TP (lib.Lib.Mem.le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  lib.Lib.Mem.bytes_at rsegs m (FS + 88) (lib.Lib.Mem.le8 (Z_to_bv 64 20)) ->
  lib.Lib.Mem.bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  lib.Lib.Mem.bytes_at rsegs m (fs_hint FS 6) (lib.Lib.Mem.le8 h) ->
  lib.Lib.Mem.bytes_at rsegs m (fs_flag FS 6 0) flags -> Z.of_nat (length flags) = fs_M 6 ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  lib.Lib.Frame.stk rsegs m lo S0 -> lo + ASAN_STACK_MALLOC_K <= S0 -> FS + FS_SIZE <= S0 - ASAN_STACK_MALLOC_K ->
  (forall a, S0 - ASAN_STACK_MALLOC_K <= a < S0 -> app_mem a) ->
  lib.Lib.Frame.disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)]
    (S0 - ASAN_STACK_MALLOC_K) ASAN_STACK_MALLOC_K ->
  lib.Lib.Exec.evt rsegs
    (asan_stack_malloc_post 6 ASAN_STACK_MALLOC_K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (lib.Lib.MState.MS
       (lib.Lib.Frame.mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 ASAN_STACK_MALLOC_6) fc None m (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  unfold ASAN_STACK_MALLOC_6, ASAN_STACK_MALLOC_K. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags.
  intros HL HL8 AC SRW MI0 TLS _ FSP PL SSL0 GC0 HINT0 FLG0 FLEN F01 ST0 LOK ROOM APS DISJ.
  apply ul_entry. rewrite mkR_ul.
  destruct (tls_leaf m (bv_unsigned tp) DT TS C T DB k AC TLS) as (tb & te & LC).
  pose proof (m2s_of_asan m AC) as M2. clear AC TLS.
  destruct PL as (FS0 & FS4K & FSGT & FAPP & FSTK0).
  assert (STF : stk rsegs m FS (FS + FS_SIZE)) by exact FSTK0. clear FSTK0.
  assert (ST : stk rsegs m lo (bv_unsigned sp)) by exact ST0. clear ST0.
  assert (MI : mem_inv rsegs m) by exact MI0. clear MI0.
  assert (TPE : tp = Z_to_bv 64 (bv_unsigned tp)) by (symmetry; apply Z_to_bv_lit_self).
  assert (AP : leaf_apart (bv_unsigned tp) (bv_unsigned DT) (bv_unsigned TS) (bv_unsigned C) (bv_unsigned T) (bv_unsigned DB) k
                 (bv_unsigned sp - 208) (bv_unsigned sp)).
  { split; [unfold FS_SIZE, ASAN_GT in *; lia|]. split; [lia|]. split; [pose proof (bv_unsigned_in_range 64 sp) as R; unfold bv_modulus in R; cbn in R; lia|].
    replace (bv_unsigned sp - (bv_unsigned sp - 208)) with 208 by lia. exact DISJ. }
  clear DISJ.
  pose proof AP as (_ & _ & _ & DJ). unfold leaf_ivs in DJ. cbn [disjoint_from] in DJ.
  destruct DJ as (DJ1 & DJ2 & DJ3 & DJ4 & DJ5 & DJ6 & DJ7 & _).
  assert (TPC : ro_cells rsegs m (bv_unsigned tp) [C8 (Z_to_bv 64 FS)]) by (apply ro8; exact FSP). clear FSP.
  assert (SSL : ro_cells rsegs m (FS + 88) [C8 (Z_to_bv 64 20)]) by (apply ro8; exact SSL0). clear SSL0.
  assert (GCC : ro_cells rsegs m (FS + 96) [C1 (Z_to_bv 8 0)]) by (apply ro1; exact GC0). clear GC0.
  replace (fs_hint FS 6) with (FS + 48) in HINT0 by (unfold fs_hint; simpl; lia).
  rewrite <- (Z_to_bv_lit_self h) in HINT0.
  assert (HN : rw_cells rsegs m (FS + 48) [C8 (Z_to_bv 64 (bv_unsigned h))]).
  { apply (stk_rw m FS (FS + FS_SIZE)); [exact STF| apply ro8; exact HINT0| lia| cbn; unfold FS_SIZE; lia]. }
  clear HINT0.
  replace (fs_flag FS 6 0) with (FS + 36352) in FLG0 by (unfold fs_flag; simpl; lia).
  assert (FLB : bytes_at rsegs m (FS + 36352) flags) by exact FLG0. clear FLG0.
  change (fs_M 6) with 256 in FLEN.
  remember (shadow_addr (FS + 6328320)) as SB eqn:ESB.
  assert (SHS : stk rsegs m SB (SB + 131072)).
  { subst SB. apply shadow_stk_on; [exact SRW| lia| unfold FS_SIZE in *; lia| lia|].
    intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (SHI : forall y, SB <= y < SB + 131072 -> in_shadow y).
  { subst SB. apply shadow_range_in; [lia| lia| lia|]. intros x Hx. apply FAPP. unfold FS_SIZE. lia. }
  assert (DSH : bv_unsigned sp <= SB \/ SB + 131072 <= bv_unsigned sp - 208).
  { apply (app_shadow_apart (bv_unsigned sp - 208) (bv_unsigned sp) SB 131072); [exact APS| lia| exact SHI| lia]. }
  pose proof (bv_unsigned_in_range 64 h) as HR. unfold bv_modulus in HR. cbn in HR.
  remember (bv_unsigned h) as hZ eqn:EhZ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold FS_SIZE, ASAN_GT in *.
  pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep.
  do 2 zstep.
  freshLC LC0.
  zstep. call_sp icpt_spec; [exact ST| lia| reflexivity| exact TPE| exact LC0| eapply leaf_apart_sub; [exact AP| lia ..]| assumption|].
  rename POST into ST. clear LC0.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
  zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; first [lia | rewrite Z.mod_small in K0 by lia; lia]|].
  zstep. zstep. zstep. if_true.
  zstep. zstep. zstep. zstep.
  zstep. if_false.
  do 15 zstep.
  replace (Z_to_bv 64 hZ) with (Z_to_bv 64 (hZ + 0)) by (rewrite Z.add_0_r; reflexivity).
  assert (DFS : FS + 11571200 <= SB \/ SB + 131072 <= FS)
    by (apply (app_shadow_apart FS (FS + 11571200) SB 131072); [exact FAPP| lia| exact SHI| lia]).
  clear DJ1 DJ2 DJ3 DJ4 DJ5 DJ6 DJ7 TPC K0.
  refine (probe sp gp tp t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mA FS hZ flags _ ltac:(lia) ltac:(lia)
            HR FLB FLEN F01 _ _ _ 0 _ _ _ eq_refl ltac:(lia) ltac:(intros; lia)).
  - intros j x5 Hj ONES ZERO.
    assert (HP : 0 <= (hZ + j) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    remember ((hZ + j) mod 256) as pos eqn:Epos.
    pose proof (bytes_at_one mA _ _ _ _ FLB ZERO) as FB. rewrite Z2Nat.id in FB by lia.
    assert (FC : rw_cells rsegs mA (FS + 36352 + pos) [C1 (Z_to_bv 8 0)])
      by (apply (stk_rw mA FS (FS + 11571200)); [exact STF| apply ro1; exact FB| lia| cbn; lia]).
    clear FB.
    remember (FS + 36352 + pos) as FLG eqn:EFLG.
    remember (FS + 6328320 + pos * 4096) as Fa eqn:EFa.
    destruct (stk_junk mA FS (FS + 11571200) (Fa + 24) 8 STF ltac:(lia) ltac:(lia)) as (j1 & FA1).
    destruct (stk_junk mA FS (FS + 11571200) (Fa + 4088) 8 STF ltac:(lia) ltac:(lia)) as (j2 & FA2).
    assert (ESA : shadow_addr Fa = SB + 512 * pos).
    { rewrite EFa, ESB. replace (FS + 6328320 + pos * 4096) with (FS + 6328320 + 8 * (512 * pos)) by lia. apply shadow_addr_add. }
    remember (shadow_addr Fa) as SA eqn:ESA'.
    destruct (stk_junk mA SB (SB + 131072) SA 512 SHS ltac:(lia) ltac:(lia)) as (j3 & SHC).
    assert (SAL : 0x5fe000 <= SA).
    { pose proof (SHI SA ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
    assert (SAU : SA + 512 <= 0x10007fff8000).
    { pose proof (SHI (SA + 511) ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
    apply (munch_weaken _ [(FS + 48, FS + 48 + 8); (FLG, FLG + 1); (Fa + 24, Fa + 32); (Fa + 4088, Fa + 4096); (SA, SA + 512);
                           (bv_unsigned sp - 208, bv_unsigned sp)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto].
    do 3 zstep.
    zstep.
    zstep.
    do 7 zstep.
    match goal with |- context [Z_to_bv 64 ?e] => lazymatch e with context [Z.shiftl pos 12] =>
      replace e with Fa by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 12) with 4096; lia) end end.
    zstep.
    zstep.
    zstep.
    zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (m2s_cells_munch m mx _ M2 MU ltac:(repeat constructor; cbn [fst]; lia)) as M2c end.
    zstep. call m2s_spec; [reflexivity| pose proof (FAPP Fa ltac:(lia)) as AF; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AF; exact AF
                          | exact M2c| assumption|].
    clear M2c.
    replace (Fa / 8 + 2147450880) with SA by (rewrite ESA'; reflexivity).
    do 2 zstep.
    do 63 (zstep; zstep; zstep; if_cases K; zify_cond K;
           [clear K| exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]]).
    zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]| clear K].
    zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. subst hZ.
    assert (EFR : fs_frame FS 6 pos = Fa).
    { rewrite EFa. unfold fs_frame, fs_B.
      change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + pos * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + pos * (64 * 64)).
      lia. }
    assert (EFG : fs_flag FS 6 pos = FLG).
    { rewrite EFLG. unfold fs_flag. change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + pos) with (FS + 4096 + 32768 - 512 + pos).
      lia. }
    eapply (post_found 6 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF j);
      [exact WM| exact MI| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 6) with 256; lia| change (fs_M 6) with 256; exact ONES
      | change (fs_M 6) with 256; rewrite <- Epos; exact ZERO| ].
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). apply rw_c8_bytes. exact HN.
    + change (fs_M 6) with 256. rewrite <- Epos, <- EFR.
      apply frame_ok; [lia| change (fs_M 6) with 256; lia| exact HL| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
                     | unfold FS_SIZE; exact STF| unfold FS_SIZE; lia| | | | | ];
        rewrite ?EFR, ?EFG; try change (fs_B 6) with 4096.
      * apply rw_c1_bytes. exact FC.
      * apply rw_c8_bytes. exact FA1.
      * replace (Fa + 4096 - 8) with (Fa + 4088) by lia. apply rw_c8_bytes. exact FA2.
      * rewrite <- ESA'. change (Z.to_nat (4096 / 8)) with (8 * 64)%nat. apply rw_zero_cells. exact SHC.
      * rewrite <- ESA'. change (4096 / 8) with 512. replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia).
        replace (Fa + 4096 - 8) with (Fa + 4088) by lia. exact MU.
  - intros x5 x12 x14 x17 ONES.
    apply (munch_weaken _ [(FS + 48, FS + 48 + 8); (bv_unsigned sp - 208, bv_unsigned sp)]) in MU;
      [| unfold sub_fp; cbn [outside]; intros; tauto].
    zstep. zstep.
    do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
    apply evt_done. subst hZ.
    eapply (post_full 6 208 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) FS h flags lo m mF);
      [exact WM| assumption| exact ST| exact FS0| exact FS4K| unfold ASAN_GT; lia| unfold FS_SIZE; exact FAPP
      | unfold FS_SIZE; exact STF| | change (fs_M 6) with 256; lia| change (fs_M 6) with 256; exact FLEN
      | change (fs_M 6) with 256; exact ONES| ].
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). apply rw_c8_bytes. exact HN.
    + replace (fs_hint FS 6) with (FS + 48) by (unfold fs_hint; simpl; lia). exact MU.
Qed.

(* a Theorem Labs lane's statement asan_stack_malloc_6_contract_on (lib/A/Prog/asan_stack_malloc_c_on.v (an earlier version, blob e08ea035a48, not in this delivery), from
   the merge of a working branch e0d0696bcb1), proved from stack_malloc_6_on: its premise region
   asan_stack_malloc_shadow_R FS 6 is stack_malloc_6_on's R, since fs_frame FS 6 0 = FS + 6328320. *)
Theorem stack_malloc_6_contract_on : A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_6_contract_on.
Proof.
  unfold A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_6_contract_on,
    A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_contract_on. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags.
  intros HL HL8 AC SRW.
  apply (stack_malloc_6_on ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           lo FS h DT TS C T DB k flags HL HL8 AC).
  revert SRW. apply A.ShadowRwOn.shadow_rw_on_mono. intros y Hy.
  unfold A.Prog.asan_stack_malloc_c_on.asan_stack_malloc_shadow_R.
  assert (EF : fs_frame FS 6 0 = FS + 6328320) by (unfold fs_frame; change (2 ^ 20) with 1048576; simpl Z.of_nat; lia).
  rewrite EF. exact Hy.
Qed.
