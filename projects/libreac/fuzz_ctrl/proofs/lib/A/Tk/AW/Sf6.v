(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Tk/AW/SmLeaf.v, with its module paths, module names and numbers changed; 141 of its 176 lines of code are new or changed and 352 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c asan_stack_free_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Tac Image ZBridge Arr SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AK Require Import StepFast StoreFast LiaFix.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLeaf SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_free_c_on.
Local Unset Lia Cache. Local Unset Nia Cache. Local Unset Nra Cache.
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

Lemma cells_bytes_rep v b n : le8 v = repeat b 8 -> cells_bytes (repeat (C8 v) n) = repeat b (8 * n).
Proof.
  intros E. induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH, E.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.

Lemma rw_rep_cells (m : word -> option byte) A n v b : rw_cells rsegs m A (repeat (C8 v) n) -> le8 v = repeat b 8 ->
  bytes_at rsegs m A (repeat b (8 * n)).
Proof. intros [[_ B] _] E. rewrite (cells_bytes_rep v b n E) in B. exact B. Qed.

Lemma bytes_at_some (m : word -> option byte) A bs a : bytes_at rsegs m A bs -> A <= a < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros (H0 & H1 & H) Ha. assert (LT : (Z.to_nat (a - A) < length bs)%nat) by lia.
  specialize (H _ LT). rewrite Z2Nat.id in H by lia. replace (A + (a - A)) with a in H by lia.
  destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.

Lemma shadow_rw_write (m m' : word -> option byte) W A n : shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> a < A \/ A + n <= a -> outside W a) ->
  (forall a, A <= a < A + n -> exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros SRW MU WM OUT IN a Ha. destruct (SRW a Ha) as [Hw [b Hb]].
  change (wview rsegs m (wa a) <> None) in Hw. change (mrd rsegs m (wa a) = Some b) in Hb.
  change (wview rsegs m' (wa a) <> None /\ exists b, mrd rsegs m' (wa a) = Some b).
  split; [apply WM; exact Hw|].
  destruct (in_shadow_range a Ha) as [R1 R2].
  destruct (Z_lt_le_dec a A) as [L1|L1]; [| destruct (Z_lt_le_dec a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply OUT; [exact Ha| left; exact L1].
  - apply IN. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply OUT; [exact Ha| right; exact L2].
Qed.

(* route (C): the transport twin of shadow_rw_write (a Theorem Labs lane 09:56Z; shadow_rw_write stays byte-identical).  No
   shadow_rw premise: the proof reads the old memory only at the guarded addresses of the post's own shadow_rw_on P m,
   so no region R and no premise; post in the wave form. *)
Lemma shadow_rw_write_on (m m' : word -> option byte) W A n : munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> a < A \/ A + n <= a -> outside W a) ->
  (forall a, A <= a < A + n -> exists b, mrd rsegs m' (wa a) = Some b) ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros MU WM OUT IN P SRW a Hp Ha. destruct (SRW a Hp Ha) as [Hw [b Hb]].
  change (wview rsegs m (wa a) <> None) in Hw. change (mrd rsegs m (wa a) = Some b) in Hb.
  change (wview rsegs m' (wa a) <> None /\ exists b, mrd rsegs m' (wa a) = Some b).
  split; [apply WM; exact Hw|].
  destruct (in_shadow_range a Ha) as [R1 R2].
  destruct (Z_lt_le_dec a A) as [L1|L1]; [| destruct (Z_lt_le_dec a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply OUT; [exact Ha| left; exact L1].
  - apply IN. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. apply OUT; [exact Ha| right; exact L2].
Qed.

(* route (C), leaf case (the walk takes no callee contract): stack_free_6's proof moves here, stated as a Theorem Labs lane's
   asan_stack_free_6_contract_on (asan_stack_free_c_on.v, statement only).  The run reads the premise exactly at the
   frame's shadow [shadow_addr fr, shadow_addr fr + 512) that its 64 stores fill with 0xf5 (shadow_stk_on below, through
   SmLib's shadow_stk_shadow_R); that is a Theorem Labs lane's asan_stack_free_shadow_R 6 L FS j, met by shadow_rw_on_mono.  Its only
   constant load is the .rodata pattern cell, not shadow.  Post through shadow_rw_write_on. *)
Theorem stack_free_6_on : asan_stack_free_6_contract_on.
Proof.
  unfold asan_stack_free_6_contract_on, asan_stack_free_contract_on, ASAN_STACK_FREE_6, ASAN_STACK_FREE_K. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS j.
  intros HJ EFR0 HL HL8 PL FLG0 FLW0 AC SRW MI0 ST0 LOK ROOM HLO HHI.
  apply ul_entry. rewrite mkR_ul.
  pose proof (m2s_of_asan m AC) as M2.
  destruct PL as (FS0 & FS4K & FSGT & FAPP & FSTK0).
  assert (STF : stk rsegs m FS (FS + FS_SIZE)) by exact FSTK0. clear FSTK0.
  assert (ST : stk rsegs m lo (bv_unsigned sp)) by exact ST0. clear ST0.
  assert (MI : mem_inv rsegs m) by exact MI0. clear MI0.
  change (fs_M 6) with 256 in HJ. change (fs_B 6) with 4096 in HL, FLW0.
  remember (FS + 6328320 + j * 4096) as Fa eqn:EFa.
  assert (EFR : fs_frame FS 6 j = Fa).
  { rewrite EFa. unfold fs_frame, fs_B.
    change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + j * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + j * (64 * 64)).
    lia. }
  remember (FS + 36352 + j) as FLG eqn:EFLG.
  assert (EFG : fs_flag FS 6 j = FLG).
  { rewrite EFLG. unfold fs_flag. change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + j) with (FS + 4096 + 32768 - 512 + j).
    lia. }
  rewrite EFR in EFR0. rewrite EFG in FLG0, FLW0. rewrite EFR0 in FLW0.
  replace (Fa + 4096 - 8) with (Fa + 4088) in FLW0 by lia.
  rewrite <- (Z_to_bv_lit_self a0), EFR0.
  assert (FLW : ro_cells rsegs m (Fa + 4088) [C8 (Z_to_bv 64 FLG)]) by (apply ro8; exact FLW0). clear FLW0.
  unfold FS_SIZE, ASAN_GT in *.
  assert (FC : rw_cells rsegs m FLG [C1 (Z_to_bv 8 1)])
    by (apply (stk_rw m FS (FS + 11571200)); [exact STF| apply ro1; exact FLG0| lia| cbn; lia]).
  clear FLG0.
  assert (AFa : app_mem Fa) by (apply FAPP; lia).
  assert (AFL : app_mem FLG) by (apply FAPP; lia).
  remember (shadow_addr (FS + 6328320)) as SB eqn:ESB.
  assert (SHI : forall y, SB <= y < SB + 131072 -> in_shadow y).
  { subst SB. apply shadow_range_in; [lia| lia| lia|]. intros x Hx. apply FAPP. lia. }
  assert (ESA : shadow_addr Fa = SB + 512 * j).
  { rewrite EFa, ESB. replace (FS + 6328320 + j * 4096) with (FS + 6328320 + 8 * (512 * j)) by lia. apply shadow_addr_add. }
  remember (shadow_addr Fa) as SA eqn:ESA'.
  assert (SHS : stk rsegs m SA (SA + 512)).
  { rewrite ESA'. apply (shadow_stk_on m Fa 512); [| lia| lia| lia|].
    - refine (A.ShadowRwOn.shadow_rw_on_mono _ _ m _ SRW). intros y Hy. unfold shadow_stk_shadow_R in Hy.
      unfold asan_stack_free_shadow_R. rewrite EFR. change (fs_shadow_n 6 (bv_unsigned a1)) with 512. exact Hy.
    - intros x Hx. apply FAPP. lia. }
  destruct (stk_junk m SA (SA + 512) SA 512 SHS ltac:(lia) ltac:(lia)) as (j3 & SHC).
  assert (SAL : 0x5fe000 <= SA).
  { pose proof (SHI SA ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (SAU : SA + 512 <= 0x10007fff8000).
  { pose proof (SHI (SA + 511) ltac:(lia)) as X. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (DFS : FS + 11571200 <= SB \/ SB + 131072 <= FS)
    by (apply (app_shadow_apart FS (FS + 11571200) SB 131072); [intros x Hx; apply FAPP; lia| lia| exact SHI| lia]).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold HIGHMEM_BEG, APPMEM_END in HLO, HHI.
  clear SHS.
  pose proof (munch_refl [(FLG, FLG + 1); (SA, SA + 512); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. do 2 zstep.
  zstep.
  zstep.
  zstep.
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (m2s_cells_munch m mx _ M2 MU ltac:(repeat constructor; cbn [fst]; lia)) as M2c end.
  zstep. call m2s_spec; [reflexivity| unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AFa; exact AFa
                        | exact M2c| assumption|].
  clear M2c.
  replace (Fa / 8 + 2147450880) with SA by (rewrite ESA'; reflexivity).
  do 3 zstep.
  do 63 (zstep; zstep; zstep; if_cases K; zify_cond K;
         [clear K| exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]]).
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; first [lia | rewrite ?Z.mod_small in K by lia; lia]| clear K].
  do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mF end.
  apply evt_done. unfold asan_stack_free_post_on. cbv zeta.
  do 15 eexists. exists mF.
  split; [cbv delta [mkR]; reflexivity|].
  rewrite EFR, EFG, <- ESA'. replace (fs_shadow_n 6 (bv_unsigned a1)) with 512 by reflexivity.
  assert (SHF : bytes_at rsegs mF SA (repeat (Z_to_bv 8 0xf5) (Z.to_nat 512))).
  { change (Z.to_nat 512) with (8 * 64)%nat. eapply rw_rep_cells; [exact SHC|].
    first [ reflexivity | vm_compute; reflexivity
          | unfold le8; cbn; repeat (apply f_equal2; [apply bv_eq; vm_compute; reflexivity|]); reflexivity ]. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [split; [exact FS0|]; split; [exact FS4K|]; split; [unfold ASAN_GT; lia|]; split; [exact FAPP| exact STF]|].
  split; [apply rw_c1_bytes; exact FC|].
  split; [exact SHF|].
  split.
  { apply (asan_cells_kept [(FLG, FLG + 1); (SA, SA + 512); (bv_unsigned sp - 32, bv_unsigned sp)] m mF AC MU).
    cbn. try unfold RT_LO, RT_HI. lia. }
  refine (shadow_rw_write_on m mF _ SA 512 MU WM _ _).
  - intros a Ha Hout. cbn [outside].
    pose proof (app_not_shadow FLG AFL) as NF.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
    split; [intros Hx; apply NF; replace FLG with a by lia; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG; lia|].
    split; [lia|]. split; [lia| exact I].
  - intros a Ha. apply (bytes_at_some mF SA _ a SHF). rewrite repeat_length. lia.
Qed.

(* The old statement, byte-identical: a corollary of stack_free_6_on (PRE by shadow_rw_on_of_shadow_rw; POST at
   P := fun _ => True, back by shadow_rw_of_on_all). *)
Theorem stack_free_6 : asan_stack_free_6_contract.
Proof.
  unfold asan_stack_free_6_contract, asan_stack_free_contract. cbv zeta.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS j.
  intros HJ EFR0 HL HL8 PL FLG0 FLW0 AC SRW MI0 ST0 LOK ROOM HLO HHI.
  eapply lib.Lib.Exec.evt_mono.
  { exact (stack_free_6_on ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m lo FS j HJ EFR0 HL HL8 PL FLG0 FLW0 AC (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m SRW) MI0 ST0 LOK ROOM HLO HHI). }
  intros ms' HQ. unfold asan_stack_free_post_on in HQ. cbv zeta in HQ. unfold asan_stack_free_post. cbv zeta.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI & ST & FP & FL & SH & AC' & PR).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj E (conj MU (conj WM (conj MI (conj ST (conj FP (conj FL (conj SH (conj AC'
    (A.ShadowRwOn.shadow_rw_of_on_all m' (PR (fun _ => True) (A.ShadowRwOn.shadow_rw_on_of_shadow_rw _ m SRW)))))))))))).
Qed.
