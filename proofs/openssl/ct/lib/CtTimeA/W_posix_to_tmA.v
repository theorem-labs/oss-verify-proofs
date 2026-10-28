(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog CtTime.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct RtCallA ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnP Require Import MagicDiv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeP Require Import TimeDefs TimeKit TimeMagic W_posix_to_tm.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import TimeDefsA TimeKitA W_posix_to_tm_segA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac rstep := OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.      (* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Lemma zero56_of_memset : forall m A,
  bytes_at ctasegs m A (repeat (Z_to_bv 8 0) (Z.to_nat 56)) -> wr_at ctasegs m A 56 ->
  rw_cells ctasegs m A ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
                        ++ [CB 32%nat (repeat (Z_to_bv 8 0) 32%nat)]).
Proof.
  intros m A HB HW. eapply (rw_cells_recast m A [CB 56%nat (repeat (Z_to_bv 8 0) 56%nat)]).
  - split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]| cbn; exact HW].
  - cbn; repeat split; exact I.
  - bytes_lit_eq.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zero32_cells : forall m A,
  bytes_at ctasegs m A (repeat (Z_to_bv 8 0) (Z.to_nat 32)) -> wr_at ctasegs m A 32 ->
  rw_cells ctasegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m A HB HW. eapply (rw_cells_recast m A [CB 32%nat (repeat (Z_to_bv 8 0) 32%nat)]).
  - split; [split; [cbn; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]| cbn; exact HW].
  - cbn; repeat split; exact I.
  - bytes_lit_eq.
  - reflexivity.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition OPENSSL_POSIX_TO_TM_STACK_A : Z := 48 + RT_STACK.

Definition p2tm_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : word -> option byte) (t D : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (p2tm_ret t)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + 56)) m m'
    /\ rw_cells ctasegs m' D (p2tm_cells t).

Lemma OPENSSL_posix_to_tm_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo : Z) (pd : bptr) (t D : Z) (junk : list byte),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + OPENSSL_POSIX_TO_TM_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  In (pd, D, 56) (OW ++ LB) -> D mod 8 = 0 -> rw_cells ctasegs m D [CB 56%nat junk] ->
  (- 2^63 <= t < 2^63)%Z -> a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 D ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 OPENSSL_POSIX_TO_TM_A) fc None m (seg_rom ctasegs))))
             (ASTA RT Σ PMc (p2tm_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m t D)).
Proof.
  intros until junk. intros HEAP ST CEIL LO SPT SP16 MI -> HIN ALD OUT Ht -> ->.
  unfold OPENSSL_POSIX_TO_TM_STACK_A, RT_STACK, OPENSSL_POSIX_TO_TM_A, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (D0 & _ & _ & DC & DI). cbn [blk_addr blk_size fst snd] in D0, DC, DI.
  ablock HEAP HIN ACC OFF.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 56)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 56)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPD : D + 56 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= D) by alia.
  assert (E63 : 2^63 = 9223372036854775808) by reflexivity. assert (E64 : 2^64 = 18446744073709551616) by reflexivity.
  assert (E31 : 2^31 = 2147483648) by reflexivity. assert (E32 : 2^32 = 4294967296) by reflexivity.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  assert (ACM : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> aclient_addr (OW ++ LB) (bv_unsigned sp + -48) a)
    by (intros a [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]).
  assert (AWO : Forall (aclient_write_ok (OW ++ LB)) [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 56)]%Z).
  { constructor; [left; cbn; alia|]. constructor; [right; right; exists (pd, D, 56); split; [exact HIN| cbn; lia]| constructor]. }
  apply cps_from_evt'.
  carve_frame 48%nat ST. do 7 zstep.
  (* [comment removed for export] *)
  do 5 zstep. zstep.
  name_mem m1.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1) by (eapply AH_frame; [exact HEAP| exact MU1| exact WM1| exact AWO]).
  apply evt_done. eapply cps_step_same.
  { eapply (asan_memset_cpsA) with (d := D) (n := 56) (c := Z_to_bv 8 0) (bd := (pd, D, 56)) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP1.
    - rewrite ESP. exact ST.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - match goal with H : mem_inv ctasegs m1 |- _ => exact H end.
    - exact HIN.
    - cbn [blk_addr blk_size fst snd]. lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  rewrite (ret_pc_even 0x270460) by (clear; lia). unfold MallocRep.wz.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
  clear ST OUT MI. rename STM into ST. rename MIM into MI.
  pose proof (zero56_of_memset mM D BZ WRM) as OUT. clear BZ WRM.
  clear ACC OFF. ablock HEAPM HIN ACC OFF.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 56)]%Z mM) as MU. pose proof (wmono_refl ctasegs mM) as WM.
  try match goal with H : ro_cells ctasegs m1 A_GOT_SHB _ |- _ => clear H end. try match goal with H : ro_cells ctasegs m1 A_SHB_CELL _ |- _ => clear H end.
  destruct (AH_shb _ _ _ _ HEAPM) as [SHB1 SHB2].
  apply cps_from_evt'.
  (* [comment removed for export] *)
  do 9 zstep. zstep. if_cases K0; zify_cond K0; rewrite ?land64, ?E64 in K0.
  { (* [comment removed for export] *)
    assert (RNG : t < MIN_POSIX_TIME \/ MAX_POSIX_TIME < t).
    { unfold MIN_POSIX_TIME, MAX_POSIX_TIME. destruct (Z_lt_le_dec t 253402300800) as [A|A]; [| lia].
      rewrite Z.mod_small in K0 by lia. lia. }
    do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
    unfold p2tm_postA, p2tm_ret, p2tm_cells.
    replace (utc_from_posix t) with (@None tm6)
      by (symmetry; unfold utc_from_posix; replace ((t <? MIN_POSIX_TIME) || (MAX_POSIX_TIME <? t)) with true; [reflexivity|];
          symmetry; apply orb_true_intro; destruct RNG; [left| right]; apply Z.ltb_lt; lia).
    do 16 eexists. exists mM. split; [reflexivity|].
    split; [exact MI|]. split; [exact ST|]. split; [exact HEAPM|]. split; [eapply wmono_trans; [exact WM1| exact WMM]|].
    split.
    { eapply agree_on_trans; [| eapply agree_on_mono; [exact AGM| intros a [Ha Hn]; split; [exact (ACM _ Ha)| exact Hn]]].
      eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]. intros a [Ha Hn]. cbn [outside fst snd].
      split; [| split; [lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). alia. }
    unfold zero56. eapply rw_cells_recast; [exact OUT| cbn; tauto| bytes_lit_eq| reflexivity]. }
  (* [comment removed for export] *)
  assert (RNG : MIN_POSIX_TIME <= t <= MAX_POSIX_TIME).
  { unfold MIN_POSIX_TIME, MAX_POSIX_TIME. destruct (Z_lt_le_dec t 253402300800) as [A|A].
    - rewrite Z.mod_small in K0 by lia. lia.
    - exfalso. rewrite <- (Z.mod_add _ (-1)) in K0 by lia. rewrite Z.mod_small in K0 by lia. lia. }
  clear K0.
  pose proof (QR_facts t RNG) as (QR & HR & HRp & HRn & HQ & HDS). pose proof (ERA_facts t RNG) as (HERA & HDOE & HEA).
  pose proof (DOE_facts t RNG) as (HYN & HDOY & HMOY & HMON & HMDAY & HYOE). pose proof (SECS_facts t RNG) as (HSECS & HHH & HS2 & HMI & HSS).
  (* [comment removed for export] *)
  eapply evt_cut; [apply p2tm_segA_A; [exact MI| exact RNG]|]. intros ms' ->.
  eapply evt_cut; [apply p2tm_segB_A; [exact RNG| lia| lia]|]. intros ms' (x5' & x6' & x7' & x17' & ->).
  unfold MIN_POSIX_TIME, MAX_POSIX_TIME in RNG.
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app mM D _ _) OUT) as [TLO THI]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in THI. clear OUT.
  (* [comment removed for export] *)
  zstep. setreg 13%Z (Z_to_bv 64 (ADJ t)) ltac:(unfold ADJ, SG; f_equal; destruct (TimeMagic.RT t <? 0); reflexivity).
  zstep. zstep. zstep.
  zstep. setreg 10%Z (Z_to_bv 64 (SECS t)) ltac:(unfold SECS; wmodk RNG).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. setreg 5%Z (Z_to_bv 64 (SECS t * 2^32)) ltac:(wmodk RNG).
  zstep.
  zstep. setreg 13%Z (Z_to_bv 64 (SECS t * 2443359173)) ltac:(f_equal; symmetry; apply mulhu_3600; lia).
  zstep. setreg 13%Z (Z_to_bv 64 (HH t))
    ltac:(unfold HH; pose proof (div3600_magic (SECS t) ltac:(lia)) as MG; f_equal; rewrite ?land64, ?mod64_small by lia; rewrite shiftr_div by lia; symmetry; exact MG).
  (* [comment removed for export] *)
  zstep. setreg 15%Z (Z_to_bv 64 (HH t * 3600)) ltac:(wmodk RNG).
  zstep. setreg 5%Z (Z_to_bv 64 (S2 t)) ltac:(unfold S2; wmodk RNG).
  zstep. setreg 10%Z (Z_to_bv 64 (S2 t * 34953)) ltac:(wmodk RNG).
  zstep. setreg 17%Z (Z_to_bv 64 (TimeMagic.MI t))
    ltac:(unfold TimeMagic.MI; pose proof (div60_magic (S2 t) ltac:(lia)) as MG; f_equal; rewrite ?land64, ?mod64_small by nia; rewrite shiftr_div by lia; symmetry; exact MG).
  zstep. setreg 15%Z (Z_to_bv 64 (TimeMagic.MI t))
    ltac:(unfold TimeMagic.MI; pose proof (div60_magic (S2 t) ltac:(lia)) as MG; rewrite <- MG; f_equal; symmetry; apply (srliw_gen _ (S2 t * 34953));
          [lia| lia| mliak HS2]).
  zstep. setreg 17%Z (Z_to_bv 64 (TimeMagic.MI t * 64)) ltac:(wmodk RNG).
  zstep. setreg 10%Z (Z_to_bv 64 (TimeMagic.MI t * 4)) ltac:(wmodk RNG).
  zstep. setreg 17%Z (Z_to_bv 64 (TimeMagic.MI t * -60)) ltac:(w32k HMI).
  (* [comment removed for export] *)
  zstep.
  zstep. setreg 17%Z (Z_to_bv 64 (SS t)) ltac:(unfold SS; wmodk RNG).
  zstep.
  zstep. zstep. setreg 17%Z (Z_to_bv 64 (SS t)) ltac:(clear - HSS E64; wmod).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. setreg 10%Z (Z_to_bv 64 (5 * DOY t)) ltac:(wmodk RNG).
  zstep.
  zstep. setreg 10%Z (Z_to_bv 64 (5 * DOY t + 2)) ltac:(w32k HDOY).
  set (W6 := (5 * DOY t + 2) * 3593175255 / 2^32). assert (HW6 : 0 <= W6 < 2^31) by (subst W6; mliak HDOY).
  assert (CG6 : ((Z.land (Z.shiftr (Z.land ((5 * DOY t + 2) * 18446744073007759575) 18446744073709551615) 32 + (5 * DOY t + 2)) 18446744073709551615) - W6) mod 2^32 = 0).
  { rewrite !land64, shiftr_div by lia. subst W6. apply (hi32_negc_congr _ 701792041); [reflexivity| reflexivity| lia| lia]. }
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. setreg 13%Z (Z_to_bv 64 0)
    ltac:(f_equal; symmetry; transitivity (if W6 <? 0 then 1 else 0);
          [apply (bit31_gen _ W6); [lia| exact CG6] | rewrite (proj2 (Z.ltb_ge W6 0)) by lia; reflexivity]).
  zstep. setreg 10%Z (Z_to_bv 64 (W6 / 2^7)) ltac:(f_equal; symmetry; apply (sraiw_gen _ W6); [lia| lia| exact CG6]).
  zstep. setreg 13%Z (Z_to_bv 64 (MOY t)) ltac:(unfold MOY; pose proof (div153_magic (5 * DOY t + 2) ltac:(lia)) as MG; subst W6; wmodk MG HDOY).
  (* [comment removed for export] *)
  zstep. zstep.
  zstep. setreg 15%Z (Z_to_bv 64 (MOY t * 153)) ltac:(wmodk RNG).
  zstep. setreg 15%Z (Z_to_bv 64 (153 * MOY t + 2)) ltac:(w32k HMOY).
  zstep. setreg 10%Z (Z_to_bv 64 ((153 * MOY t + 2) * - 1717986919)) ltac:(wmodk RNG).
  zstep. setreg 15%Z (Z_to_bv 64 1) ltac:(f_equal; symmetry; rewrite sign_bit63 by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
  zstep. setreg 10%Z (Z_to_bv 64 ((153 * MOY t + 2) * - 1717986919 / 2^33)) ltac:(f_equal; rewrite signed_lit by lia; rewrite shiftr_div by lia; reflexivity).
  zstep. setreg 15%Z (Z_to_bv 64 (- ((153 * MOY t + 2) / 5)))
    ltac:(pose proof (ndiv5_magic (153 * MOY t + 2) ltac:(lia)) as MG; replace (0 <? 153 * MOY t + 2) with true in MG by (symmetry; apply Z.ltb_lt; lia);
          change (if true then 1 else 0) with 1 in MG; wmodk MG HMOY).
  (* [comment removed for export] *)
  zstep.
  zstep. setreg 15%Z (Z_to_bv 64 (DOY t + - ((153 * MOY t + 2) / 5))) ltac:(wmodk RNG).
  zstep.
  zstep. setreg 15%Z (Z_to_bv 64 (MDAY t)) ltac:(unfold MDAY; wmodk RNG).
  zstep.
  (* [comment removed for export] *)
  zstep. setreg 13%Z (Z_to_bv 64 (MON t)) ltac:(unfold MON; wmodk RNG).
  zstep.
  zstep. setreg 14%Z (Z_to_bv 64 (MON t - 1)) ltac:(wmodk RNG).
  zstep.
  (* [comment removed for export] *)
  zstep.
  zstep. setreg 13%Z (Z_to_bv 64 (if MON t <? 3 then 1 else 0))
    ltac:(f_equal; rewrite zb_b2z_if; rewrite ?unsigned_lit, ?land64, ?mod64_small by lia; rewrite slti_lit by lia;
          destruct (Z.ltb_spec (MON t) 3); [rewrite (proj2 (Z.ltb_lt _ _)) by lia| rewrite (proj2 (Z.ltb_ge _ _)) by lia]; reflexivity).
  zstep. setreg 10%Z (Z_to_bv 64 (ERA t * 400)) ltac:(wmodk RNG).
  zstep. setreg 10%Z (Z_to_bv 64 (ERA t * 400 + YOE t)) ltac:(wmodk RNG).
  zstep. setreg 10%Z (Z_to_bv 64 (YR t)) ltac:(unfold YR; destruct (MON t <? 3); wmodk RNG).
  zstep. setreg 10%Z (Z_to_bv 64 (YR t - 1900)) ltac:(wmodk RNG).
  zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  name_mem m3.
  match goal with H : munch _ mM m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs mM m3 |- _ => rename H into WM3 end.
  assert (HEAP3 : AHEAP Σ OW LB m3) by (eapply AH_frame; [exact HEAPM| exact MU3| exact WM3| exact AWO]).
  apply evt_done. eapply cps_step_same.
  { eapply (asan_memset_cpsA) with (d := D + 24) (n := 32) (c := Z_to_bv 8 0) (bd := (pd, D, 56)) (lo := lo) (OW := OW) (LB := LB); try reflexivity.
    - exact HEAP3.
    - rewrite ESP. exact ST.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - match goal with H : mem_inv ctasegs m3 |- _ => exact H end.
    - exact HIN.
    - cbn [blk_addr blk_size fst snd]. lia.
    - cbn [blk_addr blk_size fst snd]. lia.
    - lia. }
  intros msN PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & mN & -> & MIN & STN & HEAPN & WMN & AGN & BZ2 & WR2).
  rewrite (ret_pc_even 0x270764) by (clear; lia). unfold MallocRep.wz.
  apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGN) in TLO; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pd, D, 56); split; [exact HIN| cbn; lia]| lia]].
  clear ST THI. rename STN into ST.
  pose proof (zero32_cells mN (D + 24) BZ2 WR2) as THI.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold p2tm_postA, p2tm_ret, p2tm_cells. rewrite (p2tm_agree t RNG). unfold tm_cells. cbn [t_sec t_min t_hour t_mday t_mon t_year].
  do 16 eexists. exists mN. split; [reflexivity|].
  split; [exact MIN|]. split; [exact ST|]. split; [exact HEAPN|].
  split; [eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WMM|]; first [exact WMN| eapply wmono_trans; [exact WM3| exact WMN]]|].
  split.
  { assert (MUNW : forall ma mb, munch [(bv_unsigned sp - 48, bv_unsigned sp); (D, D + 56)]%Z ma mb ->
                    agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (D <= a < D + 56)) ma mb).
    { intros ma mb MUx. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUx)|]. intros a [Ha Hn]. cbn [outside fst snd].
      split; [| split; [lia| exact I]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). alia. }
    eapply agree_on_trans; [exact (MUNW _ _ MU1)|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGM| intros a [Ha Hn]; split; [exact (ACM _ Ha)| exact Hn]]|].
    eapply agree_on_trans; [exact (MUNW _ _ MU3)|].
    eapply agree_on_mono; [exact AGN| intros a [Ha Hn]; split; [exact (ACM _ Ha)| lia]]. }
  apply (proj2 (rw_cells_app mN D [_; _; _; _; _; _] _)). split; [exact TLO|].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]. exact THI.
Qed.

End WithRT.
