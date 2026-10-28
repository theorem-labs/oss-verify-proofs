(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls F_strchrnul F_twoway_A F_twoway_B.
Import ListNotations.
Open Scope bv_scope.

Notation w z := (Z_to_bv 64 z) (only parsing).
Ltac zs := zstep; fix_lit_store.

Definition strstr_entry := 0x24bdc%Z.

Section Setup.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (H h0 : Z) (hay slack : list byte) (canary : word) (lo : Z).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) hay.
  Hypothesis PAD : ((- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis LO : (lo <= bv_unsigned sp - 2240)%Z.
  Hypothesis BND : (0 <= H /\ H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= 2^64 /\ 0 <= lo /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis SEPH : (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= H)%Z.
  Hypothesis SEPG : (got_ssp + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPC : (ssp_guard + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis SEPN : (NAD + 8 <= bv_unsigned sp - 2240)%Z.
  Hypothesis HPOS : (0 < H)%Z.
  Hypothesis H0 : (H <= h0 <= H + Z.of_nat (length hay))%Z.

  Notation len := (Z.of_nat (length hay)).
  Notation full := (hay ++ Z_to_bv 8 0 :: slack).
  Notation SP := (bv_unsigned sp).
  Notation W := [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z.
  Notation POST := (twoway_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m).

  Ltac bundle_invc := repeat (split; [eassumption|]); eassumption.

  Ltac iter1 l :=
    let K := fresh "K" in
    destruct (Z.eq_dec (h0 + l) (H + len)) as [?E|?NE];
    [ (let RD := fresh "RDZ" in
       pose proof (nul_read H hay slack _ (w (h0 + l)) ltac:(eassumption) ltac:(f_equal; lia)) as RD;
       do 3 zs; if_cases K; zify_cond K; [ | exfalso; apply K; reflexivity ];
       eapply tw_exit1; try eassumption; [ bundle_invc | reflexivity ])
    | (let RD := fresh "RD" in let b := fresh "b" in let NZ := fresh "NZ" in
       destruct (hay_read' H hay slack NONUL _ (h0 - H + l) (w (h0 + l)) ltac:(eassumption) ltac:(lia) ltac:(f_equal; lia)) as (b & RD & NZ);
       do 3 zs; if_cases K; zify_cond K; [ exfalso; lia | ]) ].
  Ltac needle k :=
    let RN := fresh "RN" in
    lazymatch goal with NEE : bytes_at rsegs ?mm 66514 _ |- _ =>
      pose proof (nee_read H hay slack mm k _ (w (66514 + Z.of_nat k)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN;
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in RN end.

  #[using="NONUL PAD LO BND SEPH SEPG SEPC HPOS H0"] Lemma tw_setup :
    mem_inv rsegs m -> bytes_at rsegs m H full -> bytes_at rsegs m NAD chunked_bytes ->
    rw_cells rsegs m got_ssp [C8 (w ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
    stk rsegs m lo SP ->
    evt rsegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (w h0) (w NAD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (w 0x24dcc) fc None m (seg_rom rsegs)).
  Proof.
    intros MI HAY NEE GOT GUARD STK. pose proof BND as BD.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    unfold NAD, NAD1, got_ssp, ssp_guard, M1, BSW1 in *. unfold chunked_bytes in NEE.
    carve_frame 112%nat STK. carve_frame 2128%nat STK.
    do 25 zs.
    needle 0%nat.
    do 8 zs. if_cases KB0; zify_cond KB0. { exfalso. clear -KB0. cbv in KB0. lia. }
    do 5 zs.
    iter1 0%Z. needle 1%nat. do 15 zs. if_cases KB1; zify_cond KB1. 2:{ exfalso. clear -KB1. cbv in KB1. lia. }
    iter1 1%Z. needle 2%nat. do 15 zs. if_cases KB2; zify_cond KB2. 2:{ exfalso. clear -KB2. cbv in KB2. lia. }
    iter1 2%Z. needle 3%nat. do 15 zs. if_cases KB3; zify_cond KB3. 2:{ exfalso. clear -KB3. cbv in KB3. lia. }
    iter1 3%Z. needle 4%nat. do 15 zs. if_cases KB4; zify_cond KB4. 2:{ exfalso. clear -KB4. cbv in KB4. lia. }
    iter1 4%Z. needle 5%nat. do 15 zs. if_cases KB5; zify_cond KB5. 2:{ exfalso. clear -KB5. cbv in KB5. lia. }
    iter1 5%Z. needle 6%nat. do 15 zs. if_cases KB6; zify_cond KB6. 2:{ exfalso. clear -KB6. cbv in KB6. lia. }
    iter1 6%Z. needle 7%nat. do 15 zs. if_cases KB7; zify_cond KB7. { exfalso. clear -KB7. cbv in KB7. lia. }
    eapply tw_setup2; try eassumption. bundle_invc.
  Qed.
End Setup.

Theorem twoway_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (H h0 : Z) (hay slack : list byte) (canary : word) (lo : Z),
  bytes_at rsegs m H (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  ((- (H + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  bytes_at rsegs m NAD chunked_bytes ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z ->
  (H + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= H)%Z ->
  (got_ssp + 8 <= bv_unsigned sp - 2240)%Z -> (ssp_guard + 8 <= bv_unsigned sp - 2240)%Z -> (NAD + 8 <= bv_unsigned sp - 2240)%Z ->
  (0 < H)%Z -> (H <= h0 <= H + Z.of_nat (length hay))%Z ->
  a0 = Z_to_bv 64 h0 -> a1 = Z_to_bv 64 NAD ->
  mem_inv rsegs m ->
  evt rsegs (twoway_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc H hay slack canary lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24dcc) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros HAY NONUL PAD NEE GOT GUARD STK LO SEPH SEPG SEPC SEPN HPOS H0 -> -> MI.
  pose proof (bytes_at_bound _ _ _ _ HAY) as B. rewrite length_app in B. cbn [length] in B.
  pose proof STK as STK0. destruct STK0 as [LO0 _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  eapply tw_setup; eauto. lia.
Qed.

Ltac ss_ret0 spv lov := do 4 zs;
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned spv + -16) _, ST : stk _ ?mm2 lov _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    release_frame FR ST (bv_unsigned spv) end;
  finish; left; first [reflexivity | lia].

Theorem strstr_chunked_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (hay slack : list byte) (canary : word) (lo : Z),
  bytes_at rsegs m (bv_unsigned a0) (hay ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) hay ->
  ((- (bv_unsigned a0 + Z.of_nat (length hay) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  bytes_at rsegs m NAD chunked_bytes ->
  rw_cells rsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m ssp_guard [C8 canary] ->
  stk rsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 2240)%Z ->
  (bv_unsigned a0 + Z.of_nat (length hay) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 2240 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (got_ssp + 8 <= bv_unsigned sp - 2240)%Z -> (ssp_guard + 8 <= bv_unsigned sp - 2240)%Z -> (NAD + 8 <= bv_unsigned sp - 2240)%Z ->
  (0 < bv_unsigned a0)%Z ->
  a1 = Z_to_bv 64 NAD ->
  mem_inv rsegs m ->
  evt rsegs (twoway_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) hay slack canary lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24bdc) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros HAY NONUL PAD NEE GOT GUARD STK LO SEPH SEPG SEPC SEPN HPOS -> MI.
  pose proof (bytes_at_bound _ _ _ _ HAY) as B. rewrite length_app in B. cbn [length] in B.
  pose proof STK as STK0. destruct STK0 as [LO0 _]. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R; cbn in R.
  pose proof (munch_refl [(bv_unsigned sp - 2240, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold NAD, NAD1, got_ssp, ssp_guard in *. unfold chunked_bytes in NEE.
  carve_frame 16%nat STK.
  do 4 zs.
  lazymatch goal with NEE : bytes_at rsegs ?mm 66514 _ |- _ =>
    pose proof (nee_read (bv_unsigned a0) hay slack mm 0 _ (Z_to_bv 64 66514) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN0 end.
  zs. zs. if_cases K0; zify_cond K0. { exfalso. clear -K0. cbv in K0. lia. }
  zs. pose proof (unsigned_lit (bv_unsigned sp + -16) ltac:(lia)) as USP.
  call strchr_spec.
  1:{ exact HAY. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ rewrite USP. exact STK. }
  all: rewrite ?USP; try lia. 1:{ exact MI. }
  rewrite ?USP in *.
  lazymatch goal with Hr : strchr_res _ _ _ ?rr |- _ => rename Hr into RES; rename rr into r end.
  pose proof RES as RES'. unfold strchr_res in RES'.
  replace (bv_unsigned (Z_to_bv 64 99) mod 256)%Z with 99%Z in RES' by reflexivity.
  zs. if_cases K1; zify_cond K1.
  {   ss_ret0 sp lo. }

  destruct RES' as [R0|[[C0 _]|[Hr Hn]]]; [exfalso; subst r; apply K1; reflexivity| exfalso; lia |].
  lazymatch goal with NEE : bytes_at rsegs ?mm 66514 _ |- _ =>
    pose proof (nee_read (bv_unsigned a0) hay slack mm 1 _ (Z_to_bv 64 (66514 + 1)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN1;
    pose proof (nee_read (bv_unsigned a0) hay slack mm 2 _ (Z_to_bv 64 (66514 + 2)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN2;
    pose proof (nee_read (bv_unsigned a0) hay slack mm 3 _ (Z_to_bv 64 (66514 + 3)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN3;
    pose proof (nee_read (bv_unsigned a0) hay slack mm 4 _ (Z_to_bv 64 (66514 + 4)) NEE eq_refl ltac:(unfold NAD; f_equal; lia)) as RN4 end.
  lazymatch goal with HAY : bytes_at rsegs ?mm (bv_unsigned a0) _ |- _ => rename HAY into HAY1 end.
  zs. zs. if_cases K2; zify_cond K2. { exfalso. clear -K2. cbv in K2. lia. }
  destruct (Z.eq_dec (r + 1) (bv_unsigned a0 + Z.of_nat (length hay))) as [E1|NE1].
  { pose proof (nul_read (bv_unsigned a0) hay slack _ (Z_to_bv 64 (r + 1)) HAY1 ltac:(f_equal; lia)) as RD1.
    zs. zs. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. } zs. ss_ret0 sp lo. }
  destruct (hay_read' (bv_unsigned a0) hay slack NONUL _ (r + 1 - bv_unsigned a0) (Z_to_bv 64 (r + 1)) HAY1 ltac:(lia) ltac:(f_equal; lia)) as (b1 & RD1 & NZ1).
  zs. zs. if_cases K3; zify_cond K3. { exfalso. lia. }
  zs. zs. if_cases K4; zify_cond K4. { exfalso. clear -K4. cbv in K4. lia. }
  destruct (Z.eq_dec (r + 2) (bv_unsigned a0 + Z.of_nat (length hay))) as [E2|NE2].
  { pose proof (nul_read (bv_unsigned a0) hay slack _ (Z_to_bv 64 (r + 2)) HAY1 ltac:(f_equal; lia)) as RD2.
    zs. zs. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. } zs. ss_ret0 sp lo. }
  destruct (hay_read' (bv_unsigned a0) hay slack NONUL _ (r + 2 - bv_unsigned a0) (Z_to_bv 64 (r + 2)) HAY1 ltac:(lia) ltac:(f_equal; lia)) as (b2 & RD2 & NZ2).
  zs. zs. if_cases K5; zify_cond K5. { exfalso. lia. }
  zs. zs. if_cases K6; zify_cond K6. { exfalso. clear -K6. cbv in K6. lia. }
  destruct (Z.eq_dec (r + 3) (bv_unsigned a0 + Z.of_nat (length hay))) as [E3|NE3].
  { pose proof (nul_read (bv_unsigned a0) hay slack _ (Z_to_bv 64 (r + 3)) HAY1 ltac:(f_equal; lia)) as RD3.
    zs. zs. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. reflexivity. } zs. ss_ret0 sp lo. }
  destruct (hay_read' (bv_unsigned a0) hay slack NONUL _ (r + 3 - bv_unsigned a0) (Z_to_bv 64 (r + 3)) HAY1 ltac:(lia) ltac:(f_equal; lia)) as (b3 & RD3 & NZ3).
  zs. zs. if_cases K7; zify_cond K7. { exfalso. lia. }
  zs. zs. if_cases K8; zify_cond K8. { exfalso. clear -K8. cbv in K8. lia. }
  do 5 zs.
  lazymatch goal with FR : rw_cells _ ?mm (bv_unsigned sp + -16) _, ST : stk _ ?mm2 lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    release_frame FR ST (bv_unsigned sp) end.
  eapply evt_mono.
  { eapply twoway_spec; try eassumption; try reflexivity; lia. }
  intros ms' PO. unfold twoway_post in *. destruct_exs PO.
  destruct PO as (E & MU2 & WM2 & MI2 & ST2 & HAY2 & GOT2 & GUARD2 & Hr2).
  subst ms'. do 16 eexists. split; [reflexivity|].
  split; [eapply munch_trans; [eassumption|exact MU2] |].
  split; [eapply wmono_trans; [eassumption|exact WM2] |].
  repeat (split; [eassumption|]). exact Hr2.
Qed.
