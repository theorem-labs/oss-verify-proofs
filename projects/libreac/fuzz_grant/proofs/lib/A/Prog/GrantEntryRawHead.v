(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetGa0), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetGa0.v; 116 of its 155 lines of code are new or changed and 140 lines of the source are left out. *)
(* The head of the hand-built allocation phase of LLVMFuzzerTestOneInput on the ASan build
   (fuzz_grant.c:366-368): the slots 0x812ac .. 0x812b4, from GI_raw (GP_raw) to GR_hdI
   (GR_hd, the `beqz s8`), and the split of GR_hdI on the bytes of input left.

   seg_raw_hd: `li a0,2; sb a0,70(s6)` marks `raw` usable (shadow byte 70 of the frame
   := 2), so GSH_a becomes GSH_raw. The store lies in the shadow band, so this run takes
   the plain engine (no shadow tokens). The memory outside that byte is carried by
   hmem_tr (GrantEntryRawHeadLib.v).
   seg_raw_split: GR_hdI is GR_hd0I, GR_hd1I or GR_hd2I (SegCLib.pos_end_le). The cases are
   proved in GrantEntryRawRd0/1/2.v on the states of GrantEntryRawHeadLib.v. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05 YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC45 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntryRawDefs GrantEntrySetDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* 0x812ac: the frame's shadow byte 70, at s6 (x22) + 70, written on the plain engine. *)
Definition R_sh70 : YP09.region := YP09.mkRegion (Some 22%nat) 70 71 70 71 [].
Definition ss_mk : sstate := mkSS GP_raw sr_atoms [R_sh70] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ---- 0x812b4: the split on the bytes of input left ---- *)
Theorem seg_raw_split : forall POST,
  ge_from B MT POST (GR_hd0I B MT) -> ge_from B MT POST (GR_hd1I B MT) -> ge_from B MT POST (GR_hd2I B MT) ->
  ge_from B MT POST (GR_hdI B MT).
Proof.
  intros POST H0 H1 H2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HG.
  pose proof (SegCLib.pos_end_le (c_pl cx)) as Hle.
  destruct (Nat.eq_dec (GrantSlotPlan.pos_end (c_pl cx)) (length (c_pl cx))) as [E0 | N0];
    [exact (H0 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (conj HG E0)) |].
  destruct (Nat.eq_dec (S (GrantSlotPlan.pos_end (c_pl cx))) (length (c_pl cx))) as [E1 | N1];
    [exact (H1 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO (conj HG E1)) |].
  apply (H2 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO). split; [exact HG | lia].
Qed.

(* ---- 0x812ac .. 0x812b4: `raw` marked usable ---- *)
Theorem seg_raw_hd : forall POST, ge_from B MT POST (GR_hdI B MT) -> ge_from B MT POST (GI_raw B MT).
Proof.
  intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & HBODY & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R24 & R25 & S88 & S96 & SL & HTAB & HWS & HST & HREL & HI1).
  pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HG & HSV & HSH & HFL & HLEN & HIN).
  pose proof HTAB as (HinT & Ht0 & HLT & HTB).
  pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (proj1 HJ) as HAR.
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR Hfin) as (_ & _ & _ & HFSh).
  rewrite L6 in HFSh. change (fs_frame_bytes GE_CID / 8) with 128 in HFSh. unfold shadow_addr in HFSh.
  rewrite <- L11 in HFSh.
  (* `lia` here does not use the meaning of `/ 8`: the bounds of the frame's shadow come
     from gshadow_band. *)
  pose proof (gshadow_band cx fp t ly3 0 HL ltac:(lia)) as (GB1 & GB2 & GB3).
  pose proof (gshadow_band cx fp t ly3 103 HL ltac:(lia)) as (GB4 & _).
  unfold kLowShadowBeg, kHighMemBeg in GB1, GB2, GB3, GB4.
  assert (HM0 : hmem cx fp t W3 ms3) by exact (conj HSV (conj HFL (conj HIN (conj SL (conj HTB (conj HWS HST)))))).
  assert (HMA : gmach cx ms3 GP_raw) by exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc HG)))))).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  rewrite (gmach_mkst cx ms3 _ HMA).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hr; subst E; apply ew_Eimg_Ereg_nat; exact Hr).
  assert (HSO : st_ok_pi SEGS VAL E ss_mk (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GP_raw)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_mk. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, R_sh70. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite (ER 22%nat 22%bv eq_refl), R22. unfold w64. rewrite unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace o with 70 by lia.
      apply (proj1 (HFSh 70 ltac:(lia))).
    - split; exact I.
    - split; [exact I | split; exact I]. }
  clear HE. subst mem.
  paj_run_to_shc RUNTOP HSO HJ GR_hd.
  { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 22%nat (gSH cx fp));
      [reflexivity | rewrite (ER 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia
      | | apply awr_ok_nil].
    intros a Ha. right; right; right. exists GE_CID, fp. split; [left; reflexivity|]. right.
    unfold in_zr, shadow_addr; cbn [fst snd YP09.r_wlo YP09.r_whi R_sh70] in *. rewrite L6.
    change (fs_frame_bytes GE_CID / 8) with 128. rewrite <- L11. lia. }
  (* at 0x812b4 *)
  let msF := rh_cur HSO in
  assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> a <> gSH cx fp + 70 ->
                 aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
  [ intros a Ha Hw;
    match goal with HFr : frame_of _ _ (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem msF)) |- _ =>
      apply (frame_wins E _ _ _ _ (fun a => a = gSH cx fp + 70) HFr); [|exact Ha | exact Hw] end;
    intros x (r & Hr & Hx); cbn [ss_mem ss_mk In] in Hr;
    destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_sh70] in Hx;
    rewrite (ER 22%nat 22%bv eq_refl), R22 in Hx; unfold w64 in Hx;
    rewrite unsigned_lit_small in Hx by lia; lia
  | apply (HN cx fp k acc ly3 S3 W3 msF _ HB HJ HFR HMO) ].
  destruct (gst_ok_mach _ _ _ _ HSO eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
  prreg HSO (2%bv : bv 5) Q2. prreg HSO (8%bv : bv 5) Q8. prreg HSO (9%bv : bv 5) Q9.
  prreg HSO (3%bv : bv 5) Q3. prreg HSO (4%bv : bv 5) Q4.
  prreg HSO (20%bv : bv 5) Q20. prreg HSO (21%bv : bv 5) Q21. prreg HSO (22%bv : bv 5) Q22.
  prreg HSO (24%bv : bv 5) Q24. prreg HSO (25%bv : bv 5) Q25.
  rewrite (ER 2%nat 2%bv eq_refl) in Q2. rewrite (ER 8%nat 8%bv eq_refl) in Q8. rewrite (ER 9%nat 9%bv eq_refl) in Q9.
  rewrite (ER 3%nat 3%bv eq_refl) in Q3. rewrite (ER 4%nat 4%bv eq_refl) in Q4.
  rewrite (ER 20%nat 20%bv eq_refl) in Q20. rewrite (ER 21%nat 21%bv eq_refl) in Q21.
  rewrite (ER 22%nat 22%bv eq_refl) in Q22. rewrite (ER 24%nat 24%bv eq_refl) in Q24.
  rewrite (ER 25%nat 25%bv eq_refl) in Q25.
  lazymatch type of HSO with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0
      (YP09.mkRegion (Some 22%nat) 70 71 70 71 [YP09.mkChunk 70 (CVal 1 (SLit 2))]) HSO ltac:(vm_compute; reflexivity)) as FR0
  end.
  cbn [ms_mem restrict] in FR0.
  assert (X22 : bv_unsigned (ew E 22) = gSH cx fp)
    by (rewrite (ER 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
  let msF := rh_cur HSO in
  assert (N70 : aview SEGS (w_H W3) (ms_mem msF) (gSH cx fp + 70) = Some 2);
  [ apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem msF)); [|lia];
    exact (field_of_regionG _ _ 22%nat (gSH cx fp) _ _ _ _ _ 70 1%N (SLit 2) 2 FR0 X22
             ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
  | ].
  subst regs.
  let msF := rh_cur HSO in
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> happ cx fp a ->
                 aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a);
  [ intros a Ha (Happ & _ & _); apply HWIN; [exact Ha|]; intros ->;
    pose proof (gshadow_band cx fp t ly3 70 HL ltac:(lia)) as (B1 & _); lia
  | ].
  unfold GR_hdI. exists t. split; [|split; [exact Hk|split; [exact Hacc|split; [exact Hbl|split; [exact Hn|]]]]].
  - pose proof (hmem_tr cx fp t ly3 W3 _ _ HL HK HM0) as (Hsv' & Hfl' & Hin' & _).
    unfold ge_body, gregs. splits; try assumption; try congruence; try apply gsh_raw_len.
    intros i Hi. rewrite gsh_raw_len in Hi. unfold GE_NSH in Hi.
    destruct (Nat.eq_dec i 70) as [-> | Hne].
    + rewrite gsh_raw_70. exact N70.
    + rewrite gsh_raw_other by lia. pose proof (gshadow_band cx fp t ly3 (Z.of_nat i) HL ltac:(lia)) as (B1 & _).
      rewrite HWIN; [apply HSH; rewrite HLEN; unfold GE_NSH; lia | unfold kLowShadowBeg, kHighMemBeg in B1; lia | lia].
  - pose proof (hmem_tr cx fp t ly3 W3 _ _ HL HK HM0) as (_ & _ & _ & SL' & HTB' & HWS' & HST').
    split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
    split; [congruence|]. split.
    + unfold gslot in *. rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) _ (c_sp1 cx + 88)); [exact S88|].
      intros j Hj. pose proof (gshadow_band cx fp t ly3 70 HL ltac:(lia)) as (B1 & B2 & _).
      apply HWIN; [lia|]. unfold kLowShadowBeg, kHighMemBeg in *. lia.
    + exact (conj SL' (conj (conj HinT (conj Ht0 (conj HLT HTB'))) (conj HWS' (conj HST' (conj HREL HI1))))).
Qed.

End c.
End b.
End a.
