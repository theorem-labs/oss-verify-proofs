(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRawRd2), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v. *)
(* Case 2 of the head of the hand-built allocation phase of LLVMFuzzerTestOneInput on the
   ASan build (fuzz_grant.c:367-368; slots 0x812b4 .. 0x81328): two bytes of input or more
   are left.

   From GR_hd2I the walk runs on the engine with shadow tokens from the symbolic state
   ss_r2 (GrantEntryRawHeadLib.v): `beqz s8` is not taken (s8 >= 2); slot 88 gives the
   input cursor c_p + pos_end; the shadow byte of the first input byte is checked (its slow
   path 0x81a3c is not reached), the byte is loaded and stored in raw.base; `bne s8,a1` is
   taken (s8 <> 1); the shadow byte of the second input byte is checked (slow path 0x81a70
   not reached), the byte is loaded, s8 -= 2, slot 88 := cursor + 2 and the byte is stored
   in raw.width; a0 := 4352. The input bytes are data slot 0 of the environment, so the two
   bytes of raw are the input's bytes pos_end and pos_end + 1, which SegCLib.raw_rd_2 names
   raw.base and raw.width, with pos_raw = pos_end + 2. The run writes only slot 88 and
   raw, so every other memory fact of the cut is kept; fin_mal gives GR_malI. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntryRawDefs GrantEntrySetDefs GrantEntryRawHeadLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan SlotNeeds_c SegCLib SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* The two bytes of data slot 0, as the engine reads them. *)
Lemma rd2_data : forall (E : env) (b0 b1 : byte), ed E 0 = [b0; b1] ->
  sv_denot E (SData 0 0 1) = Z_to_bv 64 (bv_unsigned b0) /\
  sv_denot E (SData 0 1 1) = Z_to_bv 64 (bv_unsigned b1).
Proof.
  intros E b0 b1 H. cbn [sv_denot]. unfold data_word. rewrite H. split.
  - change (firstn (N.to_nat 1) (skipn (Z.to_nat 0) [b0; b1])) with [b0]. rewrite bytes_le_single. reflexivity.
  - change (firstn (N.to_nat 1) (skipn (Z.to_nat 1) [b0; b1])) with [b1]. rewrite bytes_le_single. reflexivity.
Qed.

Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.

(* ---- 0x812b4 .. 0x81328 with two bytes of input or more left ---- *)
Theorem seg_raw_rd2 : forall POST, ge_from B MT POST (GR_malI B MT) -> ge_from B MT POST (GR_hd2I B MT).
Proof.
intros POST HNEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
  ((t & HBODY & Hk & Hacc & Hbl & Hn & R20 & R21 & R22 & R24 & R25 & S88 & SL & HTAB & HWS & HST & HREL & HI1) & Hlen2).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HG & HSV & HSH & HFL & HLEN & HIN).
pose proof HG as (G2 & G8 & G9 & G3 & G4).
pose proof HTAB as (HinT & Ht0 & HLT & HTB).
pose proof HB as (HPRE & _ & _ & Hpn & _).
pose proof (glay B MT LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 t HB HJ HFR Hbl) as HL.
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 & L15 & L16).
pose proof asan_consts as (C1 & _).
pose proof (proj1 HJ) as HAR3.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPRES & _).
assert (FFS : GE_STK = 32768) by reflexivity.
assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 GE_CID fp HAR3 Hfin) as (_ & _ & HFP & _).
rewrite L6 in HFP. change (fs_frame_bytes GE_CID) with 1024 in HFP.
set (pos := GrantSlotPlan.pos_end (c_pl cx)) in *.
assert (Hpl0 : (pos < length (c_pl cx))%nat) by lia.
assert (Hpl1 : (S pos < length (c_pl cx))%nat) by lia.
assert (Hn2 : Z.of_nat pos + 2 <= c_n cx) by (unfold c_n; lia).
assert (Hn0 : 0 < c_n cx) by lia.
destruct (L16 Hn0) as (P1 & P2 & P3 & P4 & P5).
assert (Hrq : c_n cx <= req_size (c_n cx)).
{ assert (H0 : 0 <= c_n cx) by lia. exact (proj2 (req_size_pos (c_n cx) H0)). }
assert (HinP3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
{ unfold gblk1 in Hbl. rewrite Hbl. apply in_or_app. left. destruct Hpn as [[Hz _] | [_ Hin0]]; [lia | exact Hin0]. }
assert (S70 : aview SEGS (w_H W3) (ms_mem ms3) (SHADOW_OFF + gF cx fp / 8 + 70) = Some 2).
{ assert (H70 : (70 < length GSH_raw)%nat) by (rewrite gsh_raw_len; unfold GE_NSH; lia).
  pose proof (HSH 70%nat H70) as X. rewrite gsh_raw_70, L11 in X. exact X. }
(* the model: raw = (byte pos_end, byte pos_end + 1), pos_raw = pos_end + 2 *)
assert (HPR : GrantSlotPlan.pos_raw (c_pl cx) = S (S pos)).
{ unfold GrantSlotPlan.pos_raw. rewrite (SegCLib.raw_rd_2 _ Hlen2). reflexivity. }
set (b0 := nth pos (c_pl cx) (Z_to_bv 8 0)).
set (b1 := nth (S pos) (c_pl cx) (Z_to_bv 8 0)).
assert (HRB : raw_b cx = bv_unsigned b0) by (unfold raw_b; rewrite (SegCLib.raw_rd_2 _ Hlen2); reflexivity).
assert (HRW : raw_w cx = bv_unsigned b1) by (unfold raw_w; rewrite (SegCLib.raw_rd_2 _ Hlen2); reflexivity).
(* the environment: the registers, the cursor c_p + pos_end (atom 32), the two bytes (slot 0) *)
assert (HMA : gmach cx ms3 GR_hd) by exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc HG)))))).
rewrite (gmach_mkst cx ms3 _ HMA).
remember (Eimg (edset (Ereg (ms_regs ms3) [w64 (c_p cx + Z.of_nat pos)]) 0 [b0; b1])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hnr. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat (ms_regs ms3) _ n r Hnr). }
assert (E32 : ew E 32 = w64 (c_p cx + Z.of_nat pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (ED : ed E 0 = [b0; b1]) by (subst E; reflexivity).
clear HE.
assert (EW : forall n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr (ms_regs ms3) r = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v).
{ intros n r v Hnr Hr Hv. rewrite (ER n r Hnr), Hr. unfold w64. apply unsigned_lit_small. exact Hv. }
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (apply (EW 9%nat 9%bv); [reflexivity | exact G9 | lia]).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (apply (EW 21%nat 21%bv); [reflexivity | exact R21 | unfold SHADOW_OFF; lia]).
assert (U24 : bv_unsigned (ew E 24) = c_n cx - Z.of_nat pos) by (apply (EW 24%nat 24%bv); [reflexivity | exact R24 | lia]).
assert (U25 : bv_unsigned (ew E 25) = gF cx fp + GO_RAW) by (apply (EW 25%nat 25%bv); [reflexivity | exact R25 | unfold GO_RAW; lia]).
assert (U32 : bv_unsigned (ew E 32) = c_p cx + Z.of_nat pos) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* ---- the symbolic state ss_r2 and its two shadow entries ---- *)
assert (HS : st_ok_pi SEGS VAL E ss_r2
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + GR_hd)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_r2. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
          let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
        first [ rewrite getr_zero; reflexivity
              | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply ER; reflexivity ]
      | ]).
    destruct Hr.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + (* the input's two bytes, read-only, data slot 0 *)
      unfold region_ok, R_in. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      intros i Hi. cbn [c_len YP09.c_val YP09.c_off cv_len] in Hi |- *.
      exists (nth (Z.to_nat i) [b0; b1] (Z_to_bv 8 0)).
      cbn [cbyte]. rewrite ED. split.
      * rewrite Z.add_0_l. apply nth_error_nth'. cbn [length]. lia.
      * rewrite Z.add_0_r. destruct (Z.eq_dec i 0) as [-> | Hi1].
        -- rewrite Z.add_0_r. exact (rh_in_byte _ _ _ pos HIN Hpl0).
        -- assert (Ei : i = 1) by lia. subst i.
           replace (c_p cx + Z.of_nat pos + 1) with (c_p cx + Z.of_nat (S pos)) by lia.
           exact (rh_in_byte _ _ _ (S pos) HIN Hpl1).
    + (* slot 88 at s1 *)
      unfold region_ok, R_s88. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply JPRES. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (c_sp1 cx) 88 8 (SOff 32 0) (c_p cx + Z.of_nat pos)).
        -- apply gsv0; [exact E32 | lia].
        -- cbn. lia.
        -- cbn. lia.
        -- exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ S88).
    + (* raw, in the frame *)
      unfold region_ok, R_raw. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U25. split; [unfold GO_RAW; lia|]. split; [unfold GO_RAW; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      assert (Hr : gF cx fp <= gF cx fp + GO_RAW + o < gF cx fp + 1024) by (unfold GO_RAW; lia).
      exact (proj1 (HFP _ Hr)).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val R_in R_s88 R_raw].
    rewrite U9, U25, U32. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold GO_RAW. repeat split; lia.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok, RH_SP, RH_SB, RH_PTR. cbn [af_lo af_hi af_al2].
    rewrite U9, U21, U24, U25, U32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    splits; first [ exact I | exact L5 | (change (2 ^ 5) with 32; exact L5) | (unfold SHADOW_OFF, GO_RAW; lia) ]. }
assert (UB : U E RH_Bx = SHADOW_OFF).
{ unfold RH_Bx. apply U_atom; [rewrite (ER 21%nat 21%bv eq_refl); exact R21 | unfold SHADOW_OFF; lia]. }
assert (SHOK : sh_ok SEGS RH_Bx SH_r2 E (mrestrict (w_H W3) (ms_mem ms3))).
{ unfold sh_ok, SH_r2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E RH_Bx 32 (c_p cx + Z.of_nat pos) 2 (c_p cx + Z.of_nat pos) 0 2).
    + eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR3 HinP3); lia.
    + exact UB.
    + apply U_atom; [exact E32 | lia].
    + lia.
    + lia.
    + intros x Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W3) (ms_mem ms3) E RH_Bx 25 (gF cx fp + GO_RAW) 2 (gF cx fp + GO_RAW) 0 2).
    + apply rh_raw_addressable; [exact L9 | lia | exact S70].
    + exact UB.
    + apply U_atom; [rewrite (ER 25%nat 25%bv eq_refl); exact R25 | unfold GO_RAW; lia].
    + lia.
    + lia.
    + intros x Hx. unfold GO_RAW, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
(* ---- the run to 0x81328 ---- *)
(* The write obligation: raw.base and raw.width lie in the frame; slot 88 in the stack window. *)
paj_run_to_tok RUNTO HS HJ SHOK RH_Bspan GR_mal;
  [ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fp0 ?bl0 ?blc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fp0 bl0 blc ly own) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
    eapply awr_ok_cons_stack_off with (n := 9%nat) (d := c_sp1 cx - spZ (c_regs cx));
      [ reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | ];
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 25%nat (gF cx fp + GO_RAW)); [reflexivity | exact U25 | | apply awr_ok_nil];
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; exists GE_CID, fp;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    try rewrite L6; try change (frame_addr (c_ly cx) GE_CID fp) with (gF cx fp);
    change (fs_frame_bytes GE_CID) with 1024; unfold GO_RAW in *; lia
  | ].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into ms4 end.
(* the run wrote slot 88 and raw only *)
assert (HWIN : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 88 <= a < c_sp1 cx + 96) ->
  ~ (gF cx fp + GO_RAW <= a < gF cx fp + GO_RAW + 2) ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha H1 H2.
  lazymatch goal with HFx : frame_of _ ?rs0 (mrestrict _ (ms_mem ms3)) (mrestrict _ (ms_mem ms4)) |- _ =>
    apply (frame_wins _ rs0 (w_H W3) (ms_mem ms3) (ms_mem ms4)
      (fun x => (c_sp1 cx + 88 <= x < c_sp1 cx + 96) \/ (gF cx fp + GO_RAW <= x < gF cx fp + GO_RAW + 2)) HFx);
    [ | exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)] ]
  end.
  intros x (r & Hr & Hx). cbv beta. try unfold ss_r2 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_in R_s88 R_raw] in Hx;
    rewrite ?U9, ?U25, ?U32 in Hx; lia. }
destruct (gst_ok_mach _ _ _ _ HS eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc). cbn [ss_pc] in Pc.
assert (Q2 : getr (ms_regs ms4) 2 = getr (ms_regs ms3) 2) by (prreg HS (2%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q3 : getr (ms_regs ms4) 3 = getr (ms_regs ms3) 3) by (prreg HS (3%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q4 : getr (ms_regs ms4) 4 = getr (ms_regs ms3) 4) by (prreg HS (4%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q8 : getr (ms_regs ms4) 8 = getr (ms_regs ms3) 8) by (prreg HS (8%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q9 : getr (ms_regs ms4) 9 = getr (ms_regs ms3) 9) by (prreg HS (9%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q20 : getr (ms_regs ms4) 20 = getr (ms_regs ms3) 20) by (prreg HS (20%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q21 : getr (ms_regs ms4) 21 = getr (ms_regs ms3) 21) by (prreg HS (21%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q22 : getr (ms_regs ms4) 22 = getr (ms_regs ms3) 22) by (prreg HS (22%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
assert (Q25 : getr (ms_regs ms4) 25 = getr (ms_regs ms3) 25) by (prreg HS (25%bv : bv 5) RR; rewrite RR; apply ER; reflexivity).
prreg HS (24%bv : bv 5) Q24. prreg HS (10%bv : bv 5) Q10.
(* the two regions the run wrote, read back *)
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let rr := eval vm_compute in (nth 2 (ss_mem ssx) R_raw) in
  let r8 := eval vm_compute in (nth 1 (ss_mem ssx) R_s88) in
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 2 rr HS ltac:(vm_compute; reflexivity)) as FRAW;
  pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 1 r8 HS ltac:(vm_compute; reflexivity)) as FS88
end.
cbn [ms_mem restrict] in FRAW, FS88.
lazymatch type of FRAW with region_ok _ ?Ex ?mm (YP09.mkRegion _ _ _ _ _ ?cs) =>
  lazymatch cs with context [YP09.mkChunk 0 (CVal 1%N ?e0)] =>
  lazymatch cs with context [YP09.mkChunk 1 (CVal 1%N ?e1)] =>
    assert (EDx : ed Ex 0 = [b0; b1]) by (cbn [ed ewset]; exact ED);
    assert (UX25 : bv_unsigned (ew Ex 25) = gF cx fp + GO_RAW) by (cbn [ew ewset Nat.eqb]; exact U25);
    assert (RV0 : val_mem SEGS mm (gF cx fp + GO_RAW + 0) 1 (bv_unsigned b0));
    [ eapply (field_of_regionG Ex mm 25%nat (gF cx fp + GO_RAW) cs _ _ _ _ 0 1%N e0 (bv_unsigned b0) FRAW UX25);
      [ repeat (first [left; reflexivity | right])
      | exact (proj1 (rd2_data Ex _ _ EDx))
      | change (8 * Z.of_N 1) with 8; pose proof (u8_range b0); lia
      | cbn; lia ]
    | ];
    assert (RV1 : val_mem SEGS mm (gF cx fp + GO_RAW + 1) 1 (bv_unsigned b1));
    [ eapply (field_of_regionG Ex mm 25%nat (gF cx fp + GO_RAW) cs _ _ _ _ 1 1%N e1 (bv_unsigned b1) FRAW UX25);
      [ repeat (first [left; reflexivity | right])
      | exact (proj2 (rd2_data Ex _ _ EDx))
      | change (8 * Z.of_N 1) with 8; pose proof (u8_range b1); lia
      | cbn; lia ]
    | ]
  end end
end.
lazymatch type of FS88 with region_ok _ ?Ex ?mm (YP09.mkRegion _ _ _ _ _ ?cs) =>
  lazymatch cs with context [YP09.mkChunk 88 (CVal 8%N ?e8)] =>
    assert (UX9 : bv_unsigned (ew Ex 9) = c_sp1 cx) by (cbn [ew ewset Nat.eqb]; exact U9);
    assert (RS8 : val_mem SEGS mm (c_sp1 cx + 88) 8 (c_p cx + Z.of_nat pos + 2));
    [ eapply (field_of_regionG Ex mm 9%nat (c_sp1 cx) cs _ _ _ _ 88 8%N e8 (c_p cx + Z.of_nat pos + 2) FS88 UX9);
      [ repeat (first [left; reflexivity | right])
      | cbn [sv_denot ew ewset Nat.eqb]; rewrite U32; reflexivity
      | change (8 * Z.of_N 8) with 64; lia
      | cbn; lia ]
    | ]
  end
end.
(* ---- GR_malI at 0x81328 ---- *)
apply (HNEXT cx fp k acc ly3 S3 W3 ms4 _ HB HJ HFR HMO).
apply (fin_mal B MT cx fp k acc ly3 S3 W3 ms4 _ t).
- unfold gmach, gregs. splits;
    first [ exact Pc | exact Prv | exact Psv | exact Pro | exact Pfr | exact Pfc
          | (rewrite Q2; exact G2) | (rewrite Q8; exact G8) | (rewrite Q9; exact G9)
          | (rewrite Q3; exact G3) | (rewrite Q4; exact G4) ].
- exact Hk.
- exact Hacc.
- exact Hbl.
- exact HinT.
- exact Ht0.
- exact HLT.
- exact Hn.
- intros i Hi. pose proof Hi as Hi'. rewrite HLEN in Hi'. unfold GE_NSH in Hi'.
  assert (Hiz : 0 <= Z.of_nat i < 104) by lia.
  destruct (gshadow_band cx fp t ly3 (Z.of_nat i) HL Hiz) as (B1 & B2 & B3).
  rewrite HWIN; [exact (HSH i Hi) | | |]; unfold kLowShadowBeg, kHighMemBeg, GO_RAW in *; lia.
- apply (hmem_tr cx fp t ly3 W3 ms3 ms4 HL).
  + intros a Ha (_ & Hb1 & Hb2). exact (HWIN a Ha Hb1 Hb2).
  + exact (conj HSV (conj HFL (conj HIN (conj SL (conj HTB (conj HWS HST)))))).
- rewrite Q20. exact R20.
- rewrite Q21. exact R21.
- rewrite Q22. exact R22.
- rewrite Q24, (ER 24%nat 24%bv eq_refl), R24, HPR. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
- rewrite Q25. exact R25.
- rewrite Q10. reflexivity.
- unfold gslot. rewrite HPR. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms4)); [|lia].
  replace (c_p cx + Z.of_nat (S (S pos))) with (c_p cx + Z.of_nat pos + 2) by lia. exact RS8.
- unfold gfb. rewrite HRB. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms4)); [|apply u8_range].
  replace (gF cx fp + GO_RAW) with (gF cx fp + GO_RAW + 0) by lia. exact RV0.
- unfold gfb. rewrite HRW. apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms4)); [|apply u8_range].
  replace (gF cx fp + (GO_RAW + 1)) with (gF cx fp + GO_RAW + 1) by lia. exact RV1.
- exact HREL.
- exact HI1.
Qed.

End c.
End b.
End a.
