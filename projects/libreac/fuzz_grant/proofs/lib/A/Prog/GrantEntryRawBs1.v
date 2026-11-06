(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySetDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySetDefs.v, with its numbers changed; 406 of its 486 lines of code are new or changed and 1005 lines of the source are left out. *)
(* The hand-built allocation phase of LLVMFuzzerTestOneInput on the ASan build, segment
   Bs1: the slots 0x81340 .. 0x81354 (GR_bs1 .. GR_fit of GrantEntryRawDefs.v).

   0x81340  jal reac_grant_build_sweep   (s, 128, &raw, t)
   0x81344  lbu a2,0(s9)                 raw.base
   0x81348  lbu a1,1(s9)                 raw.width
   0x8134c  mv  s7,a0                    the answer of the sweep
   0x81350  mv  a0,a2
   0x81354  jal reac_grant_alloc_fits    (the next cut, GR_fit)

   The call is made through GrantEntrySetDefs.v's `gcall` with the stack RB_TBSW_STK and
   the write window the contract gives (the sweep buffer `s` when the call builds a
   sweep, nothing when it refuses).  The two loads are not shadow-checked: `raw` is this
   function's own frame object and the compiler left the checks out. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC85 YC88 GrantFrame.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
GrantEntryDefs GrantEntrySetDefs GrantEntryRawDefs GrantEntryRawLib HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
GrantSlotPlan SlotNeeds_c SegSetModel BuildSweepLink.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis BSW : traw_bsw_spec B.

Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* ---- the shadow of the frame while `raw` is usable ---- *)
Lemma GSH_raw_len : length GSH_raw = GE_NSH.
Proof. vm_compute. reflexivity. Qed.
Lemma GSH_raw_70 : nth 70 GSH_raw 0 = 2.
Proof. vm_compute. reflexivity. Qed.

(* ---- a byte of the view, as the engine's val_mem (YC88's val_mem1_of_aview) ---- *)
Lemma rval1 : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof. intros H mem a v Hv. exact (proj1 (val_mem1_of_aview SEGS H mem a v Hv)). Qed.

(* ---- a run whose regions have no write window keeps every byte ---- *)
Lemma rframe_eq : forall (E : env) rs (H : word -> bool) (m m' : word -> option byte),
  (forall a, ~ in_wrange E rs a) -> frame_of E rs m m' ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' Hne HF a. apply aview_eq_of. unfold mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. apply Hne.
Qed.

(* ---- where things are, once the sweep buffer is allocated ---- *)
Definition rlayout (cx : ecx) (fp t s : Z) (ly3 : alayout) : Prop :=
  alloc_ceiling + 32768 <= spZ (c_regs cx) /\ spZ (c_regs cx) mod 16 = 0 /\
  spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288 /\ c_sp1 cx mod 32 = 0 /\
  frame_addr ly3 GE_CID fp = gF cx fp /\ 4096 <= gF cx fp /\
  gF cx fp + 1024 <= alloc_ceiling /\ gF cx fp mod 64 = 0 /\ in_app (gF cx fp) 1024 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  4096 <= t /\ t + 460 <= alloc_ceiling /\ in_app t 460 /\
  (t + 460 <= gF cx fp \/ gF cx fp + 1024 <= t) /\
  4096 <= s /\ s + RAW_SW <= alloc_ceiling /\ in_app s RAW_SW /\
  (s + RAW_SW <= gF cx fp \/ gF cx fp + 1024 <= s) /\
  (s + RAW_SW <= t \/ t + 460 <= s) /\
  ~ In (s, RAW_SW) (ablocks B (c_ly cx) (c_S cx)) /\
  (0 < c_n cx -> 4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
     (c_p cx + c_n cx <= gF cx fp \/ gF cx fp + 1024 <= c_p cx) /\
     (c_p cx + c_n cx <= t \/ t + 460 <= c_p cx) /\
     (c_p cx + c_n cx <= s \/ s + RAW_SW <= c_p cx)).

Lemma rlay : forall cx fp k ly3 S3 W3 mem md t s,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GE_CID, fp)] -> gblk2 B cx ly3 S3 t s -> rlayout cx fp t s ly3.
Proof.
  intros cx fp k ly3 S3 W3 mem md t s HB HJ HFR Hbl.
  pose proof HB as (HPRE & _ & _ & Hpn & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (proj1 HJ) as HAR.
  pose proof (proj1 alloc_ceiling_val) as AC.
  destruct (g_ly B cx fp k ly3 S3 W3 mem md HJ) as [Etop EF].
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem md GE_CID fp HAR Hfin) as (Hf0 & Hfc & Happ).
  destruct (frame_al64 SEGS B ly3 S3 W3 mem md GE_CID fp HAR Hfin) as (Hf64 & _).
  assert (FB : fs_frame_bytes GE_CID = 1024) by reflexivity.
  assert (EgF : frame_addr ly3 GE_CID fp = gF cx fp) by (unfold gF; apply EF).
  rewrite FB, EgF in *.
  assert (HinT : In (t, 460) (ablocks B ly3 S3))
    by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (HinS : In (s, RAW_SW) (ablocks B ly3 S3))
    by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md t 460 HAR HinT) as (_ & Ht4096 & Htc & Htapp & _).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md s RAW_SW HAR HinS) as (_ & Hs4096 & Hsc & Hsapp & _).
  change (req_size 460) with 460 in *. change (req_size RAW_SW) with RAW_SW in *.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem md t 460 GE_CID fp HAR HinT Hfin) as HTF.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem md s RAW_SW GE_CID fp HAR HinS Hfin) as HSF.
  change (req_size 460) with 460 in HTF. change (req_size RAW_SW) with RAW_SW in HSF.
  unfold zdisjoint in HTF, HSF; cbn [fst snd] in HTF, HSF. rewrite FB, EgF in HTF, HSF.
  assert (HTS : t + 460 <= s \/ s + RAW_SW <= t).
  { pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (t, 460) (s, RAW_SW)
      (ablocks B (c_ly cx) (c_S cx)) [] [] HAR ltac:(unfold gblk2 in Hbl; exact Hbl)) as HD.
    unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD.
    change (req_size 460) with 460 in HD. change (req_size RAW_SW) with RAW_SW in HD. lia. }
  assert (HSnew : ~ In (s, RAW_SW) (ablocks B (c_ly cx) (c_S cx))).
  { intros Hin0. apply in_split in Hin0 as (m1 & m2 & El).
    pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (s, RAW_SW) (s, RAW_SW)
      m1 (m2 ++ [(t, 460)]) [] HAR
      ltac:(unfold gblk2 in Hbl; rewrite Hbl, El, <- app_assoc; cbn [app];
            rewrite <- app_assoc; reflexivity)) as HD.
    unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD.
    change (req_size RAW_SW) with RAW_SW in HD. unfold RAW_SW in HD. lia. }
  assert (S1 : spZ (c_regs cx) - 320 <= c_sp1 cx <= spZ (c_regs cx) - 288).
  { rewrite Hsp1. pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)).
    pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)). lia. }
  assert (S2 : c_sp1 cx mod 32 = 0) by (rewrite Hsp1, Z.mul_comm; apply Z_mod_mult).
  unfold GE_STK in *.
  unfold rlayout. splits; try lia; try assumption.
  - unfold gSH, shadow_of_addr. reflexivity.
  - intros Hn. destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
    assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
    destruct (al_blocks _ _ LAWS ly3 S3 W3 mem md _ _ HAR HinP) as (_ & Hp4096 & Hpc & Hpapp & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem md _ _ GE_CID fp HAR HinP Hfin) as HPF.
    rewrite FB, EgF in HPF. unfold zdisjoint in HPF; cbn [fst snd] in HPF.
    apply in_split in Hin0 as (m1 & m2 & El).
    assert (HPT : c_p cx + c_n cx <= t \/ t + 460 <= c_p cx).
    { pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (c_p cx, c_n cx) (t, 460)
        m1 m2 [(s, RAW_SW)] HAR
        ltac:(unfold gblk2 in Hbl; rewrite Hbl, El, <- app_assoc; cbn [app]; reflexivity)) as HD.
      unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD.
      change (req_size 460) with 460 in HD. lia. }
    assert (HPS : c_p cx + c_n cx <= s \/ s + RAW_SW <= c_p cx).
    { pose proof (sep_blocks_pos SEGS B LAWS ly3 S3 W3 mem md (c_p cx, c_n cx) (s, RAW_SW)
        m1 (m2 ++ [(t, 460)]) [] HAR
        ltac:(unfold gblk2 in Hbl; rewrite Hbl, El, <- app_assoc; cbn [app];
              rewrite <- app_assoc; reflexivity)) as HD.
      unfold zdisjoint, block_rng in HD; cbn [fst snd] in HD.
      change (req_size RAW_SW) with RAW_SW in HD. lia. }
    splits; lia.
Qed.

(* ---- the state of the two loads at 0x81344 ---- *)
Definition R_raw : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0 2 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0))].
Definition F_raw : facts := mkFacts [(32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition ss_raw : sstate := mkSS 0xc94 sr_atoms [R_raw] None F_raw.
Definition ss_bs1 : sstate := mkSS GR_bs1 sr_atoms [] None (mkFacts [] [] []).

(* A register literal is callee-saved. *)
Ltac acs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] =>
    let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end; lia.

(* ---- the segment ---- *)
Theorem seg_raw_bs1 : forall POST,
  ge_from B MT POST (GR_fitI B MT) -> ge_from B MT POST (GR_bs1I B MT).
Proof.
  intros POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO
    (t & s & HC & Hk & Hacc & Hbl & Htab & Hs4096 & R18 & R10 & R11 & R12 & R13).
  pose proof HC as (HBD & Hn26 & R20 & R21 & R22 & R24 & R25 & H88 & Hlate & Hb0 & Hb1 &
                    Hws & Hst & Hrel & HI1).
  pose proof HBD as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfc & HG & HSV & HSHW & HFL & Hshlen & HINP).
  pose proof HG as (G2 & G8 & G9 & G3 & G4).
  pose proof (rlay cx fp k ly3 S3 W3 (ms_mem ms3) md3 t s HB HJ HFR Hbl) as HL.
  pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & L11 & L12 & L13 & L14 &
                    L15 & L16 & L17 & L18 & L19 & L20 & L21 & L22).
  pose proof (proj1 alloc_ceiling_val) as AC.
  pose proof (SegSetModel.tables_end_inv (c_pl cx)) as (LT & LW & LS & _ & _).
  pose proof (proj1 HJ) as HAR3.
  assert (HSTKv : RB_TBSW_STK = 6224) by (vm_compute; reflexivity).
  assert (Hfin : In (GE_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (HinT : In (t, TX_SIZE) (ablocks B ly3 S3))
    by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; right; left; reflexivity).
  assert (HinS : In (s, RAW_SW) (ablocks B ly3 S3))
    by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
  (* the frame's alignment, and the shadow byte of `raw` *)
  assert (HF8 : gF cx fp mod 8 = 0).
  { rewrite (Z.div_mod (gF cx fp) 64 ltac:(lia)), L9, Z.add_0_r.
    replace (64 * (gF cx fp / 64)) with (8 * (gF cx fp / 64) * 8) by lia. apply Z_mod_mult. }
  pose proof (Z.div_mod (gF cx fp) 8 ltac:(lia)) as DM8.
  pose proof (Z.mod_pos_bound (gF cx fp) 8 ltac:(lia)) as DM8b.
  assert (HAL8 : (gF cx fp + GO_RAW) mod 8 = 0)
    by (unfold GO_RAW; rewrite Z.add_mod by lia; rewrite HF8; reflexivity).
  assert (HSHa : shadow_of_addr SHADOW_OFF (gF cx fp + GO_RAW) = gSH cx fp + 70).
  { unfold shadow_of_addr. rewrite L11.
    replace (gF cx fp + GO_RAW) with (gF cx fp + 70 * 8) by (unfold GO_RAW; lia).
    rewrite Z.div_add by lia. lia. }
  (* the two bytes of `raw` are bytes of the input *)
  assert (HBW : 0 <= raw_b cx < 256 /\ 0 <= raw_w cx < 256).
  { unfold raw_b, raw_w, GrantSlotPlan.raw_rd.
    pose proof (SegSetModel.rd8_range (c_pl cx) (GrantSlotPlan.pos_end (c_pl cx))) as H1.
    destruct (GrantSlotPlan.rd8 (c_pl cx) (GrantSlotPlan.pos_end (c_pl cx))) as [rb p1] eqn:E1.
    pose proof (SegSetModel.rd8_range (c_pl cx) p1) as H2.
    destruct (GrantSlotPlan.rd8 (c_pl cx) p1) as [rw p2] eqn:E2.
    cbn [fst snd] in *. lia. }
  destruct HBW as [HB0 HW0].
  (* what `fits` gives about the width, and the contract's test *)
  assert (Hwfit : fits (raw_b cx) (raw_w cx) = true -> 1 <= raw_w cx <= 40).
  { intros Hf. unfold fits in Hf.
    apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [Hf _].
    apply andb_true_iff in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hbok : bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx) =
                 fits (raw_b cx) (raw_w cx)).
  { unfold bsw_ok. destruct (fits (raw_b cx) (raw_w cx)) eqn:Hf.
    - pose proof (Hwfit eq_refl) as Hw.
      replace (s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (gF cx fp + GO_RAW =? 0) with false
        by (symmetry; apply Z.eqb_neq; unfold GO_RAW; lia).
      replace (8 + 3 * raw_w cx <=? 128) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
    - rewrite andb_false_r, andb_false_l. reflexivity. }
  assert (HFPin : forall a,
     inFP (if bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx)
           then [(s, s + 34 * (8 + 3 * raw_w cx))] else []) a -> s <= a < s + RAW_SW).
  { intros a Ha. rewrite Hbok in Ha. destruct (fits (raw_b cx) (raw_w cx)) eqn:Hf.
    - pose proof (Hwfit eq_refl) as Hw.
      destruct Ha as (r & Hr & Hab). cbn [In] in Hr. destruct Hr as [<- | []].
      cbn [fst snd] in Hab. unfold RAW_SW. lia.
    - destruct (inFP_nil a Ha). }
  assert (HsRange : 0 <= s < 2 ^ 63) by (unfold RAW_SW in L17; lia).
  (* ---- 0x81340: the jal ---- *)
  rewrite (gmach_mkst cx ms3 GR_bs1 ltac:(unfold gmach; splits; assumption)).
  remember (ms_regs ms3) as regs eqn:Eregs. remember (ms_mem ms3) as mem eqn:Emem.
  remember (Eimg (Ereg regs [])) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r0 Hr0; subst E; apply ew_Eimg_Ereg_nat; exact Hr0).
  assert (HS : st_ok_pi SEGS VAL E ss_bs1
                 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + GR_bs1)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold ss_bs1. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - constructor.
    - exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
  assert (SHOK : sh_ok SEGS GBx [] E (mrestrict (w_H W3) mem)) by constructor.
  subst mem.
  paj_run_tok RUN HS HJ SHOK GBspan; [apply awr_ok_nil |].
  lazymatch goal with HFx : frame_of E _ (ms_mem ms3) (ms_mem ?m1) |- _ => rename HFx into HFr1 end.
  lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msX) |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
    assert (HK0 : forall a, aview SEGS (w_H W3) (ms_mem msX) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a; exact (frame_nil_eq E _ (w_H W3) _ _ eq_refl HFr1 a));
    rename HSx into HSc; rename msX into msc; remember mdX as mdc eqn:Hmdc
  end.
  prreg HSc (1%bv : bv 5) Q1. prreg HSc (2%bv : bv 5) Q2. prreg HSc (3%bv : bv 5) Q3.
  prreg HSc (4%bv : bv 5) Q4. prreg HSc (8%bv : bv 5) Q8. prreg HSc (9%bv : bv 5) Q9.
  prreg HSc (10%bv : bv 5) Q10. prreg HSc (11%bv : bv 5) Q11. prreg HSc (12%bv : bv 5) Q12.
  prreg HSc (13%bv : bv 5) Q13. prreg HSc (18%bv : bv 5) Q18. prreg HSc (20%bv : bv 5) Q20.
  prreg HSc (21%bv : bv 5) Q21. prreg HSc (22%bv : bv 5) Q22. prreg HSc (24%bv : bv 5) Q24.
  prreg HSc (25%bv : bv 5) Q25.
  rewrite (EE 2%nat 2%bv eq_refl) in Q2. rewrite (EE 3%nat 3%bv eq_refl) in Q3.
  rewrite (EE 4%nat 4%bv eq_refl) in Q4. rewrite (EE 8%nat 8%bv eq_refl) in Q8.
  rewrite (EE 9%nat 9%bv eq_refl) in Q9. rewrite (EE 10%nat 10%bv eq_refl) in Q10.
  rewrite (EE 11%nat 11%bv eq_refl) in Q11. rewrite (EE 12%nat 12%bv eq_refl) in Q12.
  rewrite (EE 13%nat 13%bv eq_refl) in Q13. rewrite (EE 18%nat 18%bv eq_refl) in Q18.
  rewrite (EE 20%nat 20%bv eq_refl) in Q20. rewrite (EE 21%nat 21%bv eq_refl) in Q21.
  rewrite (EE 22%nat 22%bv eq_refl) in Q22. rewrite (EE 24%nat 24%bv eq_refl) in Q24.
  rewrite (EE 25%nat 25%bv eq_refl) in Q25.
  subst regs.
  rewrite (st_ok_restrict_mkst SEGS (w_H W3) _ _ _ HSc eq_refl). cbn [ss_pc setpc].
  rewrite pa_sigma_reac_grant_build_sweep.
  (* the memory facts at the callee's first slot *)
  assert (HraC : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 8) =
                 Some (raZ (c_regs cx))).
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem msc))
      (spZ (c_regs cx) - 8) (fun j _ => HK0 (spZ (c_regs cx) - 8 + j))). exact (proj1 HSV). }
  assert (Hs0C : rdword (aview SEGS (w_H W3) (ms_mem msc)) (spZ (c_regs cx) - 16) =
                 Some (s0Z (c_regs cx))).
  { rewrite (rdword_tr (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem msc))
      (spZ (c_regs cx) - 16) (fun j _ => HK0 (spZ (c_regs cx) - 16 + j))).
    pose proof (proj2 HSV 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
  assert (VSH : aview SEGS (w_H W3) (ms_mem msc) (gSH cx fp + 70) = Some 2).
  { rewrite (HK0 (gSH cx fp + 70)).
    pose proof (HSHW 70%nat ltac:(rewrite GSH_raw_len; unfold GE_NSH; lia)) as H70.
    replace (Z.of_nat 70%nat) with 70 in H70 by reflexivity.
    rewrite GSH_raw_70 in H70. exact H70. }
  assert (VB0 : aview SEGS (w_H W3) (ms_mem msc) (gF cx fp + GO_RAW) = Some (raw_b cx))
    by (rewrite (HK0 (gF cx fp + GO_RAW)); exact Hb0).
  assert (VB1 : aview SEGS (w_H W3) (ms_mem msc) (gF cx fp + (GO_RAW + 1)) = Some (raw_w cx))
    by (rewrite (HK0 (gF cx fp + (GO_RAW + 1))); exact Hb1).
  assert (HtabC : gtab B cx ly3 S3 W3 msc t (GrantSlotPlan.T_end (c_pl cx)))
    by (apply (rm_gtab B cx ly3 S3 ly3 S3 W3 ms3 W3 msc t _ Htab HinT);
        intros a _; exact (HK0 a)).
  (* ---- the call ---- *)
  eapply (gcall B MT LAWS RB_TBSW_STK
    (if bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx)
     then [(s, s + 34 * (8 + 3 * raw_w cx))] else [])
    (fun ly' S' W' regs' mem' md' =>
       frames S' = frames S3 /\ ablocks B ly' S' = ablocks B ly3 S3 /\
       (exists f, S' = set_fs f S3) /\
       getr regs' 10 = w64 (if bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx)
                            then 8 + 3 * raw_w cx else -1) /\
       (bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx) = true ->
          garr8 SEGS (mrestrict (w_H W') mem') s
            (map bv_unsigned (SWEEP (raw_b cx) (Z.to_nat (raw_w cx))
               (sweep_vals (GrantSlotPlan.T_end (c_pl cx)) t (raw_b cx) (Z.to_nat (raw_w cx)))))))
    _ 0xc94 POST cx fp k ly3 S3 W3 (ms_regs msc) (ms_mem msc) mdc HB HJ
    ltac:(rewrite Q2; exact G2) ltac:(rewrite Q8; exact G8)
    ltac:(rewrite Q3; exact G3) ltac:(rewrite Q4; exact G4)
    ltac:(rewrite Q1; reflexivity) ltac:(lia) ltac:(reflexivity)
    HraC Hs0C ltac:(lia)).
  - (* the write window is inside the new block *)
    intros a Ha. pose proof (HFPin a Ha) as Hab.
    exists s, RAW_SW. split; [exact HinS | split; [exact L21|]].
    change (req_size RAW_SW) with RAW_SW. lia.
  - (* the contract *)
    intros HPRE.
    refine (BSW ly3 S3 W3 (ms_regs msc) (ms_mem msc) mdc (gch cx) s 128 (gF cx fp + GO_RAW) t
      (raw_b cx) (raw_w cx) (GrantSlotPlan.T_end (c_pl cx)) HPRE _ _ _
      ltac:(rewrite Q10; exact R10) ltac:(rewrite Q11; exact R11)
      ltac:(rewrite Q12; exact R12) ltac:(rewrite Q13; exact R13)
      HsRange ltac:(lia) ltac:(unfold GO_RAW; lia) _ HinT LT _ _ _ _).
    + rewrite HFR. cbn [length Z.of_nat]. lia.
    + unfold spZ. rewrite Q2, G2. unfold w64. rewrite unsigned_lit_small by lia.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
      pose proof HSTK as (_ & _ & _ & _ & _ & _ & _ & Htop & _).
      destruct (g_ly B cx fp k ly3 S3 W3 (ms_mem msc) mdc HJ) as [Etop _]. lia.
    + eapply garo; [exact HB | exact HJ].
    + (* `raw` is a usable object of this frame, and holds the two bytes *)
      intros _. split.
      * unfold afobj. split; [exists GE_CID, fp; splits|].
        { exact Hfin. }
        { unfold GE_CID. lia. }
        { rewrite L6. exact HF8. }
        { rewrite L6. unfold GO_RAW. lia. }
        { rewrite L6. change (fs_frame_bytes GE_CID) with 1024. unfold GO_RAW. lia. }
        { split; [exact HAL8|].
          apply (range_addressable_partial (aview SEGS (w_H W3) (ms_mem msc)) SHADOW_OFF
            (gF cx fp + GO_RAW) 2); [|exact HAL8 | lia].
          rewrite HSHa. exact VSH. }
      * intros j Hj. cbn [length] in Hj.
        destruct j as [|[|j]]; [| |cbn [length] in Hj; lia].
        { replace (Z.of_nat 0%nat) with 0 by reflexivity. rewrite Z.add_0_r.
          cbn [nth]. split; [apply rval1; exact VB0 | lia]. }
        { replace (Z.of_nat 1%nat) with 1 by reflexivity. cbn [nth].
          split; [|lia]. apply rval1.
          replace (gF cx fp + GO_RAW + 1) with (gF cx fp + (GO_RAW + 1)) by lia. exact VB1. }
    + eapply gtab_obj. exact HtabC.
    + exact (BuildSweepLink.I1_set01 _ HI1).
    + exact (BuildSweepLink.I1_legal _ HI1).
    + intros Hbo. rewrite Hbok in Hbo. pose proof (Hwfit Hbo) as Hw.
      exists s, RAW_SW. split; [exact HinS | split; [lia|]]. unfold RAW_SW. lia.
  - (* ---- 0xc94 .. 0xca4: the two loads and the two moves ---- *)
    intros W2 ly2 S2 regs2 mem2 md2 HJ2 HJc HP (QFR & QBL & (ff & QS) & Q10' & _).
    assert (PR : forall r : Z, acallee_saved r ->
                 getr regs2 (Z_to_bv 5 r) = getr (ms_regs msc) (Z_to_bv 5 r)) by exact HP.
    assert (PRb : forall r : bv 5, acallee_saved (bv_unsigned r) ->
                  getr regs2 r = getr (ms_regs msc) r).
    { intros r Hr. pose proof (PR (bv_unsigned r) Hr) as H.
      rewrite !Z_to_bv_bv_unsigned in H. exact H. }
    (* the call keeps every byte this segment speaks about *)
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & _ & F4 & _).
    assert (HnF : forall a, (s <= a < s + RAW_SW -> False) ->
                  ~ inFP (if bsw_ok s (gF cx fp + GO_RAW) 128 (raw_b cx) (raw_w cx)
                          then [(s, s + 34 * (8 + 3 * raw_w cx))] else []) a).
    { intros a Hout Hin. exact (Hout (HFPin a Hin)). }
    assert (HKEEP : forall a, rm_at cx fp t a ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem msc) a).
    { intros a Ha. unfold rm_at in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
      - apply F1; [lia | lia].
      - pose proof HB as (_ & _ & _ & Hpn & _).
        destruct Hpn as [[Hn0 _] | [Hnn Hin0]]; [unfold c_n in *; lia|].
        assert (HinP : In (c_p cx, c_n cx) (ablocks B ly3 S3))
          by (unfold gblk2 in Hbl; rewrite Hbl; apply in_or_app; left; exact Hin0).
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
        destruct (L22 ltac:(lia)) as (_ & _ & _ & _ & HPS).
        replace a with (c_p cx + (a - c_p cx)) by lia.
        apply (F2 (c_p cx) (c_n cx) (a - c_p cx) HinP ltac:(rewrite QBL; exact HinP));
          [lia | apply HnF; lia].
      - apply (F4 GE_CID fp a Hfin); [|apply HnF; lia].
        left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite L6.
        change (fs_frame_bytes GE_CID) with 1024. lia.
      - apply (F4 GE_CID fp a Hfin);
          [|apply HnF; unfold in_app, RAW_SW, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia].
        right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite L6.
        change (fs_frame_bytes GE_CID / 8) with 128. rewrite <- L11. lia.
      - replace a with (t + (a - t)) by lia.
        apply (F2 t 460 (a - t) HinT ltac:(rewrite QBL; exact HinT));
          [change (req_size 460) with 460; lia | apply HnF; lia]. }
    assert (HK1 : forall a, rm_at cx fp t a ->
       aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha; rewrite (HKEEP a Ha); exact (HK0 a)).
    assert (VB0' : aview SEGS (w_H W2) mem2 (gF cx fp + GO_RAW) = Some (raw_b cx)).
    { rewrite (HK1 (gF cx fp + GO_RAW)
        ltac:(unfold rm_at; right; right; left; unfold GO_RAW; lia)). exact Hb0. }
    assert (VB1' : aview SEGS (w_H W2) mem2 (gF cx fp + GO_RAW + 1) = Some (raw_w cx)).
    { replace (gF cx fp + GO_RAW + 1) with (gF cx fp + (GO_RAW + 1)) by lia.
      rewrite (HK1 (gF cx fp + (GO_RAW + 1))
        ltac:(unfold rm_at; right; right; left; unfold GO_RAW; lia)). exact Hb1. }
    (* the symbolic state of the four slots *)
    remember (Eimg (Ereg regs2 (map (Z_to_bv 64) [raw_b cx; raw_w cx]))) as E2 eqn:HE2.
    assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
    assert (EE2 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
      by (intros n0 r0 Hr0; subst E2; apply ew_Eimg_Ereg_nat; exact Hr0).
    assert (EX2 : forall j, (j < 2)%nat ->
        ew E2 (32 + j) = nth j (map (Z_to_bv 64) [raw_b cx; raw_w cx]) (Z_to_bv 64 0))
      by (intros j Hj; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
    assert (E32 : ew E2 32 = w64 (raw_b cx)) by exact (EX2 0%nat ltac:(lia)).
    assert (E33 : ew E2 33 = w64 (raw_w cx)) by exact (EX2 1%nat ltac:(lia)).
    assert (E25 : ew E2 25 = w64 (gF cx fp + GO_RAW))
      by (rewrite (EE2 25%nat 25%bv eq_refl), (PRb 25%bv ltac:(acs)), Q25; exact R25).
    assert (U25 : bv_unsigned (ew E2 25) = gF cx fp + GO_RAW)
      by (rewrite E25; unfold w64; apply unsigned_lit_small; unfold GO_RAW; lia).
    assert (HS2 : st_ok_pi SEGS VAL E2 ss_raw
                    (restrict (w_H W2)
                       (mkst regs2 (Z_to_bv 64 (BASE + 0xc94)) mem2 (seg_rom SEGS)))).
    { rewrite restrict_mkst_fx. unfold ss_raw. apply pa_entry_st_ok_full.
      - rewrite HE2. apply regs_ok_Eimg_Ereg.
      - vm_compute. reflexivity.
      - apply Forall_cons; [|apply Forall_nil].
        unfold region_ok, R_raw.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U25. split; [unfold GO_RAW; lia|]. split; [unfold GO_RAW; lia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        + apply (chunk_ok_val SEGS E2 _ (gF cx fp + GO_RAW) 0 1 (SOff 32 0) (raw_b cx)).
          * apply gsv0; [exact E32 | lia].
          * cbn. lia.
          * cbn. lia.
          * rewrite Z.add_0_r. apply rval1. exact VB0'.
        + apply (chunk_ok_val SEGS E2 _ (gF cx fp + GO_RAW) 1 1 (SOff 33 0) (raw_w cx)).
          * apply gsv0; [exact E33 | lia].
          * cbn. lia.
          * cbn. lia.
          * apply rval1. exact VB1'.
      - cbn [pairwise_disjoint all_disjoint]. split; exact I.
      - split; [|split; exact I]. cbn [f_atoms atoms_ok].
        split; [|split; [|exact I]];
          unfold afact_ok; cbn [af_lo af_hi af_al2];
          [rewrite E32 | rewrite E33]; unfold w64; rewrite unsigned_lit_small by lia;
          rewrite Z.pow_0_r, Z.mod_1_r; lia. }
    assert (SHOK2 : sh_ok SEGS GBx [] E2 (mrestrict (w_H W2) mem2)) by constructor.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 GBspan 0xca4;
      [apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi R_raw]; lia | apply awr_ok_nil] |].
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msF) |- SRr _ _ (mkCfg ?msF ?mdF) _ =>
      assert (HMEQ2 : forall a, aview SEGS (w_H W2) (ms_mem msF) a = aview SEGS (w_H W2) mem2 a);
      [ lazymatch goal with HFx : frame_of E2 _ mem2 (ms_mem msF) |- _ =>
          intros a; refine (rframe_eq E2 (ss_mem ss_raw) (w_H W2) _ _ _ HFx a);
          intros b (r & Hr & Hab); cbn [ss_mem ss_raw In] in Hr;
          destruct Hr as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val R_raw] in Hab; lia
        end
      | rename HSx into HSF; rename msF into msf ]
    end.
    (* the registers after the four slots *)
    destruct (gst_ok_mach _ _ _ _ HSF eq_refl) as (Pc & Prv & Psv & Pro & Pfr & Pfc).
    cbn [ss_pc] in Pc.
    prreg HSF (2%bv : bv 5) P2. prreg HSF (3%bv : bv 5) P3. prreg HSF (4%bv : bv 5) P4.
    prreg HSF (8%bv : bv 5) P8. prreg HSF (9%bv : bv 5) P9. prreg HSF (10%bv : bv 5) P10.
    prreg HSF (11%bv : bv 5) P11. prreg HSF (18%bv : bv 5) P18. prreg HSF (20%bv : bv 5) P20.
    prreg HSF (21%bv : bv 5) P21. prreg HSF (22%bv : bv 5) P22. prreg HSF (23%bv : bv 5) P23.
    prreg HSF (24%bv : bv 5) P24. prreg HSF (25%bv : bv 5) P25.
    rewrite (EE2 2%nat 2%bv eq_refl) in P2. rewrite (EE2 3%nat 3%bv eq_refl) in P3.
    rewrite (EE2 4%nat 4%bv eq_refl) in P4. rewrite (EE2 8%nat 8%bv eq_refl) in P8.
    rewrite (EE2 9%nat 9%bv eq_refl) in P9. rewrite (EE2 10%nat 10%bv eq_refl) in P23.
    rewrite (EE2 18%nat 18%bv eq_refl) in P18. rewrite (EE2 20%nat 20%bv eq_refl) in P20.
    rewrite (EE2 21%nat 21%bv eq_refl) in P21. rewrite (EE2 22%nat 22%bv eq_refl) in P22.
    rewrite (EE2 24%nat 24%bv eq_refl) in P24. rewrite (EE2 25%nat 25%bv eq_refl) in P25.
    rewrite E32 in P10. rewrite E33 in P11.
    (* the bytes the two runs and the call keep, all the way from ms3 *)
    assert (HALL : forall a, rm_at cx fp t a ->
       aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha; rewrite (HMEQ2 a); exact (HK1 a Ha)).
    (* the state the next cut asks for *)
    apply (HN cx fp k acc ly2 S2 W2 msf _ HB HJ2
      ltac:(rewrite QFR; exact HFR)
      ltac:(rewrite QS; destruct MTF as [_ MOFS _]; apply MOFS; exact HMO)).
    exists t, s. splits.
    + eapply (rm_rcore cx fp GR_bs1 GR_fit t W3 ms3 W2 msf HC ltac:(lia) ltac:(lia) HALL
        Pc Prv Psv Pro Pfr Pfc).
      * rewrite P2, (PRb 2%bv ltac:(acs)). exact Q2.
      * rewrite P3, (PRb 3%bv ltac:(acs)). exact Q3.
      * rewrite P4, (PRb 4%bv ltac:(acs)). exact Q4.
      * rewrite P8, (PRb 8%bv ltac:(acs)). exact Q8.
      * rewrite P9, (PRb 9%bv ltac:(acs)). exact Q9.
      * rewrite P20, (PRb 20%bv ltac:(acs)). exact Q20.
      * rewrite P21, (PRb 21%bv ltac:(acs)). exact Q21.
      * rewrite P22, (PRb 22%bv ltac:(acs)). exact Q22.
      * rewrite P24, (PRb 24%bv ltac:(acs)). exact Q24.
      * rewrite P25, (PRb 25%bv ltac:(acs)). exact Q25.
    + exact Hk.
    + exact Hacc.
    + unfold gblk2 in Hbl |- *. rewrite QBL. exact Hbl.
    + apply (rm_gtab B cx ly3 S3 ly2 S2 W3 ms3 W2 msf t _ Htab ltac:(rewrite QBL; exact HinT)).
      intros a Ha. apply HALL. unfold rm_at. right; right; right; right. exact Ha.
    + exact Hs4096.
    + rewrite P18, (PRb 18%bv ltac:(acs)), Q18. exact R18.
    + rewrite P23, Q10'. unfold raw_ans. rewrite <- Hbok. reflexivity.
    + rewrite P10. reflexivity.
    + rewrite P11. reflexivity.
Qed.

End c.
End b.
End a.
