(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS3d), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACgb.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySweepS3d.v. *)
(* The two calls each turn of image B's group-A loops makes in the sweep phase of
   fuzz_grant's entry function (fuzz_grant.c:326-332): want_of (0x8163c, 0x816e8) and then
   check_groupa (0x81654, 0x81700), from a cut's facts to the callee's contract and back.
   Shared by LLVMFEntrySweepS3a.v and LLVMFEntrySweepS3b.v.

   Adapted from lib/A/Prog/GrantEntrySweepS3d.v (a working branch afd75724b5b, blob
   b48edea0d, 155 lines), which carries no licence header of its own.
   Image B calls want_of where image A reads was_set /
   set_to in line and calls reac_headamp_default, so this file adds the call lemma
   `gsw_want` for GrantBContracts.tb_want_of_spec, which returns the effective value the
   table gives (`want_eff`), and `gsw_cga` meets image B's tb_check_groupa_spec (frame
   count, ly_top room, ch below 256, the class-2 side-stack frame's stack). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel HeadampLayout.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* This file's arithmetic over / and mod wants zify's euclidean-division flag true, so the file
   sets it so itself, whatever its Require closure leaves. `Local` keeps it here. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySweepS1c LLVMFEntrySweepS3c.

(* The value want_of gives for an unset or set cell is the effective value of the table
   the harness built (GrantSlotPlan.v Hrel, HeadampModel.v eff_cell): image A's own lemma,
   from its S3a, where image A needs it for its inline read. *)
Lemma want_eff : forall pl t ch p, 0 <= ch < 48 -> 0 < t -> 0 <= p < 3 ->
  Hrel (T_end pl) (ws_end pl) (st_end pl) ->
  eff (T_end pl) t ch p =
  if tb (ws_end pl) (3 * ch + p) =? 0 then dflt p else tb (st_end pl) (3 * ch + p).
Proof.
  intros pl t ch p Hch Ht Hp HR.
  rewrite eff_cell by lia.
  destruct (HR ch p ltac:(lia) ltac:(lia)) as [H1 H2].
  rewrite H1, H2. reflexivity.
Qed.

(* The frame's shadow bytes of was_set (4..21) and set_to (30..47) are 0 in GSH_a. *)
Lemma GSH_a_tables : forallb (fun j => Z.eqb (nth j GSH_a 0) 0) (seq 4 18 ++ seq 30 18) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma GSH_a_zero : forall j, 4 <= j < 22 \/ 30 <= j < 48 -> nth (Z.to_nat j) GSH_a 0 = 0.
Proof.
  intros j Hj. pose proof GSH_a_tables as Hb. rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat j) ltac:(apply in_app_iff; destruct Hj; [left | right]; apply in_seq; lia)).
  apply Z.eqb_eq in Hb. exact Hb.
Qed.

Lemma GSH_a_len : length GSH_a = GE_NSH.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The byte j of was_set or set_to is addressable for one byte while the cut's shadow is
   GSH_a: the shadow premises of want_of (GrantBContracts.v tb_want_of_spec). *)
Lemma gsw_arr_usable : forall cx fp (W3 : world SEGS) (mem : word -> option byte) off j,
  (forall i, (i < length GSH_a)%nat ->
     aview SEGS (w_H W3) mem (gSH cx fp + Z.of_nat i) = Some (nth i GSH_a 0)) ->
  gF cx fp mod 32 = 0 -> (off = GO_WAS \/ off = GO_SET) -> 0 <= j < 144 ->
  range_addressable (aview SEGS (w_H W3) mem) SHADOW_OFF (gF cx fp + off + j) 1.
Proof.
  intros cx fp W3 mem off j Hsh H32 Hoff Hj x Hx.
  assert (Ex : x = gF cx fp + off + j) by lia. subst x.
  assert (Hg8 : gF cx fp mod 8 = 0).
  { rewrite (Z.div_mod (gF cx fp) 32) by lia. rewrite H32, Z.add_0_r.
    replace (32 * (gF cx fp / 32)) with ((4 * (gF cx fp / 32)) * 8) by lia. apply Z_mod_mult. }
  assert (Ejj : (gF cx fp + off + j) / 8 = gF cx fp / 8 + (off + j) / 8).
  { rewrite (Z.div_mod (gF cx fp) 8) at 1 by lia. rewrite Hg8, Z.add_0_r.
    replace (8 * (gF cx fp / 8) + off + j) with ((off + j) + (gF cx fp / 8) * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (Hjr : 4 <= (off + j) / 8 < 22 \/ 30 <= (off + j) / 8 < 48).
  { destruct Hoff as [-> | ->]; unfold GO_WAS, GO_SET; [left | right]; split;
      first [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. }
  exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite Ejj.
  pose proof (Hsh (Z.to_nat ((off + j) / 8))) as Hs.
  rewrite Z2Nat.id in Hs by lia.
  assert (HSHe : gSH cx fp = SHADOW_OFF + gF cx fp / 8) by reflexivity.
  replace (SHADOW_OFF + (gF cx fp / 8 + (off + j) / 8)) with (gSH cx fp + (off + j) / 8) by lia.
  rewrite Hs by (rewrite GSH_a_len; unfold GE_NSH; lia).
  rewrite GSH_a_zero by exact Hjr. reflexivity.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* The head-amp table a cut tracks is the object check_groupa's contract reads
   (HeadampLayout.v tx_obj_bytes: the layout names every byte but 438, 439, 451). *)
Lemma gtab_obj : forall cx ly S W ms t T, gtab B cx ly S W ms t T ->
  obj_at SEGS (mrestrict (w_H W) (ms_mem ms)) t HeadampLayout.LAY_TX (HeadampLayout.tx_vals T).
Proof.
  intros cx ly S W ms t T (_ & _ & _ & HB). apply (proj2 (HeadampLayout.tx_obj_bytes SEGS _ _ _)). intros i Hi.
  pose proof (HeadampLayout.tx_fbyte_range i Hi) as Hr.
  assert (H438 : i <> 438) by (intros ->; vm_compute in Hi; discriminate Hi).
  assert (H439 : i <> 439) by (intros ->; vm_compute in Hi; discriminate Hi).
  assert (H451 : i <> 451) by (intros ->; vm_compute in Hi; discriminate Hi).
  specialize (HB i Hr H438 H439 H451). unfold aview in HB.
  destruct (mbyte SEGS (mrestrict (w_H W) (ms_mem ms)) (t + i)) as [b|]; [|discriminate HB].
  cbn [option_map] in HB. injection HB as HB. f_equal. apply bv_eq. rewrite HB. reflexivity.
Qed.

(* One call of want_of(was_set, set_to, c, p) from the realigned stack pointer, with
   0 <= c < 48 and 0 <= p < 3 given by the CALLER from its own path: a0 comes back as the
   effective value of the table the cut tracks, the layout, state and world are as they
   were, and every byte the cuts name is kept. *)
Lemma gsw_want : AR_laws SEGS B -> tb_want_of_spec B ->
  forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT ret t s c p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s ->
  (forall i, (i < length GSH_a)%nat ->
     aview SEGS (w_H W3) memT (gSH cx fp + Z.of_nat i) = Some (nth i GSH_a 0)) ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  getr regsT 10 = w64 (gF cx fp + GO_WAS) -> getr regsT 11 = w64 (gF cx fp + GO_SET) ->
  getr regsT 12 = w64 c -> getr regsT 13 = w64 p ->
  0 <= c < 48 -> 0 <= p < 3 ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_want_of)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly3 S3 W3 mem2 md2 k /\
       aregs_preserved regsT regs2 /\ vkeep (gsw_out cx fp t s) W3 memT W3 mem2 /\
       getr regs2 10 = w64 (eff (T_end (c_pl cx)) t c p)).
Proof.
  intros LAWS WOF cx fp k ly3 S3 W3 regsT memT mdT ret t s c p HB HJ HFR HBLK HSH R2 R3 R4 R8 R1 Hret Hret2 H8 H16
    R10 R11 R12 R13 Hc Hp.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & HROD0 & Hsp1 & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2) & _).
  pose proof HBLK as (Hab & Hins & HTAB & HWS & HST & HREL & _ & _ & _ & Ht0 & _).
  pose proof HTAB as (Hint & _ & HTl & _).
  destruct (gsw_bounds B MT cx fp k ly3 S3 W3 memT mdT t s HB HJ HFR Hint Hins LAWS)
    as (Hal & Hsp0 & H47' & Hsp1b & Hsp32 & HF0 & HFc & HF32 & Ht4 & Htc & Hs0 & Hsc & HPB).
  pose proof HJ as (HAR3 & _).
  pose proof (@alloc_ceiling_value rc) as HAC. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  rewrite IMG_LO_B_val in HBLO.
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hm.
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in *.
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
    rewrite Hsp1. replace (32 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx))
      with ((2 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx) / 16) * 16) by lia.
    apply Z_mod_mult. }
  (* the frame's two tables: lengths, and their place against the image, the stack and each other *)
  assert (Hfin : In (GE_CID, fp) (YG01.frames S3)) by (rewrite HFR; left; reflexivity).
  pose proof HJ as (_ & Hly & _).
  assert (EF : frame_addr ly3 GE_CID fp = gF cx fp).
  { unfold gF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  (* Image B's own image range, through YC1h.v:131 frm_off_imgB (image A's frm_off_imgP carries image A's
     top 0x5fa000; on the integration tree off_img is lib/B/YCbq.v's, over image B's top 0x5fb000; the walk does
     not depend on which). *)
  pose proof (frm_off_imgB B ly3 S3 W3 memT mdT GE_CID fp HAR3 Hfin) as HFo.
  rewrite EF in HFo. change (fs_frame_bytes GE_CID) with 1024 in HFo.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HFo.
  destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memT mdT GE_CID fp HAR3 Hfin) as (_ & _ & HFapp).
  rewrite EF in HFapp. change (fs_frame_bytes GE_CID) with 1024 in HFapp.
  assert (HW0 : 0 <= gF cx fp + GO_WAS) by (unfold GO_WAS; lia).
  assert (HV0 : 0 <= gF cx fp + GO_SET) by (unfold GO_SET; lia).
  assert (HWam : amem_range (gF cx fp + GO_WAS) 144)
    by (apply (amem_range_sub_app (gF cx fp) 1024); first [exact HFapp | lia | unfold GO_WAS; lia]).
  assert (HVam : amem_range (gF cx fp + GO_SET) 144)
    by (apply (amem_range_sub_app (gF cx fp) 1024); first [exact HFapp | lia | unfold GO_SET; lia]).
  assert (HWimg : gF cx fp + GO_WAS + 144 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp + GO_WAS)
    by (rewrite IMG_LO_B_val, IMG_TOP_B_val; unfold GO_WAS; lia).
  assert (HVimg : gF cx fp + GO_SET + 144 <= IMG_LO_B \/ IMG_TOP_B <= gF cx fp + GO_SET)
    by (rewrite IMG_LO_B_val, IMG_TOP_B_val; unfold GO_SET; lia).
  (* GO_WAS + 144 = 176 <= 240 = GO_SET *)
  assert (HWV : gF cx fp + GO_WAS + 144 <= gF cx fp + GO_SET \/ gF cx fp + GO_SET + 144 <= gF cx fp + GO_WAS)
    by (left; unfold GO_WAS, GO_SET; lia).
  (* the frame lies below the callee's stack window: F + 1024 <= alloc_ceiling <= s1 - ESTACK *)
  assert (HWsp : spZ regsT <= gF cx fp + GO_WAS \/ gF cx fp + GO_WAS + 144 <= spZ regsT - STK_want_of)
    by (right; rewrite USP; unfold STK_want_of, ESTACK, GO_WAS; lia).
  assert (HVsp : spZ regsT <= gF cx fp + GO_SET \/ gF cx fp + GO_SET + 144 <= spZ regsT - STK_want_of)
    by (right; rewrite USP; unfold STK_want_of, ESTACK, GO_SET; lia).
  assert (HWsh : range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (gF cx fp + GO_WAS + (3 * c + p)) 1).
  { apply (gsw_arr_usable cx fp W3 memT GO_WAS (3 * c + p) HSH HF32 (or_introl eq_refl)). lia. }
  assert (HVsh : range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (gF cx fp + GO_SET + (3 * c + p)) 1).
  { apply (gsw_arr_usable cx fp W3 memT GO_SET (3 * c + p) HSH HF32 (or_intror eq_refl)). lia. }
  unfold gfarr in HWS, HST. cbn [ms_mem mkst] in HWS, HST.
  rewrite pa_sigma_want_of.
  eapply SRr_mono.
  { apply (cl_callS B LAWS W3 regsT memT _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 mdT k STK_want_of [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => ly' = ly3 /\ S' = S3 /\ W' = W3 /\
         getr regs' 10 = w64 (if tb (ws_end (c_pl cx)) (3 * c + p) =? 0 then dflt p
                              else tb (st_end (c_pl cx)) (3 * c + p))) HJ).
    - rewrite USP. unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - exact Ho.
    - unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - unfold STK_want_of, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - unfold STK_want_of, ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; assumption.
    - rewrite R1, unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      apply (gsw_achain B MT cx fp k ly3 S3 W3 memT mdT regsT HB HJ R8 H8 H16). lia.
    - intros HPRE'.
      exact (WOF ly3 S3 W3 regsT memT mdT (gch cx) (gF cx fp + GO_WAS) (gF cx fp + GO_SET) c p
        (ws_end (c_pl cx)) (st_end (c_pl cx)) HPRE' R10 R11 R12 R13 Hc Hp
        (length_ws_end (c_pl cx)) HWS (length_st_end (c_pl cx)) HST
        HW0 HWam HWimg HV0 HVam HVimg HWV HWsp HVsp HWsh HVsh).
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP & (-> & -> & -> & H10)).
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [rewrite R1; reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact HP|].
  split.
  { replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJ1 by lia.
    apply (vkeep_callee B MT cx fp k ly3 S3 W3 memT mdT t s STK_want_of ly3 S3 W3 mem2 md2 0 HB HJ HFR Hab eq_refl);
      [unfold STK_want_of, ESTACK; lia | exact LAWS | exact HJ1]. }
  rewrite H10. f_equal. symmetry. apply want_eff; [exact Hc | lia | exact Hp | exact HREL].
Qed.

(* One call of check_groupa(row, ch, p, t, eff T t ch p) from the realigned stack
   pointer, on a row the sweep holds: the journal grows, the blocks and frames stay,
   the callee-saved registers are kept, and so is every byte the cuts name. *)
Lemma gsw_cga : AR_laws SEGS B -> tb_check_groupa_spec B ->
  forall cx fp k ly3 S3 W3 (regsT : bvmap 5 word) memT mdT ret t s row ch p,
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 memT mdT k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  gsw_blk B cx fp ly3 S3 W3 (mkst regsT (Z_to_bv 64 0) memT (seg_rom SEGS)) t s ->
  getr regsT 2 = w64 (c_sp1 cx) -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 8 = w64 (spZ (c_regs cx)) ->
  getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) memT) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  getr regsT 10 = w64 row -> getr regsT 11 = w64 ch -> getr regsT 12 = w64 p -> getr regsT 13 = w64 t ->
  getr regsT 14 = w64 (eff (T_end (c_pl cx)) t ch p) ->
  0 <= ch < 48 -> 0 <= p < 3 -> s <= row -> row + 34 <= s + sw_mbytes (c_pl cx) ->
  garr8 SEGS (mrestrict (w_H W3) memT) row (GAz ch p (eff (T_end (c_pl cx)) t ch p)) ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS_check_groupa)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
         [(GE_CID, fp)] ly2 S2 W2 mem2 md2 k /\
       YG01.frames S2 = YG01.frames S3 /\ ablocks B ly2 S2 = ablocks B ly3 S3 /\ (exists f, S2 = set_fs f S3) /\
       aregs_preserved regsT regs2 /\ vkeep (gsw_out cx fp t s) W3 memT W2 mem2).
Proof.
  intros LAWS TCG cx fp k ly3 S3 W3 regsT memT mdT ret t s row ch p HB HJ HFR HBLK R2 R3 R4 R8 R1 Hret Hret2 H8 H16
    R10 R11 R12 R13 R14 Rch Rp Hr1 Hr2 HROW.
  destruct (gsw_base_facts B MT cx HB) as (HPRE & HROD0 & Hsp1 & _).
  pose proof HPRE as (_ & _ & _ & Hgp & Htp & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2) & _).
  pose proof HBLK as (Hab & Hins & HTAB & _).
  pose proof HTAB as (Hint & Ht0 & HTl & _).
  pose proof HJ as (_ & Hly & _).
  assert (Etop : ly_top ly3 = ly_top (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
  pose proof (@alloc_ceiling_value rc) as HAC. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  rewrite IMG_LO_B_val in HBLO.
  pose proof (Z.div_mod (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -288) 32 ltac:(lia)) as Hm.
  unfold GE_STK, STK_LLVMFuzzerTestOneInput in *.
  assert (USP : spZ regsT = c_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
  assert (Ho : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
    rewrite Hsp1. replace (32 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx))
      with ((2 * ((spZ (c_regs cx) + -288) / 32) - spZ (c_regs cx) / 16) * 16) by lia.
    apply Z_mod_mult. }
  assert (HTCG : STK_check_groupa = 288 + 2 * ESTACK) by reflexivity.
  rewrite pa_sigma_check_groupa.
  eapply SRr_mono.
  { apply (cl_callS B LAWS W3 regsT memT _ GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(GE_CID, fp)] ly3 S3 mdT k STK_check_groupa [] 0 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) (gch cx)
      (fun ly' S' W' regs' mem' md' => YG01.frames S' = YG01.frames S3 /\ ablocks B ly' S' = ablocks B ly3 S3 /\
         (exists f, S' = set_fs f S3)) HJ).
    - rewrite USP. unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - exact Ho.
    - unfold GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - rewrite HTCG. unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - rewrite HTCG. unfold ESTACK, GE_STK, STK_LLVMFuzzerTestOneInput. lia.
    - rewrite R3. exact Hgp.
    - rewrite R4. exact Htp.
    - reflexivity.
    - rewrite R1. apply ret_ok_codeptr_v; assumption.
    - rewrite R1, unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      apply (gsw_achain B MT cx fp k ly3 S3 W3 memT mdT regsT HB HJ R8 H8 H16). lia.
    - intros HPRE'.
      apply (TCG ly3 S3 W3 regsT memT mdT (gch cx) row ch p t s (sw_mbytes (c_pl cx)) (T_end (c_pl cx)) HPRE').
      + rewrite HFR. cbn. lia.
      + rewrite USP, Etop. lia.
      + exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD0).
      + exact R10.
      + exact R11.
      + exact R12.
      + exact R13.
      + exact R14.
      + lia.
      + exact Rp.
      + exact Hint.
      + exact HTl.
      + exact (gtab_obj cx ly3 S3 W3 _ t _ HTAB).
      + exact Hins.
      + exact Hr1.
      + exact Hr2.
      + exact HROW.
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ1 & HP & (Hfr2 & Hab2 & Hfs)).
  exists ly2, S2, regs2, mem2, md2.
  split; [rewrite R1; reflexivity|]. split; [rewrite Z.add_0_r in HJ2; exact HJ2|].
  split; [exact Hfr2|]. split; [exact Hab2|]. split; [exact Hfs|]. split; [exact HP|].
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJ1 by lia.
  apply (vkeep_callee B MT cx fp k ly3 S3 W3 memT mdT t s STK_check_groupa ly2 S2 W2 mem2 md2 0 HB HJ HFR Hab Hab2);
    [rewrite HTCG; unfold ESTACK; lia | exact LAWS | exact HJ1].
Qed.

End c.
End b.
End a.
