(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 1121 of its 1202 lines of code are new or changed and 433 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): segment X2 of the walk of check_reject_clean_starved against
   the kit's text tcheck_reject_clean_starved_specX, row X2_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md; lane CrsX2H2,
   a working branch). It proves the row's closing lemma over the FROZEN B' kit lib/B/Prog/CrsKitBp.v
   (a working branch fb124cd27931):
     crs_seg_X2_B : HI_head -> HT_fuzz_alloc_fail -> HT_fuzz_alloc_ran_out -> HK -> HB_took -> HW_exact ->
                    crs_from_F_B .. -> crs_from_Z_B .. -> crs_from_X2_B ..
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup;
   CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its released rows
   were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). This file is one SEGMENT of that walk (kind: segment lemma); it is new.
   DONOR (rule 24, reuse): this lane's A' file lib/A/Prog/CrsSeg_X2.v (a working branch 7fea2e4fd8c0, blob
   526938d54fd8): the same transport lemmas, call rules and closing proof, with the kit's `_B` names (this file's own
   names carry `_B` / `cxb_` / `cjb_`), every class instance passed by name (prh_img_B / PI_prog_B; image A's instances
   are also loaded, through S1ImgB) and every number re-read at B'. The segment environment of the listing engine
   (TE .. ts_reg_kept_c) is lib/A/Prog/PRW_WalkEnv.v at B', Required from lib/B/Prog/PRW_WalkEnvB.v.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1);
     unstripped twin .../bound-fix/9e1283d1/unstripped/fuzz_preset/fuzz_preset.asan-ubsan sha256 c90d4fa54d43160b
     (the segment read by capstone, the internal file elfdis.py --addr 0x822f0 0xd0).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3).
     Entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved). X2 is slots 811 .. 826.
   - the kit's texts at the #102 kit tip, by path: tfuzz_alloc_fail_specX /
     tfuzz_alloc_ran_out_specX (lib/A/PRH_FnAlloc.v blob 740f4d11d144), prh_ledger .. ran most own and
     prh_ledger_own, fpre ending with frm_zero (lib/A/PRH_Base.v blob fdb45545469b), PRH_Supply.
     prhWriter_pjw_evs_w_starved, all at prh_img_B / PI_prog_B. lib/B/Prog/S1ImgB.v (pst_not_ro_B).
   - pj_write through the shared B' interim crs_wexact_B (lib/B/Prog/CrsWexBp.v, base fb124cd27931): the kit's
     tpj_write_specX (lib/A/PRH_FnWriter.v blob 2b497bc72172) at crcs's four calls, a FLOAT-form text (fpostFm), so the
     call is YCbqGcall.aj_call_xF_sp and the walk goes on at pj_write's float state (crs_ws_fx_B); its premise
     cnt < 2 ^ 62 from the boundary's crs_core_B.
   THE SEGMENT (offsets from the entry; B' listing, capstone over the twin):
     +664 bne a0, s7     a0 = the count after the whole pretty write, s7 = the count before it: a0 = s7 is refuted
                         (the write made N1 >= 1 calls, PRW_CrsModel.crs_wN_pos), so the remu arm runs
     +676 sub, +680 remu a0 = h % N1 = ck_pick tb N1 (a2 = h, cHash_B)
     +684 jal fuzz_alloc_fail          (the kit text, HT_fuzz_alloc_fail)
     +688 li a1, 1; +692 mv a0, s3; +696 jal pj_write (doc, 1) (HW_exact's X2 call; its entry run events
                         crs_ev_ws_B C true by crs_x2_run_B, from crs_pre_B's prh_run_at and PRH_Supply, at HI_head)
     +700 mv s7, a0; +704 li a0, -1; +708 jal fuzz_alloc_fail
     +712 lbu a0, -1340(s8); +716 bnez a0 (CHECK #3's OWN arm -> F): refuted, the cell reads the boundary ledger's own
                         argument 0 (prh_ledger_own; CRS_RO_B + CRS_OFF_OWN_B = pi_g_own_ran_out)
     +720 jal fuzz_alloc_ran_out; +724 beqz a0: g_ran_out = 0 -> Z (+992), else F (+728) with ran = 1, s7 = 0 and
                         Lam / the blocks back (pj_write's failed arm)
   PREMISES of crs_seg_X2_B, in the A' order: HI_head (cf_head = PresetReqAt.HEAD, the instance fact; witness at
   CfParams_preset by vm_compute in the composition), HT_fuzz_alloc_fail, HT_fuzz_alloc_ran_out (the kit's texts exactly, at
   prh_img_B / PI_prog_B, any float state fx'), HK : CrsKeep_B B ARx (the kit's transport record, proved once in the
   composition), HB_took : cb_took C <= 2 ^ 28 (CrsBoundBp.crs_took_le_B), HW_exact (crs_wexact_B, the B' writer
   interim; CrsBridgeBp discharges it from tpj_write_specX), then crs_from_F_B and crs_from_Z_B. No named hole.
   Numerals: offsets +664 .. +992 (LENGTH: 4 * slot); 530124 (ADDRESS: the B' text base pa_val A_TEXT, by vm_compute,
   in one `assert .. by vm_compute` only); 3268 / 3280 / 3292 / 3304 / 3308 / 3572 (LENGTH: CRS_PC0_B = 2580 plus the
   return sites +688 / +700 / +712 / +724, F +728 and Z +992, each checked by vm_compute where it meets a kit name);
   6152892 (ADDRESS: CRS_RO_B by vm_compute, one assert); -1340 / 1 / -1 (the listing's immediates); 144 / 128 / 120 /
   112 (LENGTH: the realigned frame and the saved slots); 2 ^ 20 .. 2 ^ 64 (LENGTH / WORD bounds). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp RttModel WriterApp WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB CrsKitBp CrsWexBp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PRW_WalkEnvB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* the segment environment TE and its lemmas (lib/A/Prog/PRW_WalkEnv.v's TE part at B'): lib/B/Prog/PRW_WalkEnvB.v,
   Required above; this file's own copy is gone (one copy for the walk) *)

(* the registers a run left alone, at any float state (the walk runs at the boundary's fxk) *)
Section rs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
Lemma cxb_regsat_run : forall r0 rgc more ss (H : word -> bool) ms l,
  st_ok_pi SEGS VAL (TE r0 rgc more) ss (restrict H ms) ->
  Forall (fun p => sr_get (ss_regs ss) (fst p) = SOff (32 + Z.to_nat (bv_unsigned (fst p))) 0) l ->
  crs_regsat_B rgc l -> crs_regsat_B (ms_regs ms) l.
Proof.
intros r0 rgc more ss H ms l HS Hk HR. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros x Hx.
rewrite (ts_reg_kept r0 rgc more ss H ms (fst x) (fst x) HS (Hk x Hx)). exact (HR x Hx).
Qed.
Lemma cxb_regsat_run_c : forall r0 rgc more ss (H : word -> bool) ms l,
  st_ok SEGS (TE r0 rgc more) ss (restrict H ms) ->
  Forall (fun p => sr_get (ss_regs ss) (fst p) = SOff (32 + Z.to_nat (bv_unsigned (fst p))) 0) l ->
  crs_regsat_B rgc l -> crs_regsat_B (ms_regs ms) l.
Proof.
intros r0 rgc more ss H ms l HS Hk HR. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros x Hx.
rewrite (ts_reg_kept_c r0 rgc more ss H ms (fst x) (fst x) HS (Hk x Hx)). exact (HR x Hx).
Qed.
End rs.

(* a PLAIN callee text (its post apost_base_x, its journal at wle) in a caller whose walk runs at a world relation R
   that contains wle: YA0nH.SRr_SRrG on the run and YCbqG.apost_base_x_R_lift on the post, in the form the R call rule
   YCbqGcall.aj_call_x_spR takes as its callee premise *)
Section lift. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variables (segs : list Segment) (B : asyms) (PST : list (Z * Z))
  (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
  (R : world segs -> world segs -> Prop).
Hypothesis Rw : forall W W', wle W W' -> R W W'.
Lemma cxb_lift_x : forall W c STK FP regs ly S Hp W0 mem md Q,
  SRr segs W c (apost_base_x segs B PST ARx STK FP regs ly S Hp W0 mem md Q) ->
  SRrG segs R W c (apost_base_xR segs B PST ARx R STK FP regs ly S Hp W0 mem md Q).
Proof.
intros W c STK FP regs ly S Hp W0 mem md Q H.
apply (SRrG_mono segs R _ _ _ _ (SRr_SRrG segs R Rw _ _ _ H)).
intros W' c' _ HP. exact (apost_base_x_R_lift segs B PST ARx R Rw _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.
End lift.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
(* the same journal over a world relation R (YCbqG.v ajournal_xR): a cut after a free or a realloc carries it at
   R := wle' SEGS RZ_cf, a cut before one at R := wle (where it is AJ) *)
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).

(* ======================================================================================================== *)
(* ---- TRANSPORT: the boundary facts across a stretch of the walk (a run that writes nothing, or a callee whose
   journal is HJ1). Each lemma takes the byte agreement it needs (aview equal on a named set) and the state's
   ARx (from the journal from entry) for the presence facts. ---- *)

Lemma cxb_rdword_ext : forall (r1 r2 : reader) a,
  (forall j, 0 <= j < 8 -> r1 (a + j) = r2 (a + j)) -> rdword r1 a = rdword r2 a.
Proof.
intros r1 r2 a H. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite !H by lia. reflexivity.
Qed.

(* the frame: frames unchanged, the flag word kept, the bytes present by the frames law at the new state *)
Lemma crs_frame_kv_B : forall R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 ly4 S4 Hp4 W4 mem4 md4 k4,
  crs_pre_B B ARx CTX0 C ->
  crs_JR_B B ARx R C ly3 S3 Hp3 W3 mem3 md3 k3 -> crs_JR_B B ARx R C ly4 S4 Hp4 W4 mem4 md4 k4 ->
  crs_frame_B C ly3 S3 W3 mem3 -> frames S4 = frames S3 ->
  (forall a, cF_B C + 120 <= a < cF_B C + 128 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  crs_frame_B C ly4 S4 W4 mem4.
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 ly4 S4 Hp4 W4 mem4 md4 k4 HP HJ3 HJ4 (Hfr & Hfl & Hpr) HfS Hkv.
assert (Eb : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 HP HJ3) as (Ef3 & Efl3).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly4 S4 Hp4 W4 mem4 md4 k4 HP HJ4) as (Ef4 & Efl4).
split; [rewrite HfS; exact Hfr|]. split.
- rewrite Efl4, <- Efl3, <- Hfl. rewrite Eb. apply cxb_rdword_ext. intros j Hj. apply Hkv. lia.
- intros a Ha. pose proof HJ4 as (HAR4 & _).
  assert (Hin : In (CRS_CID_B, cb_fpos C) (frames S4)) by (rewrite HfS, Hfr; left; reflexivity).
  destruct (alx_frames _ _ _ LAWS ly4 S4 Hp4 W4 mem4 md4 CRS_CID_B (cb_fpos C) HAR4 Hin) as (_ & _ & Fb & _).
  rewrite Ef4 in Fb. exact (proj1 (Fb a Ha)).
Qed.

(* the thirteen saved words, at or above s0 - 104 *)
Lemma crs_saved_kv_B : forall C W3 mem3 W4 mem4,
  crs_saved_B C W3 mem3 ->
  (forall a, spZ (cb_regs C) - 104 <= a < spZ (cb_regs C) ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  crs_saved_B C W4 mem4.
Proof.
intros C W3 mem3 W4 mem4 H Hkv. unfold crs_saved_B in *. rewrite Forall_forall in *.
intros x Hx. rewrite <- (H x Hx).
assert (Ho : 24 <= fst x <= 120).
{ unfold CRS_SAVED_B in Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [cbn [fst]; lia|]). destruct Hx. }
apply cxb_rdword_ext. intros j Hj. apply Hkv. lia.
Qed.

(* the local's shadow: its bytes lie in the frame's 16 shadow bytes (the frame is 32-aligned) *)
Lemma crs_slot_kv_B : forall C W3 mem3 W4 mem4,
  crs_slot_B C W3 mem3 -> cF_B C mod 32 = 0 -> 0 <= cF_B C ->
  (forall a, shadow_addr (cF_B C) <= a < shadow_addr (cF_B C) + 16 ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  crs_slot_B C W4 mem4.
Proof.
intros C W3 mem3 W4 mem4 (Hra & Hhv) H32 H0 Hkv. unfold cOut_B, CRS_OFF_DOC_B in *.
assert (Hs8 : SHADOW_OFF = 8 * 268431360) by (vm_compute; reflexivity).
assert (Hc : cF_B C = 32 * (cF_B C / 32)) by (pose proof (Z.div_mod (cF_B C) 32 ltac:(lia)); lia).
assert (Hc8 : cF_B C / 8 = 4 * (cF_B C / 32)).
{ rewrite Hc at 1. replace (32 * (cF_B C / 32)) with ((4 * (cF_B C / 32)) * 8) by lia. apply Z.div_mul. lia. }
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite Hkv; [exact Hsv|]. unfold shadow_of_addr, shadow_addr.
  unfold cOut_B, CRS_OFF_DOC_B in Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
- intros sv Hsv. rewrite Hkv; [exact (Hhv sv Hsv)|]. unfold shadow_addr, cOut_B, CRS_OFF_DOC_B in *.
  pose proof (Z.div_mod (cF_B C + 32) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (cF_B C + 32) 8 ltac:(lia)).
  pose proof (Z.div_mod (cF_B C + 32 + 56 - 1) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (cF_B C + 32 + 56 - 1) 8 ltac:(lia)).
  set (A1 := SHADOW_OFF + (cF_B C + 32) / 8) in *. set (A2 := SHADOW_OFF + (cF_B C + 32 + 56 - 1) / 8) in *.
  pose proof (Z.div_mod A1 8 ltac:(lia)). pose proof (Z.mod_pos_bound A1 8 ltac:(lia)).
  pose proof (Z.div_mod A2 8 ltac:(lia)). pose proof (Z.mod_pos_bound A2 8 ltac:(lia)).
  unfold A1, A2 in *. lia.
Qed.

(* the read-only view *)
Lemma crs_rod_kv_B : forall (W3 : world SEGS) mem3 (W4 : world SEGS) mem4,
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W3) mem3) ->
  (forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W4) mem4).
Proof. intros W3 mem3 W4 mem4 H Hkv a Hro Ho He. rewrite (Hkv a Hro Ho He). exact (H a Hro Ho He). Qed.

(* bytes agreeing in the view give the same garr8 (S10Env.v ts_garr_av, h-hpreset-7 walk-S10 88b4aea723f) *)
Lemma cxb_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r in *.
rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). pose proof (V 0%nat Hi) as V0. cbn [Z.of_nat] in V0.
rewrite Z.add_0_r in V0. exact V0.
Qed.

Lemma cxb_ra_kv : forall (rd rd' : reader) p n,
  (forall a, rd' a = rd a) -> range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof. intros rd rd' p n E H x Hx. destruct (H x Hx) as (sv & Hs & Ho). exists sv. rewrite E. auto. Qed.

(* read-only bytes are image bytes; no PST cell is read-only *)
Lemma cxb_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
Lemma cxb_ro_not_pst : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) PST.
Proof. intros a Hro Hp. exact (pst_not_ro_B a Hp Hro). Qed.

(* ---- what a callee's journal HJ1 (FP = [], own = []) keeps, by the sets the boundary facts read ---- *)
Section callee.
Variable R : world SEGS -> world SEGS -> Prop.
Variables (STK1 sp1 : Z) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world SEGS) (mem3 : word -> option byte)
  (md3 : Model) (ly4 : alayout) (S4 : astate) (Hp4 : list Z) (W4 : world SEGS) (mem4 : word -> option byte)
  (md4 : Model) (k1 : Z).
Hypothesis HJ1 : AJR R STK1 sp1 [] ly3 S3 Hp3 W3 mem3 md3 [] ly4 S4 Hp4 W4 mem4 md4 k1.

Lemma cjb_above : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STK1 <= a < sp1) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a.
Proof. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

Lemma cjb_frames : forall cid pos a, In (cid, pos) (frames S3) ->
  (in_zr a (frame_rng ly3 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly3 cid pos), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a.
Proof.
intros cid pos a Hin Ha. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _).
exact (G cid pos a Hin Ha (inFP_nil a)).
Qed.

Lemma cjb_ro : forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a.
Proof.
intros a Hro Ho He. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G & _).
exact (G a (cxb_ro_img a Hro) Ho He (cxb_ro_not_pst a Hro) (fp_spares_closed [] a sink_closed_nil)).
Qed.

Lemma cjb_block : forall p n a, In (p, n) (ablocks B ly3 S3) -> In (p, n) (ablocks B ly4 S4) ->
  p <= a < p + req_size n -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a.
Proof.
intros p n a H3 H4 Ha. pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _).
replace a with (p + (a - p)) by lia. apply (G p n (a - p) H3 H4); [lia | apply inFP_nil].
Qed.

Lemma cjb_frames_eq : frames S4 = frames S3.
Proof. pose proof HJ1 as (_ & _ & _ & _ & _ & G & _). exact G. Qed.
End callee.

(* ---- the input bytes, the tree and the doc's home across a stretch ---- *)
Lemma crs_dat_kv_B : CrsKeep_B B ARx ->
  forall C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4
    most4 own4,
  crs_dat_B B C ly3 S3 Hp3 W3 mem3 Lam3 ->
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ->
  ARx ly4 S4 Hp4 W4 mem4 md4 -> LEDGER ly4 S4 Hp4 W4 mem4 Lam4 peak4 cnt4 fail4 ran4 most4 own4 ->
  Permutation Lam4 Lam3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  0 <= cb_data C -> cb_data C + cSize_B C <= YM05.alloc_ceiling ->
  (forall a, cb_data C <= a < cb_data C + cSize_B C -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  crs_dat_B B C ly4 S4 Hp4 W4 mem4 Lam4.
Proof.
intros HK C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4
  ran4 most4 own4 (Hby & Hhm & _ & _) HL3 HAR4 HL4 HpL Hpb Hd0 Hdc Hkv.
assert (Hhm4 : PRH_FnReader.prhReader_home (PA := PA) B ly4 S4 Hp4 Lam4 (cb_data C) (cSize_B C))
  by exact (kpb_home_move B ARx HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL3 HL4 HpL Hpb Hhm).
split; [|split; [exact Hhm4|]].
- unfold PRH_Base.bytes_at in *. apply (cxb_garr_av (w_H W3) (w_H W4) mem3 mem4 _ _); [|exact Hby].
  intros j Hj. apply Hkv. unfold cSize_B. lia.
- destruct (Z_lt_le_dec 0 (cSize_B C)) as [Hn|Hn].
  + destruct (kpb_home_sh B ARx HK ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4 most4 own4 (cb_data C) (cSize_B C)
      HAR4 HL4 Hhm4 Hn Hd0 Hdc) as (Hra & Hhv).
    split; [exact Hra | intros _; exact Hhv].
  + split; [intros x Hx; lia | intros Hn'; lia].
Qed.

(* a harness block of the ledger: its bytes are present, and inside its allocator block *)
Lemma cxb_hblock_present : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> a <= x < a + k ->
  apresent (w_H W) mem x /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\
  a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HL Hin Hx.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HF.
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
pose proof (@cf_head_nonneg cp) as Hc0. assert (Hkc : 0 <= k + cf_head) by lia.
pose proof (YCbq.req_size_pos (k + cf_head) Hkc) as (_ & Hrq).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hb) as (_ & _ & _ & _ & Hpr & _).
split; [apply (Hpr x); lia|]. split; [exact Hb | lia].
Qed.

(* the tree representation is monotone in its block predicate (the lblk of PRH_Reader.v pj_nodeR: a larger live
   list keeps every block the tree's blocks were) *)
Lemma cxb_cstr_lblk : forall m (lblk lblk' : Z -> Z -> Prop) a k s,
  (forall a k, lblk a k -> lblk' a k) -> pj_cstrR SEGS m lblk a k s -> pj_cstrR SEGS m lblk' a k s.
Proof. intros m lblk lblk' a k s Hl (H1 & H2 & H3). split; [exact (Hl _ _ H1)|]. split; assumption. Qed.

Lemma cxb_mems_lblk : forall m (lblk lblk' : Z -> Z -> Prop) (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall a k, lblk a k -> lblk' a k) ->
  pj_memsR SEGS m lblk P a ka l D ->
  (forall i nm u D1, nth_error l i = Some (nm, u) -> P (a + 56 * Z.of_nat i) u D1 -> P' (a + 56 * Z.of_nat i) u D1) ->
  pj_memsR SEGS m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D Hl H HP; cbn [pj_memsR] in H |- *; [exact H|].
destruct H as (x & k & D1 & D2 & -> & Hx & Hc & H1 & H2). exists x, k, D1, D2. split; [reflexivity|].
split; [exact Hx|]. split; [exact (cxb_cstr_lblk _ _ _ _ _ _ Hl Hc)|].
split.
- specialize (HP 0%nat nm u D1 eq_refl). replace (a + 56 * Z.of_nat 0) with a in HP by lia. exact (HP H1).
- apply (IH (a + 56) (ka + 8) D2 Hl H2). intros i nm' u' D1' Hi HPi.
  specialize (HP (S i) nm' u' D1' Hi). replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HP by lia.
  exact (HP HPi).
Qed.

Lemma cxb_node_lblk : forall t m (lblk lblk' : Z -> Z -> Prop) p D,
  (forall a k, lblk a k -> lblk' a k) -> pj_nodeR SEGS m lblk p t D -> pj_nodeR SEGS m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m lblk lblk' p D Hl H; cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED). repeat (split; [assumption|]).
  exists k. split; [exact (cxb_cstr_lblk _ _ _ _ _ _ Hl Hc) | exact ED].
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED). repeat (split; [assumption|]).
  exists k. split; [exact (cxb_cstr_lblk _ _ _ _ _ _ Hl Hc) | exact ED].
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hk)]; [left; exact Hcap | right; split; [exact Hc0 | exact (Hl _ _ Hk)]]|].
  exists Di. split; [exact ED|].
  apply (pj_itemsR_mono (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') items kids Di Hi).
  intros i u D1 Hil _ HP. rewrite Forall_forall in IH.
  exact (IH u (nth_error_In items i Hil) m lblk lblk' _ D1 Hl HP).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split; [destruct Hcap as [Hcap | (Hc0 & Hk1 & Hk2)];
    [left; exact Hcap | right; split; [exact Hc0 | split; [exact (Hl _ _ Hk1) | exact (Hl _ _ Hk2)]]]|].
  exists Di. split; [exact ED|].
  apply (cxb_mems_lblk m lblk lblk' (pj_nodeR SEGS m lblk) (pj_nodeR SEGS m lblk') members kids keys Di Hl Hi).
  intros i nm u D1 Hil HP. rewrite Forall_forall in IH. specialize (IH (nm, u) (nth_error_In members i Hil)).
  cbn [snd] in IH. exact (IH m lblk lblk' _ D1 Hl HP).
Qed.

Lemma crs_tree_kv_B : CrsKeep_B B ARx ->
  forall C ly3 S3 Lam3 W3 mem3 ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4 most4 own4,
  crs_tree_B C ly3 S3 Lam3 W3 mem3 ->
  ARx ly4 S4 Hp4 W4 mem4 md4 -> LEDGER ly4 S4 Hp4 W4 mem4 Lam4 peak4 cnt4 fail4 ran4 most4 own4 ->
  (forall x, In x Lam3 -> In x Lam4) ->
  (cb_doc C <> 0 -> ck_obj_home (PA := PA) ly4 S4 W4 mem4 (cb_doc C)) ->
  (cb_doc C <> 0 -> forall a, pj_footR (cb_doc C) (cb_D C) a ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  crs_tree_B C ly4 S4 Lam4 W4 mem4.
Proof.
intros HK C ly3 S3 Lam3 W3 mem3 ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4 most4 own4 HT HAR4 HL4 Hsub Hobj Hkv Hd.
destruct (HT Hd) as (Hn & HD & _ & _). pose proof (Hobj Hd) as Hobj4.
assert (HD4 : forall bk, In bk (cb_D C) -> In bk Lam4) by (intros bk Hb; apply Hsub, HD, Hb).
split; [|split; [exact HD4 | split]].
- apply (pj_nodeR_frame SEGS (cb_t C) _ _ _ _ _ (cxb_node_lblk (cb_t C) _ (prh_lin Lam3) (prh_lin Lam4) _ _
    (fun a k H => Hsub (a, k) H) Hn)). intros x Hx. split.
  + apply (mbyte_of_aview SEGS). exact (Hkv Hd x Hx).
  + intros _. apply (apresent_writable SEGS). destruct Hx as [Hx | ((a, kk) & Hb & Hx)].
    * destruct Hobj4 as (_ & (cid & pos & Hin & Hlo & Hhi) & _).
      destruct (alx_frames _ _ _ LAWS ly4 S4 Hp4 W4 mem4 md4 cid pos HAR4 Hin) as (_ & _ & Fb & _).
      apply (Fb x). lia.
    * unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      exact (proj1 (cxb_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ a kk x HAR4 HL4 (HD4 _ Hb) Hx)).
- exact (kpb_tree_vis B ARx HK ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4 most4 own4 (cb_D C) HAR4 HL4 HD4).
- exact Hobj4.
Qed.

(* ---- THE WALK STATE inside a segment (between two boundaries): the boundary facts, the ledger at any g_fail_at,
   Lam and the blocks back, the room, the position, the input and the tree ---- *)
Definition crs_ws_B (CTX0 : list (list Z)) (C : crsC_B) (fxk : YK11.FPState) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k sp2 : Z)
  (Lam : list (Z * Z)) (peak cnt fail ran : Z) : Prop :=
  crs_baseR_B (fx := fx) B ARx (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly S Hp W regs mem md k sp2 /\
  LEDGER ly S Hp W mem Lam peak cnt fail ran (cb_most C) 0 /\
  crs_perm_B B C ly S Lam /\ cb_peak C <= peak /\ room_live_cf S /\
  crs_dat_B B C ly S Hp W mem Lam /\ crs_tree_B C ly S Lam W mem.

Lemma crs_ws_move_B : CrsKeep_B B ARx ->
  forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3
         ly4 S4 Hp4 W4 regs4 mem4 md4 k4 Lam4 peak4 cnt4 fail4 ran4,
  crs_ws_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3 ->
  crs_JR_B B ARx (wle' SEGS YGcfRehidePost.RZ_cf) C ly4 S4 Hp4 W4 mem4 md4 k4 ->
  frames S4 = frames S3 ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem4) ->
  getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  (forall a, cF_B C + 120 <= a < cF_B C + 128 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, spZ (cb_regs C) - 104 <= a < spZ (cb_regs C) ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, shadow_addr (cF_B C) <= a < shadow_addr (cF_B C) + 16 ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, cb_data C <= a < cb_data C + cSize_B C -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (cb_doc C <> 0 -> forall a, pj_footR (cb_doc C) (cb_D C) a ->
     aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) mem3 a) ->
  (cb_doc C <> 0 -> ck_obj_home (PA := PA) ly4 S4 W4 mem4 (cb_doc C)) ->
  LEDGER ly4 S4 Hp4 W4 mem4 Lam4 peak4 cnt4 fail4 ran4 (cb_most C) 0 ->
  Permutation Lam4 Lam3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  peak3 <= peak4 -> room_live_cf S4 ->
  crs_ws_B CTX0 C fxk ly4 S4 Hp4 W4 regs4 mem4 md4 k4 sp2 Lam4 peak4 cnt4 fail4 ran4.
Proof.
intros HK CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3
  ly4 S4 Hp4 W4 regs4 mem4 md4 k4 Lam4 peak4 cnt4 fail4 ran4
  (HB & HL3 & (HpL & Hpb) & Hpk & _ & HD & HT) HJ4 HfS Hmn Hr3 Hr4 Kfl Ksv Ksh Kro Kdt Ktr Kobj HL4 HpL4 Hpb4
  Hpk4 Hroom4.
destruct HB as (HPRE & Hfrm & Hfk & HJ3 & HFR & HSV & HSL & HROD & HMN & Hgp & Htp & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HJ3 as (HAR3 & _). pose proof HJ4 as (HAR4 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & Hd4096 & Hdc & _) & _).
destruct (crs_cF_keepR_B B ARx LAWS (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 HPRE HJ3) as (Ef3 & _).
assert (Hin3 : In (CRS_CID_B, cb_fpos C) (frames S3)) by (destruct HFR as (Hfr & _); rewrite Hfr; left; reflexivity).
destruct (alx_frames _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR3 Hin3) as (F32 & _).
destruct (alx_sep _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 HAR3) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin3) as (F0 & _). cbn [fst snd] in F0.
rewrite Ef3 in F32, F0.
split; [|split; [exact HL4 | split; [split; [exact (Permutation_trans HpL4 HpL) | exact (Permutation_trans Hpb4 Hpb)]|]]].
- split; [exact HPRE|]. split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact HJ4|].
  split; [exact (crs_frame_kv_B (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 ly4 S4 Hp4 W4 mem4 md4 k4 HPRE HJ3 HJ4 HFR HfS Kfl)|].
  split; [exact (crs_saved_kv_B C W3 mem3 W4 mem4 HSV Ksv)|].
  split; [exact (crs_slot_kv_B C W3 mem3 W4 mem4 HSL F32 ltac:(lia) Ksh)|].
  split; [exact (crs_rod_kv_B W3 mem3 W4 mem4 HROD Kro)|].
  split; [exact (Hmn HMN)|]. split; [rewrite Hr3; exact Hgp|]. split; [rewrite Hr4; exact Htp|].
  split; [exact Hs1|]. split; [exact Hs2 | split; [exact Hs3 | exact HDPk]].
- split; [lia|]. split; [exact Hroom4|]. split.
  + exact (crs_dat_kv_B HK C ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 _ _ ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4
      fail4 ran4 _ _ HD HL3 HAR4 HL4 HpL4 Hpb4 ltac:(lia) ltac:(unfold cSize_B; lia) Kdt).
  + apply (crs_tree_kv_B HK C ly3 S3 Lam3 W3 mem3 ly4 S4 Hp4 W4 mem4 md4 Lam4 peak4 cnt4 fail4 ran4 _ _ HT HAR4 HL4).
    * intros x Hx. exact (Permutation_in _ (Permutation_sym HpL4) Hx).
    * exact Kobj.
    * exact Ktr.
Qed.

(* ---- the two producers of crs_ws_move's agreements ---- *)
(* (1) a run that wrote nothing: the raw memory is the same at every address *)
Lemma cxb_aview_ptw : forall (H : word -> bool) (m m' : word -> option byte),
  (forall x, m' x = m x) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' E a. apply aview_eq_of. unfold mrestrict. rewrite E. reflexivity. Qed.

Lemma crs_ws_run_B : CrsKeep_B B ARx ->
  forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran regs' mem' md',
  crs_ws_B CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran ->
  crs_JR_B B ARx (wle' SEGS YGcfRehidePost.RZ_cf) C ly S Hp W mem' md' k ->
  (forall x, mem' x = mem x) ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  crs_ws_B CTX0 C fxk ly S Hp W regs' mem' md' k sp2 Lam peak cnt fail ran.
Proof.
intros HK CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran regs' mem' md' HW HJ' E Hr3 Hr4.
assert (Em : mem' = mem) by (apply FunctionalExtensionality.functional_extensionality; exact E). subst mem'.
destruct HW as (HB & HW).
destruct HB as (HPRE & Hfrm & Hfk & _ & HFR & HSV & HSL & HROD & HMN & Hgp & Htp & Hs1 & Hs2 & Hs3 & HDPk).
split; [|exact HW].
split; [exact HPRE|]. split; [exact Hfrm|]. split; [exact Hfk|]. split; [exact HJ'|].
split; [exact HFR|]. split; [exact HSV|]. split; [exact HSL|]. split; [exact HROD|]. split; [exact HMN|].
split; [rewrite Hr3; exact Hgp|]. split; [rewrite Hr4; exact Htp|].
split; [exact Hs1|]. split; [exact Hs2 | split; [exact Hs3 | exact HDPk]].
Qed.

(* (2) a callee whose journal HJ1 runs from the call's state (window below sp2, FP = [], own = []) *)
Lemma crs_ws_callee_B : CrsKeep_B B ARx ->
  forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3
         STK1 ly4 S4 Hp4 W4 regs4 mem4 md4 k1 Lam4 peak4 cnt4 fail4 ran4,
  crs_ws_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3 ->
  AJR (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 [] ly3 S3 Hp3 W3 mem3 md3 [] ly4 S4 Hp4 W4 mem4 md4 k1 ->
  crs_JR_B B ARx (wle' SEGS YGcfRehidePost.RZ_cf) C ly4 S4 Hp4 W4 mem4 md4 (k3 + k1) ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem4) ->
  getr regs4 3 = getr regs3 3 -> getr regs4 4 = getr regs3 4 ->
  LEDGER ly4 S4 Hp4 W4 mem4 Lam4 peak4 cnt4 fail4 ran4 (cb_most C) 0 ->
  Permutation Lam4 Lam3 -> Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  peak3 <= peak4 -> room_live_cf S4 ->
  crs_ws_B CTX0 C fxk ly4 S4 Hp4 W4 regs4 mem4 md4 (k3 + k1) sp2 Lam4 peak4 cnt4 fail4 ran4.
Proof.
intros HK CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3
  STK1 ly4 S4 Hp4 W4 regs4 mem4 md4 k1 Lam4 peak4 cnt4 fail4 ran4 HW HJ1 HJ4 Hmn Hr3 Hr4 HL4 HpL4 Hpb4 Hpk4 Hro4.
pose proof HW as (HB & HL3 & _ & _ & _ & HD & HT).
pose proof HB as (HPRE & _ & _ & HJ3 & HFR & _ & _ & _ & _ & _ & _ & Hs1 & Hs2 & _).
pose proof HJ3 as (HAR3 & _).
pose proof HPRE as ((HAFN & _) & _).
pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (EST : 1000 <= STK_check_reject_clean_starved (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
assert (EFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity).
assert (Eb : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
destruct (crs_cF_keepR_B B ARx LAWS (wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k3 HPRE HJ3) as (Ef3 & _).
assert (Hin3 : In (CRS_CID_B, cb_fpos C) (frames S3)) by (destruct HFR as (Hfr & _); rewrite Hfr; left; reflexivity).
assert (Hbl : forall p n, In (p, n) (ablocks B ly3 S3) -> In (p, n) (ablocks B ly4 S4))
  by (intros p n H; exact (Permutation_in _ (Permutation_sym Hpb4) H)).
apply (crs_ws_move_B HK CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k3 sp2 Lam3 peak3 cnt3 fail3 ran3
  ly4 S4 Hp4 W4 regs4 mem4 md4 (k3 + k1) Lam4 peak4 cnt4 fail4 ran4 HW HJ4
  (cjb_frames_eq (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1)
  Hmn Hr3 Hr4); try assumption.
- (* the flag word *)
  intros a Ha. apply (cjb_frames (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 CRS_CID_B (cb_fpos C) a Hin3).
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Ef3, Eb. lia.
- (* the saved words: at or above alloc_ceiling, above the callee's window *)
  intros a Ha. apply (cjb_above (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1); lia.
- (* the frame's shadow *)
  intros a Ha. apply (cjb_frames (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 CRS_CID_B (cb_fpos C) a Hin3).
  right. unfold in_zr. cbn [fst snd]. rewrite Ef3, Eb. change (128 / 8) with 16. lia.
- (* the read-only view *)
  exact (cjb_ro (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1).
- (* the input bytes, by their home *)
  intros a Ha. destruct HD as (_ & Hhm & _).
  destruct Hhm as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
  + destruct (cxb_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ b m a HAR3 HL3 Hbm ltac:(lia)) as (_ & Hblk & Hrg).
    exact (cjb_block (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 _ _ a Hblk (Hbl _ _ Hblk) Hrg).
  + destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3'). exact (cjb_ro (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 a Hr1 Hr2 Hr3').
  + destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3' & _). exact (cjb_ro (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 a Hr1 Hr2 Hr3').
  + assert (Hm0 : 0 <= m) by lia. pose proof (YCbq.req_size_pos m Hm0) as (_ & Hrq).
    exact (cjb_block (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 _ _ a Hbm (Hbl _ _ Hbm) ltac:(lia)).
- (* the tree's footprint: its root in a frame live at the call, its blocks harness blocks *)
  intros Hd a Ha. destruct (HT Hd) as (_ & HDL & _ & (_ & (cid & pos & Hin & Hlo & Hhi) & _)).
  destruct Ha as [Ha | ((x & kk) & Hb & Ha)].
  + apply (cjb_frames (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 cid pos a Hin).
    left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
  + unfold pj_holdsR in Ha. cbn [fst snd] in Ha.
    destruct (cxb_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ x kk a HAR3 HL3 (HDL _ Hb) Ha) as (_ & Hblk & Hrg).
    exact (cjb_block (wle' SEGS YGcfRehidePost.RZ_cf) STK1 sp2 ly3 S3 Hp3 W3 mem3 md3 ly4 S4 Hp4 W4 mem4 md4 k1 HJ1 _ _ a Hblk (Hbl _ _ Hblk) Hrg).
- (* the doc's home, by the kit's transport record *)
  intros Hd. destruct (HT Hd) as (_ & _ & _ & Hobj).
  exact (crs_obj_keepR_B B ARx LAWS (wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR3 HJ1 Hobj).
Qed.

(* ---- a callee in the FLOAT form (fpostFm: pj_write reaches snprintf) leaves a new float state fxk': frm back to 0
   and fs0-fs11 kept (YCbqGcall.aj_call_xF_sp); the boundary facts move to it ---- *)
Lemma cxb_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Lemma crs_ws_fx_B : forall CTX0 C fxk fxk' ly S Hp W regs mem md k sp2 Lam peak cnt fail ran,
  crs_ws_B CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran ->
  frm_zero (@YK11.fp_csr fxk') -> fregs_kept_x fxk fxk' ->
  crs_ws_B CTX0 C fxk' ly S Hp W regs mem md k sp2 Lam peak cnt fail ran.
Proof.
intros CTX0 C fxk fxk' ly S Hp W regs mem md k sp2 Lam peak cnt fail ran (HB & HW) HZ HF.
destruct HB as (HPRE & _ & Hfk & HB). split; [|exact HW].
split; [exact HPRE|]. split; [exact HZ|]. split; [exact (cxb_fregs_trans _ _ _ Hfk HF) | exact HB].
Qed.

(* ---- THE CALL'S ENTRY FACTS: the frame-pointer chain (check_reject_clean_starved keeps s0 = its entry sp, with
   ra at s0 - 8 and the caller's s0 at s0 - 16, crs_saved's slots 120 / 112), and the kit's fpre extras. The chain proof is
   H2H5's crt_chain (lib/A/Prog/H5CrtS1.v, cold/h-hpreset-7-walk-H2H5 1934271f1f4) at this kit's names. ---- *)
Lemma cxb_keep_above : forall R C ly3 S3 Hp3 W3 mem3 md3 k,
  crs_JR_B B ARx R C ly3 S3 Hp3 W3 mem3 md3 k ->
  forall a, spZ (cb_regs C) <= a < 2 ^ 64 ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (cb_W C)) (cb_mem C) a.
Proof.
intros R C ly3 S3 Hp3 W3 mem3 md3 k HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & _).
apply F1; lia.
Qed.

Lemma cxb_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r.
  rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Lemma crs_chain_B : forall R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2,
  crs_pre_B (fx := fx) B ARx CTX0 C -> crs_JR_B B ARx R C ly3 S3 Hp3 W3 mem3 md3 k -> crs_saved_B C W3 mem3 ->
  spZ (cb_regs C) - CRS_FRAME_B <= sp2 <= spZ (cb_regs C) - 128 ->
  exists ch1, achain ly3 (aview SEGS (w_H W3) mem3) sp2 (spZ (cb_regs C)) ch1.
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2 HPRE HJ HSV Hsp2.
pose proof HPRE as ((HAFN & _) & _).
pose proof HAFN as (HAR0 & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity).
assert (H8 : spZ (cb_regs C) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
  destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (proj1 (Forall_forall _ _) HSV (120, 1%bv) ltac:(cbn; tauto)) as Hw1.
pose proof (proj1 (Forall_forall _ _) HSV (112, 8%bv) ltac:(cbn; tauto)) as Hw8.
cbn [fst snd] in Hw1, Hw8.
replace (spZ (cb_regs C) - 128 + 120) with (spZ (cb_regs C) - 8) in Hw1 by lia.
replace (spZ (cb_regs C) - 128 + 112) with (spZ (cb_regs C) - 16) in Hw8 by lia.
destruct (Z_le_gt_dec (ly_top ly3 - 16) (spZ (cb_regs C))) as [Hbad|Hgood].
- exists []. left. split; [right; left; exact Hbad | reflexivity].
- exists ((spZ (cb_regs C), raZ (cb_regs C), s0Z (cb_regs C)) :: cb_ch C). right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, spZ (cb_regs C) <= a -> a < ly_top (cb_ly C) ->
            rdword (aview SEGS (w_H W3) mem3) a = rdword (aview SEGS (w_H (cb_W C)) (cb_mem C)) a).
  { intros a Ha Hat. apply cxb_rdword_ext. intros j Hj.
    apply (cxb_keep_above R C ly3 S3 Hp3 W3 mem3 md3 k HJ). lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next (spZ (cb_regs C)) (ly_top ly3) (s0Z (cb_regs C))) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (cxb_fpchain_keep (aview SEGS (w_H (cb_W C)) (cb_mem C))
               (aview SEGS (w_H W3) mem3) (spZ (cb_regs C))); [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbn beta. intros x Hx. lia.
Qed.

(* The kit's fpre at a call of this walk, AT THE WALK'S CURRENT FLOAT STATE fxk (the callee texts are quantified over it),
   from the callee's afn_pre_x (aj_call_x's), the boundary (its read-only view, its sp2 window, and frm_zero of fxk:
   f97c's fpre ends with it) and the call's return address (a text address of the listing, so below alloc_ceiling) *)
Lemma crs_callee_fpre_B : forall R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 (rg : bvmap 5 word) md ch1,
  crs_baseR_B (fx := fx) B ARx R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  spZ rg = sp2 -> raZ rg < YM05.alloc_ceiling ->
  afn_pre_x SEGS B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1 ->
  fpre (fx := fxk) (PA := PA) B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 rg md ch1 HB Hsp Hra HA.
pose proof HB as (HPRE & Hfrm & _ & HJ & _ & _ & _ & HROD & _ & _ & _ & _ & Hs2 & _).
pose proof HPRE as ((_ & _ & Hhi & _) & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
split; [exact HA|]. split; [exact HROD|]. split; [rewrite Hsp, Ehi; lia|]. split; [exact Hra | exact Hfrm].
Qed.

(* ---- the counters ---- *)
Lemma crs_first_bnd_B : forall C, 0 <= cb_took C -> 0 <= crs_first_B C <= cb_took C.
Proof.
intros C H. unfold crs_first_B. destruct (Z.eqb_spec (cb_took C) 0); [lia|].
pose proof (crs_pick_lt (cb_tb C) (cb_took C) ltac:(lia)). lia.
Qed.
Lemma crs_N_bnd_B : forall C p e, PjWriteHyp.wlen (cb_t C) p + 1 < 2 ^ e -> 0 <= e <= 62 ->
  1 <= PjWriteHyp.wcalls (cb_t C) p < 2 ^ e.
Proof.
intros C p e H He. pose proof (RttModel.wcalls_pos (cb_t C) p).
assert (He2 : 2 ^ e <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
pose proof (crs_wN_le (cb_t C) p ltac:(lia)). unfold PjWriteHyp.wcalls in *. lia.
Qed.

(* the words the X2 run leaves: a0 - s7 and h % (a0 - s7) *)
Lemma cxb_sub_word : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  alu64 ALU_ADD (w64 a) (mul_div M_MUL (w64 b) (Z_to_bv 64 (-1))) = w64 (a - b).
Proof.
intros a b H1 H2. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, mul_div_unsigned.
unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
cbn [zmd_raw]. rewrite Z.add_mod_idemp_r by lia. rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small b) by lia.
rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mul_mod_idemp_r by lia. rewrite Z.add_mod_idemp_r by lia.
f_equal. lia.
Qed.
Lemma cxb_remu_word : forall x n, 0 <= x < 2 ^ 64 -> 0 < n < 2 ^ 64 ->
  mul_div M_REMU (w64 x) (w64 n) = w64 (x mod n).
Proof.
intros x n Hx Hn. assert (Hm : 0 <= x mod n < n) by (apply Z.mod_pos_bound; lia).
unfold w64. rewrite m_remu by (rewrite unsigned_lit_small; lia). apply bv_eq.
rewrite v_remu_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* callee-saved registers across a call (S10Env.v ts_ap, h-hpreset-7 walk-S10 88b4aea723f) *)
Lemma cxb_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.
Lemma cxb_ap3 : forall rg rg', aregs_preserved rg rg' -> getr rg' 3 = getr rg 3.
Proof. intros rg rg' HP. apply cxb_ap; [exact HP|]. change (bv_unsigned (3%bv : bv 5)) with 3. unfold acallee_saved. lia. Qed.
Lemma cxb_ap4 : forall rg rg', aregs_preserved rg rg' -> getr rg' 4 = getr rg 4.
Proof. intros rg rg' HP. apply cxb_ap; [exact HP|]. change (bv_unsigned (4%bv : bv 5)) with 4. unfold acallee_saved. lia. Qed.

(* the blocks' bytes are a sum over the blocks, so a permutation of the blocks keeps them *)
Lemma cxb_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2]; cbn [bsum fold_right] in *;
  unfold bsum in *; cbn [fold_right] in *; lia.
Qed.

(* ---- the registers the segment carries across its runs and calls: every one is callee-saved ---- *)
Definition crs_rs_B (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B.
Lemma crs_rs_cs_B : forall C sp2, Forall (fun p => acallee_saved (bv_unsigned (fst p))) (crs_rs_B C sp2).
Proof.
intros C sp2. unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app].
repeat (apply Forall_cons; [cbn [fst]; lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia|]).
apply Forall_nil.
Qed.
Lemma cxb_regsat_ap : forall rg rg' l, aregs_preserved rg rg' ->
  Forall (fun p => acallee_saved (bv_unsigned (fst p))) l -> crs_regsat_B rg l -> crs_regsat_B rg' l.
Proof.
intros rg rg' l HP Hcs H. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros x Hx.
rewrite (cxb_ap rg rg' (fst x) HP (Hcs x Hx)). exact (H x Hx).
Qed.
Lemma crs_rs_get_B : forall C sp2 rg, crs_regsat_B rg (crs_rs_B C sp2) ->
  getr rg 2 = w64 sp2 /\ getr rg 8 = w64 (spZ (cb_regs C)) /\ getr rg 9 = w64 sp2 /\ getr rg 18 = w64 (cF_B C) /\
  getr rg 26 = w64 (cF_B C) /\ getr rg 27 = w64 SHADOW_OFF /\ getr rg 25 = w64 (shadow_addr (cF_B C)) /\
  getr rg 19 = w64 (cb_doc C) /\ getr rg 20 = w64 (cSize_B C) /\ getr rg 21 = w64 (cb_data C) /\
  getr rg 22 = w64 (Ledger.lsum (cb_Lam C)) /\ getr rg 24 = w64 CRS_RO_B.
Proof.
intros C sp2 rg H. unfold crs_regsat_B, crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B in H. cbn [app] in H.
repeat match type of H with Forall _ (_ :: _) => let H' := fresh "H" in apply Forall_cons_iff in H as [H' H]; cbn [fst snd] in H' end.
repeat split; assumption.
Qed.
(* the s-register kept by a run of the walk is SOff (32 + r) 0: checked on the run's symbolic registers *)
Ltac cxb_kept_regs := repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil.

(* the live-room parts are nonnegative *)
Lemma cxb_hpeak_nn : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.
Lemma cxb_live_pjp_nn : forall x, 0 <= PRH_FnPj.LIVE_pj_parse x.
Proof.
intros x. unfold PRH_FnPj.LIVE_pj_parse. pose proof (cxb_hpeak_nn (PRH_FnPj.prhPj_ptrace x)).
pose proof (@cf_head_nonneg cp). nia.
Qed.
Lemma cxb_dbl_nn : forall n c need, 0 <= c -> 0 <= WriterSpec.dbl n c need.
Proof.
induction n as [|n IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
destruct (need <=? c); [lia | apply IH; lia].
Qed.
Lemma cxb_live_pjw_nn : forall t p, 0 <= PRH_FnWriter.LIVE_pj_write t p.
Proof.
intros t p. unfold PRH_FnWriter.LIVE_pj_write, WriterSpec.newcap. cbn [Z.eqb].
pose proof (cxb_dbl_nn 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) ltac:(lia)).
pose proof (@cf_head_nonneg cp). lia.
Qed.

Lemma cxb_regsat_snoc : forall C sp2 rg (r : bv 5) v, crs_regsat_B rg (crs_rs_B C sp2) -> getr rg r = w64 v ->
  crs_regsat_B rg (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ crs_rro_B ++ [(r, v)]).
Proof.
intros C sp2 rg r v H Hv. unfold crs_rs_B in H. unfold crs_regsat_B in *. rewrite !app_assoc in *.
apply Forall_app. split; [exact H | constructor; [exact Hv | constructor]].
Qed.

Lemma cxb_regsat_F : forall C sp2 rg q, crs_regsat_B rg (crs_rs_B C sp2) -> getr rg 23 = w64 q ->
  crs_regsat_B rg (crs_rbase_B C sp2 ++ crs_rsh_B C ++ [(23%bv, q)]).
Proof.
intros C sp2 rg q H Hq. unfold crs_rs_B, crs_regsat_B in *. apply Forall_app in H as [H1 H]. apply Forall_app in H as [H2 _].
rewrite app_assoc. apply Forall_app. split; [apply Forall_app; split; assumption | constructor; [exact Hq | constructor]].
Qed.

(* an atom's value (S10Env.v ts_U0, h-hpreset-7 walk-S10 88b4aea723f) *)
Lemma cxb_U0 : forall E n, U E (SOff n 0) = bv_unsigned (ew E n).
Proof.
intros E n. rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

(* ---- the pj_write call's run events (the text's entry premise prh_run_at .. (prhWriter_pjw_evs [] ..)): the kit's
   injected pretty write crs_ev_ws_B C true, at the boundary's position, by PRH_Supply.prhWriter_pjw_evs_w_starved ---- *)
Lemma cxb_djb2_pick_h : forall x h, ck_djb2 h x = fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x h.
Proof. induction x as [|c r IH]; intros h; [reflexivity|]. cbn [ck_djb2 fold_left]. rewrite IH. f_equal. f_equal. lia. Qed.
Lemma cxb_pick_eq : forall x t p, Z.of_nat (PresetReqAt.pick x (PresetReqAt.wcalls t p)) =
  ck_pick x (PjWriteHyp.wcalls t p).
Proof.
intros x t p. pose proof (crs_wcalls_pos_B t p) as H.
assert (Ew : PjWriteHyp.wcalls t p = Z.of_nat (PresetReqAt.wcalls t p)) by reflexivity.
rewrite Ew. unfold PresetReqAt.pick. destruct (PresetReqAt.wcalls t p) as [|n] eqn:En; [lia|].
rewrite crs_pick_eq by lia. unfold PresetReqAt.pick_h. rewrite <- cxb_djb2_pick_h.
rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.
Lemma crs_x2_run_B : forall C, cf_head = PresetReqAt.HEAD -> cb_doc C <> 0 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (crs_evs_B C) ->
  0 <= crs_cnt1_B C + cN1_B C -> crs_cnt1_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C) < 2 ^ 64 ->
  prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length (crs_evs_at_X2_B C))%nat
    (PRH_FnWriter.prhWriter_pjw_evs [] (crs_cnt1_B C + cN1_B C) (crs_cnt1_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C))
       (WriterValue.wdpieces (cb_t C) true)).
Proof.
intros C Hh Hd HR H0 HM.
assert (E : crs_evs_B C = crs_evs_at_X2_B C ++ (crs_ev_ws_B C true ++ crs_ev_w_B C false ++ crs_ev_wf_B C false ++
   crs_ev_ws_B C false)).
{ rewrite (crs_evs_doc_B C Hd). unfold crs_evs_at_X3_B, crs_evs_at_H3_B, crs_evs_at_Z_B. repeat rewrite <- app_assoc.
  reflexivity. }
destruct (crs_run_split_B C _ _ E HR) as [_ H2].
apply (proj1 (prh_run_at_app_iff _ _ _ _ _ _)) in H2 as [H3 _].
pose proof (crs_wcalls_pos_B (cb_t C) true) as Hw.
assert (Hk : ck_pick (cb_tb C) (cN1_B C) = Z.of_nat (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) true)))
  by (rewrite cxb_pick_eq; reflexivity).
rewrite Hk in *.
rewrite (PRH_Supply.prhWriter_pjw_evs_w_starved (cb_t C) true _ _ _ Hh H0 eq_refl HM).
- exact H3.
- unfold PresetReqAt.pick. destruct (PresetReqAt.wcalls (cb_t C) true) as [|n] eqn:En; [lia|].
  pose proof (Z.mod_pos_bound (PresetReqAt.pick_h (cb_tb C)) (Z.of_nat (S n)) ltac:(lia)). lia.
Qed.

(* ... and its consumer window (the text's prh_cons_from at the call), from crs_pre_B's by the same split *)
Lemma crs_x2_cons_B : forall CTX0 C, cf_head = PresetReqAt.HEAD -> cb_doc C <> 0 ->
  crs_pre_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  0 <= crs_cnt1_B C + cN1_B C -> crs_cnt1_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C) < 2 ^ 64 ->
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C + length (crs_evs_at_X2_B C))%nat
    (length (PRH_FnWriter.prhWriter_pjw_evs [] (crs_cnt1_B C + cN1_B C)
       (crs_cnt1_B C + cN1_B C + ck_pick (cb_tb C) (cN1_B C)) (WriterValue.wdpieces (cb_t C) true))).
Proof.
intros CTX0 C Hh Hd HP H0 HM.
assert (E : crs_evs_B C = crs_evs_at_X2_B C ++ crs_ev_ws_B C true ++ (crs_ev_w_B C false ++ crs_ev_wf_B C false ++
   crs_ev_ws_B C false)).
{ rewrite (crs_evs_doc_B C Hd). unfold crs_evs_at_X3_B, crs_evs_at_H3_B, crs_evs_at_Z_B. repeat rewrite <- app_assoc.
  reflexivity. }
pose proof (crs_cons_split_B B ARx CTX0 C _ _ _ E HP) as H3.
pose proof (crs_wcalls_pos_B (cb_t C) true) as Hw.
assert (Hk : ck_pick (cb_tb C) (cN1_B C) = Z.of_nat (PresetReqAt.pick (cb_tb C) (PresetReqAt.wcalls (cb_t C) true)))
  by (rewrite cxb_pick_eq; reflexivity).
rewrite Hk in *.
rewrite (PRH_Supply.prhWriter_pjw_evs_w_starved (cb_t C) true _ _ _ Hh H0 eq_refl HM).
- exact H3.
- unfold PresetReqAt.pick. destruct (PresetReqAt.wcalls (cb_t C) true) as [|n] eqn:En; [lia|].
  pose proof (Z.mod_pos_bound (PresetReqAt.pick_h (cb_tb C)) (Z.of_nat (S n)) ltac:(lia)). lia.
Qed.

Lemma crs_seg_X2_B : forall CTX0 C,
  cf_head = PresetReqAt.HEAD ->
  (forall fx' : YK11.FPState, tfuzz_alloc_fail_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fx' : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  CrsKeep_B B ARx ->
  cb_took C <= 2 ^ 28 ->
  (forall fx' : YK11.FPState, crs_wexact_B (fx := fx') (rc := rc) B ARx CTX0 C) ->
  crs_from_F_B (fx := fx) (rc := rc) B ARx CTX0 C -> crs_from_Z_B (fx := fx) (rc := rc) B ARx CTX0 C ->
  crs_from_X2_B (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HI_head HT_fuzz_alloc_fail HT_fuzz_alloc_ran_out HK HB_took HW_exact KcF KcZ.
unfold crs_from_X2_B.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 Hdoc HB HR HL HD HT.
unfold SRr' in KcZ |- *.
set (R := wle' SEGS YGcfRehidePost.RZ_cf) in *.
assert (Rr : forall W, R W W) by exact (wle'_refl SEGS YGcfRehidePost.RZ_cf).
assert (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) by exact (wle'_trans SEGS YGcfRehidePost.RZ_cf).
assert (Rw : forall W W', wle W W' -> R W W') by exact (wle_wle' SEGS YGcfRehidePost.RZ_cf).
unfold crs_regsat_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B in HR. cbn [app] in HR.
apply Forall_cons_iff in HR as [R2 HR]. apply Forall_cons_iff in HR as [R8 HR].
apply Forall_cons_iff in HR as [R9 HR]. apply Forall_cons_iff in HR as [R18 HR].
apply Forall_cons_iff in HR as [R26 HR]. apply Forall_cons_iff in HR as [R27 HR].
apply Forall_cons_iff in HR as [R25 HR]. apply Forall_cons_iff in HR as [R19 HR].
apply Forall_cons_iff in HR as [R20 HR]. apply Forall_cons_iff in HR as [R21 HR].
apply Forall_cons_iff in HR as [R22 HR]. apply Forall_cons_iff in HR as [R24 HR].
apply Forall_cons_iff in HR as [R23 HR]. apply Forall_cons_iff in HR as [R10 HR].
apply Forall_cons_iff in HR as [R12 _].
cbn [fst snd] in R2, R8, R9, R18, R26, R27, R25, R19, R20, R21, R22, R24, R23, R10, R12.
assert (HRS0 : crs_regsat_B regs3 (crs_rs_B C sp2)).
{ unfold crs_regsat_B, crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app].
  repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil. }
destruct HL as ((HL0 & Hpk & Hran & Hc1 & Hc2 & Hroom & Hpos) & Hperm).
pose proof HB as (HPRE & Hfrm & Hfk & HJ & HFR & HSV & HSL & HROD & HMN & Hgp & Htp & Hsp2a & Hsp2b & Hsp2c & HDPk).
assert (HW : crs_ws_B CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 (crs_cnt1_B C + cN1_B C) SIZE_MAXZ 0).
{ split; [exact HB|]. split; [exact HL0|]. split; [exact Hperm|]. split; [exact Hpk|].
  split; [exact Hroom|]. split; [exact HD | exact HT]. }
set (E := TE (cb_regs C) regs3 []).
assert (HS : st_ok_pi SEGS VAL E (mkSS CRS_PC_X2_B cur_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W3) (@YK11.mkst fxk regs3 (Z_to_bv 64 (BASE + CRS_PC_X2_B)) mem3 (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fxk) (rc := rc) (L := B_prog_listing) (PI := PA) R).
unfold crs_JR_B in HJ. unfold crs_cfg_B.
(* ---- +616 bne a0, s7: a0 = s7 is refuted ---- *)
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
2: { exfalso. rewrite branch_ne_U, !cxb_U0 in Hc.
     rewrite (te_cur (cb_regs C) regs3 [] 10%bv 10 eq_refl), (te_cur (cb_regs C) regs3 [] 23%bv 23 eq_refl) in Hc.
     rewrite R10, R23 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
     pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HtkR & HDOCR & HLER & HcntR & _).
     destruct HDOCR as [Hd00 | (_ & _ & _ & HwlR & _)]; [exact (Hdoc Hd00)|].
     pose proof (crs_N_bnd_B C true 28 HwlR ltac:(lia)) as HN1R. fold (cN1_B C) in HN1R.
     pose proof (crs_first_bnd_B C ltac:(lia)) as HfstR.
     pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLER) as (_ & _ & HcrR & _).
     unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by (unfold crs_cnt1_B in *; lia). lia. }
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ apply awr_ok_nil. }
(* ---- at `jal fuzz_alloc_fail` (+636): the run wrote nothing ---- *)
assert (Hm1 : forall x, ms_mem ms x = mem3 x) by (intros x; apply HF; intros (r & Hr & _); destruct Hr).
clear HF HFr HG.
assert (A35 : ew E 35 = getr regs3 3) by exact (te_cur (cb_regs C) regs3 [] 3%bv 3 eq_refl).
assert (A36 : ew E 36 = getr regs3 4) by exact (te_cur (cb_regs C) regs3 [] 4%bv 4 eq_refl).
assert (A34 : ew E 34 = getr regs3 2) by exact (te_cur (cb_regs C) regs3 [] 2%bv 2 eq_refl).
assert (A40 : ew E 40 = getr regs3 8) by exact (te_cur (cb_regs C) regs3 [] 8%bv 8 eq_refl).
assert (A42 : ew E 42 = getr regs3 10) by exact (te_cur (cb_regs C) regs3 [] 10%bv 10 eq_refl).
assert (A44 : ew E 44 = getr regs3 12) by exact (te_cur (cb_regs C) regs3 [] 12%bv 12 eq_refl).
assert (A55 : ew E 55 = getr regs3 23) by exact (te_cur (cb_regs C) regs3 [] 23%bv 23 eq_refl).
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
rewrite A35 in Q3. rewrite A36 in Q4. rewrite A34, R2 in Q2. rewrite A40, R8 in Q8.
rewrite A42, A44, A55, R10, R12, R23 in Q10.
pose proof (crs_ws_run_B HK CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 _ _ _ (ms_regs ms) (ms_mem ms) _
  HW HJ Hm1 Q3 Q4) as HW1.
assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
{ apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs3 [] _ _ ms _ HS); [|exact HRS0].
  unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. cxb_kept_regs. }
(* the numbers *)
pose proof HPRE as (HPf & _ & HUNIV & _ & _ & _ & _ & _ & Hsz & Hd0 & Hd62 & HSRC & _ & Htk & HDOC & HLE & Hcnt
  & HRUN & Hran0 & _).
pose proof HPf as (HAFN & _). pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (EFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity).
assert (ESTc : 1000 <= STK_check_reject_clean_starved (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
pose proof asan_consts as (AC1 & _).
assert (EBASE : BASE = 530124) by (vm_compute; reflexivity).
destruct HDOC as [Hd00 | (Hrd & HTOK & Hwl0 & Hwl1 & Hdep)]; [exfalso; exact (Hdoc Hd00)|].
pose proof (crs_N_bnd_B C true 28 Hwl1 ltac:(lia)) as HN1. fold (cN1_B C) in HN1.
pose proof (crs_first_bnd_B C ltac:(lia)) as Hfst.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL0) as (_ & _ & Hcr & _).
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLE) as (_ & _ & Hcr0 & _).
pose proof (djb_hash_range (cb_tb C)) as Hh. fold (cHash_B C) in Hh.
assert (Hcc : cb_cnt C <= crs_cnt1_B C <= crs_cnt1_B C + cN1_B C) by (unfold crs_cnt1_B; lia).
set (kp := ck_pick (cb_tb C) (cN1_B C)).
assert (Hkp : 0 <= kp < cN1_B C) by (apply crs_pick_lt; lia).
assert (Ra0 : getr (ms_regs ms) 10 = w64 kp).
{ rewrite Q10, cxb_sub_word by lia. rewrite cxb_remu_word by lia. unfold kp. rewrite crs_pick_eq by lia.
  unfold cHash_B. f_equal. f_equal. lia. }
assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C)) by (unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; lia).
pose proof HW1 as (HB1 & HL1 & _).
pose proof HB1 as (_ & _ & _ & _ & _ & HSV1 & _).
destruct (crs_chain_B R CTX0 C ly3 S3 Hp3 W3 (ms_mem ms) _ k sp2 HPRE HJ HSV1 ltac:(lia)) as (ch1 & Hch).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (EST : STK_fuzz_alloc_fail (PI := prh_img_B) + 144 <= STK_check_reject_clean_starved (PI := prh_img_B))
  by (unfold Z.le; vm_compute; discriminate).
assert (EST0 : 0 <= STK_fuzz_alloc_fail (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W3 _ _ ms
    STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
    [(CRS_CID_B, cb_fpos C)] ly3 S3 Hp3 _ k (STK_fuzz_alloc_fail (PI := prh_img_B)) [] (sp2 - spZ (cb_regs C)) _ ch1 _
    HS eq_refl HJ).
  - rewrite Hsp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - exact EST0.
  - assert (CRS_FRAME_B = 144) by (vm_compute; reflexivity). lia.
  - rewrite Q3, Hgp. exact Hgp0.
  - rewrite Q4, Htp. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite EBASE, unsigned_lit_small; lia.
  - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
  - intros HPRE1. apply (cxb_lift_x (fx := fxk) (SK := SK) SEGS B PST ARx R Rw).
    refine (HT_fuzz_alloc_fail fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak3 _ SIZE_MAXZ 0 kp (cb_most C) 0
      (crs_callee_fpre_B R CTX0 C fxk ly3 S3 Hp3 W3 _ (ms_mem ms) _ k sp2 _ (ms_regs ms) _ ch1 HB1 Hsp _ HPRE1)
      HL1 Ra0 ltac:(lia)).
    unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W4 c4 Hwle (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & -> & HJc & HJ1 & HP & HQ & HMN4).
destruct HQ as (Hrm & -> & -> & Eab & HL4).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ1 by lia.
assert (HW4 : crs_ws_B CTX0 C fxk ly4 S3 Hp3 W4 regs4 mem4 md4 (k + k1) sp2 Lam3 peak3 (crs_cnt1_B C + cN1_B C)
   (if kp <? SIZE_MAXZ - (crs_cnt1_B C + cN1_B C) then crs_cnt1_B C + cN1_B C + kp else SIZE_MAXZ) 0).
{ apply (crs_ws_callee_B HK CTX0 C fxk ly3 S3 Hp3 W3 (ms_regs ms) (ms_mem ms) _ k sp2 Lam3 peak3 _ _ _
    _ ly4 S3 Hp3 W4 regs4 mem4 md4 k1 Lam3 peak3 _ _ _ HW1 HJ1 HJc HMN4 (cxb_ap3 _ _ HP) (cxb_ap4 _ _ HP) HL4
    (Permutation_refl _)).
  - rewrite Eab. apply Permutation_refl.
  - lia.
  - apply Hrm. exact Hroom. }
assert (HRS4 : crs_regsat_B regs4 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP (crs_rs_cs_B C sp2) HRS1).
clear HW HW1 HJ HJ1 HS SHOK HEI HRS0 HRS1 Q10 Q1 Q2 Q8 Q3 Q4 Hm1 Ra0 Hsp Hs0 Hch.
clear A34 A35 A36 A40 A42 A44 A55 ch1.
clear dependent ms. clear dependent mat.
assert (Ekp : (kp <? SIZE_MAXZ - (crs_cnt1_B C + cN1_B C)) = true) by (apply Z.ltb_lt; unfold SIZE_MAXZ; lia).
rewrite Ekp in HW4.
(* ---- +640 li a1, 1; mv a0, s3; jal pj_write (doc, 1): the injected pretty write ---- *)
set (E2 := TE (cb_regs C) regs4 []).
assert (HS : st_ok_pi SEGS VAL E2 (mkSS 3268 cur_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W4) (@YK11.mkst fxk regs4 (Z_to_bv 64 (BASE + 3268)) mem4 (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E2 (mrestrict (w_H W4) mem4)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E2) by apply te_env.
pose proof HW4 as (HB4 & _). pose proof HB4 as (_ & _ & _ & HJ & _).
unfold crs_JR_B in HJ.
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ apply awr_ok_nil. }
assert (Hm1 : forall x, ms_mem ms x = mem4 x) by (intros x; apply HF; intros (r & Hr & _); destruct Hr).
clear HF HFr HG.
assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
{ apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs4 [] _ _ ms _ HS); [|exact HRS4].
  unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. cxb_kept_regs. }
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (A51 : ew E2 51 = getr regs4 19) by exact (te_cur (cb_regs C) regs4 [] 19%bv 19 eq_refl).
assert (A35 : ew E2 35 = getr regs4 3) by exact (te_cur (cb_regs C) regs4 [] 3%bv 3 eq_refl).
assert (A36 : ew E2 36 = getr regs4 4) by exact (te_cur (cb_regs C) regs4 [] 4%bv 4 eq_refl).
rewrite A51 in Q10. rewrite A35 in Q3. rewrite A36 in Q4.
pose proof (crs_ws_run_B HK CTX0 C fxk ly4 S3 Hp3 W4 regs4 mem4 md4 (k + k1) sp2 Lam3 peak3 _ _ _ (ms_regs ms)
  (ms_mem ms) _ HW4 HJ Hm1 Q3 Q4) as HW5.
pose proof (crs_rs_get_B C sp2 _ HRS1) as (G2 & G8 & _ & _ & _ & _ & _ & G19 & _).
pose proof (crs_rs_get_B C sp2 _ HRS4) as (_ & _ & _ & _ & _ & _ & _ & G19' & _).
rewrite G19' in Q10.
assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C)) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
pose proof HW5 as (HB5 & HL5 & (HpL5 & Hpb5) & Hpk5 & Hroom5 & HD5 & HT5).
pose proof HB5 as (_ & _ & _ & _ & HFR5 & HSV5 & _ & _ & _ & Hgp5 & Htp5 & _).
destruct (crs_chain_B R CTX0 C ly4 S3 Hp3 W4 (ms_mem ms) _ (k + k1) sp2 HPRE HJ HSV5 ltac:(lia)) as (ch1 & Hch).
destruct (Hpos eq_refl) as (rph & Hrp).
destruct (HT5 Hdoc) as (Hn5 & HDL5 & Hvis5 & (_ & Hinf5 & Hra5)).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HLIVE0 & HRQ0 & HFR0 & _).
assert (EST2 : STK_pj_write DOC_D + 144 <= STK_check_reject_clean_starved (PI := prh_img_B))
  by (unfold Z.le; vm_compute; discriminate).
assert (EST20 : 0 <= STK_pj_write DOC_D) by (unfold Z.le; vm_compute; discriminate).
assert (Edd : (32 <= DOC_D)%nat) by (vm_compute; lia).
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_xF_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W4 _ _ ms
    STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
    [(CRS_CID_B, cb_fpos C)] ly4 S3 Hp3 _ (k + k1) (STK_pj_write DOC_D) [] (sp2 - spZ (cb_regs C)) _ ch1 _
    HS eq_refl HJ).
  - rewrite Hsp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - exact EST20.
  - lia.
  - rewrite Hgp5. exact Hgp0.
  - rewrite Htp5. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite EBASE, unsigned_lit_small; lia.
  - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
  - intros HPRE1.
    refine (proj1 (proj2 (HW_exact fxk)) rph ly4 S3 Hp3 W4 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak3
      (crs_cnt1_B C + cN1_B C) (crs_cnt1_B C + cN1_B C + kp) 0 eq_refl eq_refl ltac:(exact Hc2)
      (crs_callee_fpre_B R CTX0 C fxk ly4 S3 Hp3 W4 _ (ms_mem ms) _ (k + k1) sp2 _ (ms_regs ms) _ ch1 HB5 Hsp _ HPRE1)
      HUNIV Hroom5 Hrp (crs_pre_los_B B ARx CTX0 C HPRE)
      (crs_x2_cons_B CTX0 C HI_head Hdoc HPRE ltac:(unfold crs_cnt1_B in *; lia) ltac:(unfold crs_cnt1_B in *; lia))
      Q10 Q11 ltac:(lia) HL5
      (crs_x2_run_B C HI_head Hdoc HRUN ltac:(unfold crs_cnt1_B in *; lia) ltac:(unfold crs_cnt1_B in *; lia))
      (proj1 (HT5 Hdoc)) (or_intror (or_intror Hinf5)) Hra5 Hvis5
      (fun a kk H => HDL5 (a, kk) H) ltac:(lia) ltac:(lia) _ _ _ _).
    + unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
    + destruct HFR5 as (Hfr5 & _). destruct (crs_cap_callee_B (cb_S C) S3 (cb_fpos C) Hfr5 HFR0) as (_ & _ & Hcc5).
      exact Hcc5.
    + change (negb (1 =? 0)) with true. unfold PjWriteHyp.wlen in Hwl1. unfold PRH_FnWriter.prhWriter_WMAX. lia.
    + unfold RQ_crcs, zmaxl in HRQ0. cbn [fold_right] in HRQ0. lia.
    + change (negb (1 =? 0)) with true.
      rewrite (YCbq.blocks_bytes_bsum B ly4 S3), (cxb_bsum_perm _ _ Hpb5), <- (YCbq.blocks_bytes_bsum B (cb_ly C) (cb_S C)).
      unfold LIVE_check_reject_clean_starved in HLIVE0.
      pose proof (cxb_live_pjp_nn (cb_tb C)). pose proof (cxb_live_pjw_nn (cb_t C) false). lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W5 c5 Hwle5 (fx5 & ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k2 & -> & HFZ5 & HFK5 & HJc5 & HJ15 & HP5 & HQ5
  & HMN5).
destruct HQ5 as (ok & ran5 & q & Lam5 & peak5 & HQ5). cbv zeta in HQ5.
change (negb (1 =? 0)) with true in HQ5.
set (c0 := crs_cnt1_B C + cN1_B C) in *.
set (Pw := WriterValue.wdpieces (cb_t C) true) in *.
set (kw := PRH_FnWriter.prhWriter_k ok (WriterApp.w0 c0 (c0 + kp)) Pw) in *.
set (st5 := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 c0 (c0 + kp)) Pw) in *.
destruct HQ5 as (Hoks & Hq & Hroom5' & Hg5 & Hpex5 & _ & _ & HL5' & Harms & Hexact).
(* K0-DEAD-PJWRITE: nothing refused (prh_granted), so g_ran_out is kept (PRW_CrsModel.crs_ran_of_granted) *)
pose proof (crs_ran_of_granted _ _ _ _ _ _ _ _ Hoks Hg5) as Hr5e.
(* the injected write stops at its g_fail_at, inside the run (PRW_CrsModel.crs_winj) *)
assert (HN1n : (Z.to_nat kp < length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens Pw)))%nat).
{ unfold cN1_B, PjWriteHyp.wcalls in Hkp. unfold Pw. lia. }
pose proof (crs_winj Pw c0 (Z.to_nat kp) ok ltac:(unfold c0; lia) HN1n
  ltac:(unfold c0, Pw, cN1_B, PjWriteHyp.wcalls in *; lia)) as HWI.
cbv zeta in HWI. rewrite Z2Nat.id in HWI by lia. fold kw st5 in HWI.
destruct HWI as (Hfailed & Hk1 & Hkc & Hkx).
destruct Harms as [(Hf0 & _) | (_ & Hq0 & HLam5 & Hpb55 & Hpk55)]; [exfalso; exact (Hfailed Hf0)|].
subst q Lam5. rewrite Hkc in HL5'.
assert (Hpk5' : peak3 <= peak5) by (destruct Hpk55 as [(_ & ->) | (_ & ->)]; lia).
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL5') as (_ & _ & _ & _ & Hran5).
(* no refusal: every failed outcome is the injected one, so the write made pick + 1 calls *)
assert (Hk0 : ran5 = 0 -> kw = S (Z.to_nat kp)).
{ intros _. apply Hkx. intros i Hi Hf. exact (Hg5 i Hi Hf). }
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ15 by lia.
assert (HW6 : crs_ws_B CTX0 C fxk ly5 S5 Hp5 W5 regs5 mem5 md5 (k + k1 + k2) sp2 Lam3 peak5
   (c0 + Z.of_nat kw) (WriterApp.w_fail st5) ran5).
{ apply (crs_ws_callee_B HK CTX0 C fxk ly4 S3 Hp3 W4 (ms_regs ms) (ms_mem ms) _ (k + k1) sp2 Lam3 peak3 _ _ _
    _ ly5 S5 Hp5 W5 regs5 mem5 md5 k2 Lam3 peak5 _ _ _ HW5 HJ15 HJc5 HMN5 (cxb_ap3 _ _ HP5) (cxb_ap4 _ _ HP5) HL5'
    (Permutation_refl _) Hpb55 Hpk5' Hroom5'). }
pose proof (crs_ws_fx_B CTX0 C fxk fx5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW6 HFZ5 HFK5) as HW6x.
clear HW6. rename HW6x into HW6.
assert (HRS5 : crs_regsat_B regs5 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP5 (crs_rs_cs_B C sp2) HRS1).
assert (Hq5 : getr regs5 10 = w64 0) by exact Hq.
clear HW4 HW5 HJ HJ15 HS SHOK HEI HRS4 HRS1 Q10 Q11 Q1 Q3 Q4 Hm1 Hsp Hs0 Hch A51 A35 A36 G2 G8 G19 G19' ch1.
clear dependent ms. clear dependent mat.
(* the walk goes on at pj_write's float state fx5 *)
clear RUN BR. clear dependent fxk. rename fx5 into fxk.
pose (RUN := @paj_run_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
pose (BR := paj_branchR (fx := fxk) (rc := rc) (L := B_prog_listing) (PI := PA) R).
(* ---- +652 mv s7, a0; li a0, -1; jal fuzz_alloc_fail (-1) ---- *)
set (E3 := TE (cb_regs C) regs5 []).
assert (HS : st_ok_pi SEGS VAL E3 (mkSS 3280 cur_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W5) (@YK11.mkst fxk regs5 (Z_to_bv 64 (BASE + 3280)) mem5 (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E3 (mrestrict (w_H W5) mem5)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E3) by apply te_env.
pose proof HW6 as (HB6 & _). pose proof HB6 as (_ & _ & _ & HJ & _).
unfold crs_JR_B in HJ.
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ apply awr_ok_nil. }
assert (Hm1 : forall x, ms_mem ms x = mem5 x) by (intros x; apply HF; intros (r & Hr & _); destruct Hr).
clear HF HFr HG.
assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
{ apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs5 [] _ _ ms _ HS); [|exact HRS5].
  unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. cxb_kept_regs. }
prreg HS (10%bv : bv 5) Q10. prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (A42 : ew E3 42 = getr regs5 10) by exact (te_cur (cb_regs C) regs5 [] 10%bv 10 eq_refl).
assert (A35 : ew E3 35 = getr regs5 3) by exact (te_cur (cb_regs C) regs5 [] 3%bv 3 eq_refl).
assert (A36 : ew E3 36 = getr regs5 4) by exact (te_cur (cb_regs C) regs5 [] 4%bv 4 eq_refl).
rewrite A42, Hq5 in Q23. rewrite A35 in Q3. rewrite A36 in Q4.
pose proof (crs_ws_run_B HK CTX0 C fxk ly5 S5 Hp5 W5 regs5 mem5 md5 (k + k1 + k2) sp2 Lam3 peak5 _ _ _ (ms_regs ms)
  (ms_mem ms) _ HW6 HJ Hm1 Q3 Q4) as HW7.
pose proof (crs_rs_get_B C sp2 _ HRS1) as (G2 & G8 & _).
assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C)) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
pose proof HW7 as (HB7 & HL7 & _ & _ & Hroom7 & _).
pose proof HB7 as (_ & _ & _ & _ & _ & HSV7 & _ & _ & _ & Hgp7 & Htp7 & _).
destruct (crs_chain_B R CTX0 C ly5 S5 Hp5 W5 (ms_mem ms) _ (k + k1 + k2) sp2 HPRE HJ HSV7 ltac:(lia)) as (ch1 & Hch).
assert (Ra0 : getr (ms_regs ms) 10 = w64 (2 ^ 64 - 1)) by (rewrite Q10; apply bv_eq; vm_compute; reflexivity).
assert (Hcw : 0 <= c0 + Z.of_nat kw) by (unfold c0; lia).
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W5 _ _ ms
    STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
    [(CRS_CID_B, cb_fpos C)] ly5 S5 Hp5 _ (k + k1 + k2) (STK_fuzz_alloc_fail (PI := prh_img_B)) [] (sp2 - spZ (cb_regs C))
    _ ch1 _ HS eq_refl HJ).
  - rewrite Hsp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - exact EST0.
  - lia.
  - rewrite Hgp7. exact Hgp0.
  - rewrite Htp7. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite EBASE, unsigned_lit_small; lia.
  - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
  - intros HPRE1. apply (cxb_lift_x (fx := fxk) (SK := SK) SEGS B PST ARx R Rw).
    refine (HT_fuzz_alloc_fail fxk ly5 S5 Hp5 W5 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak5 (c0 + Z.of_nat kw)
      (WriterApp.w_fail st5) ran5 (2 ^ 64 - 1) (cb_most C) 0
      (crs_callee_fpre_B R CTX0 C fxk ly5 S5 Hp5 W5 _ (ms_mem ms) _ (k + k1 + k2) sp2 _ (ms_regs ms) _ ch1 HB7 Hsp _
        HPRE1) HL7 Ra0 ltac:(lia)).
    unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W6 c6 _ (ly6 & S6 & Hp6 & regs6 & mem6 & md6 & k3 & -> & HJc6 & HJ16 & HP6 & HQ6 & HMN6).
destruct HQ6 as (Hrm6 & -> & -> & Eab6 & HL6).
assert (Ef : (2 ^ 64 - 1 <? SIZE_MAXZ - (c0 + Z.of_nat kw)) = false) by (apply Z.ltb_ge; unfold SIZE_MAXZ; lia).
rewrite Ef in HL6.
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ16 by lia.
assert (HW8 : crs_ws_B CTX0 C fxk ly6 S5 Hp5 W6 regs6 mem6 md6 (k + k1 + k2 + k3) sp2 Lam3 peak5
   (c0 + Z.of_nat kw) SIZE_MAXZ ran5).
{ apply (crs_ws_callee_B HK CTX0 C fxk ly5 S5 Hp5 W5 (ms_regs ms) (ms_mem ms) _ (k + k1 + k2) sp2 Lam3 peak5 _ _ _
    _ ly6 S5 Hp5 W6 regs6 mem6 md6 k3 Lam3 peak5 _ _ _ HW7 HJ16 HJc6 HMN6 (cxb_ap3 _ _ HP6) (cxb_ap4 _ _ HP6) HL6
    (Permutation_refl _)).
  - rewrite Eab6. apply Permutation_refl.
  - lia.
  - apply Hrm6. exact Hroom7. }
assert (HRS6 : crs_regsat_B regs6 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP6 (crs_rs_cs_B C sp2) HRS1).
assert (R23' : getr regs6 23 = w64 0).
{ rewrite (cxb_ap _ _ 23%bv HP6) by (change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia).
  rewrite Q23. reflexivity. }
clear HW6 HW7 HJ HJ16 HS SHOK HEI HRS5 HRS1 Q10 Q1 Q3 Q4 Q23 Hm1 Hsp Hs0 Hch A42 A35 A36 G2 G8 ch1 Ra0.
clear dependent ms. clear dependent mat.
(* ---- +664 lbu a0, 540(s8); bnez a0 (+668, check #3's OWN arm -> F): the cell reads 0 (the boundary ledger's own
   argument, prh_ledger_own), so the arm is not taken; +672 jal fuzz_alloc_ran_out ---- *)
pose proof HW8 as (HB8 & HL8 & HPm8 & _).
pose proof (prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ HL8) as (Hown & _).
set (E4 := TE (cb_regs C) regs6 []).
pose proof (crs_rs_get_B C sp2 _ HRS6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G24).
assert (ERO : CRS_RO_B = 6152892) by (vm_compute; reflexivity).
assert (X24 : bv_unsigned (ew E4 (xr 24)) = CRS_RO_B).
{ unfold xr. rewrite (te_cur (cb_regs C) regs6 [] 24%bv 24) by reflexivity. rewrite G24. unfold w64.
  apply unsigned_lit_small. lia. }
assert (Eown : CRS_RO_B + -1340 = @pi_g_own_ran_out prh_img_B) by (vm_compute; reflexivity).
assert (HS : st_ok_pi SEGS VAL E4
   (mkSS 3292 cur_atoms [YP09.mkRegion (Some (xr 24)) (-1340) (-1339) 0 0 [YP09.mkChunk (-1340) (CVal 1 (SLit 0))]] None
      (mkFacts [] [] []))
   (restrict (w_H W6) (@YK11.mkst fxk regs6 (Z_to_bv 64 (BASE + 3292)) mem6 (seg_rom SEGS)))).
{ apply ts_st_ok.
  - apply te_regs_ok.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (ts_rok E4 _ (xr 24) CRS_RO_B); [exact X24 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E4 _ _ (-1340) 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
    rewrite Eown. change (N.to_nat 1) with (@pi_gz_own_ran_out prh_img_B). exact Hown.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E4 (mrestrict (w_H W6) mem6)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E4) by apply te_env.
pose proof HB8 as (_ & _ & _ & HJ & _).
unfold crs_JR_B in HJ.
paj_run_tok_x RUN HS HJ SHOK (2 ^ 63, 2 ^ 63).
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm1 : forall x, ms_mem ms x = mem6 x).
{ intros x; apply HF; intros (r & Hr & Hw). cbn [In] in Hr. destruct Hr as [<- | []]. cbn in Hw. lia. }
clear HF HFr HG.
assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
{ apply (cxb_regsat_run_c (fx := fxk) (cb_regs C) regs6 [] _ _ ms _ HS); [|exact HRS6].
  unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. cxb_kept_regs. }
prreg HS (1%bv : bv 5) Q1. prreg HS (23%bv : bv 5) Q23. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (A55 : ew E4 55 = getr regs6 23) by exact (te_cur (cb_regs C) regs6 [] 23%bv 23 eq_refl).
assert (A35 : ew E4 35 = getr regs6 3) by exact (te_cur (cb_regs C) regs6 [] 3%bv 3 eq_refl).
assert (A36 : ew E4 36 = getr regs6 4) by exact (te_cur (cb_regs C) regs6 [] 4%bv 4 eq_refl).
rewrite A55, R23' in Q23. rewrite A35 in Q3. rewrite A36 in Q4.
pose proof (crs_ws_run_B HK CTX0 C fxk ly6 S5 Hp5 W6 regs6 mem6 md6 (k + k1 + k2 + k3) sp2 Lam3 peak5 _ _ _
  (ms_regs ms) (ms_mem ms) _ HW8 HJ Hm1 Q3 Q4) as HW9.
pose proof (crs_rs_get_B C sp2 _ HRS1) as (G2 & G8 & _).
assert (Hsp : spZ (ms_regs ms) = sp2) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z (ms_regs ms) = spZ (cb_regs C)) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
pose proof HW9 as (HB9 & HL9 & _ & _ & Hroom9 & _).
pose proof HB9 as (_ & _ & _ & _ & _ & HSV9 & _ & _ & _ & Hgp9 & Htp9 & _).
destruct (crs_chain_B R CTX0 C ly6 S5 Hp5 W6 (ms_mem ms) _ (k + k1 + k2 + k3) sp2 HPRE HJ HSV9 ltac:(lia))
  as (ch1 & Hch).
assert (EST3 : STK_fuzz_alloc_ran_out (PI := prh_img_B) + 144 <= STK_check_reject_clean_starved (PI := prh_img_B))
  by (unfold Z.le; vm_compute; discriminate).
assert (EST30 : 0 <= STK_fuzz_alloc_ran_out (PI := prh_img_B)) by (unfold Z.le; vm_compute; discriminate).
eapply (SRrG_bind SEGS R Rt).
{ eapply (aj_call_x_spR (fx := fxk) (SK := SK) SEGS B PST ARx LAWS Hsegs R Rr Rt W6 _ _ ms
    STK_check_reject_clean_starved (spZ (cb_regs C)) [] (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C)
    [(CRS_CID_B, cb_fpos C)] ly6 S5 Hp5 _ (k + k1 + k2 + k3) (STK_fuzz_alloc_ran_out (PI := prh_img_B)) []
    (sp2 - spZ (cb_regs C)) _ ch1 _ HS eq_refl HJ).
  - rewrite Hsp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hsp2c; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hsp2c as [q2 Hq2]. exists (2 * q2 - q1). lia.
  - lia.
  - exact EST30.
  - lia.
  - rewrite Hgp9. exact Hgp0.
  - rewrite Htp9. exact Htp0.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - rewrite EBASE, unsigned_lit_small; lia.
  - rewrite Hs0. replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. exact Hch.
  - intros HPRE1. apply (cxb_lift_x (fx := fxk) (SK := SK) SEGS B PST ARx R Rw).
    refine (HT_fuzz_alloc_ran_out fxk ly6 S5 Hp5 W6 (ms_regs ms) (ms_mem ms) _ ch1 Lam3 peak5 (c0 + Z.of_nat kw)
      SIZE_MAXZ ran5 (cb_most C) 0
      (crs_callee_fpre_B R CTX0 C fxk ly6 S5 Hp5 W6 _ (ms_mem ms) _ (k + k1 + k2 + k3) sp2 _ (ms_regs ms) _ ch1 HB9
        Hsp _ HPRE1) HL9).
    unfold raZ. rewrite Q1, EBASE, unsigned_lit_small by lia. lia.
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W7 c7 _ (ly7 & S7 & Hp7 & regs7 & mem7 & md7 & k4 & -> & HJc7 & HJ17 & HP7 & HQ7 & HMN7).
destruct HQ7 as (Hrm7 & Ha07 & -> & -> & Eab7 & HL7).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ17 by lia.
assert (HW10 : crs_ws_B CTX0 C fxk ly7 S5 Hp5 W7 regs7 mem7 md7 (k + k1 + k2 + k3 + k4) sp2 Lam3 peak5
   (c0 + Z.of_nat kw) SIZE_MAXZ ran5).
{ apply (crs_ws_callee_B HK CTX0 C fxk ly6 S5 Hp5 W6 (ms_regs ms) (ms_mem ms) _ (k + k1 + k2 + k3) sp2 Lam3 peak5
    _ _ _ _ ly7 S5 Hp5 W7 regs7 mem7 md7 k4 Lam3 peak5 _ _ _ HW9 HJ17 HJc7 HMN7 (cxb_ap3 _ _ HP7) (cxb_ap4 _ _ HP7)
    HL7 (Permutation_refl _)).
  - rewrite Eab7. apply Permutation_refl.
  - lia.
  - apply Hrm7. exact Hroom9. }
assert (HRS7 : crs_regsat_B regs7 (crs_rs_B C sp2)) by exact (cxb_regsat_ap _ _ _ HP7 (crs_rs_cs_B C sp2) HRS1).
assert (R23'' : getr regs7 23 = w64 0).
{ rewrite (cxb_ap _ _ 23%bv HP7) by (change (bv_unsigned (23%bv : bv 5)) with 23; unfold acallee_saved; lia).
  rewrite Q23. reflexivity. }
clear HW8 HW9 HJ HJ17 HS SHOK HEI HRS6 HRS1 Q1 Q3 Q4 Q23 Hm1 Hsp Hs0 Hch A55 A35 A36 G2 G8 ch1.
clear dependent ms. clear dependent mat.
(* ---- +676 beqz a0: a0 = g_ran_out (the ledger's ran5); 0 -> Z (+944), else F (+680) ---- *)
pose proof (crs_N_bnd_B C false 24 Hwl0 ltac:(lia)) as HN0. fold (cN0_B C) in HN0.
assert (HcntB : c0 + Z.of_nat kw < 2 ^ 62) by (unfold c0, crs_cnt1_B in *; lia).
set (E5 := TE (cb_regs C) regs7 []).
assert (HS : st_ok_pi SEGS VAL E5 (mkSS 3304 cur_atoms [] None (mkFacts [] [] []))
   (restrict (w_H W7) (@YK11.mkst fxk regs7 (Z_to_bv 64 (BASE + 3304)) mem7 (seg_rom SEGS)))).
{ apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS (SLit 0) [] E5 (mrestrict (w_H W7) mem7)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM E5) by apply te_env.
pose proof HW10 as (HB10 & _). pose proof HB10 as (_ & _ & _ & HJ & _).
unfold crs_JR_B in HJ.
pose (RUNTO := @paj_run_to_xR fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS R Rr Rt).
assert (A42 : ew E5 42 = getr regs7 10) by exact (te_cur (cb_regs C) regs7 [] 10%bv 10 eq_refl).
assert (A55 : ew E5 55 = getr regs7 23) by exact (te_cur (cb_regs C) regs7 [] 23%bv 23 eq_refl).
assert (A35 : ew E5 35 = getr regs7 3) by exact (te_cur (cb_regs C) regs7 [] 3%bv 3 eq_refl).
assert (A36 : ew E5 36 = getr regs7 4) by exact (te_cur (cb_regs C) regs7 [] 4%bv 4 eq_refl).
assert (Ura : bv_unsigned (ew E5 42) = ran5) by (rewrite A42, Ha07; unfold w64; apply unsigned_lit_small; lia).
clear Hc.
psrr_branch_tok RUN BR HS SHOK (2 ^ 63, 2 ^ 63).
- (* g_ran_out = 0: nothing was refused, to Z *)
  rewrite branch_eq_U, cxb_U0, U_SLit, Ura in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  clear Ura. subst ran5.
  paj_run_to_tok_x RUNTO HS HJ SHOK (2 ^ 63, 2 ^ 63) CRS_PC_Z_B.
  { apply awr_ok_nil. }
  assert (Hm1 : forall x, ms_mem ms x = mem7 x) by (intros x; apply HF; intros (r & Hr & _); destruct Hr).
  assert (HRS1 : crs_regsat_B (ms_regs ms) (crs_rs_B C sp2)).
  { apply (cxb_regsat_run (fx := fxk) (cb_regs C) regs7 [] _ _ ms _ HS); [|exact HRS7].
    unfold crs_rs_B, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B, crs_rro_B. cbn [app]. cxb_kept_regs. }
  prreg HS (23%bv : bv 5) Q23. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  rewrite A55, R23'' in Q23. rewrite A35 in Q3. rewrite A36 in Q4.
  pose proof (crs_ws_run_B HK CTX0 C fxk ly7 S5 Hp5 W7 regs7 mem7 md7 (k + k1 + k2 + k3 + k4) sp2 Lam3 peak5 _ _ _
    (ms_regs ms) (ms_mem ms) _ HW10 HJ Hm1 Q3 Q4) as HWz.
  destruct HWz as (HBz & HLz & HPz & Hpkz & Hroz & HDz & HTz).
  pmkst HS.
  replace (BASE + 3572) with (BASE + CRS_PC_Z_B) by (vm_compute; reflexivity).
  assert (Ecz : crs_cnt2_B C = c0 + Z.of_nat kw).
  { rewrite (Hk0 eq_refl). unfold crs_cnt2_B. change (ck_pick (cb_tb C) (cN1_B C)) with kp. unfold c0.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
  apply (KcZ fxk ly7 S5 Hp5 W7 (ms_regs ms) (ms_mem ms) _ (k + k1 + k2 + k3 + k4) sp2 Lam3 peak5 Hdoc HBz).
  + exact (cxb_regsat_snoc C sp2 _ 23%bv 0 HRS1 Q23).
  + split; [|exact HPz]. rewrite Ecz.
    split; [exact HLz|]. split; [lia|]. split; [rewrite Hran0; reflexivity|]. split; [lia|].
    split; [lia|]. split; [exact Hroz|].
    intros _. destruct (Hexact eq_refl) as (hz & Hhz). exists hz. unfold crs_evs_at_Z_B.
    rewrite length_app, Nat.add_assoc. exact Hhz.
  + exact HDz.
  + exact HTz.
- rewrite branch_eq_U, cxb_U0, U_SLit, Ura in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc.
  assert (Er : ran5 = 1) by lia.
  (* refuted: nothing was refused (K0-DEAD-PJWRITE, Hr5e) *)
  exfalso. lia.
Qed.

End f.
End d.

(* the closing lemma, elaborated (the class position of each kit predicate holds the entry fx; fxk is crs_cfg's
   explicit current state) and its assumptions *)
Set Printing Implicit.
About crs_seg_X2_B.
Unset Printing Implicit.
Print Assumptions crs_seg_X2_B.
