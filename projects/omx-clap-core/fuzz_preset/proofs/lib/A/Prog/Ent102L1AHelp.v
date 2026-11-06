(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L1AHelp.v, with its module paths and module names changed; 604 of its 669 lines of code are new or changed and 106 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): the SUPPORT
   LEMMAS of segment L1 of LLVMFuzzerTestOneInput (entry 0x815e0), listing +0x124 .. +0x148 (A' 0x81704 .. 0x8172c),
   for the segment proof lib/A/Prog/Ent102L1A.v. No function is proved here: a concrete step rule over the listing at a
   GENERIC image ({PA : PAImg A_prog_listing}, the PAListing PL_102_A), the program-call rule at a concrete call state
   of this body, the cut invariant ec_inv across a call and across the body's own store to g_own_ran_out, and the
   empty payload's src_rd.
   STATEMENT read: lib/A/Ent102CutsA.v, written against blob c84ca4b8df62 (the R-generic text: ec_invR R with
   its wild budget wk (journal ajournal_xwR R at a budget WS, wbudget [] wk WS) and its (os_c, i_c) room position,
   ec_inv_wle', ec_pre with `length (e_os E) <= 3`, ec_frame, ec_saved, ec_own, ec_cno_evs / l1_cno_evs, ec_img's
   ei_pst / ei_pst_ro / ei_sio / ei_sio_frame / ei_empty / ei_frame, ec_hyps' ech_hull_pay).
   THE RE-HIDING MOVE (check_no_overread frees, so segment L1 runs at wle' segs RZ_cf, Ent102CutsA.v ec_laneR WLE'):
   sections K and C are stated OVER A WORLD RELATION Rel (YA0nH.SRrG, the journals at YCbqG.ajournal_xwR Rel, INV at
   ec_invR Rel), as the B' twin lib/AU/Prog/Ent102L1BHelp.v (blob 5b659353bb75) states them, A' names; the plain step
   l1_step_gen is the instance of l1_step_genR at wle; a `jal` slot steps by Ent102L6AfLem.v l6f_step_callR.
   LISTING: lib/A/Listing_prog.v blob 1ab147923c5d (slot k = byte offset 4k from the entry), through the PAListing
   PL_102_A of lib/A/Ent102PLA.v; lib/A/PAImg_prog.v is not loaded, no vm_compute on pa_val / pa_sigma.
   THE KIT TEXTS: lib/A/PRH_Base.v (fpre, fpost, fpostF, prh_ledger and its named projections, pi_frame_nonneg).
   SHARED HELPERS USED: lib/A/Prog/Ent102CallA.v (ec_chain_at) and
   lib/A/Prog/Ent102L6AfLem.v (l6f_garr8_kept, l6f_rd64_kept, l6f_land_neg32, l6f_zmaxl_in, l6f_pc4).
   rule 24: proves function LLVMFuzzerTestOneInput, segment L1 (reuse search: the proof index by name
   LLVMFuzzerTestOneInput exit 0, the fuzz_preset hits are the released plain / ubsan contract definitions only; by
   address 0x815e0 exit 4; check CONFIRM 14:51Z: NEW walk on the #102 pins). This file: support lemmas
   of that segment.
   RESTATED HERE from other files (each under an l1_ name):
   - l1_step_gen: lib/A/Prog/Ent102L6AfLem.v l6f_step_addi (:214-234), the step
     equation an argument;
   - l1_call / l1_callF: lib/Reusable/YCbqGcall.v aj_call_x_sp / aj_call_xF_sp, at a concrete call state (no symbolic
     state);
   - l1_inv_after: lib/B/Prog/EntCallB.v eb_inv_after (old image B, the family lead's l4ref copy :256-320), over this
     cut file's ec_inv;
   - l1_frame_keep: lib/B/Prog/EntS3B.v es3_frame_keep's form (same reading, l4ref/EntS3B.v:558-605);
   - l1_bb: EntS3B.v es3_bb (l4ref/EntS3B.v:416-421).
   NUMERALS: 8 / 16 / 104 / 120 / 128 / 144 are LENGTHs of this frame (EC_SAVE, EC_FRAME_BYTES, the saved block and
   the flag-pointer slot); 2 ^ 40 / 2 ^ 47 / 2 ^ 64 are the engine's code-span, stack and word ranges; 4096 is the
   engine's low page; 32768 is LLVMF_STK. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem Ent102CallA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Pure facts. *)
Ltac IN := repeat (first [left; reflexivity | right]).
Lemma l1_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof.
intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hz.
Qed.

Lemma l1_ap_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma l1_fk_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* blocks_bytes is the byte sum of the block list (as EntS3B.v es3_bb) *)
Lemma l1_bb : forall B ly S, blocks_bytes S = fold_right (fun b acc => snd b + acc) 0 (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.

Lemma l1_sum_perm : forall l l' : list (Z * Z), Permutation l l' ->
  fold_right (fun b acc => snd b + acc) 0 l = fold_right (fun b acc => snd b + acc) 0 l'.
Proof. intros l l' H. induction H; cbn; lia. Qed.

Lemma l1_bb_perm : forall B ly S ly' S', Permutation (ablocks B ly S) (ablocks B ly' S') ->
  blocks_bytes S = blocks_bytes S'.
Proof. intros B ly S ly' S' H. rewrite (l1_bb B ly S), (l1_bb B ly' S'). exact (l1_sum_perm _ _ H). Qed.

(* the empty overlay's writable byte is writable at every overlay (wview reads the overlay first) *)
Lemma l1_writable_any : forall segs (m : word -> option byte) a,
  writable_at segs (fun _ => None) a -> writable_at segs m a.
Proof.
intros segs m a H. unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [discriminate | exact H].
Qed.

(* the frame's base A = (sp0 - 128) & -32 is sp0 - 128 or sp0 - 144, 32-aligned *)
Lemma l1_A_bounds : forall sp0, 128 <= sp0 -> sp0 mod 16 = 0 ->
  sp0 - 144 <= ec_A sp0 <= sp0 - 128 /\ ec_A sp0 mod 32 = 0.
Proof.
intros sp0 H0 H16. unfold ec_A, EC_SAVE. rewrite (l6f_land_neg32 (sp0 - 128)) by lia.
pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)) as M.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. A concrete step at a generic image: one plain slot, its step equation an argument. *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {PA : @PAImg rc A_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).

(* over a world relation Rel (YA0nH.SRrG; a step keeps the world, so the proof is the plain one over YSRrG.SRrG_step);
   the plain name is its instance at wle *)
Lemma l1_step_genR : forall (Rel : world SEGS -> world SEGS -> Prop) (W : world SEGS) (regs regs' : bvmap 5 word)
  (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z),
  0 <= k < 2 ^ 40 ->
  (forall m, RiscvSemantics.step SEGS (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) m (YK11.seg_rom SEGS)) =
     MachineOk (@YK11.mkst fx regs' (v_addi (Z_to_bv 64 (BASE + k)) 4) m (YK11.seg_rom SEGS))) ->
  (forall X, SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros Rel W regs regs' mem md Q k Hk Hst HK.
eapply (SRrG_step SEGS Rel (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)). exact (Hst _).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (l6f_pc4 k Hk). apply HK.
Qed.
Lemma l1_step_gen : forall (W : world SEGS) (regs regs' : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z),
  0 <= k < 2 ^ 40 ->
  (forall m, RiscvSemantics.step SEGS (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) m (YK11.seg_rom SEGS)) =
     MachineOk (@YK11.mkst fx regs' (v_addi (Z_to_bv 64 (BASE + k)) 4) m (YK11.seg_rom SEGS))) ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof. exact (l1_step_genR (@wle SEGS)). Qed.
End S.

(* ---------------------------------------------------------------------- *)
(* 3. The program-call rule at a concrete call state (YCbqGcall.v aj_call_x_sp / aj_call_xF_sp, the symbolic state
      left out: the caller hands the callee-entry machine state in mkst form), OVER A WORLD RELATION Rel (the free
      move: segment L1 runs at wle' segs RZ_cf, YA0nH.SRrG): the caller's journal, the callee's post and the conclusion
      are at Rel (YCbqG.ajournal_xwR / apost_base_xR, YCbqGwild.apost_base_xbFR); Rel transitive composes them. *)
Section K. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable PST : list (Z * Z).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
Variable Rel : world SEGS -> world SEGS -> Prop.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARc Rel).
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARc Rel).

Lemma l1_LAWS : AR_laws_x SEGS B ARc cf_head.
Proof. exact (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)). Qed.

(* A CALLEE WHOSE TEXT DOES NOT FREE (fuzz_alloc_ran_out_reset, fuzz_alloc_most): its plain SRr and its post at wle
   read at any Rel containing wle (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift / ajournal_xwR_mono) *)
Lemma l1_lift_call : forall (Rel_wle : forall W W', wle W W' -> Rel W W') (W : world SEGS) c STK FP regs ly S Hp
  (W0 : world SEGS) mem md
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr SEGS W c (apost_base_x (SK := SK) SEGS B PST ARc STK FP regs ly S Hp W0 mem md Q) ->
  SRrG SEGS Rel W c (apost_base_xR (SK := SK) SEGS B PST ARc Rel STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel_wle W c STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG SEGS Rel Rel_wle W c _ H)|].
intros W' c' _ HQ. exact (YCbqG.apost_base_x_R_lift SEGS B PST ARc Rel Rel_wle _ _ _ _ _ _ _ _ _ _ _ _ HQ).
Qed.
(* the budgeted float form (check_no_overread's plain text): the same lift *)
Lemma l1_lift_callF : forall (Rel_wle : forall W W', wle W W' -> Rel W W') (W : world SEGS) c (P : list (list Z) -> Prop)
  STK FP regs ly S Hp (W0 : world SEGS) mem md
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  SRr SEGS W c (YCbqGwild.apost_base_xbF (fx := fx) (SK := SK) SEGS B PST ARc P STK FP regs ly S Hp W0 mem md Q) ->
  SRrG SEGS Rel W c (YCbqGwild.apost_base_xbFR (fx := fx) (SK := SK) SEGS B PST ARc Rel P STK FP regs ly S Hp W0 mem md Q).
Proof.
intros Rel_wle W c P STK FP regs ly S Hp W0 mem md Q H.
eapply SRrG_mono; [exact (SRr_SRrG SEGS Rel Rel_wle W c _ H)|].
intros W' c' _ (fx' & ly' & S' & Hp' & regs' & mem' & md' & k & WS & Hc & Hz & Hk & HP & HJ & Hr & HQ).
exists fx', ly', S', Hp', regs', mem', md', k, WS.
split; [exact Hc|]. split; [exact Hz|]. split; [exact Hk|]. split; [exact HP|].
split; [|split; [exact Hr | exact HQ]].
eapply YCbqG.ajournal_xwR_mono; [exact Rel_wle | exact HJ].
Qed.

Lemma l1_call : forall (W : world SEGS) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp (W0 : world SEGS) mem md own
  lyc Sc Hpc k WS0 STK1 FP1 (o : Z) raw ch1 (pc : Z)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regs) ch1 ->
  (afn_pre_x SEGS B ARc STK1 lyc Sc Hpc W regs memc mdc ch1 ->
   SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (apost_base_xR (SK := SK) SEGS B PST ARc Rel STK1 FP1 regs lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
      c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
      AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS0 /\
      AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
      aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k WS0 STK1 FP1 o raw ch1 pc Q
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B PST ARc Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc
    Hpc W memc mdc k WS0 regs STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
assert (EW : WS0 ++ [] = WS0) by apply List.app_nil_r. rewrite <- EW.
change own with ([] ++ own).
eapply (ajournal_xw_subR SEGS B PST ARc l1_LAWS pa_segs_low Rel Rel_trans); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

Lemma l1_callF : forall (W : world SEGS) (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp (W0 : world SEGS) mem md own
  lyc Sc Hpc k WS0 STK1 FP1 (o : Z) raw ch1 (pc : Z) (P : list (list Z) -> Prop)
  (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJW STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k WS0 ->
  spZ regs = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regs) ch1 ->
  (afn_pre_x SEGS B ARc STK1 lyc Sc Hpc W regs memc mdc ch1 ->
   SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (YCbqGwild.apost_base_xbFR (fx := fx) (SK := SK) SEGS B PST ARc Rel P STK1 FP1 regs lyc Sc Hpc W memc mdc Q)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
      c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
      frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\ P WS1 /\
      AJW STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) (WS0 ++ WS1) /\
      AJW STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 /\
      aregs_preserved regs regs2 /\ Q ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k WS0 STK1 FP1 o raw ch1 pc P Q
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRrG_mono.
{ apply Hcallee. eapply (YCbqGwild.afn_pre_x_at_wR (SK := SK) SEGS B PST ARc Rel STK sp0 FP ly S Hp W0 mem md own lyc Sc
    Hpc W memc mdc k WS0 regs STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ1 & HP & HQ).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. rewrite Hra. split; [reflexivity|].
split; [exact HFZ|]. split; [exact HFK|]. split; [exact HPW|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
eapply (ajournal_xw_subR SEGS B PST ARc l1_LAWS pa_segs_low Rel Rel_trans); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
End K.

(* ---------------------------------------------------------------------- *)
(* 4. The cut invariant of this body (Ent102CutsA.v's ec_inv) across a call, across the body's own store to a PST byte,
      and the call from a state it describes. *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
(* THE WORLD RELATION (INV follows its users: segment L1 runs at wle' segs RZ_cf, both before and across
   check_no_overread's frees): the cut invariant and the journals are at Rel (Ent102CutsA.v ec_invR, YCbqG.v
   ajournal_xwR); Rel transitive composes a call's journal with the caller's *)
Variable Rel : world SEGS -> world SEGS -> Prop.
Hypothesis Rel_trans : forall W1 W2 W3, Rel W1 W2 -> Rel W2 W3 -> Rel W1 W3.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARc Rel).
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARc Rel).
#[local] Notation INV := (@ec_invR fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_SIO Rel).
#[local] Notation IMG := (@ec_img rc cp PI A_prog_listing PA B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG).
#[local] Notation PRE := (@ec_pre fx rc ci cp PI RL A_prog_listing PA B EC_RA EC_EMPTY EC_SIO).

(* ec_pre's parts this segment reads, BY NAME (type-directed by Ent102CallA.v's ec_conj_pick, so a conjunct added to
   ec_pre moves none of them; the payload / length / bytes / + 8 parts are Ent102CallA.v's ec_pre_payload / _len /
   _bytes / _pay8) *)
Lemma l1_pre_afn : forall E, PRE E ->
  afn_pre_x SEGS B ARc LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [].
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_s0 : forall E, PRE E -> s0Z (e_regs E) < YM05.alloc_ceiling.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_ra : forall E, PRE E -> raZ (e_regs E) = EC_RA.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_frames : forall E, PRE E -> frames (e_S E) = [].
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_i0 : forall E, PRE E -> e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_ro : forall E, PRE E ->
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
    (aview SEGS (w_H (e_W E)) (e_mem E)).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_sio : forall E, PRE E -> EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E)).
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_cnt : forall E, PRE E -> e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
Lemma l1_pre_sm : forall E, PRE E -> e_sm E = ReaderRes.jr_strtod.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.
(* at most 3 earlier calls (Ent102CutsA.v ec_pre's `length (e_os E) <= 3`): the hull budget's position premise *)
Lemma l1_pre_os : forall E, PRE E -> (length (e_os E) <= 3)%nat.
Proof. intros E H. unfold ec_pre in H. ec_conj_pick H. Qed.

(* a read-only byte of the listing's view is an image byte *)
Lemma l1_ro_img : forall a, in_roP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) a ->
  in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)].
Qed.

(* the frame geometry the body's call sites read from the cut's entry premise *)
Lemma l1_geo : forall E fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k osc ic wk,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk ->
  YM05.alloc_ceiling + LLVMF_STK <= e_sp0 E <= 2 ^ 47 /\ e_sp0 E mod 16 = 0 /\
  e_sp0 E - 144 <= e_A E <= e_sp0 E - 128 /\ e_A E mod 32 = 0 /\
  e_sp0 E <= ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk HI.
destruct HI as ((WSj & HJ & _) & _ & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof (l1_pre_afn E HPRE) as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HJ as (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Eshi & _).
pose proof (l1_A_bounds (e_sp0 E)) as HA. unfold e_A.
unfold e_sp0 in *. unfold LLVMF_STK in *.
pose proof asan_consts as (C1 & _).
destruct (HA ltac:(lia) Hal16) as (HA1 & HA2).
rewrite Etop, Eshi. repeat split; lia.
Qed.

(* the invariant across a materialization of the model (a straight-line step's model) *)
Lemma l1_inv_mat : forall E fk ly S Hp (W : world SEGS) mem md own Lam peak cnt ran k osc ic wk X,
  INV E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk ->
  INV E fk ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) own Lam peak cnt ran k osc ic wk.
Proof.
intros E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk X ((WS & HJ & Hwb) & HR). split; [|exact HR].
(* a no-call stretch at the same budget: the cut file's ec_inv_wk_growR (wk <= wk) *)
eapply ec_inv_wk_growR with (LAWS := l1_LAWS (rc := rc) (cp := cp) (PA := PA) B);
  [exact HJ | exact Hwb | apply Nat.le_refl].
Qed.

Lemma l1_inv_after : forall E fk lyc Sc Hpc (Wc : world SEGS) memc mdc own Lam peak cnt ran k osc ic wk
    STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 k2 Lam2 peak2 cnt2 ran2 osc2 ic2 wk2 WS1 WS2,
  IMG ->
  INV E fk lyc Sc Hpc Wc memc mdc own Lam peak cnt ran k osc ic wk ->
  AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 k2 WS2 ->
  YCbqGwild.wbudget [] wk2 WS2 ->
  AJW STK1 sp1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (exists most own, @prh_ledger rc cp PI A_prog_listing PA B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 SIZE_MAX ran2 most own) ->
  @room_live_cf RL S2 ->
  (* the cut's room position after the call: its own (os, index) pair, the callee's exact post *)
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) osc2 ic2 (e_H0 E) hist S2) ->
  e_cnt E <= cnt2 <= e_cnt E + LCNT ->
  Permutation (ablocks B ly2 S2) (ck_hblks Lam2 ++ ablocks B (e_ly E) (e_S E)) ->
  YAkMemnorm.memnorm SEGS mem2 ->
  INV E fk ly2 S2 Hp2 W2 mem2 md2 own Lam2 peak2 cnt2 ran2 k2 osc2 ic2 wk2.
Proof.
intros E fk lyc Sc Hpc Wc memc mdc own Lam peak cnt ran k osc ic wk STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 k2 Lam2 peak2
  cnt2 ran2 osc2 ic2 wk2 WS1 WS2 HIMG HI HJ2 Hwb2 HJ1 HL2 HRL2 HRP2 HC2 HP2 HMN2.
destruct HI as ((WSc & HJc & _) & HOWN & _ & _ & _ & _ & _ & _ & HPRE & _ & _ & _ & _).
pose proof (ec_pre_payload (fx := fx) (cp := cp) (PI := PI) (RL := RL) (PA := PA) B EC_RA EC_EMPTY EC_SIO HPRE) as Hpay.
pose proof (l1_pre_ro E HPRE) as HROD. pose proof (l1_pre_sio E HPRE) as HSIO0.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
pose proof HJ1 as (_ & Hly1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrsc & _).
assert (Hsp : forall a, fp_spares (SK := SK) [] a) by (intros a; exact (fp_spares_closed [] a sink_closed_nil)).
pose proof (ei_sio _ _ _ _ _ _ HIMG) as Hsio.
pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as Hsiof.
pose proof (ei_pst_ro _ _ _ _ _ _ HIMG) as Hpstro.
(* the payload block is an entry block, so it is a block of the return state too *)
assert (Hpay2 : e_n E = 0 \/ (In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E)) /\ In (e_p E, e_n E) (ablocks B ly2 S2))).
{ destruct Hpay as [[Hn0 _] | [_ Hin]]; [left; exact Hn0 | right].
  split; [exact Hin|]. apply (Permutation_in _ (Permutation_sym HP2)). apply in_or_app. right. exact Hin. }
unfold ec_invR.
split; [exists WS2; split; [exact HJ2 | exact Hwb2]|].
split.
{ (* ec_own: the fake frame's address and flag word, through the callee journal's frames clause *)
  destruct HOWN as (pos & Hown & Hfa & Hfk0 & Hfl).
  destruct Hly1 as (_ & _ & _ & _ & _ & EF & _).
  assert (Efa : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr lyc LLVMF_FS_CLASS pos)
    by (unfold frame_addr; rewrite EF; reflexivity).
  assert (Efl : flag_addr ly2 LLVMF_FS_CLASS pos = flag_addr lyc LLVMF_FS_CLASS pos)
    by (unfold flag_addr; rewrite EF; reflexivity).
  exists pos. split; [exact Hown|]. split; [rewrite Efa; exact Hfa|]. split; [exact Hfk0|]. rewrite Efl.
  assert (HinF : In (LLVMF_FS_CLASS, pos) (frames Sc)) by (rewrite Hfrsc, Hown; left; reflexivity).
  assert (Hfb : fs_frame_bytes LLVMF_FS_CLASS = 128) by reflexivity.
  intros j Hj.
  assert (Hzr : in_zr (fk + EC_FRAME_BYTES - 8 + Z.of_nat j) (frame_rng lyc (LLVMF_FS_CLASS, pos))).
  { unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfb, <- Hfa. unfold EC_FRAME_BYTES. lia. }
  rewrite (G4 LLVMF_FS_CLASS pos _ HinF (or_introl Hzr) (inFP_nil _)). exact (Hfl j Hj). }
split; [exact HL2|].
split.
{ (* the stdio half, from the entry *)
  apply (Hsiof (aview SEGS (w_H (e_W E)) (e_mem E))); [|exact HSIO0].
  intros a Ha. destruct (Hsio a Ha) as ((Hno & Her) & Hi & Hnp).
  exact (F3 a Hi Hno Her Hnp (Hsp a)). }
split.
{ (* the read-only view, from the entry *)
  intros a Hro Hno Her.
  rewrite (F3 a (l1_ro_img a Hro) Hno Her (fun Hq => Hpstro a Hq Hro) (Hsp a)).
  exact (HROD a Hro Hno Her). }
split; [exact HRL2|]. split; [exact HRP2|]. split; [exact HC2|]. split; [exact HPRE|].
split.
{ destruct Hpay2 as [Hn0 | [_ Hin2]]; [left; exact Hn0 | right; exact Hin2]. }
split; [exact HP2|].
split; [|exact HMN2].
intros i Hi. destruct Hpay2 as [Hn0 | [Hin Hin2]]; [lia|].
pose proof (req_size_pos (e_n E) ltac:(lia)) as [_ Hrq].
exact (F2 (e_p E) (e_n E) i Hin Hin2 ltac:(lia) (inFP_nil _)).
Qed.

(* the frame (saved block, shadow, alignment) across a call made at sp1 <= sp0 - 128 with an empty footprint *)
Lemma l1_frame_keep : forall E fk lyc Sc Hpc (Wc : world SEGS) memc mdc own Lam peak cnt ran k osc ic wk
    STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 WS1,
  INV E fk lyc Sc Hpc Wc memc mdc own Lam peak cnt ran k osc ic wk ->
  AJW STK1 sp1 [] lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  sp1 <= e_sp0 E - 128 ->
  ec_frame E fk Wc memc -> ec_frame E fk W2 mem2.
Proof.
intros E fk lyc Sc Hpc Wc memc mdc own Lam peak cnt ran k osc ic wk STK1 sp1 ly2 S2 Hp2 W2 mem2 md2 k1 WS1 HI HJ1 Hsp1
  HF.
pose proof (l1_geo E fk lyc Sc Hpc Wc memc mdc own Lam peak cnt ran k osc ic wk HI) as (G1 & G2 & _).
destruct HI as ((WSc & HJc & _) & HOWN & _).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & G4 & _).
pose proof HJc as (_ & _ & _ & _ & _ & Hfrsc & _).
pose proof asan_consts as (C1 & _).
unfold LLVMF_STK in G1.
destruct HF as (HS & Hsh & Hal).
assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
  rd64 (aview SEGS (w_H Wc) memc) a v -> rd64 (aview SEGS (w_H W2) mem2) a v).
{ intros a v H1 H2 H. apply (l6f_rd64_kept (aview SEGS (w_H Wc) memc)); [|exact H].
  intros i Hi. apply F1; lia. }
destruct HS as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
split.
{ unfold ec_saved. repeat split; (eapply KS; [lia | lia | eassumption]). }
split; [|exact Hal].
destruct HOWN as (pos & Hown & Hfa & _ & _).
assert (HinF : In (LLVMF_FS_CLASS, pos) (frames Sc)) by (rewrite Hfrsc, Hown; left; reflexivity).
apply (l6f_garr8_kept (w_H Wc) (w_H W2) memc mem2); [|exact Hsh].
intros i Hi. change (Z.of_nat (length ec_frame_shadow)) with 16 in Hi.
apply (G4 LLVMF_FS_CLASS pos _ HinF); [|exact (inFP_nil _)].
right. unfold in_zr. cbn [fst snd]. rewrite <- Hfa. change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia.
Qed.

(* the cut invariant across the body's own one-byte store to a PST byte a0 (the `sb zero` to g_own_ran_out): every
   byte the invariant reads but a0 is kept, and a0 is no stdio byte, no read-only byte, no frame or block byte *)
Lemma l1_inv_store : forall E fk ly S Hp (W : world SEGS) mem md mem' md' own Lam peak cnt ran k osc ic wk WS' a0,
  IMG -> INV E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk -> ec_frame E fk W mem ->
  Exists (in_zr a0) PST ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> a0 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly S Hp W mem' md' k WS' ->
  YCbqGwild.wbudget [] wk WS' ->
  (exists most own, @prh_ledger rc cp PI A_prog_listing PA B ly S Hp W mem' Lam peak cnt SIZE_MAX ran most own) ->
  YAkMemnorm.memnorm SEGS mem' ->
  INV E fk ly S Hp W mem' md' own Lam peak cnt ran k osc ic wk /\ ec_frame E fk W mem'.
Proof.
intros E fk ly S Hp W mem md mem' md' own Lam peak cnt ran k osc ic wk WS' a0 HIMG HI HF Ha0 HK HJ' Hwb' HL' HMN'.
pose proof (l1_geo E fk ly S Hp W mem md own Lam peak cnt ran k osc ic wk HI) as (G1 & G2 & _).
destruct HI as ((WS0 & HJ & _) & HOWN & _ & HSIO & HROD & HRL & HRP & HC & HPRE & HNC & HPERM & HBY & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in G1.
pose proof (ei_pst _ _ _ _ _ _ HIMG) as Hpst.
pose proof (ei_sio _ _ _ _ _ _ HIMG) as Hsio.
pose proof (ei_sio_frame _ _ _ _ _ _ HIMG) as Hsiof.
pose proof (ei_pst_ro _ _ _ _ _ _ HIMG) as Hpstro.
destruct (Hpst a0 Ha0) as (_ & Hi0).
pose proof (pa_segs_low a0 Hi0) as Hlo0.
(* a byte off the image (or above it) is not a0 *)
assert (NI : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha Hni. apply HK; [exact Ha|]. intros ->. exact (Hni Hi0). }
assert (HI' : INV E fk ly S Hp W mem' md' own Lam peak cnt ran k osc ic wk).
{ unfold ec_invR.
  split; [exists WS'; split; [exact HJ' | exact Hwb']|].
  split.
  { destruct HOWN as (pos & Hown & Hfa & Hfk0 & Hfl).
    exists pos. split; [exact Hown|]. split; [exact Hfa|]. split; [exact Hfk0|].
    assert (HinF : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, Hown; left; reflexivity).
    destruct (alx_sep SEGS B ARc (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) ly S Hp W mem md HAR) as (_ & Hfor).
    rewrite Forall_forall in Hfor. destruct (Hfor (LLVMF_FS_CLASS, pos) HinF) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
    change (fs_frame_bytes LLVMF_FS_CLASS) with 128 in Hhi.
    apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hfl].
    intros i Hi. unfold EC_FRAME_BYTES. apply NI; [rewrite <- Hfa in Hlo, Hhi; lia|].
    intros Himg.
    apply (proj2 (alx_client_img SEGS B ARc (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) ly S Hp W mem md (fk + 128 - 8 + i) HAR
      ltac:(right; left; exists LLVMF_FS_CLASS, pos; split; [exact HinF | change (fs_frame_bytes LLVMF_FS_CLASS) with 128; rewrite <- Hfa; lia]))).
    exact Himg. }
  split; [exact HL'|].
  split.
  { apply (Hsiof (aview SEGS (w_H W) mem)); [|exact HSIO].
    intros a Ha. destruct (Hsio a Ha) as (_ & Hi & Hnp). pose proof (pa_segs_low a Hi) as Hl.
    apply HK; [lia|]. intros ->. exact (Hnp Ha0). }
  split.
  { intros a Hro Hno Her. pose proof (pa_segs_low a (l1_ro_img a Hro)) as Hl.
    rewrite HK; [exact (HROD a Hro Hno Her) | lia |]. intros ->. exact (Hpstro a0 Ha0 Hro). }
  split; [exact HRL|]. split; [exact HRP|]. split; [exact HC|]. split; [exact HPRE|]. split; [exact HNC|].
  split; [exact HPERM|].
  split; [|exact HMN'].
  intros i Hi. rewrite <- (HBY i Hi).
  destruct HNC as [Hn0 | Hin]; [lia|].
  destruct (alx_blocks SEGS B ARc (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) ly S Hp W mem md (e_p E) (e_n E) HAR Hin) as (_ & H4096 & Hc & _).
  pose proof (req_size_pos (e_n E) ltac:(lia)) as [_ Hrq].
  apply NI; [lia|]. intros Himg.
  apply (proj2 (alx_client_img SEGS B ARc (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) ly S Hp W mem md (e_p E + i) HAR
    ltac:(left; exists (e_p E), (e_n E); split; [exact Hin | lia]))).
  exact Himg. }
split; [exact HI'|].
destruct HF as (HS & Hsh & Hal).
assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
  rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W) mem') a v).
{ intros a v H1 H2 H. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact H].
  intros i Hi. apply HK; [lia | lia]. }
destruct HS as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
split.
{ unfold ec_saved. repeat split; (eapply KS; [lia | lia | eassumption]). }
split; [|exact Hal].
destruct HOWN as (pos & Hown & Hfa & _ & _).
assert (HinF : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, Hown; left; reflexivity).
destruct (alx_sep SEGS B ARc (l1_LAWS (rc := rc) (cp := cp) (PA := PA) B) ly S Hp W mem md HAR) as (_ & Hfor).
rewrite Forall_forall in Hfor. destruct (Hfor (LLVMF_FS_CLASS, pos) HinF) as (Hlo & Hhi). cbn [fst snd] in Hlo, Hhi.
change (fs_frame_bytes LLVMF_FS_CLASS) with 128 in Hhi. rewrite <- Hfa in Hlo, Hhi.
assert (Esh : shadow_addr fk = SHADOW_OFF + fk / 8) by reflexivity.
assert (Hq0 : 0 <= fk / 8) by (apply Z.div_pos; lia).
assert (Hq8 : 8 * (fk / 8) <= fk) by (apply Z.mul_div_le; lia).
apply (l6f_garr8_kept (w_H W) (w_H W) mem mem'); [|exact Hsh].
intros i Hi. change (Z.of_nat (length ec_frame_shadow)) with 16 in Hi.
apply HK; rewrite Esh; unfold SHADOW_OFF, kLowMemEnd in *; lia.
Qed.

(* the ledger across the store: the six other cells (g_live .. g_ran_out, g_most) are off the own byte (ei_pst_sep), the
   own cell reads the stored 0, and at Lam = [] the blocks part says nothing about memory *)
Lemma l1_ledger_store : forall ly S Hp (W : world SEGS) mem mem' peak cnt fail ran most own a0,
  @prh_ledger rc cp PI A_prog_listing PA B ly S Hp W mem [] peak cnt fail ran most own ->
  YG0f.pairwise zdisjoint PST ->
  in_zr a0 (@pi_g_own_ran_out PI, Z.of_nat (@pi_gz_own_ran_out PI)) ->
  (forall a, Exists (in_zr a) PST -> 0 <= a < 2 ^ 64) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> a0 ->
     mbyte SEGS (mrestrict (w_H W) mem') a = mbyte SEGS (mrestrict (w_H W) mem) a) ->
  @prh_own rc PI A_prog_listing PA W mem' 0 ->
  @prh_ledger rc cp PI A_prog_listing PA B ly S Hp W mem' [] peak cnt fail ran most 0.
Proof.
intros ly S Hp W mem mem' peak cnt fail ran most own a0 HL Hsep Ha0 Hrng HK HO'.
pose proof (PRH_Base.prh_ledger_live B ly S Hp W mem [] peak cnt fail ran most own HL) as V1.
pose proof (PRH_Base.prh_ledger_peak B ly S Hp W mem [] peak cnt fail ran most own HL) as V2.
pose proof (PRH_Base.prh_ledger_count B ly S Hp W mem [] peak cnt fail ran most own HL) as V3.
pose proof (PRH_Base.prh_ledger_fail B ly S Hp W mem [] peak cnt fail ran most own HL) as V4.
pose proof (PRH_Base.prh_ledger_ran B ly S Hp W mem [] peak cnt fail ran most own HL) as V5.
pose proof (PRH_Base.prh_ledger_most B ly S Hp W mem [] peak cnt fail ran most own HL) as (V6 & V6b).
pose proof (PRH_Base.prh_ledger_bounds B ly S Hp W mem [] peak cnt fail ran most own HL) as VB.
pose proof (PRH_Base.prh_ledger_heads B ly S Hp W mem [] peak cnt fail ran most own HL) as VH.
unfold prh_pst in Hsep. cbn [YG0f.pairwise] in Hsep.
destruct Hsep as (P1 & P2 & P3 & P4 & P5 & P6 & _).
unfold in_zr in Ha0. cbn [fst snd] in Ha0.
(* a cell c that is disjoint from the own cell and lies in PST keeps its bytes *)
assert (KC : forall c w v, Exists (fun r => r = (c, Z.of_nat w)) (prh_pst (PI := PI)) ->
  zdisjoint (c, Z.of_nat w) (@pi_g_own_ran_out PI, Z.of_nat (@pi_gz_own_ran_out PI)) ->
  val_mem SEGS (mrestrict (w_H W) mem) c w v -> val_mem SEGS (mrestrict (w_H W) mem') c w v).
{ intros c w v Hc Hd Hv. apply (prh_val_mem_keep _ _ c w v Hv). intros kk Hkk.
  apply HK.
  - apply Hrng. apply Exists_exists in Hc as (r & Hr & ->). apply Exists_exists. exists (c, Z.of_nat w).
    split; [exact Hr|]. unfold in_zr. cbn [fst snd]. lia.
  - unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Ep : forall (x : Z * Z) (l : list (Z * Z)), In x l -> Exists (fun r => r = x) l).
{ intros x l Hx. apply Exists_exists. exists x. split; [exact Hx | reflexivity]. }
unfold prh_ledger, prh_glob.
split.
- split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V1]|].
  { rewrite Forall_forall in P1. apply P1. cbn [In]. IN. }
  split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V2]|].
  { rewrite Forall_forall in P2. apply P2. cbn [In]. IN. }
  split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V3]|].
  { rewrite Forall_forall in P3. apply P3. cbn [In]. IN. }
  split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V4]|].
  { rewrite Forall_forall in P4. apply P4. cbn [In]. IN. }
  split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V5]|].
  { rewrite Forall_forall in P5. apply P5. cbn [In]. IN. }
  split; [split; [apply KC; [apply Ep; unfold prh_pst; cbn [In]; IN | | exact V6] | exact V6b]|].
  { rewrite Forall_forall in P6. apply P6. cbn [In]. IN. }
  split; [exact HO'|].
  exact VB.
- split; [constructor|]. split; [constructor | exact VH].
Qed.

(* the empty payload (n = 0, p = EC_EMPTY): src_rd of no bytes at the registered datum (ei_empty) *)
Lemma l1_src_empty : forall (E : @ecx rc A_prog_listing PA) (W : world SEGS) mem,
  IMG -> e_p E = EC_EMPTY -> Z.of_nat (length (e_x E)) = 0 ->
  src_rd W mem (e_p E) (e_x E).
Proof.
intros E W mem HIMG Hp0 HLx.
pose proof (ei_empty _ _ _ _ _ _ HIMG) as ((He1 & He2) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (e_x E) as [|x0 xs] eqn:Ex; [|cbn [length] in HLx; lia].
unfold src_rd. cbn [length Z.of_nat]. rewrite Hp0.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in He1, He2.
split; [intros j Hj; cbn [length] in Hj; lia|].
split; [lia|]. split; [lia|].
split; [unfold amem_range, kLowMemEnd; lia|].
split; [apply range_addressable_nil; lia | intros H; lia].
Qed.

(* THE CALL FROM A CUT STATE of this body (Hp = []): sp = A, s0 = sp0, gp / tp of the entry, ra a listing return
   site. Packs the chain (Ent102CallA.v ec_chain_at), fpre's last three conjuncts, l1_call and SRr_bind. *)
Lemma l1_call_cut : forall (fz : YK11.FPState) E fk ly S (W : world SEGS) mem md own Lam peak cnt ran k osc ic wk regs
  (pc ra STK1 : Z)
  (Qc : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world SEGS -> config -> Prop),
  INV E fk ly S [] W mem md own Lam peak cnt ran k osc ic wk -> ec_frame E fk W mem ->
  getr regs 2 = w64 (e_A E) -> getr regs 3 = getr (e_regs E) 3 -> getr regs 4 = getr (e_regs E) 4 ->
  getr regs 8 = w64 (e_sp0 E) -> getr regs 1 = Z_to_bv 64 ra -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  4096 <= ra < YM05.alloc_ceiling ->
  0 <= STK1 -> STK1 + 144 <= LLVMF_STK ->
  frm_zero (@YK11.fp_csr fz) ->
  (forall ch, (spine ch = [] \/ spine ch = [EC_RA]) ->
     fpre (fx := fz) B ARc STK1 ly S [] W regs mem md ch ->
     SRrG SEGS Rel W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md)
       (apost_base_xR (fx := fz) (SK := SK) SEGS B PST ARc Rel STK1 [] regs ly S [] W mem md Qc)) ->
  (forall (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 k1 WS, Rel W W2 -> YCbqGwild.wbudget [] wk WS ->
     AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 (k + k1) WS ->
     AJ STK1 (e_A E) [] ly S [] W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved regs regs2 -> Qc ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS Rel W2 (mkCfg (@YK11.mkst fz regs2 (Z_to_bv 64 ra) mem2 (YK11.seg_rom SEGS)) md2) R) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md) R.
Proof.
intros fz E fk ly S W mem md own Lam peak cnt ran k osc ic wk regs pc ra STK1 Qc R HI HF R2 R3 R4 R8 R1 Hret Hra STK0
  STKb HFZ0 Hcallee HK.
pose proof (l1_geo E fk ly S [] W mem md own Lam peak cnt ran k osc ic wk HI) as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof HI as ((WS0 & HJ & Hwb0) & _ & _ & _ & HROD & _ & _ & _ & HPRE & _).
pose proof (l1_pre_afn E HPRE) as (_ & _ & Hra40 & Hgp0 & Htp0 & _).
pose proof (l1_pre_s0 E HPRE) as Hs00. pose proof (l1_pre_ra E HPRE) as Hra0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in G1, STKb.
destruct HF as (HS & _ & _). destruct HS as (S8 & S16 & _).
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (e_A E) (e_sp0 E) (raZ (e_regs E)) (s0Z (e_regs E)) S8 S16
  ltac:(unfold raZ; apply bv_unsigned_in_range) ltac:(unfold s0Z; apply bv_unsigned_in_range) Hs00 Hra40
  ltac:(lia) ltac:(pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)); pose proof (Z.div_mod (e_sp0 E) 8 ltac:(lia));
                   pose proof (Z.mod_pos_bound (e_sp0 E) 8 ltac:(lia)); lia)
  ltac:(lia) ltac:(lia)) as (ch & Hch & Hsp).
rewrite Hra0 in Hsp.
assert (HspA : spZ regs = e_A E) by (unfold spZ; rewrite R2; apply l1_w64u; lia).
eapply (SRrG_bind SEGS Rel Rel_trans).
{ eapply (l1_call (fx := fz) B SK PST Rel Rel_trans W regs mem md LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S [] k WS0 STK1 [] (e_A E - e_sp0 E) (Z_to_bv 64 ra) ch pc Qc HJ).
  - rewrite HspA. lia.
  - pose proof (Z.div_mod (e_A E) 32 ltac:(lia)). pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)).
    replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia. apply Z.mod_mul. lia.
  - lia.
  - exact STK0.
  - unfold LLVMF_STK. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hret.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) by lia.
    unfold s0Z. rewrite R8, l1_w64u by lia. exact Hch.
  - intros Hafn. apply (Hcallee ch Hsp). split; [exact Hafn|]. split; [exact HROD|].
    split; [rewrite HspA; lia|].
    split; [unfold raZ; rewrite R1, unsigned_lit_small by lia; lia | exact HFZ0].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HP & HQ).
replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) in HJ1 by lia.
exact (HK W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS0 Hwle Hwb0 HJ2 HJ1 HP HQ).
Qed.

(* the same for a callee whose text changes the float state (apost_base_xF) *)
Lemma l1_call_cutF : forall (fz : YK11.FPState) E fk ly S (W : world SEGS) mem md own Lam peak cnt ran k osc ic wk regs
  (pc ra STK1 : Z) (P : list (list Z) -> Prop)
  (Qc : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (R : world SEGS -> config -> Prop),
  INV E fk ly S [] W mem md own Lam peak cnt ran k osc ic wk -> ec_frame E fk W mem ->
  getr regs 2 = w64 (e_A E) -> getr regs 3 = getr (e_regs E) 3 -> getr regs 4 = getr (e_regs E) 4 ->
  getr regs 8 = w64 (e_sp0 E) -> getr regs 1 = Z_to_bv 64 ra -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  4096 <= ra < YM05.alloc_ceiling ->
  0 <= STK1 -> STK1 + 144 <= LLVMF_STK ->
  frm_zero (@YK11.fp_csr fz) ->
  (forall ch, (spine ch = [] \/ spine ch = [EC_RA]) ->
     fpre (fx := fz) B ARc STK1 ly S [] W regs mem md ch ->
     SRrG SEGS Rel W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md)
       (YCbqGwild.apost_base_xbFR (fx := fz) (SK := SK) SEGS B PST ARc Rel P STK1 [] regs ly S [] W mem md Qc)) ->
  (forall (fx' : YK11.FPState) (W2 : world SEGS) ly2 S2 Hp2 regs2 mem2 md2 k1 WS WS1, Rel W W2 ->
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fz fx' -> YCbqGwild.wbudget [] wk WS -> P WS1 ->
     AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
       (WS ++ WS1) ->
     AJW STK1 (e_A E) [] ly S [] W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
     aregs_preserved regs regs2 -> Qc ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     SRrG SEGS Rel W2 (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 ra) mem2 (YK11.seg_rom SEGS)) md2) R) ->
  SRrG SEGS Rel W (mkCfg (@YK11.mkst fz regs (Z_to_bv 64 pc) mem (YK11.seg_rom SEGS)) md) R.
Proof.
intros fz E fk ly S W mem md own Lam peak cnt ran k osc ic wk regs pc ra STK1 P Qc R HI HF R2 R3 R4 R8 R1 Hret Hra
  STK0 STKb HFZ0 Hcallee HK.
pose proof (l1_geo E fk ly S [] W mem md own Lam peak cnt ran k osc ic wk HI) as (G1 & G2 & G3 & G4 & G5 & G6).
pose proof HI as ((WS0 & HJ & Hwb0) & _ & _ & _ & HROD & _ & _ & _ & HPRE & _).
pose proof (l1_pre_afn E HPRE) as (_ & _ & Hra40 & Hgp0 & Htp0 & _).
pose proof (l1_pre_s0 E HPRE) as Hs00. pose proof (l1_pre_ra E HPRE) as Hra0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold LLVMF_STK in G1, STKb.
destruct HF as (HS & _ & _). destruct HS as (S8 & S16 & _).
destruct (ec_chain_at ly (aview SEGS (w_H W) mem) (e_A E) (e_sp0 E) (raZ (e_regs E)) (s0Z (e_regs E)) S8 S16
  ltac:(unfold raZ; apply bv_unsigned_in_range) ltac:(unfold s0Z; apply bv_unsigned_in_range) Hs00 Hra40
  ltac:(lia) ltac:(pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)); pose proof (Z.div_mod (e_sp0 E) 8 ltac:(lia));
                   pose proof (Z.mod_pos_bound (e_sp0 E) 8 ltac:(lia)); lia)
  ltac:(lia) ltac:(lia)) as (ch & Hch & Hsp).
rewrite Hra0 in Hsp.
assert (HspA : spZ regs = e_A E) by (unfold spZ; rewrite R2; apply l1_w64u; lia).
eapply (SRrG_bind SEGS Rel Rel_trans).
{ eapply (l1_callF (fx := fz) B SK PST Rel Rel_trans W regs mem md LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S [] k WS0 STK1 [] (e_A E - e_sp0 E) (Z_to_bv 64 ra) ch pc P Qc HJ).
  - rewrite HspA. lia.
  - pose proof (Z.div_mod (e_A E) 32 ltac:(lia)). pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)).
    replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia. apply Z.mod_mul. lia.
  - lia.
  - exact STK0.
  - unfold LLVMF_STK. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - exact R1.
  - exact Hret.
  - rewrite unsigned_lit_small by lia. lia.
  - replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) by lia.
    unfold s0Z. rewrite R8, l1_w64u by lia. exact Hch.
  - intros Hafn. apply (Hcallee ch Hsp). split; [exact Hafn|]. split; [exact HROD|].
    split; [rewrite HspA; lia|].
    split; [unfold raZ; rewrite R1, unsigned_lit_small by lia; lia | exact HFZ0].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta.
intros W2 c2 Hwle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ & HFK & HPW & HJ2 & HJ1 & HP & HQ).
replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) in HJ1 by lia.
exact (HK fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 WS0 WS1 Hwle HFZ HFK Hwb0 HPW HJ2 HJ1 HP HQ).
Qed.
End C.

(* ---------------------------------------------------------------------- *)
(* 5. EXACT ROOM POSITION: check_no_overread's events. The cut file's ec_cno_evs is its l1_cno_evs (the advance of
      GrantA's granted form) at the call's (e_sm E, e_x E). *)
Section CE. Context {rc : YM05.RunCeil} {L : ptable asym} {PA : PAImg L}.
Lemma l1_cno_evs_ec : forall (E : @ecx rc L PA) o1 o2 o0,
  ec_cno_evs E (o1, o2, o0) = l1_cno_evs (e_sm E) (e_x E) o1 o2 o0.
Proof. intros E o1 o2 o0. reflexivity. Qed.
End CE.

(* ---------------------------------------------------------------------- *)
(* 6. THE HULL BUDGET AT check_no_overread's CALL (route (b); the callee text takes `hull_budget S (ck_cno_evs sm x
      None None None)`): the cut's position (at most 3 earlier calls, ec_pre) and the cut file's hull field (ec_hyps'
      ech_hull_pay, in its exact text) give it, the all-granted list being a prefix of one call's model events
      (PRH_FnCheck.ck_cno_evs_call; lib/A/PresetHullPay.v hull_nt_infix_call). *)
Section H. Context {cp : CfParams}.
Lemma l1_cno_hull :
  (forall sm x os i H0 hist S Eg, (length os <= 4)%nat ->
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
    @PresetHullBudget.hull_budget cp S Eg) ->
  forall sm x os i H0 hist S, (length os <= 3)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  (PresetReqAt.MAXB <? Z.of_nat (length x)) = false ->
  @PresetHullBudget.hull_budget cp S (ck_cno_evs sm x None None None).
Proof.
intros HPAY sm x os i H0 hist S Hos Hpos Hg.
destruct (PresetHullPay.hull_nt_infix_call sm x None None None [] (ck_cno_evs sm x None None None) _
  (ck_cno_evs_call sm x None None None Hg)) as (N & T).
exact (HPAY sm x os i H0 hist S _ ltac:(lia) Hpos N T).
Qed.
End H.
