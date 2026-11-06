(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 162 of its 201 lines of code are new or changed and 300 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A: an own callee (index_of, talk) called at a cut of the walk (cut
   interface lib/A/Prog/model_writeDefs.v), after srm_call_apre / srm_call_back
   (lib/A/Prog/reac_served_markKit.v):
   - mw_call_apre: the callee's `apre` at the call, at the empty relro window (the callees' contracts hold at every
     rlo rhi), from the cut's base and the call's return address;
   - mw_call_back: the callee's `apost` gives the base again at the return, with the callee's write set added to the
     exception set;
   - mw_akb_call: a read-set byte of the call is a kept byte of the callee's call.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Set Default Proof Using "All".

Lemma mw_base_mono : forall cx fpos (X X2 : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> X2 a) ->
  mw_base SK B cx fpos X2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fpos X X2 ly3 S3 W3 ms3 md3 HB HX.
  unfold mw_base in HB |- *. cbv zeta in HB |- *.
  destruct HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 &
    R2 & R9 & R8 & R18 & R27 & R21 & R23 & R19 & R20 & R3 & R4 & Hsra & Hsav & Hflw & HK & Hfd & Hfs).
  repeat (split; [eassumption|]).
  split; [|split; assumption].
  apply (akept_mono SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK).
  intros a [Ha | Ha]; [left; exact (HX a Ha) | right; exact Ha].
Qed.

Lemma mw_rsame_of_pres : forall R R', aregs_preserved R R' -> mw_rsame R R'.
Proof.
  intros R R' HP. unfold mw_rsame.
  repeat split; [ exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact (HP 9 ltac:(unfold acallee_saved; lia))
                | exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact (HP 18 ltac:(unfold acallee_saved; lia))
                | exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact (HP 21 ltac:(unfold acallee_saved; lia))
                | exact (HP 23 ltac:(unfold acallee_saved; lia)) | exact (HP 19 ltac:(unfold acallee_saved; lia))
                | exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact (HP 3 ltac:(unfold acallee_saved; lia))
                | exact (HP 4 ltac:(unfold acallee_saved; lia)) ].
Qed.

(* the stack pointer at a cut is the realigned one *)
Lemma mw_base_sp : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> spZ (ms_regs ms3) = mw_sp1 cx.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPX HB.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  unfold mw_base in HB. cbv zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & _).
  pose proof asan_consts as ((C1a & C1b) & _). assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia.
Qed.

(* ---- the callee's apre at the call ---- *)
Lemma mw_call_apre : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 (Kc : Z) (Wrc : list (Z * Z)),
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> mw_E cx a) ->
  0 <= Kc <= INDEX_OF_AK ->
  YK0s.ret_ok (getr (ms_regs ms3) 1) -> 4096 <= raZ (ms_regs ms3) ->
  (forall a, inFP Wrc a -> mw_E cx a) ->
  apre SK SEGS 0 0 B Kc 0 [] Wrc (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (mw_k cx) (ms_regs ms3).
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 Kc Wrc HPX HB HX HKc Hret Hra Hwr.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof (mw_base_sp cx fpos X ly3 S3 W3 ms3 md3 HPX HB) as Hsp.
  pose proof HPX as ((A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14) & _ & _).
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
    as (HARc & HAR3 & Hbl & Hfr & Hfa & _ & _ & _ & _ & _ & _ & _).
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    R3 & R4 & _).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  unfold apre.
  split; [exact HJ3|]. split; [exact A2|].
  split; [exact (mw_arodata0 SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 HPX HB HX)|].
  split; [exact Hret|]. split; [exact Hra|].
  split; [rewrite R3; exact A6|]. split; [rewrite R4; exact A7|].
  split; [rewrite Hsp; lia|]. split; [rewrite Hsp; unfold mw_sp in *; lia|].
  split; [rewrite Hsp; unfold mw_sp in *; lia|].
  split; [exact A11|].
  split; [apply Forall_nil|].
  split.
  { intros a Ha. destruct (mw_blk_facts SK B cx a HPX (Hwr a Ha)) as (Hw & _).
    apply (ajw_mono B _ _ _ _ _ _ _ _ _ _ _ ly3 S3 _ a Hw Hbl).
    - intros y Hy. right. exact Hy.
    - exact Hfa. }
  intros a Ha Hro. destruct (mw_blk_facts SK B cx a HPX (Hwr a Ha)) as (_ & Hnro & _).
  apply Hnro. destruct Hro as [Hs | Hr]; [left; exact Hs | lia].
Qed.

(* ---- the callee's apost gives the base again ---- *)
Lemma mw_call_back : forall cx fpos (X X2 : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 (Kc : Z) (Ec : Z -> Prop)
    (P : bvmap 5 word -> (word -> option byte) -> Prop) (W4 : world SEGS) (c4 : config),
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  0 <= Kc <= INDEX_OF_AK ->
  (forall a, X a -> X2 a) -> (forall a, Ec a -> X2 a) -> (forall a, X2 a -> mw_E cx a) ->
  apost SK SEGS B Kc 0 Ec (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (mw_k cx) (ms_regs ms3)
    (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) S3 /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\ P regs2 (rdW W2 mem2)) W4 c4 ->
  exists ly4 S4 regs4 mem4 md4,
    c4 = mkCfg (mkst regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)) md4 /\
    mw_base SK B cx fpos X2 ly4 S4 W4 (mkst regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)) md4 /\
    aregs_preserved (ms_regs ms3) regs4 /\
    akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 mem4 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) Ec /\
    P regs4 (rdW W4 mem4).
Proof.
  intros cx fpos X X2 ly3 S3 W3 ms3 md3 Kc Ec P W4 c4 HPX HB HKc HX12 HEc HX2 Hpost.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof (mw_base_sp cx fpos X ly3 S3 W3 ms3 md3 HPX HB) as Hsp.
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Hc4 & HJ4 & Hpres & Hfr4 & Hfds & Hfs & HKc4 & Hsh4
                     & HS4 & Hperm4 & HP).
  rewrite Z.add_0_r in HJ4.
  pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & Hnin & Hfpos & HfS & Hperm & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & Hfd3 & Hfs3).
  exists ly4, S4, regs4, mem4, md4.
  split; [exact Hc4|].
  split.
  2: { split; [exact Hpres|]. split; [exact HKc4 | exact HP]. }
  pose proof (mw_base_mono cx fpos X X2 ly3 S3 W3 ms3 md3 HB HX12) as HB2.
  assert (HEsep : forall a, Ec a -> ~ (mw_sp cx - 104 <= a < mw_sp cx) /\
                    ~ aside_rng (mw_lyc cx) MW_CID fpos a).
  { intros a Ha. pose proof (HX2 a (HEc a Ha)) as HE.
    split.
    - pose proof HPX as (_ & _ & (mbs & kbs & tab & nm & al & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
        & _ & _ & _ & _ & Hfrm & _)).
      destruct (mw_blk_facts SK B cx a HPX HE) as (_ & _ & Hm & _).
      unfold apart_frame, mw_m, mw_sp in *. rewrite HK in Hfrm. lia.
    - eapply mw_blk_not_side; eassumption. }
  apply (mw_base_step SK B LAWS TB HSEGS cx fpos X2 ly3 S3 W3 ms3 md3 ly4 S4 W4
           (mkst regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)) md4 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) Ec
           HPX HB2); try reflexivity.
  - exact HJ4.
  - rewrite Hfr4. unfold mw_base in HB. cbv zeta in HB. tauto.
  - exists (st_fs S4). apply (set_fs_trans S3 S4 (mw_Sc cx)); [exact (set_fs_of_exists S3 (mw_Sc cx) HfS) | exact HS4].
  - exact (perm_trans Hperm4 Hperm).
  - exact HKc4.
  - rewrite Hsp. unfold mw_sp, mw_sp1 in *. lia.
  - rewrite Hsp. lia.
  - intros a Ha. left. exact (HEc a Ha).
  - intros a Ha HE. exact (proj1 (HEsep a HE) Ha).
  - intros a Ha HE. apply (proj2 (HEsep a HE)). left. unfold in_zr, frame_rng. cbn [fst snd].
    change (fs_frame_bytes MW_CID) with 1024. unfold mw_F, MW_FLAGPTR in Ha. lia.
  - exact (mw_rsame_of_pres _ _ Hpres).
  - exact Hfds.
  - exact Hfs.
Qed.

(* ---- a read-set byte of the call is a kept byte of a callee's call at the realigned sp ---- *)
Lemma mw_akb_call : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 (Kc : Z) a,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> 0 <= Kc <= INDEX_OF_AK ->
  akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a ->
  akb SEGS B ly3 S3 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) a.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 Kc a HPX HB HKc Hakb.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof (mw_base_sp cx fpos X ly3 S3 W3 ms3 md3 HPX HB) as Hsp.
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
    as (_ & _ & Hbl & Hfr & Hfa & Elo & Ehi & _).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  apply (akb_sub SEGS B (mw_lyc cx) (mw_Sc cx) ly3 S3 _ _ _ _ a Hakb).
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - exact Elo.
  - exact Ehi.
  - exact Hbl.
  - intros c q Hcq. exact (Hfr (c, q) Hcq).
  - exact Hfa.
Qed.

(* a byte of the side frame this call took is a kept byte of every callee's call *)
Lemma mw_akb_frame : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 slo shi a,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  mw_F cx fpos <= a < mw_F cx fpos + MW_FB -> akb SEGS B ly3 S3 slo shi a.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 slo shi a HPX HB Ha.
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 HPX HB)
    as (_ & _ & _ & _ & Hfa & _ & _ & Hin3 & _).
  right; right; right. exists MW_CID, fpos. split; [exact Hin3|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa. change (fs_frame_bytes MW_CID) with MW_FB. exact Ha.
Qed.

End b.
End a.
