(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/model_readDefs.v, with its module paths and module names changed; 355 of its 400 lines of code are new or changed and 294 lines of the source are left out. *)
(* reac_code_emit (fuzz_link.asan 0x89be4) on image A: the EXIT phase of its walk, `em_exit` of
   lib/A/Prog/reac_code_emitDefs.v. From the cut EM_v1_ra (+0x13c, wrapper_vfprintf returned) the code
     +0x13c          sb s7, 4(s5): F's shadow byte 4 := 0xf8 again
     +0x140..+0x148  the retired magic 0x45e0360e at F + 0
     +0x14c          `beqz s3` -> +0x180, not taken: F >= 4096 (the fact on F's atom decides it)
     +0x150..+0x170  F's eight shadow bytes := 0xf5
     +0x174..+0x178  `ld a0,0x38(s3); sb zero,0(a0)`: the inline release of the class-0 frame's flag byte
     +0x1a0..+0x1cc  sp := s0 - 0x60, the nine restores (ra, s0, s1, s2..s7) from sp0 - 0x28 .. sp0 - 0x68,
                     sp := sp0, `ret`
   and this file builds the whole post `em_post` (link_amem.v apostF over the caller's journal) from it.

   The run is the PLAIN flag run of lib/A/Prog/LinkWalkSide.v (`paj_flag_plain_x`): the state's writable windows
   are F's first word, F's eight shadow bytes and the flag byte; the return is LinkPaLib.v `paj_ret_at`, the post
   LinkWalkSide.v `apost_side_gen`, lifted to the entry's FP state by link_amem.v `apostF_lift`. The Post's FILE
   algebra is `em_apost` (lib/A/Prog/reac_code_emitPost.v), taken here as the Section hypothesis EMPOST and
   discharged where the walk is assembled. The model is the alias-write exit lane's lib/A/Prog/reac_link_alias_writeExit.v
   (the exit piece of reac_link_alias_write's walk).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkWseg LinkWalkMkFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c reac_code_emitDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   0. The symbolic state at the exit cut
   Atoms 0..31 are the registers at the cut; 32 the entry's ra, 33..40 the entry's s0, s1, s2..s7 (the saved
   words); 41 the frame's flag address (the word at F + 56). s3 = s6 = F is atom 19, s5 = F's shadow atom 21,
   s0 = sp0 - 0x20 atom 8.
   ========================================================================== *)
Definition ex_FR : YP09.region := YP09.mkRegion (Some 19%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 41 0))].
Definition ex_SH : YP09.region := YP09.mkRegion (Some 21%nat) 0 8 0 8 [].
Definition ex_FL : YP09.region := YP09.mkRegion (Some 41%nat) 0 1 0 1 [].
Definition ex_saves_chunks : list YP09.chunk :=
  YP09.mkChunk (-8) (CVal 8 (SOff 32 0)) ::
  map (fun j => YP09.mkChunk (-16 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 8).
Definition ex_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-72) 0 0 0 ex_saves_chunks.
Definition ex_facts : facts := mkFacts [(19%nat, HPTR 6); (41%nat, HPTR 0)] [] [].
Definition ex_ss0 : sstate := mkSS EM_v1_ra sr_atoms [ex_FR; ex_SH; ex_FL; ex_saves] None ex_facts.

Lemma ex_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma ex_sbm_fds_fs : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply wvb_fds_fs. Qed.

Lemma ex_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

Lemma ex_getr_z : forall (regs : bvmap 5 word) z (r : bv 5), z = bv_unsigned r -> getr regs (Z_to_bv 5 z) = getr regs r.
Proof. intros regs z r ->. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma ex_side_unfold : forall ly fpos a,
  aside_rng ly 0 fpos a <->
  (frame_addr ly 0 fpos <= a < frame_addr ly 0 fpos + 64) \/
  (SHADOW_OFF + frame_addr ly 0 fpos / 8 <= a < SHADOW_OFF + frame_addr ly 0 fpos / 8 + 8) \/
  a = flag_addr ly 0 fpos.
Proof.
intros ly fpos a. unfold aside_rng, in_zr, frame_rng, shadow_addr. cbn [fst snd].
change (fs_frame_bytes 0) with 64. change (64 / 8) with 8. tauto.
Qed.

(* the run tactic (reac_link_alias_writeExit.v aw_run_flag) *)
Ltac ex_run_flag RUNF HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNF with
    | forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own' lyc Sc mdc k cid pos Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNF W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
        [ clear Hrun | clear Hrun | clear Hrun | clear Hrun ]
      end
    end
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
(* the segments the listing is certified against; the link PAImg instance has it (LinkImgInst.v pi_link_segs) *)
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
(* the Post's FILE algebra: em_apost (lib/A/Prog/reac_code_emitPost.v) *)
Hypothesis EMPOST : forall cx (W2 : world pa_segs) mem2 regs2,
  em_base SK B cx ->
  amf_k pa_segs link_amf (rdW W2 mem2) (e_f cx) (e_kf cx + EMIT_HEAD + Z.of_nat (length (e_T cx))) ->
  awrange pa_segs (rdW W2 mem2) (e_f cx) AMF_BLOCK ->
  awrange pa_segs (rdW W2 mem2) LA_G_SAID SAID_SIZE ->
  reac_code_emit_apost pa_segs (e_regs cx) (e_m cx) regs2 (rdW W2 mem2).

Theorem em_exit : em_from SK B fx (em_v1_inv B).
Proof.
intros fxe cx fpos k2 ly3 S3 W3 ms3 md3 Hfxr Hfrm HBASE HJ3 HGI.
(* the post at the entry's FP state from the post at the current one; then fxe leaves the context, so the
   FPState instances below resolve to fx *)
unfold em_post.
eapply SRr_mono; [| intros W' c' _ HQ;
  exact (apostF_lift SK pa_segs B fxe fx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfxr HQ)].
clear Hfxr Hfrm. clear fxe.
pose proof HBASE as HBASE0.
unfold em_v1_inv in HGI.
destruct HGI as ((Hpc & Zrsv & Zsvc & Zrom & Zfrg & Zfcsr) & (R2 & R8 & R9 & R18 & R20 & R3 & R4 & R24 & R25 & R26 & R27) &
  (R19 & R22 & R21 & R23) & (Hra & Hsav) & Hflagw & HF4096 & HFceil &
  (Ek2 & Hperm & HfsS3 & Hfrs3 & Hnin & Hfa3 & Hfl3 & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1) & Hfds3 & Hfs3) &
  (HK3 & HROD3 & _) & Hfile).
unfold em_flagw, em_at in Hflagw. unfold em_at in Hra, Hsav.
pose proof HBASE as (HPRE & HRD & Hf0 & Hfp0 & HFIN & HMF & HBLK & HFIT & HFMT & _).
pose proof HPRE as (HJ & HGX & HROD & Hraok & Hra4 & Hgp & Htp & Hsp16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as (ACv & _).
set (regs := e_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (lyc := e_lyc cx) in *. set (Sc := e_Sc cx) in *. set (Wc := e_W cx) in *. set (memc := e_memc cx) in *.
change (e_spe cx) with (spZ regs) in *.
set (sp := spZ regs) in *.
set (F := eF cx fpos) in *. set (FL := eFL cx fpos) in *. set (SH := eSH cx fpos) in *.
change EM_CID with 0 in *.
assert (EF0 : frame_addr lyc 0 fpos = F) by reflexivity.
assert (EFL0 : flag_addr lyc 0 fpos = FL) by reflexivity.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
change (fs_frame_bytes 0) with 64 in HFceil.
subst k2.
(* ---- the journal's window and the stack ---- *)
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & _) & _).
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hspr : 0 <= sp < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu).
assert (HKv : REAC_CODE_EMIT_AK = 9360) by reflexivity.
rewrite HKv in Hwlo.
assert (HspK : alloc_ceiling <= sp - REAC_CODE_EMIT_AK) by (rewrite HKv; lia).
assert (Hsp47 : sp <= 2 ^ 47) by lia.
(* ---- the frame, its shadow and its flag byte ---- *)
pose proof (ajournal_gx_AR pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (HinF : In (0, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (HinF3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
assert (EF : frame_addr ly3 0 fpos = F) by (rewrite Hfa3; reflexivity).
assert (EFL : flag_addr ly3 0 fpos = FL) by (rewrite Hfl3; reflexivity).
destruct (frames_bounds pa_segs B LAWS _ _ _ _ _ 0 fpos HAR1 HinF) as (_ & _ & HFapp).
rewrite EF0 in HFapp. change (fs_frame_bytes 0) with 64 in HFapp.
pose proof (frame_al64 pa_segs B _ _ _ _ _ 0 fpos HAR1 HinF) as (HFal & _ & _). rewrite EF0 in HFal.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 HinF3) as (_ & _ & HFpres & HFSpres).
rewrite EF in HFpres, HFSpres. change (fs_frame_bytes 0) with 64 in HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 0 fpos HAR3 HinF3) as (HFLpres & HFLown & HFLapp & HFLceil).
rewrite EFL in HFLpres, HFLown, HFLapp, HFLceil.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
destruct HFapp as (_ & HFapp'). destruct HFLapp as (HFL4096 & _).
assert (HF8 : 0 <= F / 8 /\ F / 8 + 8 <= (F + 64) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 64) with (F + 8 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 64) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in HF8c.
assert (HSHb : SHADOW_OFF <= SH /\ SH + 8 <= SHADOW_OFF + 2 ^ 44) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hc; exact (proj2 (HFpres FL Hc) HFLown)).
assert (HFLnS : ~ (SH <= FL < SH + 8)).
{ intros Hc. apply (proj2 (HFSpres (FL - shadow_addr F) ltac:(unfold shadow_addr; rewrite HSHeq in Hc; lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLown. }
assert (HdFL : FL + 1 <= F \/ F + 64 <= FL).
{ destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|].
  destruct (Z_lt_le_dec FL (F + 64)) as [Hh|Hh]; [exfalso; apply HFLnF; lia | right; lia]. }
assert (HFvsSH : forall a, F <= a < F + 64 -> ~ (SH <= a < SH + 8)).
{ intros a Ha Hc. rewrite HSHeq in Hc. unfold SHADOW_OFF in *. destruct HFapp' as [H1 | (H1 & H2)]; lia. }
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HFLb : 0 <= FL < 2 ^ 64) by lia.
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (w64 FL) = FL) by (unfold w64; apply unsigned_lit_small; lia).
assert (USH : bv_unsigned (w64 SH) = SH) by (unfold w64; apply unsigned_lit_small; lia).
set (s0 := sp + EM_VA) in *.
assert (Us0 : bv_unsigned (w64 s0) = s0) by (unfold w64, s0, EM_VA; apply unsigned_lit_small; lia).
(* the realigned stack pointer s1 *)
destruct (sp1_facts (sp - REAC_CODE_EMIT_AFRAME) ltac:(unfold REAC_CODE_EMIT_AFRAME; lia)
  ltac:(unfold REAC_CODE_EMIT_AFRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((sp - REAC_CODE_EMIT_AFRAME) / 32)) with (e_sp1 cx) in Hsp1r, Hsp1al32, Hsp1al16.
unfold REAC_CODE_EMIT_AFRAME in Hsp1r.
set (sp1 := e_sp1 cx) in *.
assert (Usp1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment: the registers at the cut, the saved words, the flag address ---- *)
set (extra := getr regs 1 ::
  map (fun j : Z => getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))) [0; 1; 2; 3; 4; 5; 6; 7] ++ [w64 FL]).
set (E := Eimg (Ereg R extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j extra (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E19 : ew E 19 = w64 F) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = w64 SH) by (rewrite (EREG 21%nat 21%bv eq_refl); exact R21).
assert (E8 : ew E 8 = w64 s0) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E41 : ew E 41 = w64 FL) by (exact (EX 9%nat ltac:(lia))).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; exact UF).
assert (U21 : bv_unsigned (ew E 21) = SH) by (rewrite E21; exact USH).
assert (U8 : bv_unsigned (ew E 8) = s0) by (rewrite E8; exact Us0).
assert (U41 : bv_unsigned (ew E 41) = FL) by (rewrite E41; exact UFL).
(* the saved words, as the saves region's chunks *)
assert (HSAV : forall j, (j < 9)%nat ->
  rdword (aview pa_segs (w_H W3) m3) (s0 + (if (j =? 0)%nat then -8 else -16 - 8 * Z.of_nat (j - 1)))
    = Some (bv_unsigned (nth j extra (w64 0)))).
{ intros j Hj. destruct j as [|j'].
  - cbn [Nat.eqb]. unfold s0, EM_VA. replace (sp + -32 + -8) with (sp + EM_RA) by (unfold EM_RA; lia). exact Hra.
  - cbn [Nat.eqb]. replace (S j' - 1)%nat with j' by lia.
    replace (s0 + (-16 - 8 * Z.of_nat j')) with (sp + EM_S0 - 8 * Z.of_nat j') by (unfold s0, EM_VA, EM_S0; lia).
    rewrite (Hsav (Z.of_nat j') ltac:(lia)).
    do 8 (destruct j' as [|j']; [reflexivity|]). lia. }
assert (HCH : forall j, (j < 9)%nat -> YP09.chunk_ok pa_segs E (rdW W3 m3) s0
   (nth j ex_saves_chunks (YP09.mkChunk 0 (CVal 8 (SLit 0))))).
{ intros j Hj.
  assert (Hc : nth j ex_saves_chunks (YP09.mkChunk 0 (CVal 8 (SLit 0)))
             = YP09.mkChunk (if (j =? 0)%nat then -8 else -16 - 8 * Z.of_nat (j - 1)) (CVal 8 (SOff (32 + j) 0))).
  { do 9 (destruct j as [|j]; [reflexivity|]). lia. }
  rewrite Hc.
  apply (chunk_ok_val pa_segs E _ s0 _ 8 (SOff (32 + j) 0) (bv_unsigned (nth j extra (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (nth j extra (w64 0))) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu;
    change (8 * Z.of_N 8) with 64; lia
  | zside
  | exact (val_mem_of_rdword pa_segs (w_H W3) m3 _ _ (HSAV j Hj)) ]. }
(* ---- the symbolic state at the cut ---- *)
assert (HS0 : st_ok_pi pa_segs VAL E ex_ss0 (restrict (w_H W3) ms3)).
{ rewrite (ex_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold ex_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
      unfold region_ok, ex_FR, ex_SH, ex_FL, ex_saves;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia)))|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val pa_segs E _ F 56 8 (SOff 41 0) FL);
      [ cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; unfold w64; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | zside
      | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword pa_segs (w_H W3) m3 _ _ Hflagw) ].
    + rewrite U21. pose proof HSHb as HSHb'. unfold SHADOW_OFF in HSHb'. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable pa_segs).
      replace (SH + o) with (shadow_addr F + o) by (rewrite HSHeq; unfold shadow_addr; lia).
      exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U41. split; [lia|]. split; [lia|].
      split; [|apply Forall_nil].
      intros o Ho. replace (FL + o) with FL by lia. apply (apresent_writable pa_segs). exact HFLpres.
    + rewrite U8. split; [unfold s0, EM_VA; lia|]. split; [unfold s0, EM_VA; lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc.
      destruct (In_nth _ _ (YP09.mkChunk 0 (CVal 8 (SLit 0))) Hc) as (j & Hj & <-).
      apply HCH. exact Hj.
  - apply pairwise_disjoint_of_extents.
    unfold ex_FR, ex_SH, ex_FL, ex_saves, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U21, U41, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HSHeq in *. unfold s0, EM_VA, SHADOW_OFF in *.
    unfold kLowMemEnd in *.
    repeat split; first [ (left; lia) | (right; lia) | lia | (destruct HdFL; [right | left]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [left | left]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [left | right]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [right | left]; lia)
                        | (destruct HFapp' as [? | (? & ?)]; [right | right]; lia)
                        | (lazymatch goal with |- ?g => idtac "DISJ" g end; fail) ].
  - split; [|split; [exact I | exact I]].
    cbn [ex_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U19, U41. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
    repeat split; first [lia | apply Z.mod_1_r]. }
(* s6 holds F as s3 does: the run's stores through s6 go to F's region *)
assert (HS : st_ok_pi pa_segs VAL E (mkSS (ss_pc ex_ss0) (sr_set (ss_regs ex_ss0) 22%bv (SOff 19 0))
  (ss_mem ex_ss0) (ss_resv ex_ss0) (ss_facts ex_ss0)) (restrict (w_H W3) ms3)).
{ apply (ast_ok_pi_set_reg_fp E _ _ (22%bv : bv 5) (SOff 19 0) HS0 ltac:(vm_compute; reflexivity)).
  rewrite (sv_off0 E 19 F E19). cbn [ms_regs restrict]. exact (eq_sym R22). }
clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ex_ss0] in HS.
clearbody E.
(* ---- the run +0x13c .. +0x1cc: F's shadow, the retired magic, `beqz s3` (not taken), the release, the restores,
   up to `ret` ---- *)
pose proof (paj_flag_plain_x SK B LAWS (e_G cx) HGX (e_XO cx) (e_OUT cx)) as RUNF.
ex_run_flag RUNF HS HJ3.
{ lia. }
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ex_FR ex_SH ex_FL ex_saves] in Ha.
  - rewrite U19 in Ha. left.
    apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 fpos a HJ3
      ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
  - rewrite U21 in Ha. left.
    apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 fpos a HJ3
      ltac:(left; reflexivity)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0 / 8) with 8.
    rewrite HSHeq in Ha. lia.
  - rewrite U41 in Ha. right. right. right. rewrite EFL. lia.
  - exfalso; lia. }
{ intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
    let r1 := eval vm_compute in (nth 2 (ss_mem ssx) ex_FL) in
    pose proof (st_ok_pi_region_nth E ssx msr 2 r1 HSr ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (field_of_region E (ms_mem msr) 41 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR1 U41
      ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as Vfl;
    change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(clear; lia));
    replace (FL + 0 + Z.of_nat 0) with FL in Vfl by (clear; lia);
    rewrite EFL, Vfl; reflexivity
  end. }
intros ms5 mat5 HS5 HJ5 _ HFr5 HG5.
(* ---- `ret` ---- *)
prreg HS5 (1%bv : bv 5) P1. prreg HS5 (2%bv : bv 5) P2. prreg HS5 (3%bv : bv 5) P3.
prreg HS5 (4%bv : bv 5) P4. prreg HS5 (8%bv : bv 5) P8. prreg HS5 (9%bv : bv 5) P9.
prreg HS5 (18%bv : bv 5) P18. prreg HS5 (19%bv : bv 5) P19.
prreg HS5 (20%bv : bv 5) P20. prreg HS5 (21%bv : bv 5) P21. prreg HS5 (22%bv : bv 5) P22.
prreg HS5 (23%bv : bv 5) P23. prreg HS5 (24%bv : bv 5) P24. prreg HS5 (25%bv : bv 5) P25.
prreg HS5 (26%bv : bv 5) P26. prreg HS5 (27%bv : bv 5) P27.
refine (paj_ret_at W3 E _ ms5 _ _ HS5 _ _ _); [reflexivity | vm_compute; reflexivity |].
intros mat6.
assert (Era : getr (ms_regs ms5) 1 = getr regs 1) by (rewrite P1; exact (EX 0%nat ltac:(lia))).
unfold YK0s.ret_ok in Hraok. rewrite Era, Hraok.
set (md5 := with_vm_backing (m_vm_lazy md3) mat5 md3) in *.
set (md6 := with_vm_backing (m_vm_lazy md5) mat6 md5) in *.
pose proof (ajournal_gx_materialize pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat6 HJ5) as HJ6.
(* ---- what the exit changed: only bytes of the side frame ---- *)
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng lyc 0 fpos a ->
  aview pa_segs (w_H W3) (ms_mem ms5) a = aview pa_segs (w_H W3) m3 a).
{ intros a Ha Hs. apply (aview_eq_of pa_segs). apply HFr5.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hrw). cbn [In] in Hr. apply Hs. apply (proj2 (ex_side_unfold lyc fpos a)). rewrite EF0, EFL0.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ex_FR ex_SH ex_FL ex_saves] in Hrw.
  - rewrite U19 in Hrw. left. lia.
  - rewrite U21 in Hrw. right; left. rewrite HSHeq in Hrw. lia.
  - rewrite U41 in Hrw. right; right. lia.
  - lia. }
assert (HPRS : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem ms5) a)
  by (intros a Ha; exact (ex_apresent_grows (w_H W3) m3 (ms_mem ms5) a HG5 Ha)).
(* ---- the FILE at the end ---- *)
assert (HFIN3 : In (e_f cx, AMF_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); exact HFIN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_f cx) AMF_BLOCK HAR3 HFIN3) as (_ & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
change (req_size AMF_BLOCK) with AMF_BLOCK in Hfceil, Hfapp, Hfpres.
pose proof (sep_block_frame pa_segs B LAWS ly3 S3 W3 m3 md3 (e_f cx) AMF_BLOCK 0 fpos HAR3 HFIN3 HinF3) as HsepF.
unfold zdisjoint in HsepF. cbn [fst snd] in HsepF. change (req_size AMF_BLOCK) with AMF_BLOCK in HsepF.
change (fs_frame_bytes 0) with 64 in HsepF. rewrite EF in HsepF.
assert (FNS : forall a, e_f cx <= a < e_f cx + AMF_BLOCK -> ~ aside_rng lyc 0 fpos a).
{ intros a Ha Hs. apply (proj1 (ex_side_unfold lyc fpos a)) in Hs. rewrite EF0, EFL0 in Hs.
  destruct Hs as [Hs | [Hs | Hs]].
  - unfold AMF_BLOCK in *. lia.
  - pose proof (in_app_addr _ _ a Hfapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    rewrite <- HSHeq in Hs. pose proof HSHb as HSHb'.
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, SHADOW_OFF in *. lia.
  - subst a. exact (proj2 (Hfpres FL Ha) HFLown). }
assert (FB5 : forall a, e_f cx <= a < e_f cx + AMF_BLOCK ->
  mbyte pa_segs (rdW W3 (ms_mem ms5)) a = mbyte pa_segs (rdW W3 m3) a).
{ intros a Ha. apply (mbyte_of_aview pa_segs). apply HKEEP; [lia | exact (FNS a Ha)]. }
unfold em_file in Hfile.
pose proof (amf_k_ext pa_segs link_amf (rdW W3 m3) (rdW W3 (ms_mem ms5)) (e_f cx) _ FB5 Hfile) as HAMF.
assert (HWF : awrange pa_segs (rdW W3 (ms_mem ms5)) (e_f cx) AMF_BLOCK).
{ intros i Hi. apply (apresent_writable pa_segs). apply HPRS. exact (proj1 (Hfpres (e_f cx + i) ltac:(lia))). }
assert (HWG : awrange pa_segs (rdW W3 (ms_mem ms5)) LA_G_SAID SAID_SIZE).
{ intros i Hi.
  pose proof (wseg_writable_tfib_rng (rdW W3 (ms_mem ms5)) (LA_G_SAID + i)
    ltac:(unfold LA_G_SAID, SAID_SIZE in *; lia)) as Hw.
  rewrite <- HSEGS in Hw. exact Hw. }
(* ---- the post ---- *)
apply (apostF_of_apost SK pa_segs B).
refine (apost_side_gen SK pa_segs B LAWS pa_segs_low REAC_CODE_EMIT_AK 0 (e_E cx)
  (e_G cx) (e_XO cx) (e_OUT cx) (e_STK cx) (e_sp0 cx) (e_FP cx) (e_ly cx) (e_S cx) (e_W0 cx)
  (e_mem0 cx) (e_md0 cx) (e_own cx) lyc Sc Wc memc (e_mdc cx) (e_k cx)
  regs (ms_regs ms5) ly3 (stack_free_state 0 fpos S3) W3 (ms_mem ms5) md6 (e_k cx) 0 fpos S1 W1 mem1 md1 _
  HJ HJ6 ltac:(lia) _ _ _ HAR1 Hfrs1 Hbl1 _ _).
- unfold md6, md5.
  destruct (wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat5 md3)) mat6
    (with_vm_backing (m_vm_lazy md3) mat5 md3)) as (A1 & _).
  destruct (wvb_fds_fs (m_vm_lazy md3) mat5 md3) as (A2 & _).
  rewrite A1, A2. exact Hfds3.
- unfold md6, md5.
  destruct (wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat5 md3)) mat6
    (with_vm_backing (m_vm_lazy md3) mat5 md3)) as (_ & A1).
  destruct (wvb_fds_fs (m_vm_lazy md3) mat5 md3) as (_ & A2).
  rewrite A1, A2. exact Hfs3.
- apply aregs_preserved_eqs.
  + rewrite P2, U8. unfold s0, EM_VA. replace (sp + -32 + 32) with sp by lia. unfold sp, spZ.
    apply Z_to_bv_bv_unsigned.
  + rewrite P3, (EREG 3%nat 3%bv eq_refl). exact R3.
  + rewrite P4, (EREG 4%nat 4%bv eq_refl). exact R4.
  + rewrite P8. pose proof (EX 1%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P9. pose proof (EX 2%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P18. pose proof (EX 3%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P19. pose proof (EX 4%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P20. pose proof (EX 5%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P21. pose proof (EX 6%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P22. pose proof (EX 7%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P23. pose proof (EX 8%nat ltac:(lia)) as XX. cbn [Nat.add] in XX. rewrite XX. clear XX. unfold extra. cbn [nth map app]. apply ex_getr_z. reflexivity.
  + rewrite P24, (EREG 24%nat 24%bv eq_refl). exact R24.
  + rewrite P25, (EREG 25%nat 25%bv eq_refl). exact R25.
  + rewrite P26, (EREG 26%nat 26%bv eq_refl). exact R26.
  + rewrite P27, (EREG 27%nat 27%bv eq_refl). exact R27.
- apply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc Wc memc (e_mdc cx)
    W3 m3 W3 (ms_mem ms5) (sp - REAC_CODE_EMIT_AK) sp _ _ (aside_rng lyc 0 fpos) HAR HspK ltac:(lia) HK3 HKEEP).
  + intros a _ Hp. exact (HPRS a Hp).
  + intros a Ha. exact Ha.
  + intros a Ha. left. right. exact Ha.
- cbv beta. split; [|split].
  + apply (set_fs_trans S3 (stack_free_state 0 fpos S3) Sc).
    * exact HfsS3.
    * apply stack_free_state_set_fs.
  + rewrite stack_free_state_set_fs, ablocks_set_fs. exact Hperm.
  + exact (EMPOST cx W3 (ms_mem ms5) (ms_regs ms5) HBASE0 HAMF HWF HWG).
Qed.


About em_exit.
Print Assumptions em_exit.

End b.
End a.
