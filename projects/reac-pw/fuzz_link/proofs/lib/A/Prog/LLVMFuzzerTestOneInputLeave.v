(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 432 of its 485 lines of code are new or changed and 351 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE FRAME'S RELEASE
   AND THE EPILOGUE, +0x13c0 .. +0x143c (0x83b94 .. 0x83c10), to the contract's post, against the cut interface
   lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x13c0  ld s4, 0x40(s1) ; ld a6, 0x38(s1)        F twice (frame_alloc_4's result and the frame)
     +0x13c8  lui/addiw a0 = 0x45e0360e ; sd a0, 0(a6)   the retired magic at F
     +0x13d4  beqz s4, +0x13f0                          not taken: F >= 4096 (the real-stack arm is not reached)
     +0x13d8  a1 := 0x80 ; a0 := s3 ; jal meta_fill_f5   F's 128 shadow bytes := 0xf5
     +0x13e4  ld a0, 0x3f8(s4) ; sb zero, 0(a0)          the inline release of the frame's flag byte
     +0x13ec  j +0x13fc ; a0 := 0 ; sp := s0 - 0x1a0 ; the thirteen restores ; sp += 0x1a0 ; ret

     lf_leave : FROM (lf_post ..) LEAVE
     lf_exit  : FROM (lf_post ..) EXIT          (LLVMFuzzerTestOneInputExit.v lf_frees, then lf_leave)

   The runs are LinkWalkSide.v's plain gx runs (paj_run_call_plain_x, paj_flag_plain_x), meta_fill_f5 is
   LinkWalkSide.v aj_gx_set_shadow_at over the Section hypothesis ASS, the return LinkPaLib.v paj_ret_at; the post
   is built from the journal after the release (own list [], stack_free_state), the cut's journal clauses, and the
   bytes the three steps keep: all but the side frame's own bytes, shadow and flag (aside_rng), which miss the
   FILE record, long_alias's NUL and the payload. The template is lib/A/Prog/reac_link_alias_writeExit.v
   (the exit piece of reac_link_alias_write's walk).

   Section hypotheses (discharged by the image instance):
     LAWS : AR_laws pa_segs B; TB : PcapSyms B; HSEGS : pa_segs = tfibsegs; LV : LinkVals;
     MT_LE / MT_OK : the trivial meter's laws;
     ASS : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f5) 0xf5 (lib/A/Rt/SetShadow.v
           link_set_shadow_f5);
     AFREE4W, LF_TRACE_FREE (for lf_exit, through lf_frees).

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputExit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. The symbolic state at +0x13c0: atoms 0..31 the registers, 32 = F, 33 = the flag byte's address,
      34 = the entry ra, 35..46 = the entry s0, s1, s2..s11 (the machine frame's saved words)
   ========================================================================== *)
Definition lv_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) LS_F (LS_FK + 8) LS_F LS_F
    [YP09.mkChunk LS_F (CVal 8 (SOff 32 0)); YP09.mkChunk LS_FK (CVal 8 (SOff 32 0))].
Definition lv_FR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1024 0 8 [YP09.mkChunk 1016 (CVal 8 (SOff 33 0))].
Definition lv_FL0 : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [].
Definition lv_saves_chunks : list YP09.chunk :=
  YP09.mkChunk (-8) (CVal 8 (SOff 34 0)) ::
  map (fun j => YP09.mkChunk (-16 - 8 * Z.of_nat j) (CVal 8 (SOff (35 + j) 0))) (seq 0 12).
Definition lv_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 lv_saves_chunks.
Definition lv_facts : facts := mkFacts [(32%nat, HPTR 0); (33%nat, HPTR 0)] [] [].
Definition lv_ss0 : sstate := mkSS LF_leave sr_atoms [lv_spill; lv_FR; lv_FL0; lv_saves] None lv_facts.

Definition lv_extra (regs : bvmap 5 word) (F FL : Z) : list word :=
  [w64 F; w64 FL; getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21;
   getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27].

Lemma lv_extra_saved : forall regs F FL j, (j < 12)%nat ->
  nth (3 + j) (lv_extra regs F FL) (Z_to_bv 64 0) =
  getr regs (Z_to_bv 5 (if Z.of_nat j <? 2 then 8 + Z.of_nat j else 16 + Z.of_nat j)).
Proof. intros regs F FL j Hj. do 12 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Ltac lv_run_call RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of RUNC with
    | forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
      lazymatch r with
      | (?ss', PRS_call ?s) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
        let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
        eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
        [ clear Hrun | clear Hrun ]
      | ?other => fail "lv_run_call: the run does not stop at a call:" other
      end
    end
  end.
Ltac lv_run_flag RUNF HS HJ :=
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

(* byte agreement from a view agreement on the 64-bit addresses *)
Lemma lv_mbyte_mod : forall segs (m : word -> option byte) a, mbyte segs m a = mbyte segs m (a mod 2 ^ 64).
Proof.
  intros segs m a. unfold mbyte. replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma lv_kagree_of_aview : forall segs (X : Z -> Prop) H H' (mem mem' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs H' mem' a = aview segs H mem a) ->
  kagree segs (fun a => X (a mod 2 ^ 64)) (mrestrict H mem) (mrestrict H' mem').
Proof.
  intros segs X H H' mem mem' HV a Ha.
  rewrite (lv_mbyte_mod segs (mrestrict H' mem') a), (lv_mbyte_mod segs (mrestrict H mem) a).
  apply (mbyte_of_aview segs). apply HV; [apply Z.mod_pos_bound; lia | exact Ha].
Qed.

Lemma lv_kt : forall segs (X : Z -> Prop) m1 m2 m3, kagree segs X m1 m2 -> kagree segs X m2 m3 -> kagree segs X m1 m3.
Proof. intros segs X m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis ASS : forall fy : YK11.FPState,
  aset_shadow_realizes (fx := fy) SEGS B (pa_sigma LS___asan_set_shadow_f5) 0xf5.

(* a heap block's byte is no byte of a taken side frame: not the frame (al_sep), not its shadow (the block is
   application memory), not its flag byte (owned by the runtime, the block's bytes are not) *)
Lemma lv_blk_not_side : forall ly S (W : world SEGS) mem md cid pos p n a,
  AR SEGS B ly S W mem md -> In (cid, pos) (frames S) -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> ~ aside_rng ly cid pos a.
Proof.
  intros ly S W mem md cid pos p n a HAR HinF Hb Ha Hs.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hb) as (_ & Hp4 & Hpc & Happ & Hown & _).
  destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (HPw & HSf).
  rewrite Forall_forall in HSf. pose proof (HSf (cid, pos) HinF) as (F1 & F2). cbn [fst snd] in F1, F2.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  destruct Hs as [Hs | [Hs | Hs]].
  - pose proof (pairwise_In zdisjoint _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) _ _ eq_refl HPw
      ltac:(apply in_map_iff; exists (p, n); split; [reflexivity | exact Hb])
      ltac:(apply in_map_iff; exists (cid, pos); split; [reflexivity | exact HinF])) as D.
    unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in *. lia.
  - unfold in_zr, shadow_addr in Hs. cbn [fst snd] in Hs. pose proof (fs_frame_bytes_nonneg cid) as Fb.
    assert (Hd : 0 <= frame_addr ly cid pos / 8 <= alloc_ceiling / 8)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
    assert (Hd2 : 0 <= fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    unfold SHADOW_OFF in Hs. lia.
  - destruct (al_flag _ _ LAWS _ _ _ _ _ _ _ HAR HinF) as (_ & HFo & _). subst a.
    exact (proj2 (Hown _ Ha) HFo).
Qed.

#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).

Lemma lf_leave : lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
  (lf_post SK B MT XN_LIB MS la_nul) (lf_leave_inv B MT MS la_nul LF_MO_SET LF_MO_OP LF_MO_END).
Proof.
  intros cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HL.
  destruct HL as (T3 & Hsh & Hcore & R19 & Hsv & Hhd & Hfs & HF & HFK & Hjbk).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof HB as (HPRE & HFRM & HGX & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & HRA & _ & _ & HPIN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNAMES & HSORT & _).
  pose proof HAFN as (_ & HRET & _ & HGP & HTP & _).
  pose proof Hjbk as (Hkev & Hbb & Hfa & _ & Hfd & Hfs3 & _ & Hwl & Hgi & Henv & Hbl & Hinc & Hla & _ & _ & Hpv).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) as (HIMG & HREL).
  pose proof asan_consts as ((C1a & C1b) & C2' & C3' & C4' & C5').
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  pose proof (lf_sp1_le cx) as (P1 & P2). pose proof (ex_sp1 cx) as P3.
  unfold LLVMF_STK, LF_MFRAME in *.
  assert (Hs32 : lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1, lf_sp1_of. rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  set (F := lf_F cx fp) in *. set (FL := lf_FL cx fp) in *. set (SH := lf_SH cx fp) in *.
  destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LF_CID fp HJ) as (EF0 & EFL0).
  assert (EF : frame_addr ly3 LF_CID fp = F) by exact EF0.
  assert (EFL : flag_addr ly3 LF_CID fp = FL) by exact EFL0.
  pose proof LF_frame_slot as (FB & _).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ LF_CID fp HAR3 HinF) as (HF4096 & HFceil & HFapp).
  rewrite EF, FB in HFceil, HFapp. rewrite EF in HF4096.
  destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID fp HAR3 HinF) as (_ & _ & HFnown & _).
  rewrite EF, FB in HFnown.
  destruct (al_flag _ _ LAWS _ _ _ _ _ LF_CID fp HAR3 HinF) as (_ & HFLown & HFLapp & HFLceil).
  rewrite EFL in HFLown, HFLapp, HFLceil.
  assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
  destruct HFapp as (_ & HFapp'). destruct HFLapp as (HFL4096 & HFLapp').
  assert (HdFL : FL + 1 <= F \/ F + 1024 <= FL).
  { destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|].
    destruct (Z_lt_le_dec FL (F + 1024)) as [Hh|Hh]; [exfalso; exact (proj2 (HFnown FL ltac:(lia)) HFLown) | right; lia]. }
  assert (HF8 : 0 <= F / 8 <= alloc_ceiling / 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  assert (HFvsSH : forall a, F <= a < F + 1024 -> ~ (SH <= a < SH + 128)).
  { intros a Ha Hc. rewrite HSHeq in Hc. unfold SHADOW_OFF in Hc. destruct HFapp' as [H1 | (H1 & H2)]; lia. }
  assert (HFLvsSH : ~ (SH <= FL < SH + 128)).
  { intros Hc. rewrite HSHeq in Hc. unfold SHADOW_OFF in Hc. destruct HFLapp' as [H1 | (H1 & H2)]; lia. }
  assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
  assert (UFL : bv_unsigned (w64 FL) = FL) by (unfold w64; apply unsigned_lit_small; lia).
  assert (Usp : bv_unsigned (w64 (spZ (c_regs cx))) = spZ (c_regs cx))
    by (unfold w64; apply unsigned_lit_small; unfold spZ; apply bv_unsigned_in_range).
  assert (Usp1 : bv_unsigned (w64 (lf_sp1 cx)) = lf_sp1 cx) by (unfold w64; apply unsigned_lit_small; lia).
  (* ---- the environment ---- *)
  set (extra := lv_extra (c_regs cx) F FL).
  set (E := Eimg (Ereg (ms_regs ms3) extra)).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
    by (intros n r Hr; subst E; exact (ew_Eimg_Ereg_nat _ _ n r Hr)).
  assert (EX : forall j, (j < 15)%nat -> ew E (32 + j) = nth j extra (Z_to_bv 64 0))
    by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
  pose proof (ex_env_agree (ms_regs ms3) extra) as HA. fold E in HA.
  assert (E32 : ew E 32 = w64 F) by exact (EX 0%nat ltac:(lia)).
  assert (E33 : ew E 33 = w64 FL) by exact (EX 1%nat ltac:(lia)).
  assert (E34 : ew E 34 = getr (c_regs cx) 1) by exact (EX 2%nat ltac:(lia)).
  assert (ESV : forall j, (j < 12)%nat ->
    ew E (35 + j) = getr (c_regs cx) (Z_to_bv 5 (if Z.of_nat j <? 2 then 8 + Z.of_nat j else 16 + Z.of_nat j))).
  { intros j Hj. replace (35 + j)%nat with (32 + (3 + j))%nat by lia. rewrite (EX (3 + j)%nat ltac:(lia)).
    exact (lv_extra_saved _ _ _ j Hj). }
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; exact UF).
  assert (U33 : bv_unsigned (ew E 33) = FL) by (rewrite E33; exact UFL).
  assert (U9 : bv_unsigned (ew E 9) = lf_sp1 cx) by (rewrite (EREG 9%nat 9%bv eq_refl), C9; exact Usp1).
  assert (U8 : bv_unsigned (ew E 8) = spZ (c_regs cx)) by (rewrite (EREG 8%nat 8%bv eq_refl), C8; exact Usp).
  assert (E19 : ew E 19 = w64 SH) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
  (* ---- the symbolic state ---- *)
  assert (HS : st_ok_pi (fx := fy) SEGS VAL E lv_ss0
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_leave)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
        unfold region_ok, lv_spill, lv_FR, lv_FL0, lv_saves;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. unfold LS_F, LS_FK. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (ex_chunk cx W3 ms3 E LS_F (SOff 32 0) F HF). cbn [sv_denot]. rewrite E32, Z.add_0_r, UF. reflexivity.
        * apply (ex_chunk cx W3 ms3 E LS_FK (SOff 32 0) F HFK). cbn [sv_denot]. rewrite E32, Z.add_0_r, UF. reflexivity.
      + rewrite U32. split; [lia|]. split; [lia|].
        split; [intros o Ho; destruct (HFnown (F + o) ltac:(lia)) as (Hp & _); exact (apresent_writable SEGS _ _ _ Hp)|].
        apply Forall_cons; [|apply Forall_nil].
        pose proof Hhd as (_ & _ & _ & Hfl). unfold lf_at in Hfl. rewrite FB in Hfl.
        pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hfl) as Rfl.
        apply (chunk_ok_val SEGS E _ F 1016 8 (SOff 33 0) FL);
        [ cbn [sv_denot]; rewrite E33, Z.add_0_r, UFL; reflexivity
        | cbn; lia | cbn; lia | ].
        replace (F + 1016) with (F + 1024 - 8) by lia. exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hfl).
      + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_nil.
      + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof Hsv as (Hra8 & Hsav).
        apply Forall_cons.
        * pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hra8) as Rra.
          apply (chunk_ok_val SEGS E _ (spZ (c_regs cx)) (-8) 8 (SOff 34 0) (raZ (c_regs cx)));
          [ cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity
          | cbn; lia | cbn; lia | ].
          replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia.
          exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hra8).
        * apply Forall_map, Forall_forall. intros j Hj. apply in_seq in Hj.
          pose proof (Hsav (Z.of_nat j) ltac:(lia)) as Hs. unfold lf_at in Hs.
          pose proof (kp_rdword_range _ _ _ (kp_aview_range SEGS (w_H W3) (ms_mem ms3)) Hs) as Rs.
          apply (chunk_ok_val SEGS E _ (spZ (c_regs cx)) (-16 - 8 * Z.of_nat j) 8 (SOff (35 + j) 0)
            (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 (if Z.of_nat j <? 2 then 8 + Z.of_nat j else 16 + Z.of_nat j)))));
          [ cbn [sv_denot]; rewrite (ESV j ltac:(lia)), Z.add_0_r; reflexivity
          | cbn; lia | cbn; lia | ].
          replace (spZ (c_regs cx) + (-16 - 8 * Z.of_nat j)) with (spZ (c_regs cx) - 16 - 8 * Z.of_nat j) by lia.
          exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hs).
    - apply pairwise_disjoint_of_extents.
      unfold lv_spill, lv_FR, lv_FL0, lv_saves, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U33, U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LS_F, LS_FK.
      repeat split; first [ (left; lia) | (right; lia) | (destruct HdFL; [right | left]; lia) ].
    - split; [|split; [exact I | exact I]].
      cbn [lv_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite U32, U33. change (2 ^ 0) with 1.
      repeat split; first [lia | apply Z.mod_1_r]. }
  clearbody E.
  rewrite (lf_shape_eta fy LF_leave ms3 Hsh).
  (* ---- +0x13c0 .. +0x13e0: F twice, the retired magic, `beqz s4` not taken, up to meta_fill_f5 ---- *)
  pose proof (@paj_run_call_plain_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNC.
  lv_run_call RUNC HS HJ.
  { intros a (r & Hr & Ha). cbn [lv_ss0 ss_mem In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val lv_spill lv_FR lv_FL0 lv_saves] in Ha;
      [exfalso; lia | | exfalso; lia | exfalso; lia].
    rewrite U32 in Ha. left. split; [|lia].
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LF_CID fp a HJ
      ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, FB. lia. }
  intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1.
  prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
  prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
  pmkst HS1.
  assert (Usp1' : bv_unsigned (ew E 2) = lf_sp1 cx) by (rewrite (EREG 2%nat 2%bv eq_refl), C2; exact Usp1).
  (* ---- meta_fill_f5(SH, 128): the frame's shadow retired ---- *)
  eapply SRr_bind.
  { eapply (aj_gx_set_shadow_at (fx := fy) SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f5) 0xf5 (ASS fy)
      _ _ _ W3 (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ _ _ _ _ ly3 S3 _ _
      LF_CID fp SH 128 (getr (ms_regs ms1) 1) HGX HJ1 ltac:(left; reflexivity)).
    - rewrite Q10, E19. reflexivity.
    - rewrite Q11. reflexivity.
    - lia.
    - rewrite EF. unfold shadow_addr. rewrite HSHeq. lia.
    - rewrite EF, FB. unfold shadow_addr. rewrite HSHeq. change (1024 / 8) with 128. lia.
    - assert (SP1 : spZ (ms_regs ms1) = lf_sp1 cx)
        by (change (bv_unsigned (getr (ms_regs ms1) 2) = lf_sp1 cx); rewrite Q2; exact Usp1').
      rewrite SP1. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D.
      rewrite D. replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - assert (SP1 : spZ (ms_regs ms1) = lf_sp1 cx)
        by (change (bv_unsigned (getr (ms_regs ms1) 2) = lf_sp1 cx); rewrite Q2; exact Usp1').
      rewrite SP1. change ESTACK with 4096. lia.
    - assert (SP1 : spZ (ms_regs ms1) = lf_sp1 cx)
        by (change (bv_unsigned (getr (ms_regs ms1) 2) = lf_sp1 cx); rewrite Q2; exact Usp1').
      rewrite SP1. lia.
    - rewrite Q3, (EREG 3%nat 3%bv eq_refl), C3. exact HGP.
    - rewrite Q4, (EREG 4%nat 4%bv eq_refl), C4. exact HTP.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
  cbv beta.
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hf5 & Hmf & Hpres2 & Hsbm2).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    mem2 md2 k2 HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID fp HAR2 HinF) as (_ & _ & HFpres2 & _). rewrite EF, FB in HFpres2.
  destruct (al_flag _ _ LAWS _ _ _ _ _ LF_CID fp HAR2 HinF) as (HFLpres2 & _). rewrite EFL in HFLpres2.
  jafter_call_keep_pi HS1 48%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
    - rewrite U9 in Ha. unfold LS_F, LS_FK in Ha. apply (mbyte_of_aview SEGS). apply Hmf; [lia|].
      rewrite HSHeq. unfold SHADOW_OFF. lia.
    - exfalso. lia.
    - rewrite U32 in Ha. apply (mbyte_of_aview SEGS). apply Hmf; [lia|]. apply HFvsSH. lia.
    - intros _. rewrite U32 in Ha. apply (apresent_writable SEGS). apply (proj1 (HFpres2 a ltac:(lia))).
    - rewrite U33 in Ha. apply (mbyte_of_aview SEGS). apply Hmf; [lia|]. intros Hc. apply HFLvsSH.
      replace FL with a by lia. exact Hc.
    - exfalso. lia.
    - rewrite U8 in Ha. apply (mbyte_of_aview SEGS). apply Hmf; [unfold spZ in *; lia|].
      rewrite HSHeq. unfold SHADOW_OFF. lia.
    - exfalso. lia. }
  rewrite <- restrict_mkst_fx in HS2.
  rewrite Q1.
  remember (havoc E 48 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS2.
  assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLD2 : forall nn, (nn < 48)%nat -> ew Ev2 nn = ew E nn)
    by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
  clear HE2.
  assert (V32 : bv_unsigned (ew Ev2 32) = F) by (rewrite OLD2 by lia; exact U32).
  assert (V33 : bv_unsigned (ew Ev2 33) = FL) by (rewrite OLD2 by lia; exact U33).
  (* the flag byte becomes writable *)
  lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx ?msx =>
    let r1 := eval vm_compute in (nth 2 (ss_mem ssx) lv_FL0) in
    pose proof (st_ok_pi_region_nth Ev2 ssx msx 2 r1 HS2 ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (ast_ok_pi_set_region Ev2 ssx msx 2 r1 (set_window r1 0 1) HS2 ltac:(vm_compute; reflexivity)
      ltac:(reflexivity) ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS Ev2 _ r1 0 1 HR1 ltac:(intros o Ho; cbn [YP09.r_base base_val];
         rewrite V33; replace (FL + o) with FL by lia; cbn [ms_mem restrict mkst];
         apply (apresent_writable SEGS); exact HFLpres2))) as HS3
  end.
  clear HS2 HR1. norm_pi HS3.
  (* ---- +0x13e4 .. +0x143c: the inline release, a0 := 0, the restores, up to `ret` ---- *)
  pose proof (@paj_flag_plain_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNF.
  lv_run_flag RUNF HS3 HJ2.
  { unfold LF_CID; lia. }
  { intros a (r & Hr & Ha). cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
    - exfalso. lia.
    - rewrite V32 in Ha. left.
      apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LF_CID fp a HJ2
        ltac:(left; reflexivity)).
      left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, FB. lia.
    - rewrite V33 in Ha. right. right. right. rewrite EFL. lia.
    - exfalso. lia. }
  { intros msr HSr.
    lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
      let r1 := eval vm_compute in (nth 2 (ss_mem ssx) lv_FL0) in
      pose proof (st_ok_pi_region_nth Ev2 ssx msr 2 r1 HSr ltac:(vm_compute; reflexivity)) as HR1;
      idtac;
      pose proof (field_of_region Ev2 (ms_mem msr) 33 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR1 V33
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)) as Vfl;
      change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(clear; lia));
      replace (FL + 0 + Z.of_nat 0) with FL in Vfl by (clear; lia);
      rewrite EFL, Vfl; reflexivity
    end. }
  intros ms5 mat5 HS5 HJ5 HF5 HFr5 HG5.
  (* ---- `ret` ---- *)
  prreg HS5 (1%bv : bv 5) Z1. prreg HS5 (2%bv : bv 5) Z2. prreg HS5 (3%bv : bv 5) Z3.
  prreg HS5 (4%bv : bv 5) Z4. prreg HS5 (8%bv : bv 5) Z8. prreg HS5 (9%bv : bv 5) Z9.
  prreg HS5 (10%bv : bv 5) Z10. prreg HS5 (18%bv : bv 5) Z18. prreg HS5 (19%bv : bv 5) Z19.
  prreg HS5 (20%bv : bv 5) Z20. prreg HS5 (21%bv : bv 5) Z21. prreg HS5 (22%bv : bv 5) Z22.
  prreg HS5 (23%bv : bv 5) Z23. prreg HS5 (24%bv : bv 5) Z24. prreg HS5 (25%bv : bv 5) Z25.
  prreg HS5 (26%bv : bv 5) Z26. prreg HS5 (27%bv : bv 5) Z27.
  pose proof (paj_ret_at (fx := fy) (L := link_listing) (PL := PL_link) (PI := PI) W3 Ev2 _ ms5
    (with_vm_backing (m_vm_lazy md2) mat5 md2) (lf_post SK B MT XN_LIB MS la_nul cx) HS5 eq_refl) as RET5.
  apply RET5; [vm_compute; reflexivity|]. clear RET5.
  intros mat6.
  pose proof (ajournal_gx_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat6 HJ5) as HJ6.
  (* ---- the bytes the three steps keep: all but the side frame's ---- *)
  set (X := fun a => aside_rng ly3 LF_CID fp (a mod 2 ^ 64)).
  assert (K1 : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms1))).
  { apply (lf_frame_kagree E _ _ _ (aside_rng ly3 LF_CID fp) HFr1).
    intros a _ (r & Hi & Hr). cbn [lv_ss0 ss_mem In] in Hi.
    destruct Hi as [<- | [<- | [<- | [<- | []]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val lv_spill lv_FR lv_FL0 lv_saves] in Hr;
      [exfalso; lia | | exfalso; lia | exfalso; lia].
    rewrite U32 in Hr. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, FB. lia. }
  assert (K2 : kagree SEGS X (rdW W3 (ms_mem ms1)) (rdW W3 mem2)).
  { apply (lv_kagree_of_aview SEGS (aside_rng ly3 LF_CID fp)). intros a Ha Hs. apply Hmf; [exact Ha|].
    intros Hc. apply Hs. right; left. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EF, FB.
    change (1024 / 8) with 128. rewrite HSHeq in Hc. lia. }
  assert (K3 : kagree SEGS X (rdW W3 mem2) (rdW W3 (ms_mem ms5))).
  { apply (lf_frame_kagree Ev2 _ _ _ (aside_rng ly3 LF_CID fp) HFr5).
    intros a _ (r & Hi & Hr). cbn [ss_mem In] in Hi.
    destruct Hi as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
    - exfalso. lia.
    - rewrite V32 in Hr. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, FB. lia.
    - rewrite V33 in Hr. right; right. rewrite EFL. lia.
    - exfalso. lia. }
  pose proof (lv_kt _ _ _ _ _ (lv_kt _ _ _ _ _ K1 K2) K3) as K.
  assert (NXI : forall a, in_img SEGS a -> ~ X a).
  { intros a Hi Hx. pose proof (pa_segs_low a Hi) as Hl. unfold X in Hx.
    rewrite Z.mod_small in Hx by (unfold kLowMemEnd in Hl; lia).
    exact (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ _ _ _ _ LF_CID fp a HAR3 HinF Hx) Hi). }
  assert (NXB : forall p n a, In (p, n) (ablocks B ly3 S3) -> p <= a < p + req_size n -> ~ X a).
  { intros p n a Hb Ha Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & Hp4 & Hpc & _).
    unfold X in Hx. rewrite Z.mod_small in Hx by lia.
    exact (lv_blk_not_side ly3 S3 W3 (ms_mem ms3) md3 LF_CID fp p n a HAR3 HinF Hb Ha Hx). }
  assert (NXF : forall a, amf_fp MS T3 a -> ~ X a).
  { intros a [Ha | [Ha | (f & m & Hf & Ha)]].
    - apply NXI. exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
    - apply NXI. exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
    - destruct (amf_gi_shape SEGS MS T3 _ Hgi) as [Et | (f' & Et)]; rewrite Et in Hf; [destruct Hf|].
      destruct Hf as [Hf | []]. injection Hf as E1 E2. subst f' m.
      apply (NXB f AMF_BLOCK a); [apply Hinc; rewrite Et; left; reflexivity|].
      unfold req_size, AMF_BLOCK in *. cbn. lia. }
  (* ---- the registers ---- *)
  assert (Era : getr (ms_regs ms5) 1 = getr (c_regs cx) 1) by (rewrite Z1, OLD2 by lia; exact E34).
  assert (Hc1 : getr (c_regs cx) 1 = w64 RA_LLVMF).
  { unfold w64. rewrite <- HRA. unfold raZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  unfold YK0s.ret_ok in HRET.
  (* ---- the post ---- *)
  unfold lf_post.
  exists fy, ly3, (stack_free_state LF_CID fp S3), (ms_regs ms5), (ms_mem ms5),
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
       (with_vm_backing (m_vm_lazy md2) mat5 md2)), k2, T3.
  split; [rewrite Era, HRET, Hc1; reflexivity|].
  split; [destruct Hfx as (_ & [Hc | Hc]); [unfold YK0o.frm_zero; rewrite Hc; exact HFRM | exact Hc]|].
  assert (FD : m_fds (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
                 (with_vm_backing (m_vm_lazy md2) mat5 md2)) = m_fds (c_md cx)).
  { rewrite !lf_wvb_fds. rewrite Hsbm2, !lf_wvb_fds. exact Hfd. }
  assert (FS : m_fs (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
                 (with_vm_backing (m_vm_lazy md2) mat5 md2)) = m_fs (c_md cx)).
  { rewrite !lf_wvb_fs. rewrite Hsbm2, !lf_wvb_fs. exact Hfs3. }
  split; [exact HJ6|]. split; [exact Hkev|].
  split.
  { apply aregs_preserved_eqs.
    - rewrite Z2, OLD2, (EREG 8%nat 8%bv eq_refl), C8 by lia. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite Z3, OLD2, (EREG 3%nat 3%bv eq_refl) by lia. exact C3.
    - rewrite Z4, OLD2, (EREG 4%nat 4%bv eq_refl) by lia. exact C4.
    - rewrite Z8, OLD2 by lia. exact (ESV 0%nat ltac:(lia)).
    - rewrite Z9, OLD2 by lia. exact (ESV 1%nat ltac:(lia)).
    - rewrite Z18, OLD2 by lia. exact (ESV 2%nat ltac:(lia)).
    - rewrite Z19, OLD2 by lia. exact (ESV 3%nat ltac:(lia)).
    - rewrite Z20, OLD2 by lia. exact (ESV 4%nat ltac:(lia)).
    - rewrite Z21, OLD2 by lia. exact (ESV 5%nat ltac:(lia)).
    - rewrite Z22, OLD2 by lia. exact (ESV 6%nat ltac:(lia)).
    - rewrite Z23, OLD2 by lia. exact (ESV 7%nat ltac:(lia)).
    - rewrite Z24, OLD2 by lia. exact (ESV 8%nat ltac:(lia)).
    - rewrite Z25, OLD2 by lia. exact (ESV 9%nat ltac:(lia)).
    - rewrite Z26, OLD2 by lia. exact (ESV 10%nat ltac:(lia)).
    - rewrite Z27, OLD2 by lia. exact (ESV 11%nat ltac:(lia)). }
  split; [rewrite Z10; reflexivity|].
  split.
  { destruct Hbl as (D & HT & HP). exists D. split; [exact HT|].
    rewrite stack_free_state_set_fs, ablocks_set_fs. exact HP. }
  split; [exact (amf_gi_keep SEGS MS X _ _ T3 K NXF Hgi)|].
  split; [exact (amf_env_keep SEGS MS X _ _ K (fun a Ha => NXF a (or_intror (or_introl Ha))) Henv)|].
  split.
  { apply (val_mem_keep SEGS X _ _ la_nul 1 0 K); [|exact Hla].
    intros k Hk. replace (la_nul + k) with la_nul by lia. apply NXI.
    exact (proj1 (HIMG la_nul ltac:(unfold lf_img_fp; right; right; right; right; right; left; lia))). }
  split; [intros fd; rewrite FD; reflexivity|].
  split; [rewrite FD; exact HNAMES|].
  split; [rewrite FS; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [apply MT_LE|].
  split.
  { assert (Edep : st_depot (stack_free_state LF_CID fp S3) = st_depot S3) by reflexivity.
    rewrite Edep. pose proof lf_wl_bound. lia. }
  intros i Hi. rewrite <- (Hpv i Hi).
  apply (aview_of_kagree SEGS X _ _ _ _ _ K).
  apply (NXB (c_p cx) (c_n cx)).
  - exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
      (ms_mem ms3) md3 k2 HB HJ ltac:(lia)).
  - unfold req_size. destruct (c_n cx =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.

(* the whole exit: the two frees (LLVMFuzzerTestOneInputExit.v), then the frame's release and the epilogue *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

Lemma lf_exit : lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
  (lf_post SK B MT XN_LIB MS la_nul) (lf_exit_inv B MT MS la_nul LF_MO_SET LF_MO_OP).
Proof.
  exact (lf_frees SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS LV MT_LE MT_OK
    AFREE4W LF_TRACE_FREE _ lf_leave).
Qed.

End a.
