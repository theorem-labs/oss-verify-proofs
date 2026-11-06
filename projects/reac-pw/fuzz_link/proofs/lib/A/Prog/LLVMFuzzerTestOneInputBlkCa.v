(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module paths and module names changed; 508 of its 563 lines of code are new or changed and 349 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...; listing
   (internal path) (internal record, sha256 e84d6f0c6974)): THE TWO CALLOCS of
   the walk, +0x494 .. +0x4b4 (0x82c68 .. 0x82c88), against the cut interface lib/A/Prog/LLVMFuzzerTestOneInputDefs.v:

     +0x494  lui s4, 2 ; addiw a1, s4, 0x298 ; a0 := 1 ; jal wrapper_calloc     calloc(1, 8856), returns at +0x4a4
     +0x4a4  mv s6, a0 ; a0 := 1 ; a1 := 0x204 ; jal wrapper_calloc              calloc(1, 516), returns at +0x4b4

   Each calloc is the raw allocator rule acalloc04_rule_w (LLVMFuzzerTestOneInputFree.v, lifted onto the walk's
   journal by aj_gx_calloc_w), at the cut `bk_cut` (the set-up's frame, slots, cursor, journal and g_nl / g_names /
   long_alias / odd data, plus the zero bytes of the blocks the phase owns). The rule's post `4096 <= res` is what
   refutes the two NULL arms (+0x4b8, +0x4c0) in LLVMFuzzerTestOneInputBlk.v; nothing here assumes calloc cannot
   fail.

     bk_callocs : FROM POST CA <- (forall .., bk_mid .. at +0x4b4 -> SRr .. POST)

   Section hypotheses: LAWS, TB, HSEGS, LV, MT_LE, MT_OK (image instance), and
     ACALLOC4W : forall fy, acalloc04_rule_w SK pa_segs B MT (pa_sigma LS___interceptor_trampoline_calloc)
                   LF_CALLOC_RA0 8856 2192   (the raw calloc rule with the io and depot clauses, open item W1;
                   at link's instance LF_CALLOC_RA0 = DEC_A_calloc_ra0 = 0x545a0, cmax = DEC_CALLOC_MAX,
                   cdepth = DEC_CALLOC_DEPTH, lib/A/LinkACalloc.v link_acalloc04 lifted to the w form)
     LF_TRACE_CALLOC : lf_trace_calloc B LF_CALLOC_RA0 (the two calloc sites' traces are in the universe).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop YGCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkPi BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputExit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* a block appended to a pairwise-apart list is not already in it *)
Lemma bk_pw_fresh : forall {X} (g : X -> Z * Z) (l : list X) (x : X) (rest : list (Z * Z)),
  pairwise zdisjoint (map g (l ++ [x]) ++ rest) -> 1 <= snd (g x) -> ~ In x l.
Proof.
  intros X g l x rest. induction l as [|y l IH]; intros HP Hn Hin; [destruct Hin|].
  cbn [app map pairwise] in HP. destruct HP as (HF & HP). rewrite Forall_forall in HF.
  destruct Hin as [-> | Hin].
  - pose proof (HF (g x) ltac:(apply in_or_app; left; apply in_map, in_or_app; right; left; reflexivity)) as D.
    unfold zdisjoint in D. lia.
  - exact (IH HP Hn Hin).
Qed.

(* the plain call run (LinkWalkSide.v paj_run_call_plain_x), as reac_link_alias_writeExit.v aw_run_call *)
Ltac bk_run_call RUNC HS HJ :=
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
      | ?other => fail "bk_run_call: the run does not stop at a call:" other
      end
    end
  end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Variable LF_CALLOC_RA0 : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis ACALLOC4W : forall fy : YK11.FPState,
  acalloc04_rule_w (fx := fy) SK SEGS B MT (pa_sigma LS___interceptor_trampoline_calloc) LF_CALLOC_RA0 8856 2192.
Hypothesis LF_TRACE_CALLOC : lf_trace_calloc B LF_CALLOC_RA0.

#[local] Notation BASEF cx := (@lf_base fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* the stack row's bottom, far below the realigned sp *)
Lemma bk_ly_bot : forall cx fp ly S W mem mdl k,
  JRN cx fp ly S W mem mdl k -> ly_bot ly + LLVMF_STK < spZ (c_regs cx) + ASTACK.
Proof.
  intros cx fp ly S W mem mdl k HJ.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  pose proof Hstatic as (_ & _ & _ & _ & _ & _ & Hbot & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  unfold ly_bot in *. rewrite Etop. try rewrite !Z.add_0_r in Hbot. lia.
Qed.

(* the carried slots of the set-up *)
Definition bk_slotvals (cx : lcx) (fp : Z) : list (Z * Z) :=
  [(LS_SHB, SHADOW_OFF); (LS_FK, lf_F cx fp); (LS_F, lf_F cx fp); (LS_F0, lf_F cx fp);
   (LS_WA, lf_F cx fp + LO_WA); (LS_B160, lf_F cx fp + LO_B160); (LS_B1A0, lf_F cx fp + LO_B1A0);
   (LS_B2E0, lf_F cx fp + LO_B2E0); (LS_B330, lf_F cx fp + LO_B330); (LS_ODD, LA_ODD)].

Lemma bk_slotvals_off : forall cx fp off v, In (off, v) (bk_slotvals cx fp) -> 0 <= off /\ off + 8 <= LF_MFRAME.
Proof.
  intros cx fp off v H. unfold bk_slotvals in H. cbn [In] in H.
  repeat (destruct H as [H | H];
    [inversion H; subst; unfold LS_SHB, LS_FK, LS_F, LS_F0, LS_WA, LS_B160, LS_B1A0, LS_B2E0, LS_B330, LS_ODD,
       LF_MFRAME; lia |]).
  destruct H.
Qed.

(* the set-up's data the loop keeps *)
Definition bk_data (kbs : list byte) (m : word -> option byte) : Prop :=
  anlk_at SEGS m LA_G_NL kbs /\ aiftab_at SEGS m LA_G_NL kbs lf_tab /\ lf_ifp m 64 /\
  lf_gnames_at 64 m /\ lf_gnames_w m /\ lf_odd_at m /\ lf_texts_at m /\ lf_la_at m.

Definition bk_zero (W : world SEGS) (mem : word -> option byte) (c : Z * Z) : Prop :=
  forall i, 0 <= i < snd c -> aview SEGS (w_H W) mem (fst c + i) = Some 0.

(* the data across a step that keeps g_nl, g_names, long_alias and odd's words; the odd and texts tables are
   taken at the new memory (unchanged read-only bytes, or Kpre.v lf_odd_texts_of_ro) *)
Lemma bk_data_keep : forall X m m' kbs, kagree SEGS X m m' ->
  (forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ X a) ->
  (forall a, LA_G_NAMES <= a < LA_G_NAMES + G_NAMES_SIZE -> ~ X a) ->
  (forall a, LA_LONG_ALIAS <= a < LA_LONG_ALIAS + 301 -> ~ X a) ->
  (forall a, LA_ODD <= a < LA_ODD + 48 -> ~ X a) ->
  lf_odd_at m' -> lf_texts_at m' -> bk_data kbs m -> bk_data kbs m'.
Proof.
  intros X m m' kbs HK XG XN XL XO Hodd' Htx' (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  assert (WG : wcarry SEGS m m' LA_G_NL NK_SIZE)
    by (intros i Hi _; rewrite HSEGS; apply LA_G_NL_writable; unfold NK_SIZE in *; lia).
  assert (WN : wcarry SEGS m m' LA_G_NAMES G_NAMES_SIZE)
    by (intros i Hi _; rewrite HSEGS; apply LA_G_NAMES_writable; unfold G_NAMES_SIZE in *; lia).
  assert (WL : wcarry SEGS m m' LA_LONG_ALIAS 301)
    by (intros i Hi _; rewrite HSEGS; apply LA_LONG_ALIAS_writable; lia).
  pose proof (lf_ifp_keep_ro X m m' 64 HK ltac:(lia) XG XO D3) as D3'.
  split; [apply (anlk_keep SEGS X m m' _ kbs HK WG); [intros i Hi; apply XG; lia | exact D1]|].
  split; [exact (lf_aiftab_keep_ro X m m' kbs HK XG XN D3 D3' Hodd' D2)|].
  split; [exact D3'|].
  split; [exact (lf_gnames_at_keep X m m' 64 HK ltac:(lia) XN D4)|].
  split; [exact (lf_gnames_w_keep X m m' HK WN XN D5)|].
  split; [exact Hodd'|]. split; [exact Htx'|].
  exact (lf_la_at_keep_ns X m m' HK WL XL (lf_la_slack_any HSEGS m') D8).
Qed.

(* the phase's cut: the set-up's frame, slots, cursor, journal and data, and the blocks it owns *)
Definition bk_cut (cx : lcx) (fp k ev : Z) (lv : Z) (ly : alayout) (S : astate) (W : world SEGS)
    (ms : machine_state) (mdl : Model) (T3 own : list (Z * Z)) (kbs : list byte) : Prop :=
  JRN cx fp ly S W (ms_mem ms) mdl k /\ frames S = [(LF_CID, fp)] /\
  lf_saved cx W ms /\ lf_header cx fp W ms /\ lf_fshadow cx fp W ms LF_SH0 /\
  (forall off v, In (off, v) (bk_slotvals cx fp) -> lf_slot cx W ms off v) /\
  lf_cur cx W ms (c_p cx) (c_n cx) /\
  lf_jbk B MT MS la_nul cx fp k ev 0 0%nat lv ly S W ms mdl T3 own /\
  bk_data kbs (rdW W (ms_mem ms)) /\
  (forall c, In c own -> In c (ablocks B ly S) /\ ~ In c (ablocks B (c_ly cx) (c_S cx)) /\ ~ In c T3 /\
     bk_zero W (ms_mem ms) c).

(* a stretch of the walk that writes nothing and only materialises the model *)
Lemma bk_cut_run : forall cx fp k ev lv ly S W ms ms' mdl mdl' T3 own kbs,
  bk_cut cx fp k ev lv ly S W ms mdl T3 own kbs ->
  JRN cx fp ly S W (ms_mem ms') mdl' k ->
  kagree SEGS (fun _ => False) (rdW W (ms_mem ms)) (rdW W (ms_mem ms')) ->
  m_fds mdl' = m_fds mdl -> m_fs mdl' = m_fs mdl ->
  bk_cut cx fp k ev lv ly S W ms' mdl' T3 own kbs.
Proof.
  intros cx fp k ev lv ly S W ms ms' mdl mdl' T3 own kbs
    (HJ & Hfr & Hsv & Hhd & Hfs & HSL & Hcur & Hjbk & Hdat & Hown) HJ' HK Hfd Hfs'.
  split; [exact HJ'|]. split; [exact Hfr|].
  split; [exact (lf_saved_keep _ cx W ms W ms' HK (fun a _ H => H) Hsv)|].
  split; [exact (lf_header_keep _ cx fp W ms W ms' HK (fun a _ H => H) Hhd)|].
  split; [exact (lf_fshadow_keep _ cx fp W ms W ms' LF_SH0 HK (fun a _ H => H) Hfs)|].
  split; [intros off v Hin; exact (lf_slot_keep _ cx W ms W ms' off v HK (fun i _ H => H) (HSL off v Hin))|].
  split; [exact (lf_cur_keep _ cx W ms W ms' _ _ HK (fun a _ H => H) Hcur)|].
  split; [exact (lf_jbk_keep B MT MS la_nul _ cx fp k ev 0 0%nat lv ly S W ms mdl T3 own W ms' mdl' HK Hfd Hfs'
                   (fun a _ H => H) Hjbk)|].
  split.
  { pose proof Hdat as (_ & _ & _ & _ & _ & D6 & D7 & _).
    apply (bk_data_keep _ _ _ kbs HK); try (intros a _ H; exact H).
    - exact (lf_odd_at_keep _ _ _ HK (fun a _ H => H) D6).
    - exact (lf_texts_at_keep _ _ _ HK (fun a _ H => H) D7).
    - exact Hdat. }
  intros c Hc. destruct (Hown c Hc) as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros i Hi. rewrite <- (H4 i Hi). apply (aview_of_kagree SEGS _ _ _ _ _ _ HK). intros H; exact H.
Qed.

(* ==========================================================================
   A calloc of the phase: calloc(1, n), at a site of LF_CALLOC_RAS
   ========================================================================== *)

Lemma bk_calloc_step : forall (fy : YK11.FPState) cx fp T3 own n ev lv k ly3 S3 W3
    (ms3 : machine_state) md3 kbs (regs : bvmap 5 word) rao (Q : world SEGS -> config -> Prop),
  BASEF cx ->
  bk_cut cx fp k ev lv ly3 S3 W3 ms3 md3 T3 own kbs ->
  k + 1 <= EV_LIB -> 0 <= n <= 8856 -> 0 <= lv -> lv + n <= LIVE_LIB ->
  getr regs 10 = w64 1 -> getr regs 11 = w64 n ->
  spZ regs = lf_sp1 cx -> s0Z regs = spZ (c_regs cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 1 = Z_to_bv 64 (link_text + rao) -> In (link_text + rao) LF_CALLOC_RAS ->
  (forall (W2 : world SEGS) ly2 S2 (regs2 : bvmap 5 word) mem2 md2 res,
     aregs_preserved regs regs2 -> getr regs2 10 = w64 res -> 4096 <= res ->
     bk_cut cx fp (k + 1) (ev + 1) (lv + n) ly2 S2 W2 (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2
       T3 ((res, n) :: own) kbs ->
     SRr SEGS W2 (mkCfg (@mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W3 (mkCfg (@mkst fy regs (Z_to_bv 64 (pa_sigma LS___interceptor_trampoline_calloc)) (ms_mem ms3)
    (seg_rom SEGS)) md3) Q.
Proof.
  intros fy cx fp T3 own n ev lv k ly3 S3 W3 ms3 md3 kbs regs rao Q
    HB (HJ & Hfr & Hsv & Hhd & Hfs & HSL & Hcur & Hjbk & Hdat & Hown) Hk Hn Hlv0 Hlv R10 R11 Hsp Hs0 R3 R4 R1 Hsite K.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HB as (HPRE & _ & _ & HLAN & HMSE & _).
  pose proof HPRE as (HAFN & _ & _ & _ & Hpin0 & _ & _ & _ & Hnev & Hlive0 & _).
  pose proof HAFN as (_ & _ & _ & HGP & HTP & _).
  pose proof Hjbk as (Hkev & Hbb & Hfa & _ & Hfd & Hfs3 & _ & Hwl & Hgi & _ & Hbl & Hinc & Hla3 & Hro3 & _).
  destruct (lf_img_facts B MS la_nul HSEGS TB HMSE HLAN) as (HIMG & HREL).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k HB HJ) as (H16 & Hceil & Hslo & Hshi & H47 & Hwin & HAR3).
  assert (Hs1 : spZ (c_regs cx) - 416 - 16 <= lf_sp1 cx <= spZ (c_regs cx) - 416 /\ lf_sp1 cx mod 32 = 0).
  { unfold lf_sp1. pose proof (lf_sp1_range (spZ (c_regs cx)) ltac:(unfold LF_MFRAME, LLVMF_STK in *; lia) H16)
      as (R & R32 & _). unfold LF_MFRAME in R. split; [exact R | exact R32]. }
  destruct Hs1 as (Hs1 & Hs32).
  pose proof (bk_ly_bot cx fp ly3 S3 W3 (ms_mem ms3) md3 k HJ) as Hbot.
  unfold LLVMF_STK in *.
  assert (HPB : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by exact (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3 W3
              (ms_mem ms3) md3 k HB HJ).
  assert (Hpin : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))
    by (intros Hc; destruct Hpin0 as [(Hz & _) | (_ & Hi)]; [lia | exact Hi]).
  destruct (lf_saved_ra_s0 cx W3 ms3 Hsv) as (H8 & H16w).
  unfold LF_CALLOC_RAS, link_text in Hsite. cbn [In] in Hsite.
  assert (Hrao : rao = 0x82c78 - 0x821cc \/ rao = 0x82c88 - 0x821cc) by lia.
  assert (Hra : raZ regs = link_text + rao)
    by (unfold raZ; rewrite R1; apply unsigned_lit_small; unfold link_text; lia).
  assert (Hra4 : 4096 <= raZ regs) by (rewrite Hra; unfold link_text; lia).
  assert (Hret : YK0s.ret_ok (getr regs 1)).
  { rewrite R1, <- (lv_text LV). apply ret_ok_codeptr_v; [lia|].
    destruct Hrao as [-> | ->]; reflexivity. }
  destruct (lf_site_chain SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
    cx [(LF_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k regs HB HJ H8 H16w ltac:(lia) Hs0 Hra4) as (HCH & _).
  assert (HTR : In (ctrace0 LF_CALLOC_RA0 regs (lf_chain cx)) (as_universe B)).
  { apply (lf_calloc_trace SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LF_CALLOC_RA0 cx regs
      HB LF_TRACE_CALLOC). rewrite Hra. unfold LF_CALLOC_RAS, link_text. cbn [In]. lia. }
  assert (Hbl0 : forall c, In c (ablocks B (c_ly cx) (c_S cx)) -> In c (ablocks B ly3 S3)).
  { destruct Hbl as (D & _ & HP). intros c Hc. apply (Permutation_in c (Permutation_sym HP)).
    apply in_or_app. right. apply in_or_app. right. exact Hc. }
  eapply SRr_bind.
  { apply (@aj_gx_calloc_w fy rc SK SEGS B MT LAWS pa_segs_low _ _ _ _ (ACALLOC4W fy) G_HARNESS 0 [] W3 regs (ms_mem ms3)
      32768 (spZ (c_regs cx)) (amf_harness_fp (c_T cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(LF_CID, fp)] ly3 S3 md3 k 1 n (getr regs 1) (lf_chain cx) HJ).
    - rewrite Hsp. unfold ASTACK in Hbot. lia.
    - exact R10.
    - exact R11.
    - lia.
    - lia.
    - unfold MALLOC_MAX. lia.
    - lia.
    - unfold LIVE_LIB in *. lia.
    - rewrite Hsp. pose proof (Z.div_mod (lf_sp1 cx) 32 ltac:(lia)) as D. rewrite Hs32 in D. rewrite D.
      replace (32 * (lf_sp1 cx / 32) + 0) with ((lf_sp1 cx / 32 * 2) * 16) by lia. apply Z.mod_mul. lia.
    - rewrite Hsp. unfold ASTACK. lia.
    - rewrite Hsp. lia.
    - rewrite Hsp. lia.
    - rewrite R3. exact HGP.
    - rewrite R4. exact HTP.
    - reflexivity.
    - exact Hret.
    - unfold EV_LIB in *. lia.
    - exact HCH.
    - exact HTR.
    - apply MT_OK. }
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & R102 & Hfr2 & H4096 & Hl2 & Hzero & HK
    & _ & HW & Hio).
  rewrite Z.mul_1_l in Hl2, Hzero, HK.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly2 S2 W2
    mem2 md2 (k + 1) HB HJ2) as (_ & _ & _ & _ & _ & _ & HAR2).
  destruct (same_io_fds_fs md3 md2 Hio) as (Hfd2 & Hfs2).
  assert (Hb : In (res, n) (ablocks B ly2 S2)) by (rewrite Hl2; apply in_or_app; right; left; reflexivity).
  assert (Hr1 : 1 <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [lia | apply Z.eqb_neq in E; lia]).
  assert (Hfresh : ~ In (res, n) (ablocks B ly3 S3)).
  { destruct (al_sep _ _ LAWS _ _ _ _ _ HAR2) as (HPw & _). rewrite Hl2 in HPw.
    exact (bk_pw_fresh (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (res, n) _ HPw Hr1). }
  assert (Hsub : forall c, In c (ablocks B ly3 S3) -> In c (ablocks B ly2 S2))
    by (intros c Hc; rewrite Hl2; apply in_or_app; left; exact Hc).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hb) as (_ & Hp4 & Hpc & Happ & _ & _ & _).
  set (E := fun a => res <= a < res + req_size n) in *.
  assert (HKP : akept SEGS B ly3 S3 W3 (ms_mem ms3) W2 mem2 (lf_sp1 cx - ASTACK) (lf_sp1 cx) E).
  { rewrite <- Hsp. apply (akept_of_acall_kept SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ HK). intros a Ha; exact Ha. }
  assert (HCALL : lf_call B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E).
  { split; [unfold ASTACK; lia|]. split; [unfold ASTACK; lia|]. split; [exact HKP|].
    exact (ashadow_kept_of_AR B LAWS ly3 S3 W3 (ms_mem ms3) md3 ly2 S2 W2 mem2 md2 HAR3 HAR2). }
  set (ms2 := @mkst fy regs2 (getr regs 1) mem2 (seg_rom SEGS)).
  assert (HinF : In (LF_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
  assert (HinF2 : In (LF_CID, fp) (frames S2)) by (rewrite Hfr2; exact HinF).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
  (* the new block's bytes are heap bytes: not the stack, the frame, the shadow, the image, another block *)
  assert (NI : forall a, E a -> ~ in_img SEGS a).
  { intros a Ha. destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR2 ltac:(left; exists res, n; split; [exact Hb | exact Ha]))
      as (_ & Hni). exact Hni. }
  assert (NB : forall c a, In c (ablocks B ly3 S3) -> E a -> ~ (fst c <= a < fst c + req_size (snd c))).
  { intros c a Hc Ha Hca.
    assert (Hne : (res, n) <> c) by (intros Heq; apply Hfresh; rewrite Heq; exact Hc).
    pose proof (ex_blk_apart B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hb (Hsub c Hc) Hne) as D.
    unfold zdisjoint, E in *. cbn [fst snd] in D. lia. }
  assert (Hfa2 : forall c q, frame_addr ly2 c q = frame_addr (c_ly cx) c q)
    by (intros c q; exact (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c q HJ2))).
  assert (NF : forall a, E a -> ~ (lf_F cx fp <= a < lf_F cx fp + 1024)).
  { intros a Ha Hfa'. pose proof LF_frame_slot as (FB & _). destruct (al_sep _ _ LAWS _ _ _ _ _ HAR2) as (HPw & _).
    pose proof (pairwise_In zdisjoint _ (res, req_size n) (frame_addr ly2 LF_CID fp, fs_frame_bytes LF_CID) _ _ eq_refl HPw
      ltac:(apply in_map_iff; exists (res, n); split; [reflexivity | exact Hb])
      ltac:(apply in_map_iff; exists (LF_CID, fp); split; [reflexivity | exact HinF2])) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. unfold lf_F in Hfa'. rewrite <- (Hfa2 LF_CID fp) in Hfa'.
    rewrite FB in *. unfold E in Ha. lia. }
  assert (NS : forall a, E a -> ~ (lf_SH cx fp <= a < lf_SH cx fp + 128)).
  { intros a Ha Hsa. destruct (al_sep _ _ LAWS _ _ _ _ _ HAR2) as (_ & HSf). rewrite Forall_forall in HSf.
    pose proof (HSf (LF_CID, fp) HinF2) as (F1 & F2). cbn [fst snd] in F1, F2.
    pose proof LF_frame_slot as (FB & _).
    assert (Fc : frame_addr ly2 LF_CID fp <= alloc_ceiling) by (rewrite FB in F2; lia).
    unfold lf_SH, lf_F, shadow_of_addr, SHADOW_OFF in Hsa. rewrite <- (Hfa2 LF_CID fp) in Hsa.
    pose proof (Z.div_le_mono _ _ 8 ltac:(lia) Fc) as Fd.
    unfold E in Ha. lia. }
  assert (NSTK : forall a, E a -> ~ (lf_sp1 cx <= a < spZ (c_regs cx))) by (intros a Ha Hs; unfold E in Ha; lia).
  (* the cut at the return state *)
  assert (Hsv2 : lf_saved cx W2 ms2).
  { exact (lf_saved_callee B cx ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL
      ltac:(intros a Ha HEa; unfold lf_saved_fp in Ha; pose proof (lf_sp1_le cx); apply (NSTK a HEa);
            unfold LF_MFRAME in *; lia) Hsv). }
  assert (Hhd2 : lf_header cx fp W2 ms2).
  { exact (lf_header_callee B cx fp ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL HinF Hfa
      ltac:(intros a Ha HEa; pose proof LF_frame_slot as (FB & _); unfold lf_header_fp in Ha; rewrite FB in Ha;
            apply (NF a HEa); lia) Hhd). }
  assert (Hfs2' : lf_fshadow cx fp W2 ms2 LF_SH0).
  { exact (lf_fshadow_callee B cx fp ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E HCALL HinF Hfa
      ltac:(intros a Ha HEa; unfold lf_fshadow_fp in Ha; apply (NS a HEa); lia) Hfs). }
  assert (Hcur2 : lf_cur cx W2 ms2 (c_p cx) (c_n cx)).
  { exact (lf_cur_callee B cx ASTACK ly3 S3 ly2 S2 W3 ms3 W2 ms2 E _ _ HCALL
      ltac:(intros a Ha HEa; unfold lf_cur_fp in Ha; pose proof (lf_sp1_le cx); apply (NSTK a HEa);
            unfold LF_MFRAME in *; lia) Hcur). }
  pose proof (lf_call_kagree B cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E HCALL) as HKG.
  assert (SL : forall off v, 0 <= off -> off + 8 <= LF_MFRAME -> lf_slot cx W3 ms3 off v -> lf_slot cx W2 ms2 off v).
  { intros off v Ho1 Ho2 Hs. apply (lf_slot_keep _ cx W3 ms3 W2 ms2 off v HKG); [|exact Hs].
    intros i Hi. pose proof (lf_sp1_le cx) as (P1 & P2).
    apply (lfx_above B cx ASTACK ly3 S3 ly2 S2 E); [unfold ASTACK; lia | unfold ASTACK; lia | lia |].
    intros HEa. apply (NSTK _ HEa). lia. }
  assert (NIM : forall a, lf_img_fp MS la_nul a -> ~ lf_X B ly3 S3 ly2 S2 (lf_sp1 cx - ASTACK) (lf_sp1 cx) E a)
    by (intros a Ha; apply (lfx_imgfp B MS la_nul ly3 S3 ly2 S2 _ _ E a HIMG Ha);
        intros HEa; exact (NI a HEa (proj1 (HIMG a Ha)))).
  assert (HnE : ~ E la_nul)
    by (intros HEa; apply (NI la_nul HEa);
        exact (proj1 (HIMG la_nul ltac:(unfold lf_img_fp; right; right; right; right; right; left; lia)))).
  assert (Hla2 : val_mem SEGS (rdW W2 mem2) la_nul 1 0)
    by exact (lf_la_nul_callee B MS la_nul cx ASTACK ly3 S3 ly2 S2 W3 (ms_mem ms3) W2 mem2 E HIMG HCALL HnE Hla3).
  assert (HRO2 : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W2) mem2)).
  { apply (lf_aro_callee B cx ASTACK ly3 S3 ly2 S2 W3 _ W2 _ E HREL HCALL); [|exact Hro3].
    intros a Hro HEa. apply (NI a HEa).
    destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL a Hr)]. }
  assert (Hjbk2 : lf_jbk B MT MS la_nul cx fp (k + 1) (ev + 1) 0 0%nat (lv + n) ly2 S2 W2 ms2 md2 T3 ((res, n) :: own)).
  { eapply lf_jbk_restate; [exact MT_LE | | | | | | | ].
    - apply (lf_jbk_callee B MT MS la_nul cx fp k ev 0 0%nat lv ly3 S3 W3 ms3 md3 T3 _ ASTACK ly2 S2 W2 ms2 md2 E
        HIMG HREL HCALL); [| | exact HPB | rewrite Hfd2; reflexivity | rewrite Hfs2; reflexivity | exact Hla2 | exact Hjbk].
      + intros a Ha HEa. unfold lf_jbk_fp_c, amf_fp in Ha.
        destruct Ha as [[Ha | [Ha | (f & m & Hf & Ha)]] | Ha].
        * apply (NI a HEa). exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
        * apply (NI a HEa). exact (proj1 (HIMG a ltac:(unfold lf_img_fp; tauto))).
        * destruct (amf_gi_shape SEGS MS T3 _ Hgi) as [Et | (f' & Et)]; rewrite Et in Hf; [destruct Hf|].
          destruct Hf as [Hf | []]. injection Hf as E1 E2. subst f' m.
          assert (HfT : In (f, AMF_BLOCK) T3) by (rewrite Et; left; reflexivity).
          apply (NB (f, AMF_BLOCK) a (Hinc _ HfT) HEa). cbn [fst snd]. unfold req_size, AMF_BLOCK in *. cbn. lia.
        * assert (Hcn : 0 < c_n cx) by lia.
          apply (NB (c_p cx, c_n cx) a (HPB Hcn) HEa).
          cbn [fst snd]. unfold req_size. destruct (c_n cx =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia | lia].
      + intros a Hro HEa. apply (NI a HEa).
        destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HREL a Hr)].
    - exact Hfa2.
    - lia.
    - rewrite (blocks_bytes_bsum B ly2 S2), Hl2. rewrite (blocks_bytes_bsum B ly3 S3) in Hbb.
      rewrite bsum_app. change (bsum [(res, n)]) with (n + 0). lia.
    - lia.
    - exact (lf_bl_cons B cx own T3 ly3 S3 ly2 S2 (res, n) Hbl Hl2).
    - intros c Hc. exact (Hsub c (Hinc c Hc)). }
  apply (K W2 ly2 S2 regs2 mem2 md2 res HP R102 H4096).
  split; [exact HJ2|]. split; [rewrite Hfr2; exact Hfr|].
  split; [exact Hsv2|]. split; [exact Hhd2|]. split; [exact Hfs2'|].
  split; [intros off v Hin; destruct (bk_slotvals_off cx fp off v Hin) as (O1 & O2); exact (SL off v O1 O2 (HSL off v Hin))|].
  split; [exact Hcur2|]. split; [exact Hjbk2|].
  split.
  { assert (Hot : lf_odd_at (rdW W2 mem2) /\ lf_texts_at (rdW W2 mem2))
      by (eapply lf_odd_texts_of_ro; eassumption).
    destruct Hot as (Hodd2 & Htx2).
    apply (bk_data_keep _ _ _ kbs HKG); [| | | | exact Hodd2 | exact Htx2 | exact Hdat];
      intros a Ha; apply NIM; unfold lf_img_fp; tauto. }
  intros c [<- | Hc].
  - split; [exact Hb|]. split; [intros Hc; exact (Hfresh (Hbl0 _ Hc))|].
    split; [intros Hc; exact (Hfresh (Hinc _ Hc))|]. intros i Hi. exact (Hzero i Hi).
  - destruct (Hown c Hc) as (H1 & H2 & H3 & H4).
    split; [exact (Hsub c H1)|]. split; [exact H2|]. split; [exact H3|].
    intros i Hi. rewrite <- (H4 i Hi). apply (aview_of_kagree SEGS _ _ _ _ _ _ HKG).
    destruct c as [cp cn]. cbn [fst snd] in *.
    apply (lfx_blk B ly3 S3 ly2 S2 _ _ E cp cn); [exact H1 | lia |].
    intros HEa. apply (NB (cp, cn) (cp + i) H1 HEa). cbn [fst snd].
    unfold req_size. destruct (cn =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.

(* ==========================================================================
   The two callocs: from the cut at +0x494 to the state at +0x4b4
   ========================================================================== *)

(* the state at +0x4b4 (LF_ca2_ra): both blocks returned (md in s6, mk in a0), s4 = 0x2000 *)
Definition bk_mid (cx : lcx) (fy : YK11.FPState) (fp k2 : Z) (ly : alayout) (S : astate) (W : world SEGS)
    (ms : machine_state) (mdl : Model) (T3 : list (Z * Z)) (md mk : Z) (kbs : list byte) : Prop :=
  lf_shape fy LF_ca2_ra ms /\ lf_core cx ms /\
  getr (ms_regs ms) 18 = w64 LA_G_NL /\ getr (ms_regs ms) 19 = w64 (lf_SH cx fp) /\
  getr (ms_regs ms) 20 = w64 0x2000 /\ getr (ms_regs ms) 22 = w64 md /\ getr (ms_regs ms) 10 = w64 mk /\
  getr (ms_regs ms) 26 = w64 (lf_F cx fp + LO_WA) /\ getr (ms_regs ms) 27 = w64 SHADOW_OFF /\
  4096 <= md /\ 4096 <= mk /\
  bk_cut cx fp (k2 + 2) 2 (MD_SIZE + MK_SIZE) ly S W ms mdl T3 [(mk, MK_SIZE); (md, MD_SIZE)] kbs /\
  nlk_wf kbs /\ nk_open kbs = 0 /\ nk_misuse kbs = 0 /\ nk_opened kbs = nk_closed kbs /\ nk_opened kbs = 0.

Lemma bk_pres4 : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  getr regs' 18 = getr regs 18 /\ getr regs' 20 = getr regs 20 /\ getr regs' 26 = getr regs 26 /\
  getr regs' 27 = getr regs 27.
Proof.
  intros regs regs' H. unfold aregs_preserved, acallee_saved in H.
  refine (conj (H 18 ltac:(lia)) (conj (H 20 ltac:(lia)) (conj (H 26 ltac:(lia)) (H 27 ltac:(lia))))).
Qed.

Lemma bk_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 26%bv; 27%bv] ->
  getr regs' r = getr regs r.
Proof.
  intros regs regs' H r Hr.
  destruct (ex_pres _ _ H) as (A2 & A3 & A4 & A8 & A9 & A19 & A22).
  destruct (bk_pres4 _ _ H) as (A18 & A20 & A26 & A27).
  repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr.
Qed.

Ltac bk_inr := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma bk_callocs : forall POST,
  (forall cx fy fp k2 ly S W ms mdl T3 md mk kbs, BASEF cx -> @BoxBase.fxr fx fy ->
     bk_mid cx fy fp k2 ly S W ms mdl T3 md mk kbs -> SRr SEGS W (mkCfg ms mdl) (POST cx)) ->
  lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST
    (lf_ca_inv B MT MS la_nul).
Proof.
  intros POST K cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HX.
  destruct HX as (kbs & Hset & R18 & R26 & R27 & HODD & Hnl & Hwf & Ho & Hmi & Hoc & Hnif & Hif & Hifp & Hnch
    & Hnsent & Hnext & Hop0 & Hgn).
  destruct Hset as (Hsh & Hcore & Hsv & Hhd & Hfs & R19 & SSHB & SFK & SF & SF0 & SWA & SB160 & SB1A0 & SB2E0 & SB330
    & Hcur & Hjbk & Hgw & Hodd & Htx & Hla).
  pose proof Hcore as (C2 & C8 & C9 & C3 & C4).
  pose proof HB as (_ & _ & HGX & _).
  pose proof Hjbk as (Hk0 & _).
  pose proof (lf_sp1_le cx) as (SP1 & SP2).
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    (ms_mem ms3) md3 k2 HB HJ) as (_ & Hceil & _).
  pose proof (ex_sp1 cx) as SP3. pose proof asan_consts as ((C1a & C1b) & _).
  assert (S10 : 0 <= lf_sp1 cx) by (unfold LLVMF_STK, LF_MFRAME in *; lia).
  assert (HC0 : bk_cut cx fp k2 0 0 ly3 S3 W3 ms3 md3 (c_T cx) [] kbs).
  { split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hsv|]. split; [exact Hhd|]. split; [exact Hfs|].
    split; [|split; [exact Hcur|]; split; [exact Hjbk|]; split; [|intros c []]].
    - intros off v Hin. unfold bk_slotvals in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [inversion Hin; subst; assumption |]). destruct Hin.
    - exact (conj Hnl (conj Hif (conj Hifp (conj Hgn (conj Hgw (conj Hodd (conj Htx Hla))))))). }
  rewrite (lf_shape_eta fy LF_ca ms3 Hsh).
  pose proof (@paj_run_call_plain_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNC.
  (* ---- +0x494 .. +0x4a0: s4 := 0x2000, a1 := 0x2298, a0 := 1, the call of calloc ---- *)
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (ex_env_agree (ms_regs ms3) []) as HA. fold E in HA.
  assert (HS : st_ok_pi (fx := fy) pa_segs pa_val E (mkSS LF_ca sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LF_ca)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  clearbody E.
  bk_run_call RUNC HS HJ.
  { apply awr_ok_x_nil. }
  intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1.
  prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
  prreg HS1 (20%bv : bv 5) Q20.
  pmkst HS1.
  lazymatch type of HS1 with st_ok _ _ ?ssx _ =>
    assert (KR1 : forall r : bv 5, sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
                   getr (ms_regs ms1) r = getr (ms_regs ms3) r)
      by (intros r Hr; exact (ex_reg_abs fy W3 E ssx ms1 _ r HS1 HA Hr))
  end.
  assert (G1 : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 26%bv; 27%bv] ->
                 getr (ms_regs ms1) r = getr (ms_regs ms3) r)
    by (intros r Hr; apply KR1; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr).
  pose proof (bk_cut_run cx fp k2 0 0 ly3 S3 W3 ms3 ms1 md3 _ (c_T cx) [] kbs HC0 HJ1 (kagree_frame_nil E _ _ HFr1)
    ltac:(rewrite lf_wvb_fds; reflexivity) ltac:(rewrite lf_wvb_fs; reflexivity)) as HC1.
  (* calloc(1, 8856), returning to +0x4a4 *)
  eapply (bk_calloc_step fy cx fp (c_T cx) [] MD_SIZE 0 0 k2 ly3 S3 W3 ms1 _ kbs (ms_regs ms1)
    (0x82c78 - 0x821cc) (POST cx) HB HC1).
  { unfold EV_LIB. lia. }
  { unfold MD_SIZE. lia. }
  { lia. }
  { unfold MD_SIZE, LIVE_LIB. lia. }
  { rewrite Q10. reflexivity. }
  { rewrite Q11. reflexivity. }
  { apply ex_sp; [exact S10|]. rewrite (G1 2%bv ltac:(bk_inr)). exact C2. }
  { apply (ex_s0 cx). rewrite (G1 8%bv ltac:(bk_inr)). exact C8. }
  { rewrite (G1 3%bv ltac:(bk_inr)). exact C3. }
  { rewrite (G1 4%bv ltac:(bk_inr)). exact C4. }
  { rewrite Q1, (lv_text LV). try (f_equal; unfold link_text; lia). }
  { unfold LF_CALLOC_RAS, link_text. cbn [In]. lia. }
  intros W2 ly2 S2 regs2 mem2 md2 md HP2 R102 Hmd4 HC2.
  pose proof (bk_pres _ _ HP2) as P2.
  assert (EQ2 : @mkst fy regs2 (getr (ms_regs ms1) 1) mem2 (seg_rom SEGS) =
                @mkst fy regs2 (Z_to_bv 64 (BASE + LF_ca1_ra)) mem2 (seg_rom SEGS))
    by (rewrite Q1; try (f_equal; f_equal; unfold LF_ca1_ra, AF_LLVMFuzzerTestOneInput; lia)).
  rewrite EQ2 in HC2 |- *.
  (* ---- +0x4a4 .. +0x4b0: s6 := md, a0 := 1, a1 := 516, the call of calloc ---- *)
  set (E2 := Eimg (Ereg regs2 [])).
  assert (HEI2 : img_env pa_val A_LIM E2) by apply Eimg_env.
  assert (E2_10 : ew E2 10 = getr regs2 10) by (apply ew_Eimg_Ereg_nat; reflexivity).
  pose proof (ex_env_agree regs2 []) as HA2. fold E2 in HA2.
  assert (HS2 : st_ok_pi (fx := fy) pa_segs pa_val E2 (mkSS LF_ca1_ra sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W2) (@mkst fy regs2 (Z_to_bv 64 (BASE + LF_ca1_ra)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - constructor.
    - cbn. tauto.
    - split; [exact I | split; exact I]. }
  clearbody E2.
  pose proof HC2 as (HJ2 & _).
  bk_run_call RUNC HS2 HJ2.
  { apply awr_ok_x_nil. }
  intros ms4 mat4 HS4 HJ4 HF4 HFr4 HG4.
  prreg HS4 (10%bv : bv 5) Q10b. prreg HS4 (11%bv : bv 5) Q11b. prreg HS4 (1%bv : bv 5) Q1b.
  prreg HS4 (22%bv : bv 5) Q22b.
  pmkst HS4.
  lazymatch type of HS4 with st_ok _ _ ?ssx _ =>
    assert (KR2 : forall r : bv 5, sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
                   getr (ms_regs ms4) r = getr regs2 r)
      by (intros r Hr; exact (ex_reg_abs fy W2 E2 ssx ms4 _ r HS4 HA2 Hr))
  end.
  assert (G4 : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 26%bv; 27%bv] ->
                 getr (ms_regs ms4) r = getr regs2 r)
    by (intros r Hr; apply KR2; repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]); destruct Hr).
  pose proof (bk_cut_run cx fp _ _ _ ly2 S2 W2 _ ms4 md2 _ (c_T cx) _ kbs HC2 HJ4 (kagree_frame_nil E2 _ _ HFr4)
    ltac:(rewrite lf_wvb_fds; reflexivity) ltac:(rewrite lf_wvb_fs; reflexivity)) as HC3.
  (* calloc(1, 516), returning to +0x4b4 *)
  eapply (bk_calloc_step fy cx fp (c_T cx) [(md, MD_SIZE)] MK_SIZE (0 + 1) (0 + MD_SIZE) (k2 + 1) ly2 S2 W2 ms4 _ kbs
    (ms_regs ms4) (0x82c88 - 0x821cc) (POST cx) HB HC3).
  { unfold EV_LIB. lia. }
  { unfold MK_SIZE. lia. }
  { unfold MD_SIZE. lia. }
  { unfold MD_SIZE, MK_SIZE, LIVE_LIB. lia. }
  { rewrite Q10b. reflexivity. }
  { rewrite Q11b. reflexivity. }
  { apply ex_sp; [exact S10|]. rewrite (G4 2%bv ltac:(bk_inr)), (P2 2%bv ltac:(bk_inr)), (G1 2%bv ltac:(bk_inr)). exact C2. }
  { apply (ex_s0 cx). rewrite (G4 8%bv ltac:(bk_inr)), (P2 8%bv ltac:(bk_inr)), (G1 8%bv ltac:(bk_inr)). exact C8. }
  { rewrite (G4 3%bv ltac:(bk_inr)), (P2 3%bv ltac:(bk_inr)), (G1 3%bv ltac:(bk_inr)). exact C3. }
  { rewrite (G4 4%bv ltac:(bk_inr)), (P2 4%bv ltac:(bk_inr)), (G1 4%bv ltac:(bk_inr)). exact C4. }
  { rewrite Q1b, (lv_text LV). try (f_equal; unfold link_text; lia). }
  { unfold LF_CALLOC_RAS, link_text. cbn [In]. lia. }
  intros W5 ly5 S5 regs5 mem5 md5 mk HP5 R105 Hmk4 HC5.
  pose proof (bk_pres _ _ HP5) as P5.
  assert (EQ5 : @mkst fy regs5 (getr (ms_regs ms4) 1) mem5 (seg_rom SEGS) =
                @mkst fy regs5 (Z_to_bv 64 (BASE + LF_ca2_ra)) mem5 (seg_rom SEGS))
    by (rewrite Q1b; try (f_equal; f_equal; unfold LF_ca2_ra, AF_LLVMFuzzerTestOneInput; lia)).
  rewrite EQ5 in HC5 |- *.
  apply (K cx fy fp k2 ly5 S5 W5 _ md5 (c_T cx) md mk kbs HB Hfx).
  (* the registers kept: three hops (the run to the first call, the first calloc, the run to the second call)
     before the second calloc *)
  assert (RK : forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 26%bv; 27%bv] ->
                 getr regs5 r = getr (ms_regs ms3) r).
  { intros r Hr. rewrite (P5 r ltac:(cbn [In] in Hr |- *; tauto)), (G4 r ltac:(cbn [In] in Hr |- *; tauto)),
      (P2 r ltac:(cbn [In] in Hr |- *; tauto)), (G1 r ltac:(cbn [In] in Hr |- *; tauto)). reflexivity. }
  split; [unfold lf_shape; repeat split; reflexivity|].
  split.
  { unfold lf_core. cbn [ms_regs mkst].
    rewrite (RK 2%bv ltac:(bk_inr)), (RK 8%bv ltac:(bk_inr)), (RK 9%bv ltac:(bk_inr)), (RK 3%bv ltac:(bk_inr)),
      (RK 4%bv ltac:(bk_inr)).
    exact (conj C2 (conj C8 (conj C9 (conj C3 C4)))). }
  cbn [ms_regs mkst].
  split; [rewrite (RK 18%bv ltac:(bk_inr)); exact R18|].
  split; [rewrite (RK 19%bv ltac:(bk_inr)); exact R19|].
  split; [rewrite (P5 20%bv ltac:(bk_inr)), (G4 20%bv ltac:(bk_inr)), (P2 20%bv ltac:(bk_inr)), Q20; reflexivity|].
  split; [rewrite (P5 22%bv ltac:(bk_inr)), Q22b, E2_10, R102; reflexivity|].
  split; [exact R105|].
  split; [rewrite (RK 26%bv ltac:(bk_inr)); exact R26|].
  split; [rewrite (RK 27%bv ltac:(bk_inr)); exact R27|].
  split; [exact Hmd4|]. split; [exact Hmk4|].
  split; [replace (k2 + 2) with (k2 + 1 + 1) by lia; replace 2 with (0 + 1 + 1) by lia;
          replace (MD_SIZE + MK_SIZE) with (0 + MD_SIZE + MK_SIZE) by lia; exact HC5|].
  exact (conj Hwf (conj Ho (conj Hmi (conj Hoc Hop0)))).
Qed.

End a.
