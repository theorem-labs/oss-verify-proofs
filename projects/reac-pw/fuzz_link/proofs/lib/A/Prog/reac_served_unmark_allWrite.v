(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 623 of its 666 lines of code are new or changed and 1262 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeArmsB.v, with its module paths and module names changed; 751 of its 828 lines of code are new or changed and 589 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08) on image A, THE
   WRITE PIECE: from the MID cut (+0x288) to the JOIN cut (+0x294). It proves reac_served_unmark_allDefs.v's
   obligation `um_mid_obl c` from `um_join_obl c`.

   The code (listing (internal path) (internal record, sha256 9bc7ee7c887a)):
     +0x288  mv   a0, s6                 the name m->name[c] = m + 4 + 16 c (inside the marks block)
     +0x28c  ld   a1, 0x18(s1)           .str.7 = "" (the slot the loop set-up filled, +0x1cc)
     +0x290  jal  reac_link_alias_write  (0x88f54), returning at +0x294
   The three instructions are one token run (LinkWalk.v paj_run_x) from a state seated afresh at the cut (the
   registers as atoms, one region: the slot s1 + 0x18); it stops at the call. The callee's contract
   (reac_link_alias_write_c.v `reac_link_alias_write_acontract`, Section hypothesis HWR) is applied under
   SRr_bind on the journal um_base carries (own' = (3, fpos) :: own): its apre, its read set in `akb`, and its Pre;
   after the return its apost gives back um_loop, the fake kernel one write step further (um_kinv at S c: the
   write branch of link_spec's unmark_walk) and um_base, and the obligation of the JOIN cut finishes the walk.

   One segment computation is unavoidable here (HSEGS): .str.7 and the seven bytes after its NUL are image bytes of a
   non-writable segment (the callee's read set needs the string's NUL in `akb`'s image clause, its Pre needs the
   seven bytes readable), and errno is writable at every memory (reac_served_unmark_allWriteKit.v).

   Proves no function (kind: segment lemma of reac_served_unmark_all's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
LinkWalk LinkWalkPi LinkWalkSide LinkWalkCall LinkWalkShadow LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_unmark_allDefs reac_served_unmark_allWriteKit reac_served_unmark_allTailVis.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* No global sink_head instance is in scope: every journal below is the Section's SK. *)
Fail Definition sink_head_probe_um_write : YI16.sink_head := _.

(* ---- the symbolic state seated at the MID cut: the registers as atoms (32: the shadow base, unused), one region,
   the slot s1 + 0x18 (atom 9 = s1) holding .str.7 (no write window) ---- *)
Definition uwBx : sv := SOff 32 0.
Definition uwSpan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition uw_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition uw_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 24 24 [YP09.mkChunk 24 (CVal 8 (SLit LA_S_EMPTY))].
Definition uw_ss : sstate := mkSS (AF_reac_served_unmark_all + 0x288) sr_atoms [uw_slot] None (mkFacts [] [] []).

Lemma uw_consts : REAC_SERVED_UNMARK_ALL_AK = 8768 /\ REAC_LINK_ALIAS_WRITE_AK = 8560 /\
  UM_CUT_MID = AF_reac_served_unmark_all + 0x288 /\ UM_CUT_JOIN = 32668 /\ LA_S_EMPTY = 0x214e0 /\
  LA_G_NL = 0x5dcac0 /\ NK_N_SENT = 271016 /\ NK_IF_NAME = 271024 /\ NK_SIZE = 271992 /\ MK_SIZE = 516 /\
  MK_NAME = 4 /\ MARK_LEN = 16 /\ MARKS_MAX = 32 /\ UM_CID = 3 /\ fs_frame_bytes 3 = 512 /\ SHADOW_OFF = 0x7fff8000 /\
  kLowMemEnd = 0x7fff8000 /\ kHighMemBeg = 0x10007fff8000 /\ AF0m.TFIB_ERRNO = 0x631b6c.
Proof. repeat split; reflexivity. Qed.

Lemma uw_pres : forall (r1 r2 : bvmap 5 word) (k : Z) (x : bv 5), aregs_preserved r1 r2 -> acallee_saved k ->
  bv_unsigned x = k -> getr r2 x = getr r1 x.
Proof.
  intros r1 r2 k x H Hk Hx. assert (E : x = Z_to_bv 5 k) by (subst k; symmetry; apply Z_to_bv_bv_unsigned).
  subst x. exact (H k Hk).
Qed.

Ltac uw_pr H k := refine (uw_pres _ _ k _ H _ _); [unfold acallee_saved; lia | reflexivity].
Ltac uw_prr PR k := refine (PR k _ _ _); [unfold acallee_saved; lia | reflexivity].

Lemma uw_ms_eta {fx : YK11.FPState} : forall (ms : machine_state) pc rom, ms_resv ms = None ->
  ms_svc_pending ms = None -> ms_rom ms = rom -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr -> ms_pc_val ms = pc ->
  ms = mkst (ms_regs ms) pc (ms_mem ms) rom.
Proof.
  intros [regs fregs pcv svc resv fcsr mem rom0] pc rom H1 H2 H3 H4 H5 H6.
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. unfold mkst. reflexivity.
Qed.

Lemma uw_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* AR's laws (the frame), link's listing values (the link instance), the start-up symbols (lib/A AD2l.PcapB_syms),
   the image's segments (LinkImgInst.v pi_link_segs), the relro window in the image (the top file) *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
(* reac_link_alias_write (0x88f54): reac_link_alias_write.v *)
Hypothesis HWR : reac_link_alias_write_acontract SK SEGS PCAP_RLO PCAP_RHI B.

Lemma uw_aj_ar : forall G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W0 mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _). exact (proj1 HJ). Qed.

Lemma uw_roP_img : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> in_img SEGS a.
Proof.
  intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)].
Qed.

Lemma uw_wr_gnl : forall cx a, LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4 -> inFP (um_wr cx) a.
Proof.
  intros cx a Ha. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). unfold um_wr, reac_served_unmark_all_awr.
  split; [left; reflexivity | exact Ha].
Qed.

Lemma uw_wr_mk : forall cx a, um_mk cx <> 0 -> um_mk cx <= a < um_mk cx + MK_SIZE -> inFP (um_wr cx) a.
Proof.
  intros cx a Hm Ha. exists (aivl (um_mk cx) MK_SIZE). unfold um_wr, reac_served_unmark_all_awr.
  split; [right; left; reflexivity|]. unfold aivl; cbn [fst snd].
  destruct (Z.eqb_spec (um_mk cx) 0); [contradiction | lia].
Qed.

Lemma uw_wr_cases : forall cx a, inFP (um_wr cx) a ->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/ (um_mk cx <> 0 /\ um_mk cx <= a < um_mk cx + MK_SIZE).
Proof.
  intros cx a (r & Hin & Hr). unfold um_wr, reac_served_unmark_all_awr in Hin. cbn [In] in Hin.
  destruct Hin as [<- | [<- | []]]; cbn [fst snd] in Hr; [left; exact Hr|].
  right. change (aarg (um_regs cx) 0) with (um_mk cx) in Hr. unfold aivl in Hr. cbn [fst snd] in Hr.
  destruct (Z.eqb_spec (um_mk cx) 0) as [E|E]; cbv beta iota in Hr; [lia | split; [exact E | lia]].
Qed.

(* the callee's write set: g_nl up to n_sent *)
Lemma uw_awr : forall regs m a, inFP (reac_link_alias_write_awr regs m) a <-> LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4.
Proof.
  intros regs m a. unfold reac_link_alias_write_awr. split.
  - intros (r & [<- | []] & H). exact H.
  - intros H. exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact H].
Qed.

(* ==========================================================================
   1. The cut: what um_pre, um_loop, um_kinv_mid and um_base give
   ========================================================================== *)
Section c.
Variable cx : umcx.
Variable c : nat.
Variable fpos : Z.
Variables (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model).
Variable kbs : list byte.
Hypothesis HPRE : um_pre SK B cx.
(* m <> 0 and the marks block untouched (um_loop's first and last conjuncts; um_gi_tail's too) *)
Hypothesis HM : um_mk cx <> 0.
Hypothesis HMK : um_marks_kept cx W3 (ms_mem ms3).
Hypothesis HLP : um_loop cx c fpos W3 ms3.
Hypothesis HKM : um_kinv_mid cx (rdW W3 (ms_mem ms3)) kbs c.
Hypothesis HB : um_base SK B cx fpos ly3 S3 W3 ms3 md3.

#[local] Notation own' := ((UM_CID, fpos) :: um_own cx).
#[local] Notation AJ ly S W m md :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx) ly S W m md (um_k cx)).
#[local] Notation AJc :=
  (ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
     (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx)
     (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx)).
#[local] Notation Ec := (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a).
#[local] Notation m3 := (ms_mem ms3).
#[local] Notation R3 := (ms_regs ms3).
#[local] Notation na := (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c).
#[local] Notation nmc := (nth c (um_names cx) []).

Lemma uw_pj : AJc.
Proof. exact (proj1 (proj1 HPRE)). Qed.

Lemma uw_pg : gx_ok SEGS B (um_G cx).
Proof. exact (proj1 (proj2 (proj1 HPRE))). Qed.

Lemma uw_par : AR SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx).
Proof. exact (uw_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_pj). Qed.

Lemma uw_pro : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H (um_W cx)) (um_memc cx)).
Proof. destruct HPRE as ((_ & _ & H & _) & _). exact H. Qed.

Lemma uw_pajw : forall a, inFP (um_wr cx) a ->
  ajw B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx)
    (um_lyc cx) (um_Sc cx) (um_own cx) a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma uw_pnro : forall a, inFP (um_wr cx) a -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a.
Proof. destruct HPRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H) & _). exact H. Qed.

Lemma uw_prd : forall a, reac_served_unmark_all_ard SEGS (um_regs cx) (um_m0 cx) a ->
  akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - 8768) (um_sp cx) a.
Proof. destruct HPRE as (_ & H & _). exact H. Qed.

Lemma uw_pnl : amk_nlk_ok SEGS (um_m0 cx) (um_kbs cx) (um_tab cx) (2 * MARKS_MAX).
Proof. destruct HPRE as (_ & _ & H & _). exact H. Qed.

Lemma uw_per : amk_errno_ok SEGS B (um_regs cx) 8768 0 0 (um_m0 cx).
Proof. destruct HPRE as (_ & _ & _ & H & _). exact H. Qed.

Lemma uw_ptb : amk_table_ok SEGS B (um_regs cx) 8768 0 0 (um_m0 cx) (um_tab cx).
Proof. destruct HPRE as (_ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_pbk : amk_block_ok SEGS B (um_regs cx) 8768 0 0 (um_m0 cx).
Proof. destruct HPRE as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_pem : acstr_at SEGS (um_m0 cx) LA_S_EMPTY [] /\
  astr_rt_ok SEGS (um_regs cx) 8768 (um_m0 cx) LA_S_EMPTY [].
Proof. destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). exact (conj H1 H2). Qed.

Lemma uw_pmk : um_mk cx <> 0 -> amarks_at SEGS (um_m0 cx) (um_mk cx) (um_gbs cx) /\ marks_wf (um_gbs cx).
Proof. destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma uw_geo : um_sp cx mod 16 = 0 /\ um_sp0 cx - um_STK cx <= um_sp cx - 8768 /\ um_sp cx <= um_sp0 cx /\
  alloc_ceiling <= um_sp0 cx - um_STK cx /\ um_sp0 cx + um_XO cx <= 2 ^ 47 /\
  um_sp cx - 176 <= um_sp1 cx <= um_sp cx - 160 /\ um_sp1 cx mod 32 = 0 /\ um_sp1 cx mod 16 = 0 /\
  0 <= um_STK cx /\ 0 <= um_XO cx /\ 0x7fff7f800000 <= alloc_ceiling.
Proof.
  pose proof HPRE as ((HJc & _ & _ & _ & _ & _ & _ & H16 & Hlo & Hhi & _) & _).
  destruct (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (R1 & R2 & R3' & R4).
  rewrite REAC_SERVED_UNMARK_ALL_AK_val in Hlo.
  fold (um_sp cx) in H16, Hlo, Hhi.
  pose proof asan_consts as ((C1a & C1b) & _).
  destruct (sp1_facts (um_sp cx - 160) ltac:(lia) ltac:(rewrite Zminus_mod, H16; reflexivity))
    as (S1 & S2 & S3').
  unfold um_sp1, UM_FRAME. repeat split; lia.
Qed.

Lemma uw_sp_rng : 0 <= um_sp cx < 2 ^ 64.
Proof. unfold um_sp, spZ. apply getr_rng. Qed.

(* um_base's parts *)
Lemma uw_bj : AJ ly3 S3 W3 m3 md3.
Proof. destruct HB as (_ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_bfr : frames S3 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ~ In (UM_CID, fpos) (frames (um_Sc cx)).
Proof. destruct HB as (_ & _ & _ & _ & _ & _ & H1 & H2 & _). exact (conj H1 H2). Qed.

Lemma uw_bfs : exists fs, S3 = set_fs fs (um_Sc cx).
Proof. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_bperm : Permutation (ablocks B ly3 S3) (ablocks B (um_lyc cx) (um_Sc cx)).
Proof. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_bfa : forall c' q, frame_addr ly3 c' q = frame_addr (um_lyc cx) c' q.
Proof. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma uw_bK : akept SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) W3 m3 (um_sp cx - 8768) (um_sp cx) Ec.
Proof.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & H & _).
  exact H.
Qed.

Lemma uw_bro : arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) m3).
Proof.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & H).
  exact H.
Qed.

Lemma uw_ar3 : AR SEGS B ly3 S3 W3 m3 md3.
Proof. exact (uw_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_bj). Qed.

Lemma uw_rows : ly_stk_lo ly3 = ly_stk_lo (um_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (um_lyc cx).
Proof.
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_bj) as [E1 E2].
  destruct (aj_stk_row_eq SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_pj) as [E3 E4].
  split; congruence.
Qed.

Lemma uw_blk : forall b m, In (b, m) (ablocks B (um_lyc cx) (um_Sc cx)) -> In (b, m) (ablocks B ly3 S3).
Proof. intros b m Hin. exact (Permutation_in _ (Permutation_sym uw_bperm) Hin). Qed.

Lemma uw_frm : forall f, In f (frames (um_Sc cx)) -> In f (frames S3).
Proof. intros f Hin. rewrite (proj1 uw_bfr). right. exact Hin. Qed.

Lemma uw_frm2 : forall c' q, In (c', q) (frames (um_Sc cx)) -> In (c', q) (frames S3).
Proof. intros c' q Hin. exact (uw_frm (c', q) Hin). Qed.

Lemma uw_fin3 : In (UM_CID, fpos) (frames S3).
Proof. rewrite (proj1 uw_bfr). left. reflexivity. Qed.

Lemma uw_fpos : 0 <= fpos < fs_frames UM_CID.
Proof.
  pose proof uw_ar3 as (M & _). destruct (frame_facts B _ S3 _ _ _ M uw_fin3) as (_ & H & _). exact H.
Qed.

Lemma uw_F : 4096 <= um_F cx fpos /\ um_F cx fpos + 512 <= alloc_ceiling /\
  off_img (um_F cx fpos) 512 /\ frame_addr ly3 UM_CID fpos = um_F cx fpos.
Proof.
  assert (Efa : frame_addr ly3 UM_CID fpos = um_F cx fpos) by (unfold um_F; apply uw_bfa).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ uw_ar3 uw_fin3) as (H1 & H2 & _).
  pose proof (frm_off_imgP B _ _ _ _ _ _ _ uw_ar3 uw_fin3) as H3.
  rewrite Efa in H1, H2, H3. change (fs_frame_bytes UM_CID) with 512 in H1, H2, H3.
  repeat split; assumption.
Qed.

(* the marks block *)
Lemma uw_mk : um_mk cx <> 0 /\ Z.of_nat c < um_n cx.
Proof. destruct HLP as (_ & H2 & _). exact (conj HM H2). Qed.

Lemma uw_mkf : 0 < um_mk cx /\ amem_range (um_mk cx) (MK_SIZE + 8) /\
  range_addressable (ard SEGS (um_m0 cx)) SHADOW_OFF (um_mk cx) MK_SIZE /\
  shadow_hull_vis (ard SEGS (um_m0 cx)) (um_mk cx) MK_SIZE /\
  apart_frame (um_regs cx) 8768 (um_mk cx) MK_SIZE /\ apart_gnl LA_G_NL (um_mk cx) MK_SIZE /\
  apart (as_errno B) 4 (um_mk cx) MK_SIZE /\
  amarks_at SEGS (um_m0 cx) (um_mk cx) (um_gbs cx) /\ marks_wf (um_gbs cx).
Proof.
  pose proof HM as Hm.
  destruct (uw_pbk Hm) as ((H0 & H1 & H2 & H3 & _ & H4) & H5 & H6 & _ & _).
  destruct (uw_pmk Hm) as [H7 H8].
  exact (conj H0 (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8)))))))).
Qed.

(* the exception set um_base's akept carries misses the shadow of every frame of Sc *)
Lemma uw_fmiss : fmiss (um_lyc cx) (um_Sc cx) Ec.
Proof.
  apply fmiss_or.
  - apply (fmiss_app SEGS B LAWS _ _ _ _ _ _ uw_par). intros a Ha.
    pose proof uw_consts as (_ & _ & _ & _ & _ & C1 & C2 & _ & _ & C3 & _ & _ & _ & _ & _ & _ & C4 & C5 & _).
    destruct (uw_wr_cases cx a Ha) as [H | (Hm & H)]; [left; lia|].
    pose proof uw_mkf as (_ & Hmr & _). unfold amem_range in Hmr. lia.
  - pose proof uw_fpos as Hp. pose proof uw_bfr as (_ & NIN).
    exact (fmiss_side SEGS B _ _ _ _ _ UM_CID fpos uw_par ltac:(unfold UM_CID; lia) Hp NIN).
Qed.

Lemma uw_mk_rng : 0 <= um_mk cx /\ um_mk cx + MK_SIZE <= 2 ^ 64.
Proof.
  pose proof uw_mkf as (_ & _ & _ & _ & _ & _ & _ & (((H0 & H1 & _) & _) & HL) & _).
  rewrite HL in H1. split; lia.
Qed.

Lemma uw_c32 : (c < Z.to_nat (mk_n (um_gbs cx)))%nat /\ Z.of_nat c < MARKS_MAX /\ Z.of_nat c < 32.
Proof.
  pose proof uw_mkf as (_ & _ & _ & _ & _ & _ & _ & _ & (Hn & _)). destruct uw_mk as [_ Hc].
  unfold um_n in Hc. unfold MARKS_MAX in *. repeat split; lia.
Qed.

Lemma uw_mk_kept : forall a, um_mk cx <= a < um_mk cx + MK_SIZE ->
  aview SEGS (w_H W3) m3 a = aview SEGS (w_H (um_W cx)) (um_memc cx) a.
Proof. exact HMK. Qed.

Lemma uw_marks3 : abytes SEGS (rdW W3 m3) (um_mk cx) (um_gbs cx).
Proof.
  pose proof uw_mkf as (_ & _ & _ & _ & _ & _ & _ & ((HB0 & _) & HL) & _).
  apply (uw_abytes_move SEGS _ _ _ _ HB0). intros x Hx. unfold um_m0. apply uw_mbyte_eq. apply uw_mk_kept. lia.
Qed.

(* the name m->name[c], at the cut's memory *)
Lemma uw_name3 : acstr_at SEGS (rdW W3 m3) na nmc /\ (length nmc < 16)%nat.
Proof.
  pose proof uw_mkf as (_ & _ & _ & _ & _ & _ & _ & (_ & HL) & (Hn & HT)).
  destruct uw_c32 as (Hc & Hc32 & _).
  unfold um_names. rewrite (uw_mk_names_nth (um_gbs cx) c Hc).
  apply (uw_slot_cstr SEGS (rdW W3 m3) (um_mk cx) (um_gbs cx) (Z.of_nat c) uw_marks3 HL ltac:(lia)).
  apply HT. lia.
Qed.

Lemma uw_na_rng : 0 < na /\ um_mk cx <= na /\ na + 16 <= um_mk cx + MK_SIZE /\ na < 2 ^ 64.
Proof.
  pose proof uw_mk_rng. pose proof uw_mkf as (H0 & _). destruct uw_c32 as (_ & _ & Hc).
  unfold MK_NAME, MARK_LEN, MK_SIZE in *. lia.
Qed.

(* .str.7 *)
Lemma uw_empty_img : in_roP SEGS PCAP_RLO PCAP_RHI LA_S_EMPTY /\ in_img SEGS LA_S_EMPTY /\
  ~ Exists (in_zr LA_S_EMPTY) (as_owned_static B) /\ ~ (as_errno B <= LA_S_EMPTY < as_errno B + 4).
Proof.
  rewrite HSEGS. destruct (uw_empty_ro LA_S_EMPTY ltac:(lia)) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  rewrite (AF0m.ts_owned B TB), (AF0m.ts_errno B TB). split; [exact uw_empty_not_static|].
  unfold AF0m.TFIB_ERRNO, LA_S_EMPTY. lia.
Qed.

Lemma uw_empty_view : aview SEGS (w_H W3) m3 LA_S_EMPTY = aview SEGS (w_H (um_W cx)) (um_memc cx) LA_S_EMPTY.
Proof.
  destruct uw_empty_img as (Hro & _ & Ho & He).
  rewrite (uw_bro LA_S_EMPTY Hro Ho He), (uw_pro LA_S_EMPTY Hro Ho He). reflexivity.
Qed.

Lemma uw_empty3 : acstr_at SEGS (rdW W3 m3) LA_S_EMPTY [].
Proof.
  apply (uw_acstr_move SEGS (um_m0 cx) _ _ _ (proj1 uw_pem)). intros x Hx. cbn [length Z.of_nat] in Hx.
  replace x with LA_S_EMPTY by lia. unfold um_m0. apply uw_mbyte_eq. exact uw_empty_view.
Qed.

(* the Rd bytes of reac_served_unmark_all the walk reads back: the if_name slots and the table's strings *)
Lemma uw_slot_kept : forall a, LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) m3 a = aview SEGS (w_H (um_W cx)) (um_memc cx) a.
Proof.
  intros a Ha.
  assert (Hk : akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - 8768) (um_sp cx) a)
    by (apply uw_prd; left; exact Ha).
  apply (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a uw_pj uw_bK Hk).
  intros [HE | HE].
  - pose proof uw_mkf as (_ & _ & _ & _ & _ & Hg & _). unfold apart_gnl in Hg.
    pose proof uw_consts as (_ & _ & _ & _ & _ & C1 & C2 & C3 & C4 & _).
    destruct (uw_wr_cases cx a HE) as [H | (_ & H)]; lia.
  - pose proof uw_fpos as Hp. pose proof uw_bfr as (_ & NIN).
    exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a uw_pj
      ltac:(unfold UM_CID; lia) Hp NIN Hk HE).
Qed.

Lemma uw_slot_vm : forall i p, 0 <= i < 80 ->
  au64_at SEGS (rdW W3 m3) (LA_G_NL + NK_IF_NAME + 8 * i) p -> au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * i) p.
Proof.
  intros i p Hi H. apply (uw_vm_move SEGS _ _ _ _ _ H). intros x Hx. unfold um_m0. symmetry. apply uw_mbyte_eq.
  apply uw_slot_kept.
  pose proof uw_consts as (_ & _ & _ & _ & _ & _ & _ & C3 & C4 & _). change (Z.of_nat 8) with 8 in Hx. lia.
Qed.

(* entry i of the table at the cut: its pointer, the same as at the call, and the facts of amk_table_ok *)
Lemma uw_tab_entry : forall i n2 ix p, nth_error (um_tab cx) i = Some (n2, ix) ->
  au64_at SEGS (rdW W3 m3) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
  exists p0, p mod 2 ^ 64 = p0 /\ 0 < p0 /\ p0 + Z.of_nat (length n2) + 1 <= 2 ^ 64 /\
    au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 /\ acstr_at SEGS (um_m0 cx) p0 n2 /\
    (Z.of_nat i < 80) /\
    astr_rt_ok SEGS (um_regs cx) 8768 (um_m0 cx) p0 n2 /\ apart_gnl LA_G_NL p0 (Z.of_nat (length n2) + 1) /\
    apart (as_errno B) 4 p0 (Z.of_nat (length n2) + 1) /\
    apart (um_mk cx) MK_SIZE p0 (Z.of_nat (length n2) + 1).
Proof.
  intros i n2 ix p Hn Hp.
  pose proof uw_pnl as (_ & _ & _ & _ & _ & (HL & H80 & HIF) & _).
  destruct (HIF i n2 ix Hn) as (_ & p0 & Hp0 & Hp0n & Hc0 & _).
  assert (Hi80 : Z.of_nat i < 80).
  { assert (i < length (um_tab cx))%nat by (apply nth_error_Some; congruence). lia. }
  pose proof (uw_slot_vm (Z.of_nat i) p ltac:(lia) Hp) as Hp'.
  pose proof (uw_au64_unique SEGS _ _ _ _ Hp' Hp0) as Ep.
  pose proof (uw_acstr_range SEGS _ _ _ Hc0) as Hr0.
  rewrite (Z.mod_small p0) in Ep by lia.
  pose proof HM as Hm.
  destruct (uw_ptb i n2 ix p0 Hn Hp0 ltac:(lia)) as (Hrt & Hg & He & _ & Hmk).
  exists p0. split; [exact Ep|]. split; [lia|]. split; [lia|]. split; [exact Hp0|]. split; [exact Hc0|].
  split; [exact Hi80|]. split; [exact Hrt|]. split; [exact Hg|]. split; [exact He | exact (Hmk Hm)].
Qed.

Lemma uw_tab_akb : forall i n2 ix p0 a, nth_error (um_tab cx) i = Some (n2, ix) -> Z.of_nat i < 80 ->
  au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 -> 0 < p0 ->
  acstr_at SEGS (um_m0 cx) p0 n2 -> p0 <= a <= p0 + Z.of_nat (length n2) ->
  akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - 8768) (um_sp cx) a.
Proof.
  intros i n2 ix p0 a Hn Hi Hp0 H0 Hc Ha. apply uw_prd. right.
  pose proof uw_pnl as (NK & _ & _ & _ & _ & IT & _).
  exists (um_kbs cx), (um_tab cx), i, n2, ix, p0.
  split; [exact NK|]. split; [exact IT|]. split; [exact Hn|]. split; [exact Hp0|]. split; [exact Hc | exact Ha].
Qed.

Lemma uw_tab_kept : forall i n2 ix p0, nth_error (um_tab cx) i = Some (n2, ix) -> Z.of_nat i < 80 ->
  au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 -> 0 < p0 ->
  acstr_at SEGS (um_m0 cx) p0 n2 -> apart_gnl LA_G_NL p0 (Z.of_nat (length n2) + 1) ->
  apart (um_mk cx) MK_SIZE p0 (Z.of_nat (length n2) + 1) ->
  forall a, p0 <= a <= p0 + Z.of_nat (length n2) ->
  aview SEGS (w_H W3) m3 a = aview SEGS (w_H (um_W cx)) (um_memc cx) a.
Proof.
  intros i n2 ix p0 Hn Hi Hp0 H0 Hc Hg Hm a Ha.
  pose proof (uw_tab_akb i n2 ix p0 a Hn Hi Hp0 H0 Hc Ha) as Hk.
  apply (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a uw_pj uw_bK Hk).
  intros [HE | HE].
  - unfold apart_gnl, apart in Hg, Hm.
    pose proof uw_consts as (_ & _ & _ & _ & _ & C1 & C2 & C3 & C4 & _).
    destruct (uw_wr_cases cx a HE) as [H | (_ & H)]; lia.
  - pose proof uw_fpos as Hp. pose proof uw_bfr as (_ & NIN).
    exact (akb_not_side SK SEGS B pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ UM_CID fpos a uw_pj
      ltac:(unfold UM_CID; lia) Hp NIN Hk HE).
Qed.

(* the fake kernel at the cut *)
Lemma uw_kinv : anlk_at SEGS (rdW W3 m3) LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at SEGS (rdW W3 m3) LA_G_NL kbs (um_tab cx) /\
  nk_open kbs = 0 /\ nk_opened kbs + 1 < 2 ^ 31 /\ nk_closed kbs + 1 < 2 ^ 31.
Proof.
  pose proof HKM as (H1 & H2 & H3 & _ & _ & _ & _ & H4 & _ & H5 & H6).
  pose proof uw_pnl as (_ & _ & _ & N1 & N2 & _).
  destruct uw_c32 as (_ & _ & Hc).
  unfold MARKS_MAX in N1, N2.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; lia.
Qed.

(* the shadow facts at the cut: from the call's by um_base's akept *)
Lemma uw_shadow3 : forall p n, 0 < n -> (forall x, p <= x < p + n -> sclass SEGS B (um_lyc cx) (um_Sc cx) x) ->
  range_addressable (ard SEGS (um_m0 cx)) SHADOW_OFF p n -> shadow_hull_vis (ard SEGS (um_m0 cx)) p n ->
  range_addressable (ard SEGS (rdW W3 m3)) SHADOW_OFF p n /\ shadow_hull_vis (ard SEGS (rdW W3 m3)) p n.
Proof.
  intros p n Hn Hc HR HH.
  exact (shadow_transport SEGS B LAWS TB pa_img_range _ _ _ _ _ _ _ _ _ _ _ _ _ p n uw_par uw_ar3
    (proj1 uw_rows) (proj2 uw_rows) uw_blk uw_bK uw_fmiss Hn Hc HR HH).
Qed.

(* ==========================================================================
   2. The call: the callee's premises at the register file the run leaves
   ========================================================================== *)
Section d.
Variable R' : bvmap 5 word.
Variable md' : Model.
Hypothesis RC10 : getr R' 10 = w64 (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c).
Hypothesis RC11 : getr R' 11 = w64 LA_S_EMPTY.
Hypothesis RC1 : getr R' 1 = w64 (BASE + UM_CUT_JOIN).
Hypothesis RCP : aregs_preserved R3 R'.
Hypothesis HJ' : AJ ly3 S3 W3 m3 md'.

Lemma uw_a0 : aarg R' 0 = na.
Proof.
  pose proof uw_na_rng as (H0 & _ & _ & Hr).
  unfold aarg, argZ. transitivity (bv_unsigned (getr R' 10)); [reflexivity|].
  rewrite RC10. unfold w64. apply unsigned_lit_small. lia.
Qed.

Lemma uw_a1 : aarg R' 1 = LA_S_EMPTY.
Proof.
  unfold aarg, argZ. transitivity (bv_unsigned (getr R' 11)); [reflexivity|].
  rewrite RC11. unfold w64. apply unsigned_lit_small. unfold LA_S_EMPTY. lia.
Qed.

Lemma uw_spc : spZ R' = um_sp1 cx.
Proof.
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & _).
  pose proof uw_geo as (_ & G2 & _ & G4 & _ & G6 & _ & _ & _ & _ & G11).
  pose proof uw_sp_rng.
  unfold spZ. transitivity (bv_unsigned (getr R3 2)).
  - f_equal. uw_pr RCP 2.
  - rewrite R2. unfold w64. apply unsigned_lit_small. lia.
Qed.

Lemma uw_ra : raZ R' = BASE + UM_CUT_JOIN.
Proof.
  pose proof pa_B_ok as (HB0 & HB1 & _).
  unfold raZ. rewrite RC1. unfold w64. apply unsigned_lit_small. unfold UM_CUT_JOIN, AF_reac_served_unmark_all. lia.
Qed.

Lemma uw_ar' : AR SEGS B ly3 S3 W3 m3 md'.
Proof. exact (uw_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ'). Qed.

(* the callee window [sp1 - 8560, sp1) lies inside the caller's [sp - 8768, sp) *)
Lemma uw_win : um_sp cx - 8768 <= um_sp1 cx - 8560 /\ um_sp1 cx <= um_sp cx /\
  um_sp0 cx - um_STK cx <= um_sp1 cx - 8560 /\ alloc_ceiling <= um_sp cx - 8768.
Proof. pose proof uw_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _). lia. Qed.

(* ---- 2a. link_amem.v apre at the call ---- *)
Lemma uw_apre :
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_WRITE_AK 0 REAC_LINK_ALIAS_WRITE_ASIDE
    (reac_link_alias_write_awr R' (rdW W3 m3)) (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
    (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) own' ly3 S3 W3 m3 md' (um_k cx) R'.
Proof.
  pose proof HPRE as ((_ & _ & _ & _ & _ & Hgp & Htp & _ & _ & _ & Hev & Hside & _) & _).
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R3e & R4e & _).
  pose proof uw_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  pose proof uw_win as (W1 & W2 & W3' & W4).
  pose proof pa_base_lo as HBL. pose proof pa_B_ok as (HB0 & HB1 & _).
  split; [exact HJ'|]. split; [exact uw_pg|]. split; [exact uw_bro|].
  split; [rewrite RC1; apply ret_ok_codeptr_v; unfold UM_CUT_JOIN, AF_reac_served_unmark_all; [lia | reflexivity]|].
  split; [rewrite uw_ra; unfold UM_CUT_JOIN, AF_reac_served_unmark_all; lia|].
  split; [etransitivity; [uw_pr RCP 3 | etransitivity; [exact R3e | exact Hgp]]|].
  split; [etransitivity; [uw_pr RCP 4 | etransitivity; [exact R4e | exact Htp]]|].
  rewrite uw_spc. rewrite REAC_LINK_ALIAS_WRITE_AK_val.
  split; [exact G8|]. split; [lia|]. split; [lia|].
  split; [exact Hev|].
  split.
  { pose proof uw_bfr as (Hfr & _).
    apply (aside_room_push (um_Sc cx) S3 REAC_SERVED_UNMARK_ALL_ASIDE REAC_LINK_ALIAS_WRITE_ASIDE UM_CID fpos Hfr Hside).
    intros c' d' Hin. unfold REAC_LINK_ALIAS_WRITE_ASIDE in Hin. cbn [In] in Hin.
    destruct Hin as [E | [E | []]]; injection E as <- <-.
    - exists 2. split; [unfold REAC_SERVED_UNMARK_ALL_ASIDE; cbn [In]; left; reflexivity|].
      assert (E3 : (UM_CID =? 3) = true) by reflexivity. rewrite E3. lia.
    - exists 1. split; [unfold REAC_SERVED_UNMARK_ALL_ASIDE; cbn [In]; right; right; left; reflexivity|].
      assert (E9 : (UM_CID =? 9) = false) by reflexivity. rewrite E9. lia. }
  split.
  { intros a Ha. apply uw_awr in Ha.
    apply (ajw_mono B _ _ _ _ _ _ _ _ _ _ _ _ _ _ a (uw_pajw a (uw_wr_gnl cx a Ha)) uw_blk).
    - intros x Hx. right. exact Hx.
    - exact uw_bfa. }
  intros a Ha. apply uw_awr in Ha. exact (uw_pnro a (uw_wr_gnl cx a Ha)).
Qed.

(* ---- 2b. the callee's read set lies in `akb` at the call ---- *)
Lemma uw_mk_akb : forall a, um_mk cx <= a < um_mk cx + MK_SIZE ->
  akb SEGS B ly3 S3 (spZ R' - REAC_LINK_ALIAS_WRITE_AK) (spZ R') a.
Proof.
  intros a Ha. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val.
  pose proof uw_mkf as (_ & Hmr & _ & _ & Hfr & _ & He & _). pose proof HM as Hm.
  pose proof uw_win as (W1 & W2 & _).
  pose proof uw_consts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & C1 & _ & _ & _ & _ & _ & _ & C2 & C3 & _).
  unfold apart_frame, apart, amem_range in Hmr, Hfr, He. fold (um_sp cx) in Hfr.
  apply (ajw_akb SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_pg uw_pj
    (uw_pajw a (uw_wr_mk cx a Hm Ha))); [lia | lia | lia | exact (proj1 uw_rows) | exact (proj2 uw_rows)
    | exact uw_blk | exact uw_frm2 | exact uw_bfa].
Qed.

Lemma uw_ard_akb : forall a, reac_link_alias_write_ard SEGS R' (rdW W3 m3) a ->
  akb SEGS B ly3 S3 (spZ R' - REAC_LINK_ALIAS_WRITE_AK) (spZ R') a.
Proof.
  intros a [(_ & s & Hs & Ha) | [(_ & s & Hs & Ha) | (bs & tab & i & n2 & ix & p & Hbs & Htab & Hn & Hp & Hc & Ha)]].
  - (* the name: a byte of the marks block *)
    rewrite uw_a0 in Hs, Ha. destruct uw_name3 as [Hc3 Hl3].
    rewrite (uw_acstr_unique SEGS _ _ _ _ Hs Hc3) in Ha.
    pose proof uw_na_rng as (_ & H1 & H2 & _).
    apply uw_mk_akb. lia.
  - (* the alias: .str.7's NUL, an image byte *)
    rewrite uw_a1 in Hs, Ha. rewrite (uw_acstr_unique SEGS _ _ _ _ Hs uw_empty3) in Ha. cbn [length Z.of_nat] in Ha.
    replace a with LA_S_EMPTY by lia.
    destruct uw_empty_img as (_ & Hi & Ho & He).
    right; right; left. exact (conj Hi (conj Ho He)).
  - (* a table string: in the caller's read set, then akb_sub *)
    destruct uw_kinv as (HNL3 & _ & HIF3 & _).
    rewrite (uw_anlk_unique SEGS _ _ _ _ Hbs HNL3) in Htab.
    rewrite (uw_aiftab_unique SEGS _ _ _ _ Htab HIF3) in Hn.
    destruct (uw_tab_entry i n2 ix p Hn Hp) as (p0 & Ep & H0 & Hr0 & Hp0 & Hc0 & Hi80 & _).
    pose proof (uw_acstr_range SEGS _ _ _ Hc) as Hrp.
    rewrite Z.mod_small in Ep by lia. subst p0.
    pose proof (uw_tab_akb i n2 ix p a Hn Hi80 Hp0 H0 Hc0 Ha) as Hk.
    rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val. pose proof uw_win as (W1 & W2 & _).
    apply (akb_sub SEGS B _ _ _ _ _ _ _ _ a Hk W1 W2 (proj1 uw_rows) (proj2 uw_rows) uw_blk uw_frm2 uw_bfa).
Qed.

(* ---- 2c. reac_link_alias_write_apre at the call ---- *)
Lemma uw_errno_w : forall (m : word -> option byte), awrange SEGS m (as_errno B) 4.
Proof.
  intros m i Hi. rewrite (AF0m.ts_errno B TB).
  assert (H : forall segs, segs = AB1v.tfibsegs -> writable_at segs m (AF0m.TFIB_ERRNO + i)).
  { intros segs ->. apply uw_rw_window. unfold AF0m.TFIB_ERRNO. lia. }
  exact (H SEGS HSEGS).
Qed.

Lemma uw_pre :
  reac_link_alias_write_apre SEGS B R' (rdW W3 m3).
Proof.
  destruct uw_kinv as (HNL3 & HWF3 & HIF3 & HOP3 & HO1 & HC1).
  destruct uw_name3 as [Hnm3 Hl3].
  pose proof uw_na_rng as (Hna0 & Hna1 & Hna2 & Hna3).
  pose proof uw_win as (W1 & W2 & W3' & W4).
  pose proof uw_geo as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof uw_consts as (_ & _ & _ & _ & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _ & _ & _ & C16 & C17 & C18 & _).
  pose proof uw_ar' as HAR'.
  pose proof uw_sp_rng as Hsp. pose proof asan_consts as ((AC1 & AC2) & _).
  pose proof (AF0m.ts_errno B TB) as Herr. unfold AF0m.TFIB_ERRNO in Herr.
  exists kbs, (um_tab cx), (Some nmc), (Some []).
  split; [exact HNL3|]. split; [exact HWF3|]. split; [exact HOP3|]. split; [exact HO1|]. split; [exact HC1|].
  split; [exact HIF3|].
  split; [exact (proj1 (zsh_gnl_ard B TB SEGS _ _ _ _ _ HAR'))|].
  split; [exact (proj2 (zsh_gnl_ard B TB SEGS _ _ _ _ _ HAR'))|].
  split.
  { (* errno *)
    pose proof uw_per as (E1 & _ & _ & E4 & E5 & _).
    split; [exact E1|]. split; [apply uw_errno_w|].
    split; [exact (proj1 (zsh_errno_ard B TB SEGS _ _ _ _ _ HAR'))|].
    split; [|exact E5].
    unfold apart_frame in E4 |- *. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val. fold (um_sp cx) in E4. lia. }
  split; [rewrite uw_a0; split; [lia | exact Hnm3]|].
  split; [rewrite uw_a1; split; [unfold LA_S_EMPTY; lia | exact uw_empty3]|].
  split.
  { (* the table strings *)
    intros i n2 ix p Hn Hp.
    destruct (uw_tab_entry i n2 ix p Hn Hp) as (p0 & Ep & H0 & Hr0 & Hp0 & Hc0 & Hi80 & Hrt & Hg & He & Hm).
    pose proof (Z.div_mod p (2 ^ 64) ltac:(lia)) as Dp. rewrite Ep in Dp. clear Ep.
    set (q := p / 2 ^ 64) in Dp. clearbody q.
    destruct Hrt as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
    unfold apart_frame, apart_gnl, apart in Hg, He, T7 |- *. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val.
    fold (um_sp cx) in T7.
    assert (Hq : q = 0 \/ 1 <= q \/ q <= -1) by lia.
    destruct Hq as [Hq | [Hq | Hq]].
    - subst q. replace p with p0 by lia.
      split; [lia|]. split; [lia|]. split; [lia|].
      intros _. split; [lia|]. split; [lia|].
      split.
      { destruct (uw_shadow3 p0 (Z.of_nat (length n2) + 1) ltac:(lia)
          ltac:(intros x Hx; apply (sclass_of_akb SEGS B _ _ _ _ _ (uw_tab_akb i n2 ix p0 x Hn Hi80 Hp0 H0 Hc0 ltac:(lia))))
          T4 T5) as [S1 S2].
        split; [apply (uw_amem_sub p0 (Z.of_nat (length n2) + 8)); [exact T3 | lia | lia]|].
        split; [exact S1 | exact S2]. }
      (* the strcmp tail: TailVis.v from the table's astr_rt_ok at the call *)
      intros a Ha.
      exact (utv_tab SK B LAWS HSEGS cx HPRE ly3 S3 W3 m3 md3 _ uw_ar3 uw_blk uw_frm2 uw_bfa uw_bK
        i n2 ix p0 Hn Hp0 ltac:(lia) a Ha).
    - split; [lia|]. split; [lia|]. split; [lia|]. intros Hpr. lia.
    - split; [lia|]. split; [lia|]. split; [lia|]. intros Hpr. lia. }
  split.
  { (* the name *)
    intros s Es. injection Es as <-. rewrite uw_a0.
    pose proof uw_mkf as (_ & Hmr & HR0 & HH0 & Hfr & Hg & _).
    unfold apart_frame, apart_gnl in Hfr, Hg |- *. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val. fold (um_sp cx) in Hfr.
    pose proof HM as Hm.
    destruct (uw_shadow3 (um_mk cx) MK_SIZE ltac:(lia)
      ltac:(intros x Hx; apply (sclass_of_ajw SK SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x uw_pg uw_pj
              (uw_pajw x (uw_wr_mk cx x Hm Hx))); unfold amem_range in Hmr; lia)
      HR0 HH0) as [S1 S2].
    split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { split; [apply (uw_amem_sub (um_mk cx) (MK_SIZE + 8)); [exact Hmr | lia | lia]|].
      split; [apply (uw_ra_sub _ SHADOW_OFF (um_mk cx) MK_SIZE); [exact S1 | lia | lia]|].
      apply (uw_hull_sub _ (um_mk cx) MK_SIZE); [exact S2 | lia | lia | lia]. }
    (* the strcmp tail: TailVis.v from the marks block at the call *)
    intros a Ha.
    destruct uw_c32 as (Hc & _).
    exact (utv_name SK B LAWS HSEGS cx HPRE ly3 S3 W3 m3 md3 _ uw_ar3 uw_blk uw_frm2 uw_bfa uw_bK c HM Hc a Ha). }
  split.
  { (* the alias "" *)
    intros s Es. injection Es as <-. rewrite uw_a1. cbn [length Z.of_nat].
    pose proof uw_pem as (_ & (A1 & A2 & A3 & A4 & A5 & A6 & A7)). cbn [length Z.of_nat] in A2, A3, A4, A5, A6, A7.
    unfold apart_frame, apart_gnl in A7 |- *. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val. fold (um_sp cx) in A7.
    destruct uw_empty_img as (_ & Hi & _ & _).
    destruct (uw_shadow3 LA_S_EMPTY 1 ltac:(lia)
      ltac:(intros x Hx; replace x with LA_S_EMPTY by lia; right; right; left; exact Hi) A4 A5) as [S1 S2].
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [apply (uw_amem_sub LA_S_EMPTY (0 + 8)); [exact A3 | lia | lia]|].
    split; [exact S1 | exact S2]. }
  (* strlen's slack after "" *)
  intros s Es. injection Es as <-. rewrite uw_a1. cbn [length Z.of_nat].
  exists (abytes_of SEGS (rdW W3 m3) (LA_S_EMPTY + 0 + 1) 7).
  split.
  - apply abytes_of_abytes; [lia | lia|].
    intros i Hi. apply (uw_slack_readable SEGS); [exact HSEGS | lia].
  - rewrite abytes_of_length. unfold LA_S_EMPTY. change ((- (0x214e0 + 0 + 1)) mod 8) with 7. lia.
Qed.

(* ---- 2d. after the call: the JOIN cut ---- *)
Lemma uw_after : forall W2 c2, wle W3 W2 ->
  apost SK SEGS B REAC_LINK_ALIAS_WRITE_AK 0 (fun a => inFP (reac_link_alias_write_awr R' (rdW W3 m3)) a)
    (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
    (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) own' ly3 S3 W3 m3 md' (um_k cx) R'
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) S3 /\ Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\
       reac_link_alias_write_apost SEGS R' (rdW W3 m3) regs2 (rdW W2 mem2)) W2 c2 ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  exists ms2 md2 ly2 S2, c2 = mkCfg ms2 md2 /\ um_gi_join SK B cx c fpos ly2 S2 W2 ms2 md2.
Proof.
  intros W2 c2 Hle (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJ2 & HPR2 & Hfr2 & Hfd2 & Hfs2 & HK2 & _
    & (Hsfs & Hperm2 & HPO)) Hfd' Hfs'.
  exists (mkst regs2 (getr R' 1) mem2 (seg_rom SEGS)), md2, ly2, S2. split; [exact Hc2|].
  rewrite Z.add_0_r in HJ2.
  pose proof (uw_aj_ar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val in HK2.
  pose proof uw_win as (W1 & W2' & W3' & W4).
  pose proof uw_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof uw_sp_rng as Hsp.
  pose proof uw_consts as (_ & _ & _ & _ & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _ & _ & _ & C16 & C17 & C18 & _).
  pose proof uw_F as (F1 & F2 & F3 & F4).
  pose proof asan_consts as ((AC1 & AC2) & _).
  (* the bytes the callee kept: above its window (the frame, the slots), outside g_nl *)
  assert (KUP : forall a, um_sp1 cx <= a < 2 ^ 64 ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m3 a).
  { intros a Ha. pose proof HK2 as (K1 & _). apply K1; [lia | lia|].
    intros Hw. cbv beta in Hw. apply uw_awr in Hw. unfold LA_G_NL, NK_N_SENT in Hw. lia. }
  (* the marks block: in the callee's read set, outside its write set *)
  assert (KMK : forall a, um_mk cx <= a < um_mk cx + MK_SIZE ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) m3 a).
  { intros a Ha. pose proof (uw_mk_akb a Ha) as Hk. rewrite uw_spc, REAC_LINK_ALIAS_WRITE_AK_val in Hk.
    apply (akept_akb_gx SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ' HK2 Hk).
    intros Hw. cbv beta in Hw. apply uw_awr in Hw. pose proof uw_mkf as (_ & _ & _ & _ & _ & Hg & _).
    unfold apart_gnl in Hg. lia. }
  (* registers *)
  assert (PR : forall k (x : bv 5), acallee_saved k -> bv_unsigned x = k -> getr regs2 x = getr R3 x).
  { intros k x Hk Hx. rewrite (uw_pres R' regs2 k x HPR2 Hk Hx). exact (uw_pres R3 R' k x RCP Hk Hx). }
  (* the fake kernel after the write *)
  destruct uw_kinv as (HNL3 & HWF3 & HIF3 & HOP3 & HO1 & HC1).
  destruct uw_name3 as [Hnm3 Hl3].
  assert (Hnm : astr_arg SEGS (rdW W3 m3) (aarg R' 0) (Some nmc))
    by (rewrite uw_a0; split; [pose proof uw_na_rng; lia | exact Hnm3]).
  assert (Hal : astr_arg SEGS (rdW W3 m3) (aarg R' 1) (Some []))
    by (rewrite uw_a1; split; [unfold LA_S_EMPTY; lia | exact uw_empty3]).
  pose proof (HPO kbs (um_tab cx) (Some nmc) (Some []) HNL3 HIF3 Hnm Hal) as HPO'.
  cbv zeta in HPO'.
  destruct HPO' as (_ & (kbs' & HNL2 & HWF2 & HCH2 & HEE2 & HNI2 & HIF2 & HNX2 & HSO2 & HSE2 & HSN2 & HNS2
    & HOP2 & HMS2 & HOC2 & HOB2 & _)).
  pose proof HKM as (_ & _ & _ & K4 & K5 & K6 & K7 & _ & K9 & K10 & K11).
  set (WR := write_lib (um_tab cx) (Some nmc) (Some []) (nk_sent kbs) (nk_kstate kbs)) in *.
  assert (KS2 : nk_kstate kbs' = w_state WR).
  { destruct (uw_write_state_ce (um_tab cx) (Some nmc) (Some []) (nk_sent kbs) (nk_kstate kbs)) as [CE1 CE2].
    change (write_core (um_tab cx) (Some nmc) (Some []) (nk_sent kbs) (nk_kstate kbs)) with WR in CE1, CE2.
    apply uw_nk_kstate_eq; [rewrite HCH2, CE1; reflexivity | exact HNX2 | rewrite HEE2, CE2; reflexivity
                           | exact HSO2 | exact HSE2]. }
  unfold um_gi_join.
  split; [exact RC1|].
  split.
  { (* um_loop at c *)
    destruct HLP as (L1 & L2 & L21 & L22 & L23 & L24 & L26 & L27 & L18 & L10 & L11).
    split; [exact L1|]. split; [exact L2|].
    cbn [ms_regs ms_mem mkst].
    split; [etransitivity; [uw_prr PR 21 | exact L21]|].
    split; [etransitivity; [uw_prr PR 22 | exact L22]|].
    split; [etransitivity; [uw_prr PR 23 | exact L23]|].
    split; [etransitivity; [uw_prr PR 24 | exact L24]|].
    split; [etransitivity; [uw_prr PR 26 | exact L26]|].
    split; [etransitivity; [uw_prr PR 27 | exact L27]|].
    split; [rewrite <- L18; apply uw_rdword_ext; intros i Hi; apply KUP; unfold UM_SLOT_EMPTY; lia|].
    split; [rewrite <- L10; apply uw_rdword_ext; intros i Hi; apply KUP; unfold UM_SLOT_LIM; lia|].
    intros a Ha. rewrite (KMK a Ha). exact (L11 a Ha). }
  split.
  { (* the fake kernel, c + 1 names done *)
    exists kbs'. cbn [ms_mem mkst].
    split; [exact HNL2|]. split; [exact HWF2|]. split; [exact HIF2|].
    split; [rewrite HCH2; exact K4|]. split; [rewrite HEE2; exact K5|]. split; [rewrite HNI2; exact K6|].
    split; [rewrite HSN2, KS2; exact K7|].
    split; [exact HOP2|]. split; [rewrite HMS2; exact K9|]. split; [lia|].
    rewrite Nat2Z.inj_succ. lia. }
  (* um_base at the JOIN cut *)
  pose proof HB as (_ & _ & _ & _ & _ & _ & Hfr3 & Hnin & _ & _ & HS1 & _ & B2 & B9 & B8 & B18 & B19 & B25 & B20
    & B3 & B4 & Bra & Bsv & Bfl & _ & _ & _ & Bfd & Bfs & _).
  assert (Efa2 : forall c' q, frame_addr ly2 c' q = frame_addr (um_lyc cx) c' q).
  { intros c' q.
    rewrite (proj1 (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c' q HJ2)).
    symmetry. exact (aj_frame_addr SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ uw_pj c' q). }
  assert (Hfin2 : In (UM_CID, fpos) (frames S2)) by (rewrite Hfr2; exact uw_fin3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR2 Hfin2) as (_ & _ & HFp & HSp).
  rewrite (Efa2 UM_CID fpos) in HFp, HSp. fold (um_F cx fpos) in HFp, HSp.
  change (fs_frame_bytes UM_CID) with 512 in HFp, HSp. change (512 / 8) with 64 in HSp.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HJ2|].
  split; [rewrite Hfr2; exact Hfr3|]. split; [exact Hnin|].
  split; [destruct uw_bfs as (fs & Efs); exists (st_fs S2); transitivity (set_fs (st_fs S2) S3);
          [exact Hsfs | rewrite Efs; reflexivity]|].
  split; [exact (Permutation_trans Hperm2 uw_bperm)|].
  split; [exact HS1|].
  split; [exact Efa2|].
  cbn [ms_regs ms_mem mkst].
  split; [etransitivity; [uw_prr PR 2 | exact B2]|].
  split; [etransitivity; [uw_prr PR 9 | exact B9]|].
  split; [etransitivity; [uw_prr PR 8 | exact B8]|].
  split; [etransitivity; [uw_prr PR 18 | exact B18]|].
  split; [etransitivity; [uw_prr PR 19 | exact B19]|].
  split; [etransitivity; [uw_prr PR 25 | exact B25]|].
  split; [etransitivity; [uw_prr PR 20 | exact B20]|].
  split; [etransitivity; [uw_prr PR 3 | exact B3]|].
  split; [etransitivity; [uw_prr PR 4 | exact B4]|].
  split; [rewrite <- Bra; apply uw_rdword_ext; intros i Hi; apply KUP; lia|].
  split; [intros j Hj; rewrite <- (Bsv j Hj); apply uw_rdword_ext; intros i Hi; apply KUP; lia|].
  split.
  { rewrite <- Bfl. apply uw_rdword_ext. intros i Hi. pose proof HK2 as (_ & _ & _ & K4' & _).
    apply (K4' UM_CID fpos (um_F cx fpos + UM_FLAGPTR + i) uw_fin3).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite F4. change (fs_frame_bytes UM_CID) with 512.
      unfold UM_FLAGPTR. lia.
    - intros Hw. cbv beta in Hw. apply uw_awr in Hw. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in F3.
      unfold UM_FLAGPTR in Hw. lia. }
  split; [intros a Ha; exact (proj1 (HFp a Ha))|].
  split.
  { intros a Ha. unfold um_SH in Ha. replace a with (shadow_addr (um_F cx fpos) + (a - shadow_addr (um_F cx fpos)))
      by (unfold shadow_addr; lia).
    apply (proj1 (HSp (a - shadow_addr (um_F cx fpos)) ltac:(unfold shadow_addr; unfold UM_SHN in Ha; lia))). }
  split.
  { apply (akept_trans_ly SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) ly3 S3 W3 m3 W2 mem2
      (um_sp cx - 8768) (um_sp cx) (um_sp1 cx - 8560) (um_sp1 cx) Ec
      (fun a => inFP (reac_link_alias_write_awr R' (rdW W3 m3)) a) Ec ltac:(lia) ltac:(lia) uw_bK HK2
      W1 W2' uw_blk uw_frm uw_bfa).
    - intros a H. exact H.
    - intros a Hw. cbv beta in Hw. apply uw_awr in Hw. left. exact (uw_wr_gnl cx a Hw). }
  split; [rewrite Hfd2, Hfd'; exact Bfd|]. split; [rewrite Hfs2, Hfs'; exact Bfs|].
  intros a Hro Ho He. pose proof HK2 as (_ & _ & K3' & _).
  rewrite (K3' a (uw_roP_img a Hro) Ho He).
  - exact (uw_bro a Hro Ho He).
  - intros Hw. cbv beta in Hw. apply uw_awr in Hw. exact (uw_pnro a (uw_wr_gnl cx a Hw) Hro).
Qed.

End d.

(* the call, from the register file the run leaves *)
Lemma uw_call : forall (R' : bvmap 5 word) md',
  getr R' 10 = w64 (um_mk cx + MK_NAME + MARK_LEN * Z.of_nat c) ->
  getr R' 11 = w64 LA_S_EMPTY ->
  getr R' 1 = w64 (BASE + UM_CUT_JOIN) ->
  aregs_preserved R3 R' ->
  AJ ly3 S3 W3 m3 md' -> m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  um_join_obl SK B c ->
  SRr SEGS W3 (cfg_at SEGS REAC_LINK_ALIAS_WRITE_A R' m3 md') (um_post SK B cx).
Proof.
  intros R' md' RC10 RC11 RC1 RCP HJ' Hfd' Hfs' HJN.
  eapply SRr_bind.
  { exact (HWR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R' (uw_apre R' md' RC1 RCP HJ')
      (uw_ard_akb R' RC10 RC11 RCP) (uw_pre R' md' RC10 RC11 RCP HJ')). }
  intros W2 c2 Hle Hpost.
  destruct (uw_after R' md' RC10 RC11 RC1 RCP HJ' W2 c2 Hle Hpost Hfd' Hfs') as (ms2 & md2 & ly2 & S2 & -> & HG).
  exact (HJN cx fpos ly2 S2 W2 ms2 md2 HPRE HG).
Qed.

End c.

(* ==========================================================================
   3. The run of the three instructions, and the piece
   ========================================================================== *)

Theorem um_write : forall c, um_join_obl SK B c -> um_mid_obl SK B c.
Proof.
  intros c HJN cx fpos ly3 S3 W3 ms3 md3 HPRE (Hpc & HLP & (kbs & HKM) & HB).
  pose proof HB as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & _ & _ & _ & _ & _ & _ & R2 & R9 & _).
  pose proof (uw_geo cx HPRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
  pose proof (uw_sp_rng cx) as Hsp.
  pose proof HLP as (_ & _ & _ & _ & _ & _ & _ & _ & L18 & _).
  (* the seated state *)
  pose proof (uw_ms_eta ms3 (Z_to_bv 64 (BASE + UM_CUT_MID)) (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc Hpc) as Hms.
  remember (Eimg (Ereg (ms_regs ms3) uw_extra)) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
    symmetry. apply Z.mod_small. lia. }
  assert (U9 : bv_unsigned (ew E 9) = um_sp1 cx).
  { rewrite (EREG 9%nat ltac:(lia)). change (Z_to_bv 5 (Z.of_nat 9)) with (Z_to_bv 5 9).
    transitivity (bv_unsigned (getr (ms_regs ms3) 9)); [reflexivity|]. rewrite R9. unfold w64.
    apply unsigned_lit_small. lia. }
  assert (HS : st_ok_pi SEGS VAL E uw_ss (restrict (w_H W3) ms3)).
  { rewrite Hms. rewrite restrict_mkst_fx. unfold uw_ss.
    apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, uw_slot.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (um_sp1 cx) 24 8 (SLit LA_S_EMPTY) LA_S_EMPTY);
        [reflexivity | cbn; unfold LA_S_EMPTY; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). unfold UM_SLOT_EMPTY in L18. exact L18.
    - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
    - split; [|split]; exact I. }
  assert (SHOK : sh_ok SEGS uwBx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by (apply Forall_nil).
  pose (RUN := paj_run_x SK B LAWS (um_G cx) (uw_pg cx HPRE) (um_XO cx) (um_OUT cx)).
  clear Hms.
  (* +0x288 .. +0x290: mv a0, s6; ld a1, 0x18(s1); jal reac_link_alias_write *)
  paj_run_tok RUN HS HJ3 SHOK uwSpan.
  { unfold uw_ss. cbn [ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi uw_slot base_val] in Ha. lia. }
  (* at the call *)
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1.
  assert (Em : ms_mem ms = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF. intros (r & [<- | []] & Hr).
    cbn [YP09.r_wlo YP09.r_whi uw_slot] in Hr. lia. }
  rewrite Em in HJ3 |- *.
  assert (HCFG : forall md',
    mkCfg (mkst (ms_regs ms) (Z_to_bv 64 (pa_sigma LS_reac_link_alias_write)) (ms_mem ms3) (seg_rom SEGS)) md' =
    cfg_at SEGS REAC_LINK_ALIAS_WRITE_A (ms_regs ms) (ms_mem ms3) md').
  { intros md'. unfold cfg_at, w64. rewrite (lv_sigma LV). reflexivity. }
  rewrite HCFG. clear HCFG.
  pose proof HLP as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMK).
  apply (uw_call cx c fpos ly3 S3 W3 ms3 md3 kbs HPRE HM HMK HLP HKM HB).
  - rewrite Q10, (EREG 22%nat ltac:(lia)). destruct HLP as (_ & _ & _ & L22 & _). exact L22.
  - rewrite Q11. reflexivity.
  - rewrite Q1. reflexivity.
  - intros k Hk. unfold acallee_saved in Hk.
    assert (Hk' : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/
                  k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27) by lia.
    clear Hk.
    repeat (destruct Hk' as [-> | Hk']; [
      lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
        let n := eval vm_compute in (Z.to_nat kk) in
        let Hr := fresh "Hr" in
        prreg HS (Z_to_bv 5 kk) Hr; rewrite Hr, (EREG n ltac:(lia)); reflexivity
      end |]).
    subst k.
    prreg HS (Z_to_bv 5 27) Hr; rewrite Hr, (EREG 27%nat ltac:(lia)); reflexivity.
  - exact HJ3.
  - rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
  - exact HJN.
Qed.

About um_write.
Print Assumptions um_write.

End b.
End a.
