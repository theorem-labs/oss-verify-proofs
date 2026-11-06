(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pitems_dev.v, with its module paths and module names changed; 149 of its 179 lines of code are new or changed and 512 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_epi.v
   (a working branch 2ed11a3c43f), the same names over B's own code (B listing: capstone over the
   unstripped twin of fs.asan-ubsan, whose instructions 0x8164c .. 0x81b5c equal the pinned image's).
   check_as_written over fs.asan-ubsan, the epilogue (B 0x81aa4 .. 0x81ad0): from the state FSW_caw_back.cawb_mid gives
   at the bcmp return 0x81aa4 (a0 = 0, equal bytes) or at the join 0x81aa8, to check_as_written_spec's post cawb_post:
   - 0x81aa4 `bnez a0, 0x81ad8` falls through (a0 = 0, an assumed branch condition of the symbolic state);
   - 0x81aa8 `mv a0, s2` (a0 = want), 0x81aac .. 0x81ac8 the eight reloads of ra, s0 .. s6 from the frame (the extra
     atoms 39 .. 32 of FSW_caw_back.cawb_cs), 0x81acc `addi sp, sp, 64`;
   - 0x81ad0 `j 0x530e0`, the tail call of __wrap_free (PC_free = pc_wrap_free (as_code B), RTf: FsRt.fr_free's
     type), whose return is check_as_written's: FSW_caw_back.cawb_tail from there.
   The reloads are frame-spill loads with no ASan check (B listing 0x81aac .. 0x81ac8: plain `ld` off sp), and no UBSan
   trap lies in 0x81aa4 .. 0x81ad0, so the run is the plain engine (FSW_K fsw_aj_runU) over the frame region
   [sp, sp + 64) at atom 2 holding cawb_cs.
   Rule 24: proves function check_as_written (segment: epilogue cawb_epi; check_as_written B 0x8164c, CONFIRM by
   a Theorem Labs lane); none ported, written new; template lib/A/FSW_caw_epi.v.
   Section hypotheses: FSW_caw_back.v's Section W, by name (of the runtime, RTf only). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_caw_epi.v; 813 of its 871 lines of code are new or changed and 121 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_back.v
   (a working branch 2ed11a3c43f), the same names over B's own code. Every B literal below is from
   B's listing (capstone over the unstripped twin of fs.asan-ubsan, (internal path), whose
   instructions 0x8164c .. 0x81b5c equal the pinned image's, sha256 5ac5ce0954f8...) or from B's constants (lib/B/FSH_Base.v
   PC_free 0x530e0, PC_bcmp 0x426d8, FRAME_check_as_written = 64). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_caw_back.v, with its module names changed; 1171 of its 1260 lines of code are new or changed and 782 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_caw_front.v
   (a working branch 98acdce1d16), re-walked on B's own listing (capstone over the unstripped twin
   of fs.asan-ubsan, sha256 b1566a1c..., whose bytes 0x8164c .. 0x81b5c equal the pinned image's, sha256
   5ac5ce0954f8...). The image imports point at lib/B; the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay
   lib/A's (as lib/B/FSW_K.v imports them); the shared B states (caw_tbl, caw_stk, caw_ss1, caw_ss810) are
   lib/B/FSW_caw_defs.v's and the scan loop's premises (caw_static, caw_memf, caw_six, caw_atoms) lib/B/FSW_caw_scan.v's,
   both taken BY NAME (a working branch a0658ed93a0). *)
(*   rule 24: proves no function (kind: segment lemma; check_as_written, B 0x8164c, CONFIRM by a Theorem Labs lane 04:15Z).

   check_as_written (fs.asan-ubsan 0x8164c): the FRONT of the function, machine code 0x8164c .. 0x8170c, in
   continuation-passing form. From the spec's entry premise (lib/B/FSH_Fn_checks.v check_as_written_spec, Section c:
   fpreU at STK_check_as_written = 64 + 16384 with the text t in a0) the walk runs

     0x8164c prologue (frame 64: ra, s0 .. s6 saved; s0 := l, s1 := bd, s4 := the ASan shadow base read through the GOT
             at 0x81678 .. 0x81680, s3 := t)
     -> `jal __wrap_strlen` 0x81688            (FsRt.fr_strlen on the text, |tb| in a0)
     -> a0 := |tb| / 4 * 3 + 3                 (fs.c:167 B64_ALLOC_BOUND; 0x8168c .. 0x81698)
     -> `jal __wrap_malloc` 0x8169c            (want; FsRt.fr_malloc through FSW_malloc_free.fsw_aj_malloc04U, so the
                                                `beqz a0` at 0x816a0 to the abort 0x81ad8 is decided untaken: 4096 <= want)
     -> `jal __wrap_strlen` 0x816ac            (the same text again)
     -> a0 := max |tb| 1                       (0x816b0 `seqz`, 0x816b4 `add`)
     -> `jal __wrap_malloc` 0x816b8            (six; the `beqz a0` at 0x816bc to 0x81ad8 decided untaken)
     -> the inline shadow check of t (0x816c0 .. 0x816cc), the load of t[0] (0x816d0) and `not a3, a0` (0x816d4, a3 :=
        ~six), walked with the TOKEN engine over caw_Bx with one shadow entry for the byte at t (cawf_SH); the
        `__asan_report_load1` arm 0x81ae4 .. 0x81af0 (report-sites-B.tsv row 13, 0x816cc:bne->0x81ae4) is never reached,
        because that entry is discharged by cstr_ok's range_addressable; t[0] is the atom 97 of the region cawf_txtR
     -> `beqz a2` 0x816d8 (YA0o.SRr_sym_branch on the zero-extended byte), the two arms:
        * t[0] <> 0 (the text is not empty): the loop setup 0x816dc .. 0x81708 (a4 := 0, t3 := 0, a1 := t + 1, the
          classification constants, a7 = s5 := SIZE_MAX) to the scan loop head 0x8170c in FSW_caw_defs' state
          caw_ss1 1 255 with j = 0, sx = [], pad = 0 (continuation KLOOP; cawf_head_ok);
        * t[0] = 0 (the empty text): straight to 0x81810, FSW_caw_defs' hand-over caw_ss810 (continuation K810;
          cawf_810_ok); B's arm reads no memory there (A's reloads the text at 0x81738).
   Report sites of check_as_written on this segment (report-sites-B.tsv): row 13 (load1 of t, refuted by the token run
   above), row 12 (the abort 0x81ad8 .. 0x81ae0 after `jal` at 0x81ad8, reached only from the two `beqz a0`, refuted by
   the two non-NULL mallocs); no UBSan trap (row 11's branches all lie at or after 0x8177c) and no atexit call here.

   The symbolic states keep the ENTRY convention of the loop states (FSW_caw_defs): atom 2 is the ENTRY sp (the frame
   region caw_stk is based at it with the window [-64, 0)), atoms 0 .. 31 are the entry registers, atom 32 the shadow
   base. A call is resumed with YN3v.st_ok_splice_havoc: the callee-saved registers keep their symbolic values and the
   caller-saved ones, ra included, get fresh atoms (the junk list CAWF_CLOB; the frame [sp0 - 64, sp0) is carried
   by acall_kept / the runtime post, cawf_keep_frame), so the env stays the entry env extended by havoc and never
   re-keys to the callee's sp. No contract gives ra after `jal __wrap_malloc`, so the loop states hold ra as atom 31
   (a Theorem Labs lane ruling 2026-10-29) and ~six (a3) as atom 30: the two handover states are re-keyed with YL09.st_ok_reabs
   keeping cawf_P (the atoms below 33 except 30 and 31) and setting atom 30 to the machine's a3 and 31 to its ra
   (cawf_env810 / cawf_envH).

   Section hypotheses (owners), each taken BY NAME:
   - IMG : fs_img_facts tfibsegs B                        (S0, lib/B/FSH_Rt.v)
   - SYMS : FsShadowSyms B                                (RELOC, lib/B/FSH_Base.v: the GOT slot and the shadow cell)
   - RTs, RTm : FsRt's fr_strlen, fr_malloc, by their field types (RUNTIME, lib/B/FSH_Rt.v; the only two fields the
     front uses)
   - FS_ENV : api_env tfibsegs B                          (RELOC / the core's allocator interface)
   - ML : model_laws (as_universe B)                      (RELOC, the generated universe)
   rule 24: no function is proved here; this file proves no *_spec. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL02 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YF0l YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_rres FSW_malloc_free FSW_strkit FSW_caw_defs FSW_caw_scan
FSH_Fn_checks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- image facts (the twins of FSW_strdup.sd_pstat_img / sd_relro_img / sd_ro_img / sd_range_order; this file does
   not load FSW_strdup, an allocator-lane walk) ---- *)
Lemma cawf_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => seg_covers (fst r) (snd r - fst r)) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.
Lemma cawf_relro_img : forall a, FS_RLO <= a < FS_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. assert (H : seg_covers FS_RLO (FS_RHI - FS_RLO) = true) by (vm_compute; reflexivity).
exact (seg_covers_img _ _ a H ltac:(lia)).
Qed.
Lemma cawf_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (cawf_relro_img a Hr)].
Qed.
Lemma cawf_range_order : forall p a q c, 0 < a -> 0 < c ->
  (forall x, p <= x < p + a -> ~ (q <= x < q + c)) -> p + a <= q \/ q + c <= p.
Proof.
intros p a q c Ha Hc H. destruct (Z_le_gt_dec (p + a) q) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (q + c) p) as [L'|L']; [right; exact L'|].
exfalso. apply (H (Z.max p q)); lia.
Qed.

(* ---- the return addresses of the four calls (MEASURED, capstone on fs.asan-ubsan) ---- *)
Definition RA_CAWF_STRLEN1 : Z := 0x8168c.
Definition RA_CAWF_MALLOC1 : Z := 0x816a0.
Definition RA_CAWF_STRLEN2 : Z := 0x816b0.
Definition RA_CAWF_MALLOC2 : Z := 0x816bc.

(* ---- the resume list: every caller-saved register a callee may clobber gets a fresh atom (junk_upd), ra included: the
   loop states hold ra as atom 31 and ~six (a3) as atom 30 (FSW_caw_defs caw_regs1 / caw_regs810), which the
   hand-overs set to the machine's ra and a3 ---- *)
Definition CAWF_CLOB : list (bv 5) := [10; 1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

(* ---- the first byte of the text, read through the entry atom 10 (= t, kept in s3) at 0x816d0; atom 97 is its value
   (the atom after the fourth resume's 81 .. 96) ---- *)
Definition cawf_txtR : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 97 0))].
(* the shadow entry of the inline check at 0x816c0: the byte at t *)
Definition cawf_SH : list shent := [mkSHE 10 0 1].
(* the atoms both hand-overs keep: the entry registers and the shadow base, except 30 and 31 (the entry t5 / t6, which
   no state of the walk names after the first call; the loop states use them for ~six and ra) *)
Definition cawf_P (n : nat) : bool := Nat.ltb n 33 && negb (Nat.eqb n 30) && negb (Nat.eqb n 31).

(* the two block sizes of this function: want = B64_ALLOC_BOUND |tb| (fs.c:167), six = max |tb| 1 (fs.c:71) *)
Definition cawf_want_size (tb : list Z) : Z := b64_alloc_bound (Z.of_nat (length tb)).
Definition cawf_six_size (tb : list Z) : Z := Z.max (Z.of_nat (length tb)) 1.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.


(* one more atom fact on a state (YP06 facts_ok_add_atom) *)
Lemma cawf_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
      (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms n f HS Hf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))))) | exact Hf].
Qed.

(* an atom fact from a value equation *)
Lemma cawf_afact : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hn, unsigned_lit_small by exact Hv. rewrite Z.pow_0_r, Z.mod_1_r.
split; [lia | split; [reflexivity | lia]].
Qed.

(* the read-only view on the unpoisoned memory, rom_view, and a runtime post (strlen) in fsw_intrin_atU's form (the
   twins of FSW_strdup.sd_arodata_unpoison / sd_rom_view / sd_unpoison_frame / sd_unpoison_present / sd_rt_ro_to_aru) *)
Lemma cawf_arodata_unpoison : forall ly S Up (W : world tfibsegs) m md, ARU tfibsegs B ly S Up W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison Up m)).
Proof.
intros ly S Up W m md H HR a Hro Ho He.
pose proof (fsk_segs_img a (cawf_ro_img a Hro)) as Hl. unfold FS_IMG_END in Hl.
rewrite (aview_at tfibsegs (w_H W) (unpoison Up m) m a); [exact (HR a Hro Ho He)|].
apply (unpoison_app B ly S Up W m md a H); unfold SHADOW_OFF; lia.
Qed.
Lemma cawf_rom_view : forall ly S Up (W : world tfibsegs) m md, fs_img_facts tfibsegs B -> ARU tfibsegs B ly S Up W m md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) -> rom_view tfibsegs W m.
Proof.
intros ly S Up W m md IMG H HR a Hrom.
pose proof H as (HAR & _ & _).
destruct (proj2 IMG ly S W (unpoison Up m) md HAR (cawf_arodata_unpoison ly S Up W m md H HR)) as (Hrv & _).
destruct Hrom as (sg & Hsg & Hw & Hr).
pose proof (fsk_segs_img a (ex_intro _ sg (conj Hsg Hr))) as Hl. unfold FS_IMG_END in Hl.
rewrite <- (aview_at tfibsegs (w_H W) (unpoison Up m) m a (unpoison_app B ly S Up W m md a H ltac:(lia)
  ltac:(left; unfold SHADOW_OFF; lia))).
apply Hrv. exists sg. split; [exact Hsg | split; [exact Hw | exact Hr]].
Qed.
Lemma cawf_unpoison_frame : forall (Uc : list (Z * Z)) (W : world tfibsegs) m m' (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ X a ->
  aview tfibsegs (w_H W) (unpoison Uc m') a = aview tfibsegs (w_H W) (unpoison Uc m) a.
Proof.
intros Uc W m m' X Hfr a Ha Hx. destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- apply (aview_unpoison_in tfibsegs). exact E.
- rewrite !(aview_unpoison_out tfibsegs) by exact E. exact (Hfr a Ha Hx).
Qed.
Lemma cawf_unpoison_present : forall (Uc : list (Z * Z)) (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (unpoison Uc m) a -> apresent H (unpoison Uc m') a.
Proof.
intros Uc H m m' Hg a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
destruct (Hg a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
Qed.
Lemma cawf_rt_ro_to_aru : forall K lyc Sc Uc (W : world tfibsegs) regsT memT mdT (R : Z -> Prop) W' c',
  upoison_ok B lyc Sc Uc ->
  rt_post_roU tfibsegs B K lyc Sc Uc W regsT memT mdT R W' c' ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (YK11.mkst regs' (YK11.getr regsT 1) mem' (YK11.seg_rom tfibsegs)) md' /\
    ARU tfibsegs B lyc Sc Uc W mem' md' /\ same_but_materialized mdT md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - K <= a < spZ regsT) ->
       aview tfibsegs (w_H W) (unpoison Uc mem') a = aview tfibsegs (w_H W) (unpoison Uc memT) a) /\
    (forall a, apresent (w_H W) (unpoison Uc memT) a -> apresent (w_H W) (unpoison Uc mem') a) /\
    (aregs_preserved regsT regs' /\ (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - K <= a < spZ regsT) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) memT a)).
Proof.
intros K lyc Sc Uc W regsT memT mdT R W' c' OK
  (-> & regs' & mem' & md' & v & -> & HAR' & PO' & HP & Hsame & H10 & Hv & HR & Hfr & Hgr).
split; [reflexivity|]. exists regs', mem', md'.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [split; [exact HAR' | split; [exact OK | exact PO']]|].
split; [exact Hsame|].
split; [exact (cawf_unpoison_frame Uc W memT mem' (fun a => spZ regsT - K <= a < spZ regsT) Hfr)|].
split; [exact (cawf_unpoison_present Uc (w_H W) memT mem' Hgr)|].
split; [exact HP|]. split; [exists v; split; [exact H10 | split; [exact Hv | exact HR]] | exact Hfr].
Qed.

(* the read-only view rides through a journal with an EMPTY footprint (the twin of FSW_strdup.sd_arodata_kept, which
   is keyed to FS_PSTAT_FP; check_as_written writes no static, so its FP is []) *)
Lemma cawf_arodata_kept : forall STK sp0 ly S Up W mem md own lyc Sc Uc Wc memc mdc k,
  ARU tfibsegs B ly S Up W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison Up mem) md own lyc Sc Wc (unpoison Uc memc) mdc k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).
Proof.
intros STK sp0 ly S Up W mem md own lyc Sc Uc Wc memc mdc k H0 H1 HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
pose proof (cawf_ro_img a Hro) as Hi. pose proof (fsk_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold SHADOW_OFF; lia).
rewrite <- (aview_at tfibsegs (w_H Wc) (unpoison Uc memc) memc a
  (unpoison_app B lyc Sc Uc Wc memc mdc a H1 ltac:(lia) Happ)).
rewrite (F3 a Hi Ho He (fun X => inFP_nil a X)).
- rewrite (aview_at tfibsegs (w_H W) (unpoison Up mem) mem a (unpoison_app B ly S Up W mem md a H0 ltac:(lia) Happ)).
  exact (HR a Hro Ho He).
- apply fp_spares_closed. exact sink_closed_nil.
Qed.

(* the frame region of check_as_written (FSW_caw_defs.caw_stk: the 64-byte frame the prologue leaves, based at the
   ENTRY sp) on a memory that keeps the window [sp0 - 64, sp0) *)
Lemma cawf_frame_ok : forall STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) memT mem2 md2 k E,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  bv_unsigned (ew E 2) = sp0 -> 64 <= STK ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) memT) sp0) (YP09.r_chunks caw_stk) ->
  (forall a, sp0 - 64 <= a < sp0 ->
     mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) ->
  region_ok tfibsegs E (mrestrict (w_H W) mem2) caw_stk.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc U2 W memT mem2 md2 k E HJ HARU E2 HSTK Hcs Hkeep.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold region_ok, caw_stk.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split.
- intros o Ho. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
- apply (fsw_chunks_kept E (w_H W) memT mem2 sp0 (-64) 0 (YP09.r_chunks caw_stk));
    [unfold caw_stk; cbn [YP09.r_chunks]; repeat constructor; cbn; lia | exact Hcs |].
  intros a Ha. apply Hkeep. lia.
Qed.

(* the chunks of the frame read off a state whose first region is caw_stk *)
Lemma cawf_frame_chunks : forall E ss ms (H : word -> bool) sp0,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) 0 = Some caw_stk ->
  bv_unsigned (ew E 2) = sp0 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) sp0) (YP09.r_chunks caw_stk).
Proof.
intros E ss ms H sp0 HS Hm E2.
pose proof (fsw_region_nth E ss (restrict H ms) 0 caw_stk HS Hm) as HR.
cbn [ms_mem restrict] in HR. destruct HR as (_ & _ & _ & Hcs).
unfold caw_stk in *. cbn [YP09.r_base base_val] in Hcs. rewrite E2 in Hcs. exact Hcs.
Qed.

(* the strlen call's ecall premise at this function's frame (the twin of FSW_strdup.sd_strlen_pre at STK 48) *)
Lemma cawf_ecall_pre : forall ly S Up W mem md lyc Sc Wc regsT memT mdT k sp0,
  ARU tfibsegs B lyc Sc Up Wc memT mdT ->
  ajournal tfibsegs B STK_check_as_written sp0 [] ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison Up memT) mdT k ->
  spZ regsT = sp0 - 64 -> YK0s.ret_ok (YK11.getr regsT 1) ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  ecall_preU_k tfibsegs B STK_RT_STR lyc Sc Up Wc regsT memT mdT.
Proof.
intros ly S Up W mem md lyc Sc Wc regsT memT mdT k sp0 HC HJ Esp Hra R3 R4.
pose proof HC as (_ & OK & PO).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FS : STK_check_as_written = 64 + 16384) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
split; [split; [|split; [exact OK | exact PO]]|].
- apply (ecall_pre_at tfibsegs B STK_check_as_written sp0 [] ly S W (unpoison Up mem) md [] lyc Sc Wc
    (unpoison Up memT) mdT k regsT (-64) HJ);
    first [solve [exact Hra] | solve [exact R3] | solve [exact R4]
          | lazymatch goal with |- _ mod _ = _ => solve [reflexivity] end | solve [lia]].
- split; [rewrite Eslo; lia|].
  intros a Ha. apply (fsw_apresent_unpoison B lyc Sc Up Wc memT mdT a HC); first [solve [lia] | solve [apply Hpres; lia]].
Qed.
(* a register's machine value is the denotation of its symbolic value (st_ok's regs_ok, for any env) *)
Lemma cawf_reg_sv : forall E ss (H : word -> bool) ms,
  st_ok tfibsegs E ss (restrict H ms) ->
  forall r, YK11.getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r).
Proof.
intros E ss H ms HS r.
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HS)))))) r).
Qed.


(* a register outside the junk list keeps its value across a call (the twin of YI04.regs_preserved_frame for the
   walk's own junk lists) *)
Lemma cawf_kept_clob : forall (regsA regsB : bvmap 5 word) (r : bv 5),
  aregs_preserved regsA regsB -> reg_in r CAWF_CLOB = false -> YK11.getr regsB r = YK11.getr regsA r.
Proof.
intros regsA regsB r HP Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin];
  [first [ rewrite !getr_zero; reflexivity
         | vm_compute in Hr; discriminate
         | apply (fsw_pres regsA regsB); [exact HP|];
           lazymatch goal with |- context [bv_unsigned ?x] =>
             let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
           unfold acallee_saved; lia ] |]).
destruct Hin.
Qed.
(* the frame's chunks carried to another memory that holds the same bytes on [sp0 - 64, sp0) *)
Lemma cawf_chunks_move : forall E (m m' : word -> option byte) sp0,
  Forall (YP09.chunk_ok tfibsegs E m sp0) (YP09.r_chunks caw_stk) ->
  (forall a, sp0 - 64 <= a < sp0 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m' sp0) (YP09.r_chunks caw_stk).
Proof.
intros E m m' sp0 Hcs Hk. apply Forall_forall. intros c Hc.
apply (chunk_ok_mbyte _ m); [|exact (proj1 (Forall_forall _ _) Hcs c Hc)].
intros i Hi. apply Hk.
unfold caw_stk in Hc. cbn [YP09.r_chunks In] in Hc.
repeat (destruct Hc as [<-|Hc]; [cbn in Hi |- *; lia|]). destruct Hc.
Qed.

(* the frame [sp0 - 64, sp0) is kept, on the machine's memories, by a call whose window [slo, shi) ends at or below its
   bottom (acall_kept's first clause over the unpoisoned readings; the frame is high memory, where they agree) *)
Lemma cawf_keep_frame : forall ly S U (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' md' sp0 slo shi,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview tfibsegs (w_H W') (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
  shi <= sp0 - 64 -> alloc_ceiling <= sp0 - 64 -> sp0 <= 2 ^ 47 ->
  forall a, sp0 - 64 <= a < sp0 ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U W mem md ly' S' W' mem' md' sp0 slo shi H H' Hk Hs Hc H47 a Ha.
pose proof asan_consts as (C1 & _ & C3 & _).
apply (mbyte_of_aview tfibsegs).
rewrite <- (fsw_aview_unpoison_high B ly' S' U W' mem' md' a H') by lia.
rewrite <- (fsw_aview_unpoison_high B ly S U W mem md a H) by lia.
apply Hk; lia.
Qed.

(* the shadow byte of x is in no U range when every range is a 16-byte head (q, 16), q 8-aligned, not holding x (the
   twin of FSW_rd.fsw_head_ush_out, which this file does not load) *)
Lemma cawf_head_ush_out : forall (U : list (Z * Z)) x, 0 <= x ->
  (forall r, In r U -> snd r = 16 /\ fst r mod 8 = 0 /\ ~ (fst r <= x < fst r + 16)) ->
  in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros U x Hx HU. destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs). destruct (HU r Hr) as (E16 & Q8 & Nx).
rewrite E16 in Hs. unfold shadow_addr, shadow_of_addr in Hs.
apply Z.mod_divide in Q8 as [k Hk]; [|lia]. rewrite Hk in Hs, Nx.
Z.div_mod_to_equations. lia.
Qed.

(* a block a malloc call granted (any block not among the heads' blocks L): not one of L, its bounds, disjoint from
   every block of L, outside the shadow region, its shadow addressable and its bytes writable on the machine's memory
   (no head of U lies in it, so U's shadow bytes are not its shadow bytes) *)
Lemma cawf_new_block : forall ly S U (W : world tfibsegs) mem md L L2 b n,
  ARU tfibsegs B ly S U W mem md -> ablocks B ly S = L ++ (b, n) :: L2 ->
  (forall r, In r U -> snd r = 16 /\ exists m, In (fst r, m) L /\ 16 <= req_size m) ->
  (forall m, ~ In (b, m) L) /\ 4096 <= b /\ b + req_size n <= alloc_ceiling /\ 0 <= n /\ n <= req_size n /\
  (forall p m, In (p, m) L -> p + req_size m <= b \/ b + req_size n <= p) /\
  (forall x, b <= x < b + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF b n /\
  (forall a, b <= a < b + n -> writable_at tfibsegs (mrestrict (w_H W) mem) a).
Proof.
intros ly S U W mem md L L2 b n H Eab HU.
pose proof H as (HAR & _ & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hnew : In (b, n) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b n HAR Hnew) as (Hal & H4096 & Hceil & Happ & Hpres & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (Rq1 & Rq2).
assert (Hdisj : forall p m, In (p, m) L -> p + req_size m <= b \/ b + req_size n <= p).
{ intros p m Hin.
  assert (Hin' : In (p, m) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p m HAR Hin') as (_ & _ & _ & _ & _ & _ & Hm).
  apply in_split in Hin as (l1 & l2 & El).
  assert (E2 : ablocks B ly S = l1 ++ (p, m) :: l2 ++ (b, n) :: L2) by (rewrite Eab, El, <- app_assoc; reflexivity).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison U mem) md _ _ l1 l2 L2 HAR E2) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. exact D. }
assert (Happ' : forall x, b <= x < b + req_size n -> x < SHADOW_OFF \/ kHighMemBeg <= x).
{ intros x Hx. destruct Happ as [_ [Hl | [Hh1 _]]]; [left | right]; unfold kLowShadowBeg, SHADOW_OFF in *; lia. }
split.
{ intros m Hin.
  assert (Hin' : In (b, m) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md b m HAR Hin') as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)). destruct (Hdisj b m Hin) as [D|D]; lia. }
split; [exact H4096|]. split; [exact Hceil|]. split; [lia|]. split; [exact Rq2|]. split; [exact Hdisj|].
split.
{ intros x Hx Hs. destruct (Happ' x ltac:(lia)) as [Hl|Hl]; unfold SHADOW_OFF in *; lia. }
split.
{ intros x Hx.
  destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md b n b n HAR Hnew ltac:(lia)
    ltac:(lia) x Hx) as (s & Hs & Hok).
  exists s. split; [|exact Hok].
  rewrite <- (aview_unpoison_sh U W mem (shadow_of_addr SHADOW_OFF x)); [exact Hs | |].
  - unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia.
  - apply cawf_head_ush_out; [lia|]. intros r Hr. destruct (HU r Hr) as (H16 & m & Hm & Hm16).
    assert (Hm' : In (fst r, m) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; left; exact Hm).
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (fst r) m HAR Hm') as (Halr & _).
    split; [exact H16|]. split.
    + apply Z.mod_divide in Halr; [|lia]. destruct Halr as [q Hq]. rewrite Hq.
      replace (q * 16) with ((q * 2) * 8) by lia. apply Z.mod_mul. lia.
    + destruct (Hdisj (fst r) m Hm) as [D|D]; lia. }
intros a Ha. destruct (Hpres a ltac:(lia)) as ((Hh & v & Hv) & _).
apply (apresent_writable tfibsegs). split; [exact Hh|]. exists v.
rewrite <- (unpoison_app B ly S U W mem md a H ltac:(lia) (Happ' a ltac:(lia))). exact Hv.
Qed.

(* a kept string misses a block that is none of the string's blocks: a block home is disjoint from it (AR's pairwise
   disjoint blocks), a table home is image bytes and the block holds none *)
Lemma cawf_str_off_new : forall ly S (W : world tfibsegs) mem md L L2 b n ly0 S0 (U0 : list (Z * Z)) t tb,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = L ++ (b, n) :: L2 ->
  (forall x, In x (ablocks B ly0 S0) -> In x L) -> cstr_kept B ly0 S0 U0 t tb ->
  t + Z.of_nat (length tb) + 1 <= b \/ b + req_size n <= t.
Proof.
intros ly S W mem md L L2 b n ly0 S0 U0 t tb HAR Eab Hinc Hk.
assert (Hnew : In (b, n) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hnew) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as (Rq1 & Rq2).
destruct Hk as [(b0 & m0 & Hin & Hb & Hbm & _) | Htbl].
- apply Hinc in Hin.
  assert (Hin0 : In (b0, m0) (ablocks B ly S)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS ly S W mem md b0 m0 HAR Hin0) as (_ & _ & _ & _ & _ & _ & Hm0).
  pose proof (req_size_pos m0 ltac:(lia)).
  apply in_split in Hin as (l1 & l2 & El).
  assert (E2 : ablocks B ly S = l1 ++ (b0, m0) :: l2 ++ (b, n) :: L2) by (rewrite Eab, El, <- app_assoc; reflexivity).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md _ _ l1 l2 L2 HAR E2) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
- assert (Himg : forall x, t <= x < t + Z.of_nat (length tb) + 1 -> in_img tfibsegs x).
  { destruct Htbl as [Hs | (ps & Hf & ->)];
      [exact (fun a => fs_ro_strs_img t tb a Hs) | exact (fun a => fs_sn_fmts_img t ps a Hf)]. }
  assert (Hdj : forall x, t <= x < t + (Z.of_nat (length tb) + 1) -> ~ (b <= x < b + req_size n)).
  { intros x Hx Hxb. apply (blk_img tfibsegs B LAWS ly S W mem md b n x HAR Hnew Hxb). apply Himg. lia. }
  pose proof (cawf_range_order t (Z.of_nat (length tb) + 1) b (req_size n) ltac:(lia) ltac:(lia) Hdj) as Hor. lia.
Qed.

(* small readings of a state and an env *)
Lemma cawf_bb : forall ly S, blocks_bytes S = bsum (ablocks B ly S).
Proof.
intros ly S. unfold blocks_bytes, ablocks, blocks, bsum.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.
Lemma cawf_w_of_u : forall (w : word) v, bv_unsigned w = v -> w = Z_to_bv 64 v.
Proof. intros w v H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma cawf_U0 : forall E n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v.
Proof.
intros E n v H. rewrite U_SOff, Z.add_0_r, H. apply zcanon_id. subst v. unfold M64. apply u64_range.
Qed.
Lemma cawf_den0 : forall E n v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. reflexivity. Qed.
Lemma cawf_ew_lit : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
(* an atom pinned by a state's atom fact [v, v] *)
Lemma cawf_atom_val : forall E ss ms n v,
  st_ok tfibsegs E ss ms -> In (n, mkAF v v 0) (f_atoms (ss_facts ss)) -> 0 <= v < 2 ^ 64 -> ew E n = Z_to_bv 64 v.
Proof.
intros E ss ms n v HS Hin Hv.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & _ & _)).
pose proof (atoms_ok_In E _ n _ HA Hin) as Hf. unfold afact_ok in Hf. cbn [af_lo af_hi af_al2] in Hf.
apply cawf_w_of_u. lia.
Qed.

(* ---- what both continuations get: the two blocks (bounds, freshness, disjointness from each other and from the text,
   shadow, writability, the write permission of want's bytes), the journal with the two allocator events, ARU, the
   reader bookkeeping, and the memory facts of the text and of six ---- *)
Definition cawf_post (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (t : Z) (tb : list Z) (live peak cnt fail : Z)
  (W2 : world tfibsegs) (ly2 : alayout) (S2 : astate) (want six : Z) (ms' : machine_state) (mdc' : Model) : Prop :=
  wle W W2 /\
  ablocks B ly2 S2 = (ablocks B ly S ++ [(want, cawf_want_size tb)]) ++ [(six, cawf_six_size tb)] /\
  frames S2 = frames S /\ st_nev S2 <= st_nev S + 2 /\
  4096 <= want /\ want + cawf_want_size tb <= alloc_ceiling /\
  4096 <= six /\ six + cawf_six_size tb <= alloc_ceiling /\
  ajournal tfibsegs B STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U (ms_mem ms')) mdc' 2 /\
  ARU tfibsegs B ly2 S2 U W2 (ms_mem ms') mdc' /\
  fs_heads B ly2 S2 U /\ cstr_kept B ly2 S2 U t tb /\
  fs_glob tfibsegs W2 (ms_mem ms') live peak cnt fail /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) (ms_mem ms')) /\
  caw_memf W2 t tb six (cawf_six_size tb) (ms_mem ms') /\
  range_addressable (aview tfibsegs (w_H W2) (ms_mem ms')) SHADOW_OFF want (cawf_want_size tb) /\
  (forall a, want <= a < want + cawf_want_size tb -> writable_at tfibsegs (mrestrict (w_H W2) (ms_mem ms')) a) /\
  (six + cawf_six_size tb <= want \/ want + cawf_want_size tb <= six) /\
  (t + Z.of_nat (length tb) + 1 <= want \/ want + cawf_want_size tb <= t) /\
  (forall m, ~ In (want, m) (ablocks B ly S)) /\
  (forall m, ~ In (six, m) (ablocks B ly S ++ [(want, cawf_want_size tb)])) /\
  (forall a, want <= a < want + cawf_want_size tb ->
     awr_byte tfibsegs B STK_check_as_written (spZ regs) [] (ablocks B ly S) (ablocks B ly2 S2) ly2 [] (frames S) a).

Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis SYMS : FsShadowSyms B.
Hypothesis RTs : astrlen_realizesU tfibsegs B PC_strlen.
Hypothesis RTm : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* what rides through the journal from the entry (footprint []): the read-only view, the text (cstr_ok, cstr_kept) and
   the allocator statics (image bytes outside the owned statics and errno, fs_img_facts' first conjunct) *)
Lemma cawf_carry : forall STK sp0 ly S U (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' md' k t tb
    live peak cnt fail,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U mem') md' k ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  cstr_kept B ly S U t tb -> cstr_ok tfibsegs W mem t tb ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem') /\ cstr_ok tfibsegs W' mem' t tb /\
  cstr_kept B ly' S' U t tb /\ fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros STK sp0 ly S U W mem md ly' S' W' mem' md' k t tb live peak cnt fail H0 H1 HJ Hinc HR Hk Hc HG.
pose proof H1 as (HAR1 & OK1 & PO1).
assert (HR' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem'))
  by exact (cawf_arodata_kept STK sp0 ly S U W mem md [] ly' S' U W' mem' md' k H0 H1 HJ HR).
split; [exact HR'|]. split.
{ exact (cstr_ok_keptU B STK sp0 [] ly S U W mem md [] ly' S' U W' mem' md' k t tb IMG H0 HJ OK1 PO1 Hinc
    (fun a Ha => False_ind _ (inFP_nil a Ha)) HR' Hk (fun r Hr => or_introl Hr) Hc). }
split; [exact (cstr_kept_kept B ly S U ly' S' U t tb Hinc (fun r Hr => or_introl Hr) Hk)|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (KA : forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. pose proof (cawf_pstat_img a Ha) as Hi. pose proof (fsk_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
  destruct (proj1 IMG a Ha) as (Ho & He).
  assert (Happ : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold SHADOW_OFF; lia).
  rewrite <- (aview_at tfibsegs (w_H W') (unpoison U mem') mem' a
    (unpoison_app B ly' S' U W' mem' md' a H1 ltac:(lia) Happ)).
  rewrite (F3 a Hi Ho He (fun X => inFP_nil a X)).
  - exact (aview_at tfibsegs (w_H W) (unpoison U mem) mem a (unpoison_app B ly S U W mem md a H0 ltac:(lia) Happ)).
  - apply fp_spares_closed. exact sink_closed_nil. }
destruct HG as (G1 & G2 & G3 & G4 & R).
assert (VK : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W') mem mem'); first [solve [exact Hv] | idtac].
  intros j Hj. apply KA. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
unfold fs_glob, fs_glob_at.
split; [apply VK; [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto | exact G1]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto | exact G2]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto | exact G3]|].
split; [apply VK; [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto | exact G4]|].
exact R.
Qed.

(* cawf_post at the hand-over, from the composed journal and ARU there (both blocks granted, the text carried) *)
Lemma cawf_post_ok : forall ly S U W regs mem md t tb live peak cnt fail W2 ly2 S2 want six ms' mdc',
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  cstr_kept B ly S U t tb -> cstr_ok tfibsegs W mem t tb -> fs_glob tfibsegs W mem live peak cnt fail ->
  ablocks B ly2 S2 = (ablocks B ly S ++ [(want, cawf_want_size tb)]) ++ [(six, cawf_six_size tb)] ->
  ajournal tfibsegs B STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 W2
    (unpoison U (ms_mem ms')) mdc' 2 ->
  ARU tfibsegs B ly2 S2 U W2 (ms_mem ms') mdc' ->
  cawf_post ly S U W regs mem md t tb live peak cnt fail W2 ly2 S2 want six ms' mdc'.
Proof.
intros ly S U W regs mem md t tb live peak cnt fail W2 ly2 S2 want six ms' mdc' H0 FH HRO Hk Hc HG Eab HJ H2.
pose proof HJ as (_ & _ & _ & Hwle & _ & Hfrs & Hnev & _).
assert (Hinc : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Eab; apply in_or_app; left; apply in_or_app; left; exact Hx).
destruct (cawf_carry STK_check_as_written (spZ regs) ly S U W mem md ly2 S2 W2 (ms_mem ms') mdc' 2 t tb
  live peak cnt fail H0 H2 HJ Hinc HRO Hk Hc HG) as (HRO2 & Hc2 & Hk2 & HG2).
assert (EabW : ablocks B ly2 S2 = ablocks B ly S ++ (want, cawf_want_size tb) :: [(six, cawf_six_size tb)])
  by (rewrite Eab, <- app_assoc; reflexivity).
assert (HUS : forall r, In r U -> snd r = 16 /\
  exists m, In (fst r, m) (ablocks B ly S ++ [(want, cawf_want_size tb)]) /\ 16 <= req_size m).
{ intros r Hr. destruct (FH r Hr) as (H16 & m & Hm & Hm16). split; [exact H16|].
  exists m. split; [apply in_or_app; left; exact Hm | exact Hm16]. }
destruct (cawf_new_block ly2 S2 U W2 (ms_mem ms') mdc' _ [] six (cawf_six_size tb) H2 Eab HUS)
  as (Fs & Hs4096 & Hsceil & Hs0 & Hsreq & Hsdisj & _ & Hsra & Hsw).
destruct (cawf_new_block ly2 S2 U W2 (ms_mem ms') mdc' _ _ want (cawf_want_size tb) H2 EabW FH)
  as (Fw & Hw4096 & Hwceil & Hw0 & Hwreq & _ & _ & Hwra & Hww).
pose proof (Hsdisj want (cawf_want_size tb) ltac:(apply in_or_app; right; left; reflexivity)) as Hsw'.
pose proof (cawf_str_off_new ly2 S2 W2 _ mdc' _ _ want (cawf_want_size tb) ly S U t tb (proj1 H2) EabW
  (fun x Hx => Hx) Hk) as Htw.
pose proof Hc2 as ((Hg2 & _) & _ & _ & _ & _ & Hra2 & _).
unfold cawf_post, caw_memf.
split; [exact Hwle|]. split; [exact Eab|]. split; [exact Hfrs|]. split; [exact Hnev|].
split; [exact Hw4096|]. split; [lia|]. split; [exact Hs4096|]. split; [lia|].
split; [exact HJ|]. split; [exact H2|].
split.
{ intros r Hr. destruct (FH r Hr) as (H16 & m & Hm & Hm16). split; [exact H16|].
  exists m. split; [exact (Hinc _ Hm) | exact Hm16]. }
split; [exact Hk2|]. split; [exact HG2|]. split; [exact HRO2|].
split; [split; [exact Hg2 | split; [exact Hra2 | split; [exact Hsra | exact Hsw]]]|].
split; [exact Hwra|]. split; [exact Hww|].
split; [lia|]. split; [lia|]. split; [exact Fw|]. split; [exact Fs|].
intros a Ha. unfold awr_byte, awr_byte0. left. right. right. left.
exists want, (cawf_want_size tb).
split; [rewrite Eab; apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
split; [exact (Fw _) | lia].
Qed.

(* the scan loop's static premise (FSW_caw_scan caw_static) at the hand-over *)
Lemma cawf_static_ok : forall ly S U W mem t tb W2 ly2 S2 want six m2 md2 sp0,
  ARU tfibsegs B ly2 S2 U W2 m2 md2 -> fs_heads B ly S U ->
  ablocks B ly2 S2 = (ablocks B ly S ++ [(want, cawf_want_size tb)]) ++ [(six, cawf_six_size tb)] ->
  cstr_ok tfibsegs W mem t tb -> cstr_kept B ly S U t tb -> Z.of_nat (length tb) <= 3145728 ->
  alloc_ceiling + STK_check_as_written <= sp0 -> sp0 <= 2 ^ 47 ->
  caw_static B STK_check_as_written sp0 [] ly S [] ly2 S2 t tb six (cawf_six_size tb) sp0.
Proof.
intros ly S U W mem t tb W2 ly2 S2 want six m2 md2 sp0 H2 FH Eab Hc Hk Hlen Hsp H47.
pose proof Hc as ((Hg & Hnz) & Ht4096 & Htceil & _ & Htam & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_check_as_written = 64 + 16384) by reflexivity.
assert (HUS : forall r, In r U -> snd r = 16 /\
  exists m, In (fst r, m) (ablocks B ly S ++ [(want, cawf_want_size tb)]) /\ 16 <= req_size m).
{ intros r Hr. destruct (FH r Hr) as (H16 & m & Hm & Hm16). split; [exact H16|].
  exists m. split; [apply in_or_app; left; exact Hm | exact Hm16]. }
destruct (cawf_new_block ly2 S2 U W2 m2 md2 _ [] six (cawf_six_size tb) H2 Eab HUS)
  as (Fs & Hs4096 & Hsceil & Hs0 & Hsreq & _ & Hssh & _ & _).
pose proof (cawf_str_off_new ly2 S2 W2 _ md2 _ [] six (cawf_six_size tb) ly S U t tb (proj1 H2) Eab
  (fun x Hx => in_or_app _ _ _ (or_introl Hx)) Hk) as Hts.
unfold caw_static.
split; [exact Hnz|]. split; [exact Hlen|]. split; [exact Ht4096|]. split; [exact Htceil|].
split; [intros x Hx; unfold amem_range in Htam; unfold SHADOW_OFF; rewrite C5, C3 in Htam; lia|].
split; [exact Hs4096|]. split; [lia|]. split; [unfold cawf_six_size; lia|]. split; [exact Hssh|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros a Ha. unfold awr_byte, awr_byte0. left. right. right. left.
exists six, (cawf_six_size tb). split; [rewrite Eab; apply in_or_app; right; left; reflexivity|].
split; [intros Hin; exact (Fs _ (in_or_app _ _ _ (or_introl Hin))) | lia].
Qed.
(* ---- the re-keys of the two hand-overs (YL09.st_ok_reabs with the kept atoms cawf_P) ---- *)
Ltac cawf_obls_tac tac :=
  apply Forall_forall; let nf := fresh "nf" in let Hin := fresh "Hin" in intros nf Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin]; [subst nf; cbn [fst snd]; unfold afact_ok; cbn [af_lo af_hi af_al2];
    rewrite Z.pow_0_r, Z.mod_1_r; tac|]); destruct Hin.
Lemma cawf_P_agree : forall E E', (forall n, (n < 30)%nat -> ew E' n = ew E n) -> ew E' 32 = ew E 32 ->
  (forall d, ed E' d = ed E d) -> env_agree_pd cawf_P PT E E'.
Proof.
intros E E' Hlo H32 Hd. split; [|intros d _; exact (Hd d)].
intros n Hn. unfold cawf_P in Hn. apply andb_prop in Hn as [Hn H31]. apply andb_prop in Hn as [H1 H30].
apply Nat.ltb_lt in H1. apply negb_true_iff, Nat.eqb_neq in H30. apply negb_true_iff, Nat.eqb_neq in H31.
destruct (Nat.lt_ge_cases n 30) as [Hl|Hg]; [apply Hlo; exact Hl|].
assert (n = 32)%nat as -> by lia. exact H32.
Qed.
(* the env of the empty-text hand-over caw_ss810: atom 30 = ~six (a3), 31 = ra, 32 kept, 33 .. 50 from the machine's
   registers as caw_regs810 names them; 38 = m = 0, which no register of caw_ss810 names (the arm sets a4 := 0 at
   0x81814 and the empty-text lemma asks ew E 38 = 0) *)
Definition cawf_env810 (E : env) (regs : bvmap 5 word) : env :=
  havoc E 30 [YK11.getr regs 13; YK11.getr regs 1; ew E 32; YK11.getr regs 10; YK11.getr regs 18;
              YK11.getr regs 5; YK11.getr regs 6; YK11.getr regs 7; Z_to_bv 64 0;
              YK11.getr regs 11; YK11.getr regs 12; YK11.getr regs 14; YK11.getr regs 15; YK11.getr regs 16;
              YK11.getr regs 17; YK11.getr regs 19; YK11.getr regs 21; YK11.getr regs 28; YK11.getr regs 29;
              YK11.getr regs 30; YK11.getr regs 31].
Lemma cawf_env810_old : forall E regs n, (n < 30)%nat -> ew (cawf_env810 E regs) n = ew E n.
Proof. intros E regs n Hn. apply ew_havoc_old. exact Hn. Qed.
Lemma cawf_agree810 : forall E regs, env_agree_pd cawf_P PT E (cawf_env810 E regs).
Proof. intros E regs. apply cawf_P_agree; [apply cawf_env810_old | reflexivity | intros d; reflexivity]. Qed.
Lemma cawf_obl810 : forall E regs,
  Forall (fun rj : bv 5 * nat => ew (cawf_env810 E regs) (snd rj) = YK11.getr regs (fst rj))
    (reabs_obl cawf_P caw_regs810).
Proof.
intros E regs.
match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
repeat constructor.
Qed.
Lemma cawf_810_ok : forall E ss ms (W : world tfibsegs) i sp0 six want,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = 0x81810 ->
  reabs_check cawf_P ss caw_regs810 caw_facts810 = true ->
  nth_error (ss_mem ss) i = Some caw_stk -> bv_unsigned (ew E 2) = sp0 ->
  bv_unsigned (YK11.getr (ms_regs ms) 10) = six -> bv_unsigned (YK11.getr (ms_regs ms) 18) = want ->
  bv_unsigned (YK11.getr (ms_regs ms) 13) = 2 ^ 64 - 1 - six ->
  4096 <= six <= CAW_CEIL -> 4096 <= want <= CAW_CEIL ->
  st_ok tfibsegs (cawf_env810 E (ms_regs ms)) caw_ss810 (restrict (w_H W) ms).
Proof.
intros E ss ms W i sp0 six want HS Hpc Hck Hstk E2 R10 R18 R13 Hsix Hwant.
set (E' := cawf_env810 E (ms_regs ms)).
assert (E30' : bv_unsigned (ew E' 30) = 2 ^ 64 - 1 - six) by exact R13.
assert (E33' : bv_unsigned (ew E' 33) = six) by exact R10.
assert (E34' : bv_unsigned (ew E' 34) = want) by exact R18.
assert (HM' : mem_ok tfibsegs E' (ms_mem (restrict (w_H W) ms)) [caw_stk]).
{ cbn [ms_mem restrict]. split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  pose proof (fsw_region_nth E ss (restrict (w_H W) ms) i caw_stk HS Hstk) as R0. cbn [ms_mem restrict] in R0.
  exact (region_ok_agree tfibsegs 30 E E' _ caw_stk (env_agree_havoc E 30 _) ltac:(vm_compute; reflexivity) R0). }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E' (fst nf) (snd nf)) (fact_obls cawf_P caw_facts810)).
{ cawf_obls_tac ltac:(rewrite ?E30', ?E33', ?E34'; unfold CAW_NLO, CAW_NHI, CAW_CEIL in *; lia). }
pose proof (st_ok_reabs tfibsegs cawf_P E E' ss (restrict (w_H W) ms) caw_regs810 [caw_stk]
  caw_facts810 HS (cawf_agree810 _ _) Hck (cawf_obl810 _ _) HFO HM') as HS'.
rewrite Hpc in HS'. exact HS'.
Qed.
(* the env of the loop hand-over: atom 30 = ~six (a3), 31 = ra, 32 kept, 33 .. 44 as caw_regs1 names them (40 = six +
   0, 41 = the text's second byte) *)
Definition cawf_envH (E : env) (regs : bvmap 5 word) (v40 v41 : word) : env :=
  havoc E 30 [YK11.getr regs 13; YK11.getr regs 1; ew E 32; YK11.getr regs 10; YK11.getr regs 18;
              YK11.getr regs 19; YK11.getr regs 11; YK11.getr regs 12; YK11.getr regs 14; YK11.getr regs 28;
              v40; v41; YK11.getr regs 29; YK11.getr regs 30; YK11.getr regs 31].
Lemma cawf_envH_old : forall E regs v40 v41 n, (n < 30)%nat -> ew (cawf_envH E regs v40 v41) n = ew E n.
Proof. intros E regs v40 v41 n Hn. apply ew_havoc_old. exact Hn. Qed.
Lemma cawf_agreeH : forall E regs v40 v41, env_agree_pd cawf_P PT E (cawf_envH E regs v40 v41).
Proof. intros E regs v40 v41. apply cawf_P_agree; [apply cawf_envH_old | reflexivity | intros d; reflexivity]. Qed.
Lemma cawf_oblH : forall E regs v40 v41,
  Forall (fun rj : bv 5 * nat => ew (cawf_envH E regs v40 v41) (snd rj) = YK11.getr regs (fst rj))
    (reabs_obl cawf_P caw_regs1).
Proof.
intros E regs v40 v41.
match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end.
repeat constructor.
Qed.
Definition cawf_factsH : facts := mkFacts (f_atoms (caw_facts1 1 255)) [] [].
Lemma cawf_head_ok : forall E ss ms (W : world tfibsegs) i sp0 six want t c0 c1,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = 0x8170c ->
  reabs_check cawf_P ss caw_regs1 cawf_factsH = true ->
  nth_error (ss_mem ss) i = Some caw_stk -> bv_unsigned (ew E 2) = sp0 ->
  bv_unsigned (YK11.getr (ms_regs ms) 10) = six -> bv_unsigned (YK11.getr (ms_regs ms) 18) = want ->
  bv_unsigned (YK11.getr (ms_regs ms) 19) = t -> bv_unsigned (YK11.getr (ms_regs ms) 11) = t + 1 ->
  bv_unsigned (YK11.getr (ms_regs ms) 12) = c0 -> bv_unsigned (YK11.getr (ms_regs ms) 13) = 2 ^ 64 - 1 - six ->
  bv_unsigned (YK11.getr (ms_regs ms) 14) = 0 -> bv_unsigned (YK11.getr (ms_regs ms) 28) = 0 ->
  4096 <= six <= CAW_CEIL -> 4096 <= want <= CAW_CEIL -> 4096 <= t -> t + 2 <= CAW_CEIL ->
  1 <= c0 <= 255 -> 0 <= c1 <= 255 ->
  t + 2 <= sp0 - 64 -> six + 1 <= sp0 - 64 -> (t + 2 <= six \/ six + 1 <= t + 1) ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (t + 1) 1 c1 ->
  writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) six ->
  st_ok tfibsegs (cawf_envH E (ms_regs ms) (Z_to_bv 64 six) (Z_to_bv 64 c1)) (caw_ss1 1 255) (restrict (w_H W) ms).
Proof.
intros E ss ms W i sp0 six want t c0 c1 HS Hpc Hck Hstk E2 R10 R18 R19 R11 R12 R13 R14 R28 Hsix Hwant Ht Ht2 Hc0 Hc1
  Hsp1 Hsp2 Hts Hv1 Hw6.
unfold CAW_CEIL in *.
set (E' := cawf_envH E (ms_regs ms) (Z_to_bv 64 six) (Z_to_bv 64 c1)).
assert (E2' : bv_unsigned (ew E' 2) = sp0) by (unfold E'; rewrite cawf_envH_old by lia; exact E2).
assert (E30' : bv_unsigned (ew E' 30) = 2 ^ 64 - 1 - six) by exact R13.
assert (E33' : bv_unsigned (ew E' 33) = six) by exact R10.
assert (E34' : bv_unsigned (ew E' 34) = want) by exact R18.
assert (E35' : bv_unsigned (ew E' 35) = t) by exact R19.
assert (E36' : bv_unsigned (ew E' 36) = t + 1) by exact R11.
assert (E37' : bv_unsigned (ew E' 37) = c0) by exact R12.
assert (E38' : bv_unsigned (ew E' 38) = 0) by exact R14.
assert (E39' : bv_unsigned (ew E' 39) = 0) by exact R28.
assert (E40' : bv_unsigned (ew E' 40) = six) by (apply unsigned_lit_small; lia).
assert (E41' : bv_unsigned (ew E' 41) = c1) by (apply unsigned_lit_small; lia).
assert (HM' : mem_ok tfibsegs E' (ms_mem (restrict (w_H W) ms)) caw_mem1).
{ cbn [ms_mem restrict]. split; [vm_compute; reflexivity|]. split.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + pose proof (fsw_region_nth E ss (restrict (w_H W) ms) i caw_stk HS Hstk) as R0. cbn [ms_mem restrict] in R0.
      exact (region_ok_agree tfibsegs 30 E E' _ caw_stk (env_agree_havoc E 30 _) ltac:(vm_compute; reflexivity) R0).
    + unfold region_ok, caw_txt1. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E35'. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val tfibsegs E' _ _ 1 1%N (SOff 41 0) c1); [apply cawf_den0; exact E41' | cbn; lia | cbn; lia |].
      exact Hv1.
    + unfold region_ok, caw_six1. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E40'. split; [lia|]. split; [lia|].
      split; [intros o Ho; replace (six + o) with six by lia; exact Hw6 | constructor].
  - unfold caw_mem1, caw_stk, caw_txt1, caw_six1. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2', E35', E40'. repeat split; lia. }
assert (HFO : Forall (fun nf : nat * afact => afact_ok E' (fst nf) (snd nf)) (fact_obls cawf_P cawf_factsH)).
{ cawf_obls_tac ltac:(rewrite ?E30', ?E33', ?E34', ?E35', ?E36', ?E37', ?E38', ?E39', ?E40', ?E41';
    unfold CAW_NLO, CAW_NHI in *; lia). }
pose proof (st_ok_reabs tfibsegs cawf_P E E' ss (restrict (w_H W) ms) caw_regs1 caw_mem1 cawf_factsH
  HS (cawf_agreeH _ _ _ _) Hck (cawf_oblH _ _ _ _) HFO HM') as HS'.
rewrite Hpc in HS'.
pose proof HS' as (_ & _ & _ & _ & _ & _ & _ & _ & HF').
assert (HF : facts_ok E' (caw_facts1 1 255)).
{ split; [exact (proj1 HF')|]. split; [exact I|]. cbn [caw_facts1 f_alias alias_ok]. split; [|exact I].
  cbn [sv_denot]. rewrite E33', E38', E40'. rewrite !Z.add_0_r.
  transitivity (Z_to_bv 64 (six + 0)); [apply alu_add_small; unfold M64; lia | rewrite Z.add_0_r; reflexivity]. }
exact (st_ok_facts tfibsegs E' _ _ (caw_facts1 1 255) HS' HF).
Qed.

(* ~six: `not a3, a0` at 0x816d4 is `xori a3, a0, -1`, which the engine keeps as SAlu ALU_XOR a0 (SLit -1) *)
Lemma cawf_not_val : forall E n v z, bv_unsigned (ew E n) = v -> zcanon z = 2 ^ 64 - 1 ->
  bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit z))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v z H Hz. pose proof (u64_range (ew E n)) as Hr. rewrite H in Hr.
change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit z)))) with (U E (SAlu ALU_XOR (SOff n 0) (SLit z))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cawf_U0 E n v H), U_SLit, Hz.
rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma cawf_not_val' : forall E n v z, bv_unsigned (ew E n) = v -> zcanon z = 2 ^ 64 - 1 ->
  bv_unsigned (sv_denot E (SAlu ALU_XOR (SLit z) (SOff n 0))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v z H Hz. pose proof (u64_range (ew E n)) as Hr. rewrite H in Hr.
change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SLit z) (SOff n 0)))) with (U E (SAlu ALU_XOR (SLit z) (SOff n 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (cawf_U0 E n v H), U_SLit, Hz, Z.lxor_comm.
rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Ltac cawf_not_tac Ev :=
  first [ apply (cawf_not_val _ _ _ _ Ev); reflexivity | apply (cawf_not_val' _ _ _ _ Ev); reflexivity ].

(* the byte test of 0x816d8 (`beqz a2`, a2 the zero-extended byte at t, loaded at 0x816d0) *)
Lemma cawf_byte_branch : forall E c, ew E 97 = Z_to_bv 64 c -> 0 <= c < 256 ->
  branch_taken BC_EQ (sv_denot E (SExt false 8 (SOff 97 0))) (sv_denot E (SLit 0)) = (c =? 0).
Proof.
intros E c H Hc. rewrite branch_eq_U, U_SExt, (U_atom E 97 c H ltac:(lia)), U_lit by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma cawf_byte_val : forall E c, ew E 97 = Z_to_bv 64 c -> 0 <= c < 256 ->
  bv_unsigned (sv_denot E (SExt false 8 (SOff 97 0))) = c.
Proof.
intros E c H Hc. change (bv_unsigned (sv_denot E (SExt false 8 (SOff 97 0)))) with (U E (SExt false 8 (SOff 97 0))).
rewrite U_SExt, (U_atom E 97 c H ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.
(* the text is empty exactly when its first byte is the NUL *)
Lemma cawf_c0_nil : forall tb : list Z, Forall (fun c => c <> 0) tb -> nth 0 (tb ++ [0]) 0 = 0 -> tb = [].
Proof. intros [|c tb] H E; [reflexivity|]. cbn in E. inversion H as [|? ? Hc _]; subst. contradiction. Qed.
Lemma cawf_c0_cons : forall tb : list Z, nth 0 (tb ++ [0]) 0 <> 0 -> (0 < length tb)%nat.
Proof. intros [|x tb] H; [exfalso; apply H; reflexivity | cbn; apply Nat.lt_0_succ]. Qed.
(* a register's value read off a run's state: the register's symbolic value, computed *)
Ltac cawf_regU HS rr :=
  lazymatch type of HS with st_ok _ ?E _ (restrict _ ?ms) =>
    rewrite (cawf_reg_sv E _ _ ms HS rr);
    lazymatch goal with |- context [sr_get ?l rr] =>
      let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end
  end.

(* a register rr the state holds as the entry atom nn < 33 (the entry register re) reads the entry register's value
   (Ev: the env agrees with the entry env there) *)
Ltac cawf_entry_reg Ev HS rr nn re Hval :=
  lazymatch type of HS with st_ok _ ?E _ (restrict _ ?ms) =>
    rewrite (cawf_reg_sv E _ _ ms HS rr);
    lazymatch goal with |- context [sr_get ?l rr] =>
      let v := eval vm_compute in (sr_get l rr) in change (sr_get l rr) with v end;
    rewrite fsw_SOff0, (Ev nn re ltac:(lia) eq_refl); exact Hval
  end.

(* ---- THE FRONT ---- *)
Theorem caw_front : forall ly S U W regs mem md ch t bd l (tb : list Z) live peak cnt fail
    (Q : world tfibsegs -> config -> Prop),
  fpreU tfibsegs B STK_check_as_written ly S U W regs mem md ch -> fs_heads B ly S U ->
  YK11.getr regs 10 = w64 t -> YK11.getr regs 11 = w64 bd -> YK11.getr regs 12 = w64 l ->
  cstr_ok tfibsegs W mem t tb -> cstr_kept B ly S U t tb ->
  Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  caw_answerA tfibsegs B ly S U W mem tb bd l ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + EV_check_as_written <= EV_MAX -> blocks_bytes S + LIVE_check_as_written <= LIVE_MAX ->
  (* (1) the text is not empty: the scan loop head 0x8170c, in caw_ss1 1 255 at j = 0, sx = [], pad = 0 *)
  (forall W2 ly2 S2 E' ms' mdc' want six,
     cawf_post ly S U W regs mem md t tb live peak cnt fail W2 ly2 S2 want six ms' mdc' ->
     (0 < length tb)%nat ->
     st_ok tfibsegs E' (caw_ss1 1 255) (restrict (w_H W2) ms') ->
     caw_atoms t tb six (spZ regs) E' 0 0 0 ->
     ew E' 30 = Z_to_bv 64 (2 ^ 64 - 1 - six) ->
     ew E' 34 = Z_to_bv 64 want -> ew E' 11 = YK11.getr regs 11 -> ew E' 12 = YK11.getr regs 12 ->
     (forall n, (n < 30)%nat -> ew E' n = YK11.getr regs (Z_to_bv 5 (Z.of_nat n))) ->
     ew E' 31 = YK11.getr (ms_regs ms') 1 -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
     caw_static B STK_check_as_written (spZ regs) [] ly S [] ly2 S2 t tb six (cawf_six_size tb) (spZ regs) ->
     caw_six W2 six (ms_mem ms') [] ->
     SRr tfibsegs W2 (mkCfg ms' mdc') Q) ->
  (* (2) the text is empty: the hand-over 0x81810 (FSW_caw_defs caw_ss810) *)
  (forall W2 ly2 S2 E' ms' mdc' want six,
     cawf_post ly S U W regs mem md t tb live peak cnt fail W2 ly2 S2 want six ms' mdc' ->
     tb = [] ->
     st_ok tfibsegs E' caw_ss810 (restrict (w_H W2) ms') ->
     ew E' 2 = Z_to_bv 64 (spZ regs) -> ew E' 30 = Z_to_bv 64 (2 ^ 64 - 1 - six) ->
     ew E' 33 = Z_to_bv 64 six -> ew E' 34 = Z_to_bv 64 want -> ew E' 38 = Z_to_bv 64 0 ->
     ew E' 11 = YK11.getr regs 11 -> ew E' 12 = YK11.getr regs 12 ->
     (forall n, (n < 30)%nat -> ew E' n = YK11.getr regs (Z_to_bv 5 (Z.of_nat n))) ->
     ew E' 31 = YK11.getr (ms_regs ms') 1 -> ew E' 32 = Z_to_bv 64 SHADOW_OFF ->
     SRr tfibsegs W2 (mkCfg ms' mdc') Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_check_as_written regs mem md) Q.
Proof.
intros ly S U W regs mem md ch t bd l tb live peak cnt fail Q HPRE FH H10 H11 H12 Hc Hk Hlen HANS HG Hev Hlv KLOOP K810.
pose proof HPRE as (HAPU & HRO).
pose proof HAPU as (HAP & OK & PO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_ARU B STK_check_as_written ly S U W regs mem md ch HAPU) as HARU.
pose proof HARU as HARUe.
pose proof (fsw_sp B STK_check_as_written ly S U W regs mem md ch HAPU) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hc as (Hcstr & Ht4096 & Htceil & Htlen32 & Htamem & Htra & Hthull & Htword).
assert (Hlen3 : Z.of_nat (length tb) <= 3145728) by (unfold PRESET_FILE_MAX_BYTES in Hlen; lia).
assert (FS : STK_check_as_written = 64 + 16384) by reflexivity.
assert (FR : STK_RT_STR = 8192) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
(* ---- the entry state and the run to the first strlen call ---- *)
pose proof (fsw_entryT B STK_check_as_written 64 ly S U W regs mem md ch A_check_as_written
  (proj1 SYMS) (proj2 SYMS) HAPU ltac:(lia)
  ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_init tfibsegs B STK_check_as_written [] ly S W regs (unpoison U mem) md ch HAP) as HJ.
set (E0 := Ereg regs fs_extraT) in HS.
assert (E2a : bv_unsigned (ew E0 2) = spZ regs)
  by (subst E0; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_check_as_written) with (Z_to_bv 64 A_check_as_written).
fsw_aj_run_toU caw_tbl_ok HS HJ HARU PC_strlen.
{ unfold fss0T, fsT_regions; cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E2a | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* ---- the first strlen call at 0x81688 ---- *)
assert (SB1 : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx. apply HF. rewrite (wz x ltac:(lia)). intros (r & Hin & Hr).
  unfold fss0T, fsT_regions, fstk, fs_got_region, fs_bcell_region in Hin. cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<-|Hin]); try destruct Hin;
    cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?E2a in Hr; lia. }
pose proof (fsw_reg_lit _ E0 _ ms 1%bv RA_CAWF_STRLEN1 HS ltac:(vm_compute; reflexivity)
  ltac:(unfold RA_CAWF_STRLEN1; lia)) as R1.
pose proof (fsw_reg_off _ E0 _ ms 2%bv 2 (-64) (spZ regs) HS ltac:(vm_compute; reflexivity) E2a ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 64) by (unfold spZ at 1; rewrite R2; lia).
assert (Hraok : YK0s.ret_ok (YK11.getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_CAWF_STRLEN1; lia); reflexivity).
assert (HcT : cstr_ok tfibsegs W (ms_mem ms) t tb) by exact (cstr_ok_below W mem (ms_mem ms) t tb SB1 Hc).
assert (HROT : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms)))
  by exact (arodata_below B W mem (ms_mem ms) SB1 HRO).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E0 _ ms HS eq_refl) as Hms. cbn [ss_pc] in Hms.
rewrite Hms. change (Z_to_bv 64 272068) with (w64 PC_strlen).
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly S U W (ms_mem ms)
    _ 0 U (fun a => spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) (YK11.getr (ms_regs ms) 1)
    (cfg_at tfibsegs PC_strlen (ms_regs ms) (ms_mem ms) _)
    (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
       (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ v = Z.of_nat (length tb)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)) HJ).
  - eapply SRr_mono.
    + apply (RTs ly S U W (ms_regs ms) (ms_mem ms) _ t tb).
      * exact (cawf_ecall_pre ly S U W mem md ly S W (ms_regs ms) (ms_mem ms) _ 0 (spZ regs) HARU HJ Hspc Hraok
          ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp)).
      * exact (cawf_rom_view ly S U W (ms_mem ms) _ IMG HARU HROT).
      * rewrite R10. exact H10.
      * exact HcT.
    + intros W' c' _ Hpost. exact (cawf_rt_ro_to_aru STK_RT_STR ly S U W (ms_regs ms) (ms_mem ms) _ _ W' c' OK Hpost).
  - intros a Ha. rewrite Hspc in Ha. left. left. lia. }
intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & HARU1 & (HP1 & (v1 & H101 & Hv1 & Ev1) & Hfr1)).
(* ---- the state resumed at 0x8168c: the callee-saved registers keep their symbolic values, the caller-saved ones
   get the fresh atoms 33 .. 48 (atom 33 = a0 = |tb|) ---- *)
rewrite R1.
assert (Usp1 : spZ regs1 = spZ regs - 64).
{ unfold spZ at 1.
  rewrite (fsw_pres (ms_regs ms) regs1 2%bv HP1 ltac:(unfold acallee_saved; vm_compute; lia)). exact Hspc. }
assert (Hkeep1 : forall a, spZ regs - 64 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W) mem1) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr1; [lia | rewrite Hspc; lia]. }
assert (HM1 : mem_ok tfibsegs E0 (mrestrict (w_H W) mem1) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  apply (cawf_frame_ok STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly S U W (ms_mem ms) mem1 md1 0
    E0 HJ1 HARU1 E2a ltac:(lia)
    (cawf_frame_chunks E0 _ ms (w_H W) (spZ regs) HS ltac:(vm_compute; reflexivity) E2a) Hkeep1). }
rewrite Hms, restrict_mkst_fx in HS.
pose proof (st_ok_splice_havoc tfibsegs 33%nat E0 _ (ms_regs ms) regs1 (Z_to_bv 64 272068) RA_CAWF_STRLEN1
  (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem1) [caw_stk] [] CAWF_CLOB HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(intros r Hr; apply (cawf_kept_clob (ms_regs ms) regs1 r HP1); cbn in Hr; exact Hr)
  (Forall_nil _) HM1) as HS1.
set (E1 := havoc E0 33 (map (YK11.getr regs1) CAWF_CLOB)) in HS1.
assert (E1_33 : ew E1 33 = Z_to_bv 64 (Z.of_nat (length tb))).
{ subst E1.
  pose proof (ew_havoc_new E0 33 (map (YK11.getr regs1) CAWF_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as HX.
  cbn [Nat.add] in HX. rewrite HX. cbn [CAWF_CLOB map nth]. rewrite H101, Ev1. reflexivity. }
assert (E1_old : forall n, (n < 33)%nat -> ew E1 n = ew E0 n) by (intros n Hn; subst E1; apply ew_havoc_old; lia).
assert (E1_2 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (E1_old 2%nat ltac:(lia)); exact E2a).
pose proof (cawf_add_atom E1 _ _ 33%nat (mkAF 0 3145728 0) HS1
  (cawf_afact E1 33 (Z.of_nat (length tb)) 0 3145728 E1_33 ltac:(lia) ltac:(lia))) as HS1f.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1f.
rewrite <- restrict_mkst_fx in HS1f.
clear HS HM1 Hkeep1.
fsw_aj_run_toU caw_tbl_ok HS1f HJ1 HARU1 PC_malloc.
{ cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E1_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
(* ---- the malloc of want at 0x8169c ---- *)
assert (E1v : forall (n : nat) (r : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned r ->
  ew E1 n = YK11.getr regs r).
{ intros n r Hn Hr. rewrite (E1_old n Hn). subst E0. exact (ew_Ereg_nat regs fs_extraT n r Hr). }
pose proof (fsw_reg_lit _ E1 _ ms0 1%bv RA_CAWF_MALLOC1 HS1f ltac:(vm_compute; reflexivity)
  ltac:(unfold RA_CAWF_MALLOC1; lia)) as R1M.
pose proof (fsw_reg_off _ E1 _ ms0 2%bv 2 (-64) (spZ regs) HS1f ltac:(vm_compute; reflexivity) E1_2 ltac:(lia)) as R2M.
assert (R3M : YK11.getr (ms_regs ms0) 3 = w64 (as_gp B)).
{ rewrite (cawf_reg_sv E1 _ (w_H W) ms0 HS1f 3%bv).
  lazymatch goal with |- context [sr_get ?l 3%bv] =>
    let v := eval vm_compute in (sr_get l 3%bv) in change (sr_get l 3%bv) with v end.
  rewrite fsw_SOff0, (E1v 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp. }
assert (R4M : YK11.getr (ms_regs ms0) 4 = w64 (as_tp B)).
{ rewrite (cawf_reg_sv E1 _ (w_H W) ms0 HS1f 4%bv).
  lazymatch goal with |- context [sr_get ?l 4%bv] =>
    let v := eval vm_compute in (sr_get l 4%bv) in change (sr_get l 4%bv) with v end.
  rewrite fsw_SOff0, (E1v 4%nat 4%bv ltac:(lia) eq_refl). exact Htp. }
assert (R8M : YK11.getr (ms_regs ms0) 8 = w64 l).
{ rewrite (cawf_reg_sv E1 _ (w_H W) ms0 HS1f 8%bv).
  lazymatch goal with |- context [sr_get ?l 8%bv] =>
    let v := eval vm_compute in (sr_get l 8%bv) in change (sr_get l 8%bv) with v end.
  rewrite fsw_SOff0, (E1v 12%nat 12%bv ltac:(lia) eq_refl). exact H12. }
assert (R10M : YK11.getr (ms_regs ms0) 10 = w64 (cawf_want_size tb)).
{ unfold w64, cawf_want_size. rewrite (cawf_reg_sv E1 _ (w_H W) ms0 HS1f 10%bv).
  lazymatch goal with |- context [sr_get ?l 10%bv] =>
    let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v end.
  rewrite denot_lit_U. f_equal. rewrite ?U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E1 33 (Z.of_nat (length tb)) E1_33 ltac:(lia)), !U_lit by lia.
  change (Z.land 2 63) with 2. change (Z.land 1 63) with 1.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
  assert (Hq : 0 <= Z.of_nat (length tb) / 4 <= 786432) by (Z.div_mod_to_equations; lia).
  rewrite (zcanon_id (Z.of_nat (length tb) / 4)) by (unfold M64; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (zcanon_id (Z.of_nat (length tb) / 4 * 2)) by (unfold M64; lia).
  rewrite (zcanon_id (Z.of_nat (length tb) / 4 * 2 + Z.of_nat (length tb) / 4)) by (unfold M64; lia).
  rewrite (zcanon_id (Z.of_nat (length tb) / 4 * 2 + Z.of_nat (length tb) / 4 + 3)) by (unfold M64; lia).
  unfold b64_alloc_bound. lia. }
(* the decoder's answer bounds the frame-chain head s0 = l: either l is SIZE_MAX (odd, so the chain is empty) or it
   is a reader block's length, below alloc_ceiling *)
assert (Hl8 : bv_unsigned (YK11.getr (ms_regs ms0) 8) < alloc_ceiling \/
              bv_unsigned (YK11.getr (ms_regs ms0) 8) mod 8 <> 0).
{ rewrite R8M. unfold w64.
  destruct HANS as [(_ & _ & ->) | (bs & m & _ & _ & El & _ & Hrb & Hlm & _)].
  - right. rewrite unsigned_lit_small by (unfold SIZE_MAXZ; lia). unfold SIZE_MAXZ. vm_compute. discriminate.
  - left. destruct Hrb as (Hin & _ & Hm0 & _).
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (bd - HEAD) (m + HEAD) HAR Hin)
      as (_ & H4096b & Hcl & _).
    assert (Hreq : req_size (m + HEAD) = m + HEAD)
      by (unfold req_size; destruct (Z.eqb_spec (m + HEAD) 0); [unfold HEAD in *; lia | reflexivity]).
    rewrite Hreq in Hcl. rewrite unsigned_lit_small; unfold HEAD in *; lia. }
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms0 HS1f eq_refl) as Hms0. cbn [ss_pc] in Hms0.
pose proof RTm as [HMPC AMALLOC].
rewrite Hms0. change (Z_to_bv 64 340196) with (w64 PC_malloc). rewrite <- HMPC.
eapply SRr_bind.
{ apply (fsw_aj_malloc04U B FS_ENV ML AMALLOC W (ms_regs ms0) (ms_mem ms0) STK_check_as_written (spZ regs) []
    ly S W mem md [] ly S U _ 0 (cawf_want_size tb) (-64) (Z_to_bv 64 RA_CAWF_MALLOC1) [] HJ1 HARU1).
  - exact R10M.
  - unfold MALLOC_MAX, cawf_want_size, b64_alloc_bound. Z.div_mod_to_equations. lia.
  - unfold LIVE_check_as_written in Hlv. unfold cawf_want_size, b64_alloc_bound.
    Z.div_mod_to_equations. lia.
  - unfold spZ at 1. rewrite R2M. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - exact R3M.
  - exact R4M.
  - exact R1M.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold RA_CAWF_MALLOC1; lia). reflexivity.
  - unfold EV_check_as_written in Hev. lia.
  - apply (achain_chain_pre ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms0))) (spZ (ms_regs ms0))
      (s0Z (ms_regs ms0)) [] (ms_regs ms0)).
    + left. split; [|reflexivity]. unfold s0Z.
      destruct Hl8 as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
    + unfold spZ at 1. rewrite R2M. lia.
    + reflexivity.
    + unfold raZ. rewrite R1M, unsigned_lit_small by (unfold RA_CAWF_MALLOC1; lia).
      unfold RA_CAWF_MALLOC1. lia. }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & want & -> & HARU2 & HJ2 & HP2 & H10w & Hfr2 & Hw4096 & Hab2 & HK2).
(* ---- the state resumed at 0x816a0: fresh atoms 49 .. 64 for the caller-saved registers (49 = a0 = want) ---- *)
assert (Hkeep2 : forall a, spZ regs - 64 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a)
  by exact (cawf_keep_frame ly S U W (ms_mem ms0) _ ly2 S2 W2 mem2 md2 (spZ regs) _ _ HARU1 HARU2 (proj1 HK2)
    ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof (cawf_frame_chunks E1 _ ms0 (w_H W) (spZ regs) HS1f ltac:(vm_compute; reflexivity) E1_2) as Hcs2.
assert (HM2 : mem_ok tfibsegs E1 (mrestrict (w_H W2) mem2) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  exact (cawf_frame_ok STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 mem2 mem2 md2
    (0 + 1) E1 HJ2 HARU2 E1_2 ltac:(lia) (cawf_chunks_move E1 _ _ (spZ regs) Hcs2 Hkeep2) (fun _ _ => eq_refl)). }
rewrite Hms0, restrict_mkst_fx in HS1f.
pose proof (st_ok_splice_havoc tfibsegs 49%nat E1 _ (ms_regs ms0) regs2 _ RA_CAWF_MALLOC1
  _ (mrestrict (w_H W2) mem2) [caw_stk] [] CAWF_CLOB HS1f
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(intros r Hr; apply (cawf_kept_clob (ms_regs ms0) regs2 r HP2); cbn in Hr; exact Hr)
  (Forall_nil _) HM2) as HS2.
set (E2 := havoc E1 49 (map (YK11.getr regs2) CAWF_CLOB)) in HS2.
assert (E2_49 : ew E2 49 = Z_to_bv 64 want).
{ subst E2. pose proof (ew_havoc_new E1 49 (map (YK11.getr regs2) CAWF_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as HX.
  cbn [Nat.add] in HX. rewrite HX. cbn [CAWF_CLOB map nth]. exact H10w. }
assert (E2_old : forall n, (n < 49)%nat -> ew E2 n = ew E1 n) by (intros n Hn; subst E2; apply ew_havoc_old; lia).
assert (E2_2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite (E2_old 2%nat ltac:(lia)); exact E1_2).
assert (E2v : forall (n : nat) (r : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs r)
  by (intros n r Hn Hr; rewrite (E2_old n ltac:(lia)); exact (E1v n r Hn Hr)).
assert (Hwin2 : In (want, cawf_want_size tb) (ablocks B ly2 S2))
  by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 want (cawf_want_size tb) (proj1 HARU2) Hwin2)
  as (_ & _ & Hwceil & _ & _ & _ & Hwn).
pose proof (req_size_pos (cawf_want_size tb) ltac:(lia)) as (Rw1 & Rw2).
pose proof (cawf_add_atom E2 _ _ 49%nat (mkAF 4096 CAW_CEIL 0) HS2
  (cawf_afact E2 49 want 4096 CAW_CEIL E2_49 ltac:(lia) ltac:(unfold CAW_CEIL; lia))) as HS2f.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2f.
rewrite <- restrict_mkst_fx in HS2f.
clear HS2 HM2 Hkeep2 Hcs2.
fsw_aj_run_toU caw_tbl_ok HS2f HJ2 HARU2 PC_strlen.
{ cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E2_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msS2 end.
(* ---- the second strlen call at 0x816ac ---- *)
pose proof (fsw_reg_lit _ E2 _ msS2 1%bv RA_CAWF_STRLEN2 HS2f ltac:(vm_compute; reflexivity)
  ltac:(unfold RA_CAWF_STRLEN2; lia)) as R1S.
pose proof (fsw_reg_off _ E2 _ msS2 2%bv 2 (-64) (spZ regs) HS2f ltac:(vm_compute; reflexivity) E2_2 ltac:(lia)) as R2S.
assert (HspcS : spZ (ms_regs msS2) = spZ regs - 64) by (unfold spZ at 1; rewrite R2S; lia).
assert (RAokS : YK0s.ret_ok (YK11.getr (ms_regs msS2) 1))
  by (rewrite R1S; apply ret_ok_even; rewrite unsigned_lit_small by (unfold RA_CAWF_STRLEN2; lia); reflexivity).
assert (R3S : YK11.getr (ms_regs msS2) 3 = w64 (as_gp B))
  by cawf_entry_reg E2v HS2f (3%bv : bv 5) 3%nat (3%bv : bv 5) Hgp.
assert (R4S : YK11.getr (ms_regs msS2) 4 = w64 (as_tp B))
  by cawf_entry_reg E2v HS2f (4%bv : bv 5) 4%nat (4%bv : bv 5) Htp.
assert (R10S : YK11.getr (ms_regs msS2) 10 = w64 t)
  by cawf_entry_reg E2v HS2f (10%bv : bv 5) 10%nat (10%bv : bv 5) H10.
assert (Hinc2 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hab2; apply in_or_app; left; exact Hx).
destruct (cawf_carry STK_check_as_written (spZ regs) ly S U W mem md ly2 S2 W2 (ms_mem msS2) _ (0 + 1) t tb
  live peak cnt fail HARUe HARU2 HJ2 Hinc2 HRO Hk Hc HG) as (HROS & HcS & _ & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E2 _ msS2 HS2f eq_refl) as HmsS2. cbn [ss_pc] in HmsS2.
rewrite HmsS2. change (Z_to_bv 64 272068) with (w64 PC_strlen).
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 (ms_mem msS2)
    _ (0 + 1) U (fun a => spZ (ms_regs msS2) - STK_RT_STR <= a < spZ (ms_regs msS2)) (YK11.getr (ms_regs msS2) 1)
    (cfg_at tfibsegs PC_strlen (ms_regs msS2) (ms_mem msS2) _)
    (fun regs' mem' md' => aregs_preserved (ms_regs msS2) regs' /\
       (exists v, YK11.getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ v = Z.of_nat (length tb)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs msS2) - STK_RT_STR <= a < spZ (ms_regs msS2)) ->
          aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) (ms_mem msS2) a)) HJ2).
  - eapply SRr_mono.
    + apply (RTs ly2 S2 U W2 (ms_regs msS2) (ms_mem msS2) _ t tb).
      * exact (cawf_ecall_pre ly S U W mem md ly2 S2 W2 (ms_regs msS2) (ms_mem msS2) _ (0 + 1) (spZ regs) HARU2 HJ2
          HspcS RAokS R3S R4S).
      * exact (cawf_rom_view ly2 S2 U W2 (ms_mem msS2) _ IMG HARU2 HROS).
      * exact R10S.
      * exact HcS.
    + intros W' c' _ Hpost.
      exact (cawf_rt_ro_to_aru STK_RT_STR ly2 S2 U W2 (ms_regs msS2) (ms_mem msS2) _ _ W' c' (proj1 (proj2 HARU2)) Hpost).
  - intros a Ha. rewrite HspcS in Ha. left. left. lia. }
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU3 & (HP3 & (v3 & H103 & Hv3 & Ev3) & Hfr3)).
rewrite R1S.
(* ---- the state resumed at 0x816b0: fresh atoms 65 .. 80 (65 = a0 = |tb|) ---- *)
assert (Hkeep3 : forall a, spZ regs - 64 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W2) mem3) a = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msS2)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr3; [lia | rewrite HspcS; lia]. }
pose proof (cawf_frame_chunks E2 _ msS2 (w_H W2) (spZ regs) HS2f ltac:(vm_compute; reflexivity) E2_2) as Hcs3.
assert (HM3 : mem_ok tfibsegs E2 (mrestrict (w_H W2) mem3) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  exact (cawf_frame_ok STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly2 S2 U W2 mem3 mem3 md3
    (0 + 1) E2 HJ3 HARU3 E2_2 ltac:(lia) (cawf_chunks_move E2 _ _ (spZ regs) Hcs3 Hkeep3) (fun _ _ => eq_refl)). }
rewrite HmsS2, restrict_mkst_fx in HS2f.
pose proof (st_ok_splice_havoc tfibsegs 65%nat E2 _ (ms_regs msS2) regs3 _ RA_CAWF_STRLEN2
  _ (mrestrict (w_H W2) mem3) [caw_stk] [] CAWF_CLOB HS2f
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(intros r Hr; apply (cawf_kept_clob (ms_regs msS2) regs3 r HP3); cbn in Hr; exact Hr)
  (Forall_nil _) HM3) as HS3.
set (E3 := havoc E2 65 (map (YK11.getr regs3) CAWF_CLOB)) in HS3.
assert (E3_65 : ew E3 65 = Z_to_bv 64 (Z.of_nat (length tb))).
{ subst E3. pose proof (ew_havoc_new E2 65 (map (YK11.getr regs3) CAWF_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as HX.
  cbn [Nat.add] in HX. rewrite HX. cbn [CAWF_CLOB map nth]. rewrite H103, Ev3. reflexivity. }
assert (E3_old : forall n, (n < 65)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; apply ew_havoc_old; lia).
assert (E3_2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite (E3_old 2%nat ltac:(lia)); exact E2_2).
assert (E3v : forall (n : nat) (r : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs r)
  by (intros n r Hn Hr; rewrite (E3_old n ltac:(lia)); exact (E2v n r Hn Hr)).
pose proof (cawf_add_atom E3 _ _ 65%nat (mkAF 0 3145728 0) HS3
  (cawf_afact E3 65 (Z.of_nat (length tb)) 0 3145728 E3_65 ltac:(lia) ltac:(lia))) as HS3f.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3f.
rewrite <- restrict_mkst_fx in HS3f.
clear HS3 HM3 Hkeep3 Hcs3.
fsw_aj_run_toU caw_tbl_ok HS3f HJ3 HARU3 PC_malloc.
{ cbn [ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E3_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msM2 end.
(* ---- the malloc of six at 0x816b8 ---- *)
pose proof (fsw_reg_lit _ E3 _ msM2 1%bv RA_CAWF_MALLOC2 HS3f ltac:(vm_compute; reflexivity)
  ltac:(unfold RA_CAWF_MALLOC2; lia)) as R1M2.
pose proof (fsw_reg_off _ E3 _ msM2 2%bv 2 (-64) (spZ regs) HS3f ltac:(vm_compute; reflexivity) E3_2 ltac:(lia)) as R2M2.
assert (R3M2 : YK11.getr (ms_regs msM2) 3 = w64 (as_gp B))
  by cawf_entry_reg E3v HS3f (3%bv : bv 5) 3%nat (3%bv : bv 5) Hgp.
assert (R4M2 : YK11.getr (ms_regs msM2) 4 = w64 (as_tp B))
  by cawf_entry_reg E3v HS3f (4%bv : bv 5) 4%nat (4%bv : bv 5) Htp.
assert (R8M2 : YK11.getr (ms_regs msM2) 8 = w64 l)
  by cawf_entry_reg E3v HS3f (8%bv : bv 5) 12%nat (12%bv : bv 5) H12.
assert (R10M2 : YK11.getr (ms_regs msM2) 10 = w64 (cawf_six_size tb)).
{ unfold w64, cawf_six_size. rewrite (cawf_reg_sv E3 _ (w_H W2) msM2 HS3f 10%bv).
  lazymatch goal with |- context [sr_get ?l 10%bv] =>
    let v := eval vm_compute in (sr_get l 10%bv) in change (sr_get l 10%bv) with v end.
  rewrite denot_lit_U. f_equal. rewrite ?U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E3 65 (Z.of_nat (length tb)) E3_65 ltac:(lia)), !U_lit by lia.
  destruct (Z.ltb_spec (Z.of_nat (length tb)) 1) as [Hlt|Hge].
  - rewrite (zcanon_id 1) by (unfold M64; lia).
    rewrite (zcanon_id (Z.of_nat (length tb) + 1)) by (unfold M64; lia). lia.
  - rewrite (zcanon_id 0) by (unfold M64; lia).
    rewrite (zcanon_id (Z.of_nat (length tb) + 0)) by (unfold M64; lia). lia. }
assert (Hl8b : bv_unsigned (YK11.getr (ms_regs msM2) 8) < alloc_ceiling \/
               bv_unsigned (YK11.getr (ms_regs msM2) 8) mod 8 <> 0) by (rewrite R8M2, <- R8M; exact Hl8).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E3 _ msM2 HS3f eq_refl) as HmsM2. cbn [ss_pc] in HmsM2.
rewrite HmsM2. change (Z_to_bv 64 340196) with (w64 PC_malloc). rewrite <- HMPC.
eapply SRr_bind.
{ apply (fsw_aj_malloc04U B FS_ENV ML AMALLOC W2 (ms_regs msM2) (ms_mem msM2) STK_check_as_written (spZ regs) []
    ly S W mem md [] ly2 S2 U _ (0 + 1) (cawf_six_size tb) (-64) (Z_to_bv 64 RA_CAWF_MALLOC2) [] HJ3 HARU3).
  - exact R10M2.
  - unfold MALLOC_MAX, cawf_six_size. lia.
  - rewrite (cawf_bb ly2 S2), Hab2, bsum_app, <- (cawf_bb ly S). cbn [bsum fold_right snd].
    unfold LIVE_check_as_written in Hlv. unfold cawf_want_size, cawf_six_size, b64_alloc_bound.
    Z.div_mod_to_equations. lia.
  - unfold spZ at 1. rewrite R2M2. lia.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - exact R3M2.
  - exact R4M2.
  - exact R1M2.
  - apply ret_ok_even. rewrite unsigned_lit_small by (unfold RA_CAWF_MALLOC2; lia). reflexivity.
  - unfold EV_check_as_written in Hev. lia.
  - apply (achain_chain_pre ly2 (aview tfibsegs (w_H W2) (unpoison U (ms_mem msM2))) (spZ (ms_regs msM2))
      (s0Z (ms_regs msM2)) [] (ms_regs msM2)).
    + left. split; [|reflexivity]. unfold s0Z.
      destruct Hl8b as [Hx|Hx]; [left; exact Hx | right; right; exact Hx].
    + unfold spZ at 1. rewrite R2M2. lia.
    + reflexivity.
    + unfold raZ. rewrite R1M2, unsigned_lit_small by (unfold RA_CAWF_MALLOC2; lia).
      unfold RA_CAWF_MALLOC2. lia. }
intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & six & -> & HARU4 & HJ4 & HP4 & H10s & Hfr4 & Hs4096 & Hab4 & HK4).
(* ---- the state resumed at 0x816bc: fresh atoms 81 .. 96 (81 = a0 = six, 82 = ra) ---- *)
assert (Hkeep4 : forall a, spZ regs - 64 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W4) mem4) a = mbyte tfibsegs (mrestrict (w_H W2) (ms_mem msM2)) a)
  by exact (cawf_keep_frame ly2 S2 U W2 (ms_mem msM2) _ ly4 S4 W4 mem4 md4 (spZ regs) _ _ HARU3 HARU4 (proj1 HK4)
    ltac:(lia) ltac:(lia) ltac:(lia)).
pose proof (cawf_frame_chunks E3 _ msM2 (w_H W2) (spZ regs) HS3f ltac:(vm_compute; reflexivity) E3_2) as Hcs4.
assert (HM4 : mem_ok tfibsegs E3 (mrestrict (w_H W4) mem4) [caw_stk]).
{ split; [vm_compute; reflexivity|]. split; [|cbn [pairwise_disjoint all_disjoint]; tauto].
  constructor; [|constructor].
  exact (cawf_frame_ok STK_check_as_written (spZ regs) [] ly S W (unpoison U mem) md [] ly4 S4 U W4 mem4 mem4 md4
    (0 + 1 + 1) E3 HJ4 HARU4 E3_2 ltac:(lia) (cawf_chunks_move E3 _ _ (spZ regs) Hcs4 Hkeep4) (fun _ _ => eq_refl)). }
rewrite HmsM2, restrict_mkst_fx in HS3f.
pose proof (st_ok_splice_havoc tfibsegs 81%nat E3 _ (ms_regs msM2) regs4 _ RA_CAWF_MALLOC2
  _ (mrestrict (w_H W4) mem4) [caw_stk] [] CAWF_CLOB HS3f
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(intros r Hr; apply (cawf_kept_clob (ms_regs msM2) regs4 r HP4); cbn in Hr; exact Hr)
  (Forall_nil _) HM4) as HS4.
set (E4 := havoc E3 81 (map (YK11.getr regs4) CAWF_CLOB)) in HS4.
assert (E4_81 : ew E4 81 = Z_to_bv 64 six).
{ subst E4. pose proof (ew_havoc_new E3 81 (map (YK11.getr regs4) CAWF_CLOB) 0 (Z_to_bv 64 0) ltac:(cbn; lia)) as HX.
  cbn [Nat.add] in HX. rewrite HX. cbn [CAWF_CLOB map nth]. exact H10s. }
assert (E4_82 : ew E4 82 = YK11.getr regs4 1).
{ subst E4. pose proof (ew_havoc_new E3 81 (map (YK11.getr regs4) CAWF_CLOB) 1 (Z_to_bv 64 0) ltac:(cbn; lia)) as HX.
  cbn [Nat.add] in HX. rewrite HX. reflexivity. }
assert (E4_old : forall n, (n < 81)%nat -> ew E4 n = ew E3 n) by (intros n Hn; subst E4; apply ew_havoc_old; lia).
assert (E4_2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite (E4_old 2%nat ltac:(lia)); exact E3_2).
assert (E4v : forall (n : nat) (r : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned r -> ew E4 n = YK11.getr regs r)
  by (intros n r Hn Hr; rewrite (E4_old n ltac:(lia)); exact (E3v n r Hn Hr)).
assert (Eab4 : ablocks B ly4 S4 = (ablocks B ly S ++ [(want, cawf_want_size tb)]) ++ (six, cawf_six_size tb) :: [])
  by (rewrite Hab4, Hab2; reflexivity).
assert (HU4 : forall r, In r U -> snd r = 16 /\
  exists m, In (fst r, m) (ablocks B ly S ++ [(want, cawf_want_size tb)]) /\ 16 <= req_size m).
{ intros r Hr. destruct (FH r Hr) as (H16 & m & Hm & Hm16). split; [exact H16|].
  exists m. split; [apply in_or_app; left; exact Hm | exact Hm16]. }
destruct (cawf_new_block ly4 S4 U W4 mem4 md4 _ [] six (cawf_six_size tb) HARU4 Eab4 HU4)
  as (_ & _ & Hsceil & Hs0 & Hsreq & _ & _ & _ & _).
assert (E4_10 : ew E4 10 = Z_to_bv 64 t) by (rewrite (E4v 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
pose proof (cawf_add_atom E4 _ _ 81%nat (mkAF 4096 CAW_CEIL 0) HS4
  (cawf_afact E4 81 six 4096 CAW_CEIL E4_81 ltac:(lia) ltac:(unfold CAW_CEIL; lia))) as HS4a.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4a.
pose proof (cawf_add_atom E4 _ _ 10%nat (mkAF 4096 CAW_CEIL 0) HS4a
  (cawf_afact E4 10 t 4096 CAW_CEIL E4_10 ltac:(lia) ltac:(unfold CAW_CEIL; lia))) as HS4b.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4b.
clear HS4 HS4a HM4 Hkeep4 Hcs4.
(* the text's first byte as atom 97, and the region that holds it *)
assert (Hinc4 : forall x, In x (ablocks B ly S) -> In x (ablocks B ly4 S4))
  by (intros x Hx; rewrite Eab4; apply in_or_app; left; apply in_or_app; left; exact Hx).
destruct (cawf_carry STK_check_as_written (spZ regs) ly S U W mem md ly4 S4 W4 mem4 _ (0 + 1 + 1) t tb
  live peak cnt fail HARUe HARU4 HJ4 Hinc4 HRO Hk Hc HG) as (HRO4 & Hc4 & _ & _).
pose proof Hc4 as ((Hg4 & Hnz4) & _ & _ & _ & _ & HraT4 & _).
assert (Hlen1 : length (tb ++ [0]) = Nat.succ (length tb)) by (rewrite length_app, Nat.add_comm; reflexivity).
destruct (Hg4 0%nat ltac:(rewrite Hlen1; apply Nat.lt_0_succ)) as [V40 R40].
set (c0 := nth 0 (tb ++ [0]) 0) in V40, R40.
set (E5 := havoc E4 97 [Z_to_bv 64 c0]).
assert (E5_old : forall n, (n < 97)%nat -> ew E5 n = ew E4 n) by (intros n Hn; subst E5; apply ew_havoc_old; lia).
assert (E5_97 : ew E5 97 = Z_to_bv 64 c0) by reflexivity.
pose proof (st_ok_agree tfibsegs 97 E4 E5 _ _ HS4b (env_agree_havoc E4 97 _) ltac:(vm_compute; reflexivity)) as HS5.
assert (E5_2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite (E5_old 2%nat ltac:(lia)); exact E4_2).
assert (E5_10 : bv_unsigned (ew E5 10) = t)
  by (rewrite (E5_old 10%nat ltac:(lia)), E4_10; apply unsigned_lit_small; lia).
assert (HR5 : region_ok tfibsegs E5 (mrestrict (w_H W4) mem4) cawf_txtR).
{ unfold region_ok, cawf_txtR. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E5_10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E5 _ _ 0 1%N (SOff 97 0) c0);
    [apply cawf_den0; rewrite E5_97; apply unsigned_lit_small; lia | cbn; lia | cbn; lia |].
  replace (t + 0) with (t + Z.of_nat 0) by lia. exact V40. }
pose proof (YI0n.st_ok_add_region' tfibsegs E5 _ _ cawf_txtR HS5 ltac:(vm_compute; reflexivity) HR5) as HS6.
lazymatch type of HS6 with ?P -> _ => assert (HD6 : P) end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, caw_stk, cawf_txtR.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E5_10, E5_2. left. lia. }
specialize (HS6 HD6). clear HS5 HD6.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS6.
rewrite <- restrict_mkst_fx in HS6.
(* the shadow entry of the inline check at 0x816c0 *)
assert (E5_32 : ew E5 32 = Z_to_bv 64 SHADOW_OFF).
{ apply (cawf_atom_val E5 _ _ 32%nat SHADOW_OFF HS6); [cbn [ss_facts f_atoms]; repeat (first [left; reflexivity | right])
  | unfold SHADOW_OFF; lia]. }
assert (SHOK : sh_ok tfibsegs caw_Bx cawf_SH E5 (mrestrict (w_H W4) mem4)).
{ assert (HB : YP0e.U E5 caw_Bx = SHADOW_OFF) by (unfold caw_Bx; apply U_atom; [exact E5_32 | unfold SHADOW_OFF; lia]).
  unfold sh_ok, cawf_SH. constructor; [|constructor].
  eapply (shent_ok_of_range tfibsegs (w_H W4) mem4 E5 caw_Bx 10 t (Z.of_nat (length tb) + 1) t 0 1 HraT4 HB);
    [apply cawf_U0; exact E5_10 | lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range in Htamem. unfold SHADOW_OFF.
  rewrite C5 in Htamem. rewrite C3 in Htamem. lia. }
fsw_aj_run_to_tokU caw_tbl_ok HS6 HJ4 HARU4 SHOK caw_Bspan 0x8170c.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact E5_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msB end.
(* ---- the byte test `beqz a2` at 0x816d8: the env after the token run is E5 with the two token atoms 98, 99 ---- *)
lazymatch type of HS6 with st_ok _ ?Ef _ _ => set (EF := Ef) in HS6 end.
assert (HAgf : forall n, (n < 98)%nat -> ew EF n = ew E5 n).
{ intros n Hn. subst EF. cbn [ew ewset].
  repeat match goal with |- context [Nat.eqb n ?k] => destruct (Nat.eqb_spec n k); [lia|] end. reflexivity. }
assert (EFv : forall n, (n < 33)%nat -> ew EF n = ew E0 n).
{ intros n Hn. rewrite (HAgf n ltac:(lia)), (E5_old n ltac:(lia)), (E4_old n ltac:(lia)), (E3_old n ltac:(lia)),
    (E2_old n ltac:(lia)), (E1_old n ltac:(lia)). reflexivity. }
assert (EFent : forall (n : nat) (r : bv 5), (n < 33)%nat -> Z.of_nat n = bv_unsigned r -> ew EF n = YK11.getr regs r).
{ intros n r Hn Hr. rewrite (EFv n Hn). subst E0. exact (ew_Ereg_nat regs fs_extraT n r Hr). }
assert (Hr5 : forall n, (n < 32)%nat -> Z.of_nat n = bv_unsigned (Z_to_bv 5 (Z.of_nat n))).
{ intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia. }
assert (EF_2 : bv_unsigned (ew EF 2) = spZ regs) by (rewrite (EFv 2%nat ltac:(lia)); exact E2a).
assert (EF_32 : ew EF 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HAgf 32%nat ltac:(lia)); exact E5_32).
assert (EF_97 : ew EF 97 = Z_to_bv 64 c0) by (rewrite (HAgf 97%nat ltac:(lia)); exact E5_97).
assert (EF_81 : bv_unsigned (ew EF 81) = six)
  by (rewrite (HAgf 81%nat ltac:(lia)), (E5_old 81%nat ltac:(lia)), E4_81; apply unsigned_lit_small; lia).
assert (EF_49 : bv_unsigned (ew EF 49) = want)
  by (rewrite (HAgf 49%nat ltac:(lia)), (E5_old 49%nat ltac:(lia)), (E4_old 49%nat ltac:(lia)),
        (E3_old 49%nat ltac:(lia)), E2_49; apply unsigned_lit_small; lia).
assert (EF_10 : bv_unsigned (ew EF 10) = t) by (rewrite (HAgf 10%nat ltac:(lia)); exact E5_10).
eapply SRr_sym_branch with (c := BC_EQ) (a := SExt false 8 (SOff 97 0)) (b := SLit 0);
  [exact HS6 | intros Hb HS7 | intros Hb HS7]; rewrite (cawf_byte_branch EF c0 EF_97 ltac:(lia)) in Hb; clear HS6.
- (* t[0] = 0, the empty text: `beqz a2` at 0x816d8 taken, straight to 0x81810 *)
  apply Z.eqb_eq in Hb. pose proof (cawf_c0_nil tb Hnz4 Hb) as Htb0.
  fsw_aj_run_toU caw_tbl_ok HS7 HJ4 HARU4 0x81810.
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact EF_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msE end.
  pose proof (cawf_post_ok ly S U W regs mem md t tb live peak cnt fail W4 ly4 S4 want six msE _
    HARUe FH HRO Hk Hc HG Eab4 HJ4 HARU4) as HPOST.
  assert (R10E : bv_unsigned (YK11.getr (ms_regs msE) 10) = six)
    by (cawf_regU HS7 (10%bv : bv 5); rewrite fsw_SOff0; exact EF_81).
  assert (R18E : bv_unsigned (YK11.getr (ms_regs msE) 18) = want)
    by (cawf_regU HS7 (18%bv : bv 5); rewrite fsw_SOff0; exact EF_49).
  assert (R13E : bv_unsigned (YK11.getr (ms_regs msE) 13) = 2 ^ 64 - 1 - six)
    by (cawf_regU HS7 (13%bv : bv 5); cawf_not_tac EF_81).
  pose proof (cawf_810_ok EF _ msE W4 1 (spZ regs) six want HS7 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EF_2 R10E R18E R13E
    ltac:(unfold CAW_CEIL; lia) ltac:(unfold CAW_CEIL; lia)) as HS8.
  set (E' := cawf_env810 EF (ms_regs msE)) in HS8.
  apply (K810 W4 ly4 S4 E' msE _ want six HPOST Htb0 HS8).
  + subst E'. rewrite cawf_env810_old by lia. apply cawf_w_of_u. exact EF_2.
  + apply cawf_w_of_u. exact R13E.
  + apply cawf_w_of_u. exact R10E.
  + apply cawf_w_of_u. exact R18E.
  + reflexivity.
  + subst E'. rewrite cawf_env810_old by lia. exact (EFent 11%nat 11%bv ltac:(lia) eq_refl).
  + subst E'. rewrite cawf_env810_old by lia. exact (EFent 12%nat 12%bv ltac:(lia) eq_refl).
  + intros n Hn. subst E'. rewrite cawf_env810_old by lia. apply EFent; [lia | apply Hr5; lia].
  + reflexivity.
  + exact EF_32.
- (* t[0] <> 0, the text is not empty: the loop setup 0x816dc .. 0x81708 -> the scan loop head 0x8170c *)
  apply Z.eqb_neq in Hb. pose proof (cawf_c0_cons tb Hb) as Hne.
  fsw_aj_run_toU caw_tbl_ok HS7 HJ4 HARU4 0x8170c.
  { cbn [ss_mem add_cond]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_stack with (n := 2%nat); [reflexivity | exact EF_2 | cbn; lia | cbn; lia |]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msH end.
  pose proof (cawf_post_ok ly S U W regs mem md t tb live peak cnt fail W4 ly4 S4 want six msH _
    HARUe FH HRO Hk Hc HG Eab4 HJ4 HARU4) as HPOST.
  pose proof HPOST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HgH & HraH & HrasH & HwsH) & _).
  pose proof (cawf_static_ok ly S U W mem t tb W4 ly4 S4 want six (ms_mem msH) _ (spZ regs) HARU4 FH Eab4 Hc Hk Hlen3
    ltac:(lia) H47) as HST.
  pose proof HST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hdisj6 & _).
  assert (R10H : bv_unsigned (YK11.getr (ms_regs msH) 10) = six)
    by (cawf_regU HS7 (10%bv : bv 5); rewrite fsw_SOff0; exact EF_81).
  assert (R18H : bv_unsigned (YK11.getr (ms_regs msH) 18) = want)
    by (cawf_regU HS7 (18%bv : bv 5); rewrite fsw_SOff0; exact EF_49).
  assert (R19H : bv_unsigned (YK11.getr (ms_regs msH) 19) = t)
    by (cawf_regU HS7 (19%bv : bv 5); rewrite fsw_SOff0; exact EF_10).
  assert (R12H : bv_unsigned (YK11.getr (ms_regs msH) 12) = c0)
    by (cawf_regU HS7 (12%bv : bv 5); exact (cawf_byte_val EF c0 EF_97 ltac:(lia))).
  assert (R13H : bv_unsigned (YK11.getr (ms_regs msH) 13) = 2 ^ 64 - 1 - six)
    by (cawf_regU HS7 (13%bv : bv 5); cawf_not_tac EF_81).
  pose proof (fsw_reg_off _ EF _ msH 11%bv 10 1 t HS7 ltac:(vm_compute; reflexivity) EF_10 ltac:(lia)) as R11H.
  pose proof (fsw_reg_lit _ EF _ msH 14%bv 0 HS7 ltac:(vm_compute; reflexivity) ltac:(lia)) as R14H.
  pose proof (fsw_reg_lit _ EF _ msH 28%bv 0 HS7 ltac:(vm_compute; reflexivity) ltac:(lia)) as R28H.
  assert (U14 : bv_unsigned (YK11.getr (ms_regs msH) 14) = 0) by (rewrite R14H; reflexivity).
  assert (U28 : bv_unsigned (YK11.getr (ms_regs msH) 28) = 0) by (rewrite R28H; reflexivity).
  destruct (HgH 1%nat ltac:(rewrite Hlen1; apply -> Nat.succ_lt_mono; exact Hne)) as [V1H Rc1].
  set (c1 := nth 1 (tb ++ [0]) 0) in V1H, Rc1. replace (t + Z.of_nat 1) with (t + 1) in V1H by lia.
  pose proof (cawf_head_ok EF _ msH W4 1 (spZ regs) six want t c0 c1 HS7 ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) EF_2 R10H R18H R19H R11H R12H R13H U14 U28
    ltac:(unfold CAW_CEIL; lia) ltac:(unfold CAW_CEIL; lia) ltac:(lia) ltac:(unfold CAW_CEIL; lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(unfold cawf_six_size in *; lia) ltac:(unfold cawf_six_size in Hdisj6; lia) V1H
    (HwsH six ltac:(unfold cawf_six_size; lia))) as HS8.
  set (E' := cawf_envH EF (ms_regs msH) (Z_to_bv 64 six) (Z_to_bv 64 c1)) in HS8.
  apply (KLOOP W4 ly4 S4 E' msH _ want six HPOST Hne HS8).
  + unfold caw_atoms. split; [subst E'; rewrite cawf_envH_old by lia; apply cawf_w_of_u; exact EF_2|].
    split; [apply cawf_w_of_u; exact R10H|].
    split; [apply cawf_w_of_u; cbn [Z.of_nat]; rewrite Z.add_0_r; exact R19H|].
    split; [apply cawf_w_of_u; cbn [Z.of_nat]; rewrite Z.add_0_r; exact R11H|].
    split; [apply cawf_w_of_u; transitivity c0;
      [exact R12H | change (nth 0 (tb ++ [0]) 0 = nth 0 tb 0); apply app_nth1; exact Hne]|].
    split; [apply cawf_w_of_u; exact U14|].
    split; [apply cawf_w_of_u; exact U28|].
    split; [cbn [Z.of_nat]; rewrite Z.add_0_r; reflexivity | reflexivity].
  + apply cawf_w_of_u. exact R13H.
  + apply cawf_w_of_u. exact R18H.
  + subst E'. rewrite cawf_envH_old by lia. exact (EFent 11%nat 11%bv ltac:(lia) eq_refl).
  + subst E'. rewrite cawf_envH_old by lia. exact (EFent 12%nat 12%bv ltac:(lia) eq_refl).
  + intros n Hn. subst E'. rewrite cawf_envH_old by lia. apply EFent; [lia | apply Hr5; lia].
  + reflexivity.
  + exact EF_32.
  + exact HST.
  + intros i Hi. cbn in Hi. lia.
Qed.
End c.
