(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 327 of its 364 lines of code are new or changed and 1268 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readDefs.v, with its module names changed; 1004 of its 1049 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/copy_attr.v, with its module names changed; 373 of its 423 lines of code are new or changed and 999 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's SET-UP phase, kin_setup (+0x494) -> kin_head (+0x51c) with ci = 0 and j = 0 (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4; link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3),
   +0x494 .. +0x518; straight-line: no call, no branch, no instrumented check):
   - +0x494 s6 := 0 (ci); +0x498 a4 := [s1 + 0x30] = F; +0x49c a5 := w1 = F + 0x20;
   - +0x4a0 .. +0x4c8: a0 := 0x1000, a1 := -0x1000, a3 := 1, s9 := 0x1000, a6 := 0x40000, a2 := the .rodata page
     (`auipc`), s5 := 0x1130, slot 0xd8 := 2 ^ 64 - 4093, a0 := 2 ^ 32, a3 := 0x1008;
   - +0x4cc `ld a2, 0x19c(a2)`: the magic multiplier 0x2aaaaaaaaaaaaaab at 0x10380 (listing object A_OBJ 11,
     kernel_img.v ki_m6_val_mem through kkept's arodata_okP), spilled to slot 0xb8 (+0x4d0);
   - slot 0xd0 := 2 ^ 64 - 4098 (+0x4d8); s5 := F + 0x1130 = w2 (+0x4dc); slot 0x98 := 0xfffffffc (+0x4e4);
     slot 0x28 := &w1.full (+0x4ec); slot 0xc8 := &w2.full (+0x4f4); slot 0x40 := w1 (+0x4f8); slot 0x48 := &w1.n
     (+0x500); slot 0x58 := 4112 (+0x508); slot 0x70 := g_nl + 0x40000 (+0x50c .. +0x514, g_nl read back from
     slot 0x38); s9 := w2 + 0x1000 = &w2.n (+0x518).

   THE PROOF. The symbolic state is rebuilt from kin_setup (registers sr_atoms over Eimg (Ereg regs su_ext), the
   spill area [s1 + 0x28, s1 + 0xe0) as one region of atom 9 (s1) whose slots the phase reads or keeps are chunks,
   and the object at 0x10380 as a read-only region), the run goes to +0x51c, and kin_head is read off the end
   state: the written slots and the registers from the symbolic state, everything else from the run's frame
   (it wrote only [s1 + 0x28, s1 + 0xe0), inside kernel's window [sp - K, sp)).

   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at +0x494 ----
   Atoms 0..31: the registers at the cut; 32..37 (su_ext): F, shadow(F) + 4, c, shadow(F) + 0x226, a0 + 8,
   shadow(a0): the values of the spill slots 0x30, 0x50, 0x60, 0x80, 0xb0, 0xc0, which lie inside the written
   window but which the phase does not write. Slot 0x38 holds g_nl, a literal. *)
Definition su_Bx : sv := SOff 20 0.
Definition su_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition su_stack : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x28 0xe0 0x28 0xe0
    [YP09.mkChunk 0x30 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x38 (CVal 8 (SLit LA_G_NL));
     YP09.mkChunk 0x50 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 34 0));
     YP09.mkChunk 0x80 (CVal 8 (SOff 35 0)); YP09.mkChunk 0xb0 (CVal 8 (SOff 36 0));
     YP09.mkChunk 0xc0 (CVal 8 (SOff 37 0))].
Definition su_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5)] [] [].
Definition su_ss : sstate :=
  mkSS (kpc KP_SETUP) sr_atoms [su_stack; obj8_region 11 (SLit KI_M6_V)] None su_facts.

(* the cut's spill-slot membership, by computation *)
Ltac su_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.                                   (* kernel_img_syms at the image *)

Definition su_ext (cx : kcx) (fpos c : Z) : list word :=
  [w64 (kF cx fpos); w64 (kFSH cx fpos + 4); w64 c; w64 (kFSH cx fpos + 0x226); w64 (ka0 cx + 8);
   w64 (shadow_of_addr SHADOW_OFF (ka0 cx))].

(* ---- byte and word helpers ---- *)

Lemma su_ms_shape : forall (ms : machine_state) (pc : Z),
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (w64 pc) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros [rg fr pcv sv rv fc mm rm] pc H1 H2 H3 H4 H5 H6.
  cbn in H1, H2, H3, H4, H5, H6. subst. reflexivity.
Qed.

Lemma su_apres_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a Hg (Hh & b & Hb). split; [exact Hh|].
  specialize (Hg (Z_to_bv 64 a)). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply Hg; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma su_rdword_range : forall (H : word -> bool) (m : word -> option byte) a v,
  rdword (aview SEGS H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H m a v Hv.
  assert (R : forall x b, aview SEGS H m x = Some b -> 0 <= b < 256).
  { intros x b Hb. destruct (aview_byte SEGS H m x b Hb) as (_ & _ & _ & Hr). exact Hr. }
  unfold rdword in Hv.
  destruct (aview SEGS H m a) as [b0|] eqn:E0; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 1)) as [b1|] eqn:E1; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 2)) as [b2|] eqn:E2; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 3)) as [b3|] eqn:E3; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 4)) as [b4|] eqn:E4; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 5)) as [b5|] eqn:E5; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 6)) as [b6|] eqn:E6; [|cbv iota beta in Hv; discriminate Hv].
  destruct (aview SEGS H m (a + 7)) as [b7|] eqn:E7; [|cbv iota beta in Hv; discriminate Hv].
  cbv iota beta in Hv. injection Hv as <-.
  apply R in E0. apply R in E1. apply R in E2. apply R in E3.
  apply R in E4. apply R in E5. apply R in E6. apply R in E7. lia.
Qed.

Lemma su_rdword_agree : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
  rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma su_au8arr_keep : forall (H : word -> bool) (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview SEGS H m' (a + i) = aview SEGS H m (a + i)) ->
  mem_grows (mrestrict H m) (mrestrict H m') ->
  au8arr SEGS (mrestrict H m) a bs -> au8arr SEGS (mrestrict H m') a bs.
Proof.
  intros H m m' a bs Hk Hg ((H0 & H1 & Hb) & Hw).
  split; [split; [exact H0 | split; [exact H1|]]|].
  - intros i Hi. rewrite <- (Hb i Hi). apply (mbyte_of_aview SEGS H H m m'). apply Hk. lia.
  - intros i Hi. exact (writable_at_grows SEGS _ _ _ Hg (Hw i Hi)).
Qed.

(* a spill slot's 8 bytes as a chunk of the state's region *)
Lemma su_chunk_rd : forall E (H : word -> bool) (mm : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mm) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mm) base (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E H mm base off e v He Hr.
  pose proof (su_rdword_range H mm (base + off) v Hr) as Hv.
  apply (chunk_ok_val SEGS E (mrestrict H mm) base off 8 e v He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
  - exact (val_mem_of_rdword SEGS H mm (base + off) v Hr).
Qed.

(* and back: a chunk of a region of an end state as a spill slot's word *)
Lemma su_rd_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v,
  region_ok SEGS E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mm) (b + off) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := SEGS) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

(* every byte akb places (the read set of kernel_ard) lies below 2 ^ 47 *)
Lemma su_akb_bound : forall lyc Sc W memc mdc slo shi a,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= ly_stk_lo lyc -> ly_stk_hi lyc <= 2 ^ 47 ->
  akb SEGS B lyc Sc slo shi a -> 0 <= a < 2 ^ 47.
Proof.
  intros lyc Sc W memc mdc slo shi a HAR Hlo Hhi Hb.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct Hb as [(H1 & _) | [(b & m & Hin & Hr) | [(H1 & _ & _) | (cid & pos & Hin & Hr)]]].
  - lia.
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hbc & _). lia.
  - pose proof (pa_segs_low a H1) as Ha. rewrite C5 in Ha. lia.
  - destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4 & Hfc & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. lia.
Qed.

(* ---- the phase ---- *)

Theorem kn_setup : forall POST (Rc : kcx -> Z -> Prop), (forall cx v, 1 <= v <= 3 -> Rc cx v) ->
  kfrom SK B POST (kin_head B Rc) -> kfrom SK B POST (kin_setup B).
Proof.
intros POST Rc HRc HNEXT cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
unfold kin_setup in HI. destruct HI as (c & adv & Hc & HK). unfold kat in HK.
destruct HK as (Hkms & Hkr0 & Hkre & Hksv & Hkfr & Hksh & Hksl & Hkjbk & Hkkept & Hkcur & Hkg & Hkla).
pose proof HB as HB'. unfold kbase in HB'. destruct HB' as (HPRE & HRD & HKP & _).
pose proof HPRE as (HJ0 & HGok & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
destruct HKP as (kbs0 & _ & _ & _ & _ & _ & _ & _ & HAPF & _).
pose proof HJ0 as (HSTK0 & HXO0 & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
pose proof HJ0 as HROW. eapply ajournal_gx_row in HROW. destruct HROW as (Hrow1 & Hrow2 & Hrow3 & Hrow4).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HKA : KERNEL_AK = 4640) by reflexivity.
unfold apart_frame in HAPF.
change (spZ (k_regs cx)) with (ksp cx) in Hwlo, Hwhi, HAPF.
change (aarg (k_regs cx) 0) with (ka0 cx) in HAPF.
rewrite HKA in Hwlo, HAPF.
assert (Hsp : alloc_ceiling + 4640 <= ksp cx <= 2 ^ 47) by lia.
assert (Hs1 : ksp cx - 384 < ksp1 cx <= ksp cx - 352) by (unfold ksp1, ksp1_of, KN_MFRAME; lia).
assert (Hs1al : ksp1 cx mod 32 = 0) by (unfold ksp1, ksp1_of; rewrite Z.mul_comm; apply Z_mod_mult).
(* F and its shadow, below the allocator's ceiling (kjbk's state just after frame_alloc_8) *)
pose proof Hkjbk as (_ & _ & _ & _ & (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & _) & _).
assert (HinF : In (KN_CID, fpos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (k_lyc cx) S1 W1 mem1 md1 KN_CID fpos HAR1 HinF) as (Hfa0 & Hfa1 & _).
assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
assert (HFb : 4096 <= kF cx fpos /\ kF cx fpos + 16384 <= alloc_ceiling) by (unfold kF; lia).
assert (HFSH : 2147450880 + 512 <= kFSH cx fpos /\ kFSH cx fpos + 0x448 <= 2147450880 + 2 ^ 44)
  by (unfold kFSH, shadow_of_addr, SHADOW_OFF; lia).
(* the cut's registers and slots *)
destruct Hkr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
unfold kregs_eq in Hkre.
pose proof (Forall_inv Hkre) as R19. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hkre))) as R24.
cbn [fst snd] in R19, R24.
unfold kslots_eq in Hksl. rewrite Forall_forall in Hksl.
pose proof (Hksl (KS_FSH, kFSH cx fpos) ltac:(su_inl)) as SL_FSH.
pose proof (Hksl (KS_FRES, kF cx fpos) ltac:(su_inl)) as SL_FRES.
pose proof (Hksl (KS_F, kF cx fpos) ltac:(su_inl)) as SL_F.
pose proof (Hksl (KS_GNL, LA_G_NL) ltac:(su_inl)) as SL_GNL.
pose proof (Hksl (KS_W1SH, kFSH cx fpos + 4) ltac:(su_inl)) as SL_W1SH.
pose proof (Hksl (KS_W2SH, kFSH cx fpos + 0x226) ltac:(su_inl)) as SL_W2SH.
pose proof (Hksl (KS_F2, kF cx fpos) ltac:(su_inl)) as SL_F2.
pose proof (Hksl (KS_CN, ka0 cx + 8) ltac:(su_inl)) as SL_CN.
pose proof (Hksl (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx)) ltac:(su_inl)) as SL_CSH.
pose proof (Hksl (KS_C, c) ltac:(su_inl)) as SL_C.
cbn [fst snd] in SL_FSH, SL_FRES, SL_F, SL_GNL, SL_W1SH, SL_W2SH, SL_F2, SL_CN, SL_CSH, SL_C.
pose proof (su_rdword_range _ _ _ _ SL_CN) as Rg_CN.
pose proof (su_rdword_range _ _ _ _ SL_CSH) as Rg_CSH.
(* the journal's window is present at the cut *)
pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HPRES.
pose proof Hkkept as (K1 & HRO3).
(* ---- the environment ---- *)
remember (Eimg (Ereg (ms_regs ms3) (su_ext cx fpos c))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (ER : forall (j : nat) (r : bv 5), Z.of_nat j = bv_unsigned r -> ew E j = getr (ms_regs ms3) r)
  by (intros j r Hj; rewrite HEdef; exact (ew_Eimg_Ereg_nat _ _ j r Hj)).
assert (EXT : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (su_ext cx fpos c) (Z_to_bv 64 0))
  by (intros j Hj; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
cbn [su_ext nth Nat.add] in E32, E33, E34, E35, E36, E37.
pose proof (ER 9%nat 9%bv eq_refl) as E9.
assert (E9' : ew E 9 = w64 (ksp1 cx)) by (rewrite E9; exact R9).
assert (BV9u : bv_unsigned (ew E 9) = ksp1 cx) by (rewrite E9'; unfold w64; apply unsigned_lit_small; lia).
assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by (cbn [base_val]; exact BV9u).
assert (BVK : base_val E (Some (A_OBJ 11)) = 0x10380).
{ cbn [base_val]. rewrite HEdef, Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_obj LV 11%nat) by (unfold link_nobj; lia).
  change (link_obj 11) with 0x10380. apply unsigned_lit_small. lia. }
(* ---- the symbolic state at +0x494 ---- *)
assert (HS : st_ok_pi SEGS pa_val E su_ss (restrict (w_H W3) ms3)).
{ destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  rewrite (su_ms_shape ms3 (BASE + kpc KP_SETUP) Hpc Hrv Hsvc Hrom Hfrg Hfcs).
  rewrite restrict_mkst_fx. unfold su_ss. apply pa_entry_st_ok_full.
  - rewrite HEdef. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold su_stack, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BV9.
      split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply HPRES. lia. }
      repeat apply Forall_cons; [..|apply Forall_nil].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x30 (SOff 32 0) (kF cx fpos));
          [apply sv_off0; exact E32 | exact SL_F].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x38 (SLit LA_G_NL) LA_G_NL);
          [reflexivity | exact SL_GNL].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x50 (SOff 33 0) (kFSH cx fpos + 4));
          [apply sv_off0; exact E33 | exact SL_W1SH].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x60 (SOff 34 0) c);
          [apply sv_off0; exact E34 | exact SL_C].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0x80 (SOff 35 0) (kFSH cx fpos + 0x226));
          [apply sv_off0; exact E35 | exact SL_W2SH].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 36 0) (ka0 cx + 8));
          [apply sv_off0; exact E36 | exact SL_CN].
      * apply (su_chunk_rd E (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (SOff 37 0)
                 (shadow_of_addr SHADOW_OFF (ka0 cx)));
          [apply sv_off0; exact E37 | exact SL_CSH].
    + unfold obj8_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite BVK.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ 0x10380 0 8 (SLit KI_M6_V) KI_M6_V);
        [reflexivity | unfold KI_M6_V; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (ki_m6_val_mem SEGS PCAP_RLO PCAP_RHI B KI (w_H W3) (ms_mem ms3) HRO3).
  - cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I] | split; exact I].
    unfold extent_disjoint, su_stack, obj8_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite BV9, BVK. lia.
  - unfold su_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [split; [|exact I] | split; exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite BV9u. change (2 ^ 5) with 32.
    split; [lia | split; [exact Hs1al | lia]]. }
assert (SHOK : sh_ok SEGS su_Bx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
(* +0x494 .. +0x518 *)
paj_run_to_tok RUNTO HS HJ SHOK su_span (kpc KP_HEAD).
{ unfold su_ss. cbn [ss_mem].
  apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]].
  - intros x Hx. unfold su_stack in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. rewrite BV9 in Hx.
    left. split; [left; lia | lia].
  - intros x Hx. unfold obj8_region in Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx. lia. }
(* ---- the end state, at +0x51c ---- *)
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (ksp1 cx + 0x28 <= a < ksp1 cx + 0xe0) ->
          aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn.
  apply (kept_of_frame (segs := SEGS) E (ss_mem su_ss) (w_H W3) (ms_mem ms3) (ms_mem ms)
           (fun x => ksp1 cx + 0x28 <= x < ksp1 cx + 0xe0) HFr); [| exact Ha | exact Hn].
  intros bb wlo whi x Hin Hx. cbv beta. vm_compute in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; [rewrite BV9 in Hx; lia | lia]. }
assert (RDW : forall a v, 0 <= a -> (a + 8 <= ksp1 cx + 0x28 \/ ksp1 cx + 0xe0 <= a) -> a + 8 <= 2 ^ 64 ->
          rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v ->
          rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v).
{ intros a v Ha0 Hout Ha64 Hv. rewrite <- Hv. apply su_rdword_agree. intros i Hi.
  apply UN; [lia|]. destruct Hout; lia. }
assert (CURK : forall i, 0 <= i < 16 ->
          aview SEGS (w_H W3) (ms_mem ms) (ka0 cx + i) = aview SEGS (w_H W3) (ms_mem ms3) (ka0 cx + i)).
{ intros i Hi.
  assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) (ka0 cx + i)) by (unfold kernel_ard; left; unfold ka0; lia).
  pose proof (su_akb_bound _ _ _ _ _ _ _ _ HAR0 Hrow1 Hrow2 (HRD _ Hrd)) as Hb.
  apply UN; [lia|]. destruct HAPF as [HA | HA]; lia. }
assert (RK : forall ssx (r : bv 5), st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) ms) ->
          sr_get (ss_regs ssx) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
          getr (ms_regs ms) r = getr (ms_regs ms3) r).
{ intros ssx r HSx Hr. rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx ms r HSx), Hr. cbn [sv_denot].
  rewrite Z.add_0_r, (ER (Z.to_nat (bv_unsigned r)) r).
  - apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 5 r). lia. }
assert (RV : forall ssx (r : bv 5) n k v, st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) ms) ->
          sr_get (ss_regs ssx) r = SOff n k -> ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
          getr (ms_regs ms) r = Z_to_bv 64 (v + k)).
{ intros ssx r n k v HSx Hr Hn Hv. rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx ms r HSx), Hr.
  cbn [sv_denot]. rewrite Hn, unsigned_lit_small by exact Hv. reflexivity. }
assert (RL : forall ssx (r : bv 5) z, st_ok_pi SEGS pa_val E ssx (restrict (w_H W3) ms) ->
          sr_get (ss_regs ssx) r = SLit z -> getr (ms_regs ms) r = sv_denot E (SLit z)).
{ intros ssx r z HSx Hr. rewrite (st_ok_pi_restrict_reg (w_H W3) E ssx ms r HSx), Hr. reflexivity. }
pose proof (st_ok_pi_restrict_mkst (w_H W3) E _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
destruct (ms_shape_mkst SEGS ms _ _ _ Hshape) as (Q2 & Q3 & Q4 & Q5 & Q6 & Q1).
spregion HS 0%nat HR.
assert (FRG : 0 <= kF cx fpos < 2 ^ 64) by lia.
(* ---- the next cut ---- *)
apply (HNEXT cx fpos k2 ly3 S3 W3 ms _ HB HJ Hfrm).
unfold kin_head. exists c, 0, 0, adv.
split; [apply HRc; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
unfold kat.
(* kms *)
split.
{ split; [rewrite Q1; reflexivity|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact Q5 | exact Q6]. }
(* kregs0 *)
split.
{ split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R2|].
  split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R9|].
  split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R8|].
  split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R3|].
  split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R4|].
  split; [rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R18|].
  rewrite (RK _ _ HS) by (vm_compute; reflexivity); exact R20. }
(* kregs_eq: s3, s5 = w2, s6 = 0, s8, s9 = &w2.n *)
split.
{ unfold kregs_eq, kregs_chunk. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  - rewrite (RK _ _ HS) by (vm_compute; reflexivity). exact R19.
  - rewrite (RV _ _ 32%nat 4400 (kF cx fpos) HS); [| vm_compute; reflexivity | exact E32 | exact FRG].
    unfold w64, kW2, KN_W2. f_equal; lia.
  - rewrite (RL _ _ 0 HS) by (vm_compute; reflexivity). reflexivity.
  - rewrite (RK _ _ HS) by (vm_compute; reflexivity). exact R24.
  - rewrite (RV _ _ 32%nat 8496 (kF cx fpos) HS); [| vm_compute; reflexivity | exact E32 | exact FRG].
    unfold w64, kW2, KN_W2, NW_N. f_equal; lia. }
(* ksaved *)
split.
{ destruct Hksv as (SV1 & SV2). split.
  - apply RDW; [lia | right; lia | lia | exact SV1].
  - intros j Hj. apply RDW; [lia | right; lia | lia | exact (SV2 j Hj)]. }
(* kframe *)
split.
{ destruct Hkfr as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6).
  split; [apply RDW; [lia | left; lia | lia | exact FR1]|].
  split; [apply RDW; [lia | left; lia | lia | exact FR2]|].
  split; [apply RDW; [lia | left; lia | lia | exact FR3]|].
  split; [apply RDW; [lia | left; lia | lia | exact FR4]|].
  split; [intros a Ha; exact (su_apres_grows _ _ _ a HG (FR5 a Ha))|].
  intros a Ha; exact (su_apres_grows _ _ _ a HG (FR6 a Ha)). }
(* kshadow *)
split.
{ intros i Hi. pose proof (kfsh_length 0xf8 0xf8 0xf3) as Hl. rewrite Hl in Hi.
  rewrite UN; [exact (Hksh i ltac:(rewrite Hl; exact Hi)) | lia | lia]. }
(* kslots_eq: the slots of the chunk loop *)
split.
{ unfold kslots_eq, kslots_setup. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  - apply RDW; [unfold KS_FSH; lia | left; unfold KS_FSH; lia | unfold KS_FSH; lia | exact SL_FSH].
  - apply RDW; [unfold KS_FRES; lia | left; unfold KS_FRES; lia | unfold KS_FRES; lia | exact SL_FRES].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x28 (SOff 32 4136)
             (kW1 cx fpos + NW_FULL) HR BV9u); [su_inl | | unfold kW1, KN_W1, NW_FULL; lia].
    cbn [sv_denot]. rewrite E32, unsigned_lit_small by exact FRG. unfold kW1, KN_W1, NW_FULL. f_equal; lia.
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x30 (SOff 32 0)
             (kF cx fpos) HR BV9u); [su_inl | apply sv_off0; exact E32 | exact FRG].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x38 (SLit 6146752)
             LA_G_NL HR BV9u); [su_inl | reflexivity | unfold LA_G_NL; lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x40 (SOff 32 32)
             (kW1 cx fpos) HR BV9u); [su_inl | | unfold kW1, KN_W1; lia].
    cbn [sv_denot]. rewrite E32, unsigned_lit_small by exact FRG. unfold kW1, KN_W1. reflexivity.
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x48 (SOff 32 4128)
             (kW1 cx fpos + NW_N) HR BV9u); [su_inl | | unfold kW1, KN_W1, NW_N; lia].
    cbn [sv_denot]. rewrite E32, unsigned_lit_small by exact FRG. unfold kW1, KN_W1, NW_N. f_equal; lia.
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x50 (SOff 33 0)
             (kFSH cx fpos + 4) HR BV9u); [su_inl | apply sv_off0; exact E33 | lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x58 (SLit 4112)
             NW_SIZE HR BV9u); [su_inl | reflexivity | unfold NW_SIZE; lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x60 (SOff 34 0)
             c HR BV9u); [su_inl | apply sv_off0; exact E34 | lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x70 (SLit 6408896)
             (LA_G_NL + NK_CHUNK_LEN) HR BV9u); [su_inl | reflexivity | unfold LA_G_NL, NK_CHUNK_LEN; lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x80 (SOff 35 0)
             (kFSH cx fpos + 0x226) HR BV9u); [su_inl | apply sv_off0; exact E35 | lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0x98 (SLit 4294967292)
             0xfffffffc HR BV9u); [su_inl | reflexivity | lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xb0 (SOff 36 0)
             (ka0 cx + 8) HR BV9u); [su_inl | apply sv_off0; exact E36 | exact Rg_CN].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xb8
             (SLit 3074457345618258603) KI_M6_V HR BV9u); [su_inl | reflexivity | unfold KI_M6_V; lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xc0 (SOff 37 0)
             (shadow_of_addr SHADOW_OFF (ka0 cx)) HR BV9u); [su_inl | apply sv_off0; exact E37 | exact Rg_CSH].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xc8 (SOff 32 8504)
             (kW2 cx fpos + NW_FULL) HR BV9u); [su_inl | | unfold kW2, KN_W2, NW_FULL; lia].
    cbn [sv_denot]. rewrite E32, unsigned_lit_small by exact FRG. unfold kW2, KN_W2, NW_FULL. f_equal; lia.
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xd0
             (SLit 18446744073709547518) (2 ^ 64 - 4098) HR BV9u); [su_inl | reflexivity | lia].
  - apply (su_rd_of_region E (w_H W3) (ms_mem ms) 9%nat (ksp1 cx) _ _ _ _ _ 0xd8
             (SLit 18446744073709547523) (2 ^ 64 - 4093) HR BV9u); [su_inl | reflexivity | lia].
  - apply RDW; [unfold KS_F2; lia | right; unfold KS_F2; lia | unfold KS_F2; lia | exact SL_F2]. }
(* kjbk *)
split.
{ destruct Hkjbk as (J1 & J2 & J3 & J4 & J5 & J6 & J7).
  split; [exact J1|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|].
  split; [rewrite (proj1 (wvb_fds_fs _ _ _)); exact J6 | rewrite (proj2 (wvb_fds_fs _ _ _)); exact J7]. }
(* kkept *)
split.
{ split.
  - apply (akept_step SK SEGS B LAWS pa_segs_low (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
             W3 (ms_mem ms3) W3 (ms_mem ms) (ksp cx - KERNEL_AK) (ksp cx)
             (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)
             (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a)
             (fun a => ksp1 cx + 0x28 <= a < ksp1 cx + 0xe0) HAR0).
    + rewrite HKA. lia.
    + lia.
    + exact K1.
    + intros a Ha Hn. exact (UN a Ha Hn).
    + intros a Ha Hp. exact (su_apres_grows _ _ _ a HG Hp).
    + intros a Ha. exact Ha.
    + intros a Ha. cbv beta in Ha. right. rewrite HKA. lia.
  - intros a Hro Hns Herr.
    assert (Ha : 0 <= a < 0x7fff8000).
    { destruct Hro as [(s & Hin & _ & Hb) | Hr].
      - pose proof (pa_segs_low a (ex_intro _ s (conj Hin Hb))) as Hl. rewrite C5 in Hl. exact Hl.
      - unfold PCAP_RLO, PCAP_RHI in Hr. lia. }
    rewrite UN; [exact (HRO3 a Hro Hns Herr) | lia | lia]. }
(* kcursor *)
split.
{ destruct Hkcur as (Hadv & HCP & HCN & HCW).
  split; [exact Hadv|]. split; [|split].
  - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms) (ka0 cx) (ka0 cx) 8 (k_wp cx + adv));
      [|exact HCP].
    intros k Hk. apply CURK. lia.
  - apply (val_mem_moved SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms) (ka0 cx + 8) (ka0 cx + 8) 8
             (k_wn cx - adv)); [|exact HCN].
    intros k Hk. replace (ka0 cx + 8 + k) with (ka0 cx + (8 + k)) by lia. apply CURK. lia.
  - intros i Hi. exact (writable_at_grows SEGS _ _ _ HG (HCW i Hi)). }
(* kgnl_at, kla_at *)
split.
{ cbn [kgnl_at] in Hkg |- *. destruct Hkg as (kbs3 & (HA3 & HAL3) & HKG3).
  exists kbs3. split; [split; [|exact HAL3] | exact HKG3].
  apply (su_au8arr_keep (w_H W3) (ms_mem ms3) (ms_mem ms)); [|exact HG | exact HA3].
  intros i Hi. rewrite HAL3 in Hi. unfold NK_SIZE in Hi. apply UN; unfold LA_G_NL; lia. }
{ destruct Hkla as (la3 & HLA3 & HLAL3). exists la3. split; [|exact HLAL3].
  apply (su_au8arr_keep (w_H W3) (ms_mem ms3) (ms_mem ms)); [|exact HG | exact HLA3].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply UN; unfold LA_LONG_ALIAS; lia. }
Qed.

End b.
End a.
