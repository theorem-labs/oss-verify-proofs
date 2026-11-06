(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 261 of its 302 lines of code are new or changed and 412 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): the ONE shared fold call step of the
   image-B m_file segment walks, stated over lib/B/Prog/m_file_m.v's cut predicates, in the continuation form of
   lib/B/Prog/m_file_iq.v's mf_ieq_call. A walk lane of the image-B m_file-family owner's G2B (owner's decision 18:4xZ: the shared
   B copy; S_MF_KROLE and S_MF_KMOD use it). proves no function (kind: segment lemma of m_file's walk: the call step
   of fold).

   mf_fold_call: a call of fold (image B 0x87c94; image A has none, it inlines fold; m_file's sites 0x86738 with cap
   64 in S_MF_KROLE and 0x8686c with cap 24 in S_MF_KMOD; the image-B m_file cut map section 3 rows 22 and 28), from the state at
   fold's entry (the `jal` executed: pc = BASE + AF_fold, ra = BASE + ret, a0 = s the n bytes l of the text, a1 = n,
   a2 = out = low = FB + 32 (144(s1)), a3 = cap, sp = s1), low.i in scope (MF_LOW_ON): fold_contract (lib/B/Prog/
   fold_c.v, at SegInstB.STK_fold = 16) taken through PaNoChain.cl_callS_wide, whose footprint [out, out + k + 1),
   k = length (fold_out l cap) = min(n, cap - 1), lies in m_file's own side-stack frame (1, pos) (in_frames, the
   journal's own list). fold's post is apost_base, so the walk goes on at BASE + ret at the SAME FP state, with
   a0 = k, the k + 1 bytes at out = fold_out l cap and its NUL, and every cut fact kept (fd_keep): fold writes only
   its stack window [s1 - 16, s1) and [out, out + k + 1) inside low.i [FB + 32, FB + 96); no cut predicate reads a
   byte of low.i (mf_core reads low.i's shadow bytes, which are shadow memory, not low.i).
   The callee's premises: fold_args from the caller's s (sa_bytes of all n bytes l, sa_addr, sa_heap, s <> 0; only
   the first k are asked) and from mf_low_addr (m_file_sd.v: low.i's first k + 1 <= cap <= 64 bytes addressable and
   in the live frame); sa_disj from the heap block and the frame being apart (sep_block_frame).
   IMAGE B: s1 = (sp0 - 320) & -32 (iq_s1), STK_m_file = 8,592, STK_fold = 16 (SegInstB.v).
   Section hypotheses: FOLD (fold_contract at its listing entry, at every FP state) and KCHAIN (m_file_iq.v's form;
   B's m_file_k.v gives it as mf_chain). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_iq fold_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the shadow bytes a range below 2 ^ 47 reads (its shadow and the shadow's hull) lie in [SHADOW_OFF, kHighMemBeg):
   carried across a change outside that band *)
Lemma fd_ra_keep : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg.
assert (0 <= x / 8) by (apply Z.div_pos; lia).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma fd_hull_keep : forall (rd rd' : Z -> option Z) a n,
  (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
  shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + (a + n - 1) / 8) 8).
pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
Lemma fd_addr_keep : forall (rd rd' : reader) q n,
  (forall s, SHADOW_OFF <= s < kHighMemBeg -> rd' s = rd s) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' q n K (H0 & H63 & HAM & HRA & HHV).
assert (H47 : q + n <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; lia).
split; [exact H0|]. split; [exact H63|]. split; [exact HAM|]. split.
- exact (fd_ra_keep rd rd' q n K H0 H47 HRA).
- intros Hn. exact (fd_hull_keep rd rd' q n K H0 H47 Hn (HHV Hn)).
Qed.
(* sa_bytes of a prefix *)
Lemma fd_bytes_firstn : forall (rd : reader) a (l : list byte) k, sa_bytes rd a l -> sa_bytes rd a (firstn k l).
Proof.
intros rd a l k H i Hi. rewrite length_firstn in Hi.
rewrite nth_firstn. destruct (Nat.ltb_spec i k) as [_ | Hc]; [|lia]. cbn [andb]. apply H. lia.
Qed.
(* sa_addr of a prefix *)
Lemma fd_addr_prefix : forall (rd : reader) q n n', sa_addr rd q n -> 0 <= n' <= n -> sa_addr rd q n'.
Proof.
intros rd q n n' (H0 & H63 & HR & HA & HV) Hn'.
split; [lia|]. split; [lia|]. split.
{ unfold amem_range in *. lia. }
split; [exact (range_addressable_sub rd SHADOW_OFF q n q n' HA ltac:(lia) ltac:(lia))|].
intros Hp s Hs. apply (HV ltac:(lia)). unfold shadow_addr in *. split; [lia|].
pose proof (Z.div_le_mono (q + n' - 1) (q + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (q + n' - 1) / 8) (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the callee, at every FP state *)
Hypothesis FOLD : forall fx0 : YK11.FPState,
  fold_contract (fx := fx0) SEGS B (BASE + AF_fold) SegInstB.STK_fold.
(* the frame chain at s1 (B's m_file_k.v gives it as mf_chain; m_file_iq.v's KCHAIN) *)
Hypothesis KCHAIN : forall v lyc Sc Wc memc mdc pos lowsh mcc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
  exists ch1, achain lyc (rdW Wc memc) (mf_s1 (mv_sp v)) (mv_sp v) ch1.

(* every fact of a cut carried across a memory change inside a window [lo, hi) between the allocator ceiling (with
   room for a block's 8-byte slack) and s1, and inside a window [wlo, whi) of low.i [FB + 32, FB + 96) *)
Lemma fd_keep : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest np S2 W2 mem2 md2 lo hi wlo whi,
  mf_cx B v -> mf_ls v lyc Sc ->
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc np ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc S2 W2 mem2 md2 0 ->
  Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (wlo <= a < whi) -> rdW W2 mem2 a = rdW Wc memc a) ->
  alloc_ceiling + 16 <= lo -> hi <= mf_s1 (mv_sp v) ->
  frame_addr lyc 1 pos + 32 <= wlo -> whi <= frame_addr lyc 1 pos + 96 ->
  mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 W2 cur /\
  mf_loop v W2 mem2 mcc cur line p rest /\ mf_np v mem2 W2 np.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest np S2 W2 mem2 md2 lo hi wlo whi
  CX LS CORE CELLS LOOP NP HJ2 HPm2 K Hlo Hhi Hwlo Hwhi.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _ & _ & _ & _ & _ & Ht0 & HTS & Hsl & HTH & HTA & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & _).
pose proof LS as (Ely & f & ESc).
(* where things lie: the mconf block and the text below the allocator ceiling, each apart from the frame *)
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HFal & _).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
set (F := frame_addr lyc 1 pos) in *.
assert (HF8m : F mod 8 = 0).
{ replace F with ((F / 32) * 4 * 8) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia). apply Z.mod_mul. lia. }
destruct HCH as (bc & mc0 & Hinc & Hbc & Hec).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc0 HAR0 Hinc) as (_ & Hbc4096 & Hbcceil & _ & _ & _ & Hmc0).
pose proof (req_size_pos mc0 ltac:(lia)) as [_ Hrc].
assert (Hinc2 : In (bc, mc0) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPm)); exact Hinc).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc0 1 pos HAR Hinc2 Hfin) as HSc.
destruct HTH as (bt & mt0 & Hint & Hbt & Het).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt0 HAR0 Hint) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt0).
pose proof (req_size_pos mt0 ltac:(lia)) as [_ Hrt].
assert (Hint2 : In (bt, mt0) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPm)); exact Hint).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bt mt0 1 pos HAR Hint2 Hfin) as HSt.
unfold zdisjoint in HSc, HSt. cbn [fst snd] in HSc, HSt. change (fs_frame_bytes 1) with 128 in HSc, HSt.
assert (HF8 : 0 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
assert (Hhi64 : hi <= 2 ^ 47) by (destruct Hs1 as [E | E]; rewrite E in Hhi; lia).
assert (Hs1lo : alloc_ceiling <= mf_s1 (mv_sp v)) by (destruct Hs1 as [E | E]; rewrite E; lia).
(* the low.i window lies in app memory: below the shadow band or above it *)
assert (Happ : whi <= SHADOW_OFF \/ kHighMemBeg <= wlo).
{ unfold in_app, kLowShadowBeg in HFapp. unfold SHADOW_OFF. lia. }
(* four views of the change *)
assert (Kb : forall x, 0 <= x < alloc_ceiling + 16 -> ~ (wlo <= x < whi) -> rdW W2 mem2 x = rdW Wc memc x)
  by (intros x Hx Hw; apply K; lia).
assert (Ku : forall x, mf_s1 (mv_sp v) <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW Wc memc x)
  by (intros x Hx; apply K; lia).
assert (Ks : forall x, SHADOW_OFF <= x < kHighMemBeg -> rdW W2 mem2 x = rdW Wc memc x)
  by (intros x Hx; apply K; unfold SHADOW_OFF in *; lia).
(* the bytes [x0, x0 + n0 + 8) of a heap block apart from the frame are outside the low.i window *)
assert (Kblk : forall b m x, (b + req_size m <= F \/ F + 128 <= b) -> b <= x -> x < b + req_size m + 8 ->
  ~ (wlo <= x < whi)) by (intros; lia).
pose proof LOOP as (L1 & L2 & L3 & LSTR & LADDR & L6).
pose proof LSTR as ((LZ & _) & _).
assert (Hplen : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hp0 : 0 <= p) by (destruct LADDR as (H0 & _); exact H0).
assert (Htp : mv_t v <= p) by (rewrite L3; lia).
split; [|split; [|split]].
- unfold mf_core. fold F. split; [exact HJ2|]. split; [exact (perm_trans HPm2 HPm)|].
  split; [apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Kb; lia | exact VFL]|].
  assert (HF8' : F / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; lia).
  split; [intros i Hi; apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ks; unfold SHADOW_OFF in *; lia | exact (VSH i Hi)]|].
  split; [intros j r Hj; apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku | exact (VSV j r Hj)]|].
  { assert (Hjl : (j < 13)%nat) by (change 13%nat with (length mf_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
    cbn [Z.of_nat] in Hx. lia. }
  split; [apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | exact V120]|].
  split; [apply (iq_mconf_keep (rdW Wc memc)); [intros x Hx; apply Kb; [unfold seg_spec.SEG_M_SIZE in *; lia | apply (Kblk bc mc0); unfold seg_spec.SEG_M_SIZE in *; lia] | exact HMC]|].
  split; [exact (fd_addr_keep (rdW Wc memc) _ _ _ Ks HMA)|].
  apply (iq_tail_keep (rdW Wc memc)); [|exact HMT]. intros x Hx.
  pose proof (Z.mod_pos_bound (mv_c v + seg_spec.SEG_M_SIZE - 1) 8 ltac:(lia)).
  apply Kb; [unfold seg_spec.SEG_M_SIZE in *; lia | apply (Kblk bc mc0); unfold seg_spec.SEG_M_SIZE in *; lia].
- unfold mf_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | assumption]).
- split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
  + apply (iq_str_keep (rdW Wc memc)); [|exact LSTR]. intros x Hx.
    apply Kb; [lia | apply (Kblk bt mt0); lia].
  + split; [exact (fd_addr_keep (rdW Wc memc) _ _ _ Ks LADDR) | exact L6].
- unfold mf_np, mf_slot in *. apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | exact NP].
Qed.

(* fold from its entry, out = low = FB + 32 with low.i in scope and 1 <= cap <= 64: a0 = k = length (fold_out l
   cap) at BASE + ret, out's k + 1 bytes the folded text and its NUL, every cut fact kept *)
Lemma mf_fold_call : forall v lyc Sc Wc (regsc : bvmap 5 word) memc mdc pos (mcc : mconf) (cur : option nat)
  (line p : Z) (rest : list Z) (np ret s n cap : Z) (l : list byte),
  mf_cx B v -> mf_ls v lyc Sc ->
  mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc np ->
  getr regsc 2 = w64 (mf_s1 (mv_sp v)) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 8 = w64 (mv_sp v) ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  getr regsc 10 = w64 s -> getr regsc 11 = w64 n -> getr regsc 12 = w64 (frame_addr lyc 1 pos + 32) ->
  getr regsc 13 = w64 cap -> 1 <= cap <= 64 ->
  s <> 0 -> sa_bytes (rdW Wc memc) s l -> Z.of_nat (length l) = n -> sa_addr (rdW Wc memc) s n ->
  sa_heap B lyc Sc s n ->
  (forall S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    wle Wc W2 -> mf_ls v lyc S2 ->
    mf_core B v lyc S2 W2 mem2 md2 pos MF_LOW_ON mcc -> mf_cells v lyc pos mem2 W2 cur ->
    mf_loop v W2 mem2 mcc cur line p rest -> mf_np v mem2 W2 np ->
    aregs_preserved regsc regs2 -> getr regs2 10 = w64 (Z.of_nat (length (fold_out l cap))) ->
    sa_bytes (rdW W2 mem2) (frame_addr lyc 1 pos + 32) (seg_spec.zb (fold_out l cap ++ [0])) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - SegInstB.STK_fold <= a < mf_s1 (mv_sp v)) ->
     ~ (frame_addr lyc 1 pos + 32 <= a < frame_addr lyc 1 pos + 32 + Z.of_nat (length (fold_out l cap)) + 1) ->
     rdW W2 mem2 a = rdW Wc memc a) ->
    SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fold)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros v lyc Sc Wc regsc memc mdc pos mcc cur line p rest np ret s n cap l
  CX LS CORE CELLS LOOP NP R2 R3 R4 R8 R1 Hret Hret2 R10 R11 R12 R13 Hcap Hs0 HSB HLEN HSA HSH KC.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
pose proof CORE as (HJ & HPm & _).
pose proof HJ as (HAR & Hly & _ & Hwle & _ & Hfrs & Hnev & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & Ho16).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity).
assert (HSTK1 : SegInstB.STK_fold = 16) by (vm_compute; reflexivity).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
set (sp0 := mv_sp v) in *.
set (F := frame_addr lyc 1 pos) in *.
set (k := Z.of_nat (length (fold_out l cap))).
assert (Hk : k = Z.min n (cap - 1)) by (unfold k; rewrite (fold_out_length l cap ltac:(lia)), HLEN; reflexivity).
assert (Hkn : (length (fold_out l cap) <= length l)%nat) by (unfold k in Hk; lia).
assert (Hsp : spZ regsc = sp0 + (mf_s1 sp0 - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
destruct (KCHAIN v lyc Sc Wc memc mdc pos MF_LOW_ON mcc CX CORE) as (ch1 & HCH).
assert (Hs64 : 0 <= s < 2 ^ 64) by (destruct HSA as (A0 & A1 & _); lia).
assert (Hn64 : 0 <= n < 2 ^ 64) by (destruct HSA as (A0 & A1 & _); lia).
assert (HF64 : 0 <= F + 32 < 2 ^ 64) by lia.
assert (Hc64 : 0 <= cap < 2 ^ 64) by lia.
(* low.i's first k + 1 bytes: addressable, in the live frame (1, pos) *)
destruct (mf_low_addr B v lyc Sc Wc memc mdc pos mcc (k + 1) CORE ltac:(lia)) as (HLRA & HLFF).
(* s's k bytes lie in a heap block, apart from the frame *)
assert (HDJ : sa_disj s k (F + 32) (k + 1)).
{ destruct HSH as (b & m & Hbm & Hb1 & Hb2).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 1 pos HAR Hbm Hfin) as Hsep.
  pose proof (req_size_pos m) as Hrq.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm) as (_ & _ & _ & _ & _ & _ & Hm0).
  specialize (Hrq ltac:(lia)). destruct Hrq as [_ Hrq].
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. change (fs_frame_bytes 1) with 128 in Hsep.
  unfold sa_disj. lia. }
assert (HPRE1 : fold_pre SEGS B lyc Sc Wc memc s n (F + 32) cap l).
{ split; [|split].
  - split; [lia|]. split; [exact HLEN|]. split; [intros _; exact Hs0|].
    split; [exact (fd_bytes_firstn _ s l _ HSB)|].
    split; [exact (fd_addr_prefix _ s n k HSA ltac:(lia))|].
    split; [exact HLRA | exact HDJ].
  - left. destruct HSH as (b & m & Hbm & Hb1 & Hb2). exists b, m. split; [exact Hbm|]. lia.
  - exact HLFF. }
eapply SRr_bind.
{ apply (cl_callS_wide B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_fold)) SegInstB.STK_m_file sp0
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdc 0 SegInstB.STK_fold [(F + 32, F + 32 + k + 1)] EV_fold (mf_s1 sp0 - sp0) (Z_to_bv 64 (BASE + ret)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 k /\
       sa_bytes (rdW W2 mem2) (F + 32) (seg_spec.zb (fold_out l cap ++ [0])) /\
       sa_kept SEGS Wc memc W2 mem2 regsc SegInstB.STK_fold (fun a => F + 32 <= a < F + 32 + k + 1) /\
       sa_noalloc B lyc Sc ly2 S2)
    HJ Hsp Ho16).
  - lia.
  - rewrite HSTK1; lia.
  - rewrite HSTK, HSTK1; lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (mf_s1 sp0 - sp0)) with (mf_s1 sp0) by lia.
    unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE2. eapply SRr_mono.
    + apply (FOLD fx lyc Sc Wc regsc memc mdc ch1 s n (F + 32) cap l HPRE2 R10 Hs64 R11 Hn64 R12 HF64 R13 Hc64
        HPRE1).
      unfold EV_fold. unfold EV_m_file in HEV. destruct LS as (_ & f & ESc). rewrite ESc. cbn [st_nev set_fs]. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, R1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - (* the footprint [out, out + k + 1) is m_file's own frame *)
    intros a Ha. apply inFP_cons in Ha. destruct Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)].
    right; right; right; left. exists 1, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
  - (* no footprint byte lies in the caller's stack window *)
    intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. apply inFP_cons in Ha.
    destruct Ha as [Ha | Ha]; [|destruct (inFP_nil a Ha)]. rewrite HSTK in Hw. lia. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & HBY & HKP & HNA)).
destruct HNA as (HPm3 & -> & (f3 & ->)).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 sp0 - SegInstB.STK_fold <= a < mf_s1 sp0) ->
  ~ (F + 32 <= a < F + 32 + k + 1) -> rdW W3 mem3 a = rdW Wc memc a).
{ intros a Ha Hw He. apply (HKP a Ha); [rewrite Hsp; replace (sp0 + (mf_s1 sp0 - sp0)) with (mf_s1 sp0) by lia; exact Hw | exact He]. }
unfold EV_fold in HJo. rewrite Z.add_0_r in HJo.
pose proof HJi as (_ & _ & _ & Hwle3 & _).
destruct (fd_keep v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur line p rest np (set_fs f3 Sc) W3 mem3 md3
  (mf_s1 sp0 - SegInstB.STK_fold) (mf_s1 sp0) (F + 32) (F + 32 + k + 1) CX LS CORE CELLS LOOP NP HJo HPm3 K3
  ltac:(rewrite HSTK1; destruct Hs1 as [E | E]; rewrite E; lia) (Z.le_refl _) ltac:(lia) ltac:(lia))
  as (CORE3 & CELLS3 & LOOP3 & NP3).
apply (KC (set_fs f3 Sc) W3 regs3 mem3 md3 Hwle3).
- destruct LS as (Ely & f & ESc). split; [exact Ely|]. exists f3. rewrite ESc. apply iq_set_fs_set_fs.
- exact CORE3.
- exact CELLS3.
- exact LOOP3.
- exact NP3.
- exact HP3.
- exact A0.
- exact HBY.
- exact K3.
Qed.
End e.
End f.
End d.
