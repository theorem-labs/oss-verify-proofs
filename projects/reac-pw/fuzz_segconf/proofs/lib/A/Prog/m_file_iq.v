(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 239 of its 274 lines of code are new or changed and 219 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the ONE shared ieq call step of the m_file segment walks (ruling
   of the m_file cut-statement lane, writer of m_file_m.v, 2026-10-30 17:0xZ), stated over m_file_m.v's cut predicates. The KIGNP segment lane
   of the G2 walk owner's G2. proves no function (kind: segment lemma of m_file's walk: the call step of ieq).

   mf_ieq_call: a call of ieq (0x87904; m_file's sites 0x864b0 S_segment, 0x86694 S_role, 0x867c8 S_model, 0x8694c
   S_ignore, 0x86964 S_yes, 0x86980 S_true, 0x869c0 S_no, 0x869d8 S_false, 0x86b30 S_knock; MF-CUTS-A.md section 4),
   from the state at ieq's entry (the `jal` executed: pc = BASE + AF_ieq, ra = BASE + ret, a0 = s the n bytes l of
   the text left, a1 = n, a2 = the literal seg_litA_fz x, sp = s1): ieq_contract (lib/A/Prog/ieq_c.v, at
   SegInstA.STK_ieq) taken through PaCall.cl_callS; ieq's post is apost_base, so the walk goes on at BASE + ret at the
   SAME FP state, with a0 = b2z (ieq (zs l) x) and every cut fact kept: ieq writes only its own stack window
   [s1 - STK_ieq, s1) (its sa_kept), which lies above the allocator ceiling, above every heap block, frame and
   shadow byte, and below s1, under every spill slot and saved register.
   The callee's afn_pre comes from the walk's journal (PaCall.afn_pre_at inside cl_callS) with the frame chain at s1
   and s0 = sp0 (m_file's own record: the entry's ra at sp0 - 8, its s0 at sp0 - 16).
   Section hypotheses: the shared list of the m_file cut-statement lane's ruling (a) as amended 17:1xZ (LAWS a Let; TL, TLF, VOBJS,
   SIGP, SSP, RELRO, RO) and ieq_contract at its listing entry, at every FP state. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaFx SegPgBase SegBase SegObj SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_k ieq_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the literals m_file hands to ieq are short (strlen's range check asks |w| + 1 < 2 ^ 32) *)
Lemma iq_lits_short : forall x, In x M_FILE_LITS -> (length x < 16)%nat.
Proof.
intros x Hx. unfold M_FILE_LITS in Hx.
repeat (destruct Hx as [<- | Hx]; [vm_compute; lia|]). destruct Hx.
Qed.

(* s1 = (sp0 - 288) & -32 lies 288 or 304 bytes below the 16-aligned sp0 *)
Lemma iq_s1 : forall sp0, sp0 mod 16 = 0 ->
  (mf_s1 sp0 = sp0 - 288 \/ mf_s1 sp0 = sp0 - 304) /\ (mf_s1 sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H16. unfold mf_s1.
pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (sp0 - 288) 32 ltac:(lia)) as Hd. pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16.
assert (E : (sp0 - 288) mod 32 = 0 \/ (sp0 - 288) mod 32 = 16) by lia.
destruct E as [E | E]; rewrite E; split.
- left; lia.
- replace (sp0 - 288 - 0 - sp0) with (-18 * 16) by lia. apply Z_mod_mult.
- right; lia.
- replace (sp0 - 288 - 16 - sp0) with (-19 * 16) by lia. apply Z_mod_mult.
Qed.

Lemma iq_set_fs_set_fs : forall f g S, set_fs f (set_fs g S) = set_fs f S.
Proof. intros f g S. destruct S. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* ===================================== reader transports ===================================== *)
(* a fact about a few bytes carried to a memory the reader agrees with on them *)
Lemma iq_val_keep : forall (W W' : world SEGS) m m' a (n : nat) val,
  (forall x, a <= x < a + Z.of_nat n -> rdW W' m' x = rdW W m x) ->
  val_mem SEGS (mrestrict (w_H W) m) a n val -> val_mem SEGS (mrestrict (w_H W') m') a n val.
Proof.
intros W W' m m' a n val K Hv k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k) (K (a + Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
Lemma iq_bytes_keep : forall (rd rd' : reader) a (l : list byte),
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof. intros rd rd' a l K H i Hi. rewrite (K (a + Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma iq_zs_keep : forall (rd rd' : reader) a (l : list Z),
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l K H i Hi. rewrite (K (a + Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma iq_tail_keep : forall (rd rd' : reader) e,
  (forall x, e < x < e - e mod 8 + 8 -> rd' x = rd x) -> sa_tail rd e -> sa_tail rd' e.
Proof. intros rd rd' e K H x Hx. rewrite (K x Hx). exact (H x Hx). Qed.
Lemma iq_str_keep : forall (rd rd' : reader) p (s : list Z),
  (forall x, p <= x < p + Z.of_nat (length s) + 8 -> rd' x = rd x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s K ((HZ & HN) & HT). split; [split; [|exact HN]|].
- apply (iq_zs_keep rd); [|exact HZ]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply K. lia.
- apply (iq_tail_keep rd); [|exact HT]. intros x Hx.
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)). apply K. lia.
Qed.
Lemma iq_mconf_keep : forall (rd rd' : reader) c mc,
  (forall x, c <= x < c + seg_spec.SEG_M_SIZE -> rd' x = rd x) -> sa_mconf rd c mc -> sa_mconf rd' c mc.
Proof.
intros rd rd' c mc K (bs & HB & HE). exists bs. split; [|exact HE].
apply (iq_bytes_keep rd); [|exact HB]. intros x Hx. apply K.
destruct HE as (HL & _). lia.
Qed.
(* sa_addr of a range below 2 ^ 47, carried across a change inside a window above the shadow band *)
Lemma iq_addr_keep : forall (rd rd' : reader) lo hi q n,
  (forall s, 0 <= s < 2 ^ 64 -> ~ (lo <= s < hi) -> rd' s = rd s) -> kHighShadowEnd <= lo ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros rd rd' lo hi q n K Hlo (H0 & H63 & HAM & HRA & HHV).
assert (H47 : q + n <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; lia).
split; [exact H0|]. split; [exact H63|]. split; [exact HAM|]. split.
- exact (range_addressable_kept_win rd rd' lo hi q n K Hlo H0 H47 HRA).
- intros Hn. exact (shadow_hull_vis_kept_win rd rd' lo hi q n K Hlo H0 H47 Hn (HHV Hn)).
Qed.

Section e.
Variable B : asyms.
(* the shared Section hypotheses (the m_file cut-statement lane's ruling (a), amended 17:1xZ) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis SSP : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Context {RO : ro_below_ofl SEGS SegInstA.RLO_A SegInstA.RHI_A}.
(* the callee, at every FP state *)
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.

(* every fact of a cut carried across a memory change inside a window [lo, hi) between the allocator ceiling (with
   room for a block's 8-byte slack) and s1 *)
Lemma iq_keep : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest np S2 W2 mem2 md2 lo hi,
  mf_cx B v -> mf_ls v lyc Sc ->
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc np ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc S2 W2 mem2 md2 0 ->
  Permutation (ablocks B lyc S2) (ablocks B lyc Sc) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W2 mem2 a = rdW Wc memc a) ->
  alloc_ceiling + 16 <= lo -> hi <= mf_s1 (mv_sp v) ->
  mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc /\ mf_cells v lyc pos mem2 W2 cur /\
  mf_loop v W2 mem2 mcc cur line p rest /\ mf_np v mem2 W2 np.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest np S2 W2 mem2 md2 lo hi
  CX LS CORE CELLS LOOP NP HJ2 HPm2 K Hlo Hhi.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof CORE as (HJ & HPm & VFL & VSH & VSV & V112 & HMC & HMA & HMT).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof HMP as (Hc0 & Hc16 & _ & HCH & _ & _ & _ & _ & _ & Ht0 & HTS & Hsl & HTH & HTA & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & _).
destruct LS as (Ely & f & ESc).
(* where things lie: the mconf block and the text below the allocator ceiling, the frame too *)
destruct HCH as (bc & mc0 & Hinc & Hbc & Hec).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc0 HAR0 Hinc) as (_ & Hbc4096 & Hbcceil & _ & _ & _ & Hmc0).
pose proof (req_size_pos mc0 ltac:(lia)) as [_ Hrc].
destruct HTH as (bt & mt0 & Hint & Hbt & Het).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt0 HAR0 Hint) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt0).
pose proof (req_size_pos mt0 ltac:(lia)) as [_ Hrt].
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HAR Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
assert (HF8 : 0 <= frame_addr lyc 1 pos / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (Hlo' : kHighShadowEnd <= lo) by lia.
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
assert (Hhi64 : hi <= 2 ^ 47) by (destruct Hs1 as [E | E]; rewrite E in Hhi; lia).
assert (Kv : forall x, 0 <= x < alloc_ceiling + 16 -> rdW W2 mem2 x = rdW Wc memc x) by (intros x Hx; apply K; lia).
assert (Hs1lo : alloc_ceiling <= mf_s1 (mv_sp v)) by (destruct Hs1 as [E | E]; rewrite E; lia).
assert (Ku : forall x, mf_s1 (mv_sp v) <= x < 2 ^ 64 -> rdW W2 mem2 x = rdW Wc memc x) by (intros x Hx; apply K; lia).
pose proof LOOP as (L1 & L2 & L3 & LSTR & LADDR & L6).
pose proof LSTR as ((LZ & _) & _).
assert (Hplen : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hp0 : 0 <= p) by (destruct LADDR as (H0 & _); exact H0).
split; [|split; [|split]].
- unfold mf_core. split; [exact HJ2|]. split; [exact (perm_trans HPm2 HPm)|].
  split; [apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Kv; lia | exact VFL]|].
  split; [intros i Hi; apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Kv; unfold SHADOW_OFF in *; lia | exact (VSH i Hi)]|].
  split; [intros j r Hj; apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku | exact (VSV j r Hj)]|].
  { assert (Hjl : (j < 13)%nat) by (change 13%nat with (length mf_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
    cbn [Z.of_nat] in Hx. lia. }
  split; [apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | exact V112]|].
  split; [apply (iq_mconf_keep (rdW Wc memc)); [intros x Hx; apply Kv; unfold seg_spec.SEG_M_SIZE in *; lia | exact HMC]|].
  split; [exact (iq_addr_keep (rdW Wc memc) _ lo hi _ _ K Hlo' HMA)|].
  apply (iq_tail_keep (rdW Wc memc)); [|exact HMT]. intros x Hx.
  pose proof (Z.mod_pos_bound (mv_c v + seg_spec.SEG_M_SIZE - 1) 8 ltac:(lia)). apply Kv.
  unfold seg_spec.SEG_M_SIZE in *. lia.
- unfold mf_cells in *.
  destruct CELLS as (V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V104 & V120 & V128 & V136 & V152).
  repeat split; (apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | assumption]).
- split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split.
  + apply (iq_str_keep (rdW Wc memc)); [|exact LSTR]. intros x Hx. apply Kv.
    unfold seg_spec.cstr_span in *. lia.
  + split; [exact (iq_addr_keep (rdW Wc memc) _ lo hi _ _ K Hlo' LADDR) | exact L6].
- apply (iq_val_keep Wc W2 memc mem2); [intros x Hx; apply Ku; lia | exact NP].
Qed.

(* ieq from its entry with a word of M_FILE_LITS: a0 = b2z (ieq (zs l) x) at BASE + ret, every cut fact kept *)
Lemma mf_ieq_call : forall v lyc Sc Wc (regsc : bvmap 5 word) memc mdc pos lowsh (mcc : mconf) (cur : option nat)
  (line p : Z) (rest : list Z) (np ret s n : Z) (l : list byte) (x : list Z),
  mf_cx B v -> mf_ls v lyc Sc ->
  mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_cells v lyc pos memc Wc cur ->
  mf_loop v Wc memc mcc cur line p rest -> mf_np v memc Wc np ->
  getr regsc 2 = w64 (mf_s1 (mv_sp v)) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 8 = w64 (mv_sp v) ->
  getr regsc 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
  In x M_FILE_LITS ->
  getr regsc 10 = w64 s -> getr regsc 11 = w64 n -> getr regsc 12 = w64 (SegInstA.seg_litA_fz x) ->
  s <> 0 -> sa_bytes (rdW Wc memc) s l -> Z.of_nat (length l) = n -> sa_addr (rdW Wc memc) s n ->
  sa_heap B lyc Sc s n ->
  (forall S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    wle Wc W2 -> mf_ls v lyc S2 ->
    mf_core B v lyc S2 W2 mem2 md2 pos lowsh mcc -> mf_cells v lyc pos mem2 W2 cur ->
    mf_loop v W2 mem2 mcc cur line p rest -> mf_np v mem2 W2 np ->
    aregs_preserved regsc regs2 -> getr regs2 10 = w64 (seg_spec.b2z (ieq (seg_spec.zs l) x)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - SegInstA.STK_ieq <= a < mf_s1 (mv_sp v)) ->
     rdW W2 mem2 a = rdW Wc memc a) ->
    SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_ieq)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros v lyc Sc Wc regsc memc mdc pos lowsh mcc cur line p rest np ret s n l x
  CX LS CORE CELLS LOOP NP R2 R3 R4 R8 R1 Hret Hret2 HX R10 R11 R12 Hs0 HSB HLEN HSA HSH KC.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (mv_regs v)) with (mv_sp v) in Hal16, Hslo, Hshi.
pose proof CORE as (HJ & HPm & _).
pose proof HJ as (HAR & Hly & _ & Hwle & _ & Hfrs & Hnev & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBASE2.
destruct (iq_s1 (mv_sp v) Hal16) as (Hs1 & Ho16).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HSTK1 : SegInstA.STK_ieq = 4144) by reflexivity.
set (sp0 := mv_sp v) in *.
assert (Hsp : spZ regsc = sp0 + (mf_s1 sp0 - sp0)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
destruct (mf_chain B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (ch1 & HCH).
pose proof (mf_rod_now B RELRO v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as HROD.
pose proof (mf_lit_now B v lyc Sc Wc memc mdc pos lowsh mcc x CX CORE HX) as (Hw0 & HWS & HWP & _ & HWI).
pose proof (iq_lits_short x HX) as HXL.
assert (HWA : sa_addr (rdW Wc memc) (SegInstA.seg_litA_fz x) (Z.of_nat (length x) + 1)) by exact (HWP _ _ _ _ _ HAR).
assert (Hw64 : 0 <= SegInstA.seg_litA_fz x < 2 ^ 64) by (destruct HWA as (A0 & A1 & _); lia).
assert (Hs64 : 0 <= s < 2 ^ 64) by (destruct HSA as (A0 & A1 & _); lia).
assert (Hn64 : 0 <= n < 2 ^ 64) by (destruct HSA as (A0 & A1 & _); lia).
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc regsc memc (Z_to_bv 64 (BASE + AF_ieq)) SegInstA.STK_m_file sp0
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)]
    lyc Sc mdc 0 SegInstA.STK_ieq [] EV_ieq (mf_s1 sp0 - sp0) (Z_to_bv 64 (BASE + ret)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (seg_spec.b2z (SegModel.ieq (seg_spec.zs l) x)) /\
       sa_kept SEGS Wc memc W2 mem2 regsc SegInstA.STK_ieq (fun _ => False) /\ sa_noalloc B lyc Sc ly2 S2)
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
  - intros HPRE1. eapply SRr_mono.
    + apply (IEQ fx lyc Sc Wc regsc memc mdc ch1 s n (SegInstA.seg_litA_fz x) l x HPRE1 HROD R10 Hs64 R11 Hn64 R12
        Hw64).
      * split; [exact Hs0|]. split; [exact HSB|]. split; [exact HLEN|]. split; [exact HSA|].
        split; [left; exact HSH|]. split; [lia|]. split; [exact HWS|]. split; [exact HWA|].
        split; [right; right; exact HWI | lia].
      * unfold EV_ieq. unfold EV_m_file in HEV. destruct LS as (_ & f & ESc). rewrite ESc. cbn [st_nev set_fs]. lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, R1; reflexivity|]. split; [exact HJc|].
      split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJo & HJi & HP3 & (A0 & HKP & HNA)).
destruct HNA as (HPm3 & -> & (f3 & ->)).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 sp0 - SegInstA.STK_ieq <= a < mf_s1 sp0) ->
  rdW W3 mem3 a = rdW Wc memc a).
{ intros a Ha Hw. apply (HKP a Ha); [rewrite Hsp; replace (sp0 + (mf_s1 sp0 - sp0)) with (mf_s1 sp0) by lia; exact Hw | intros []]. }
unfold EV_ieq in HJo. rewrite Z.add_0_r in HJo.
pose proof HJi as (_ & _ & _ & Hwle3 & _).
destruct (iq_keep v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest np (set_fs f3 Sc) W3 mem3 md3
  (mf_s1 sp0 - SegInstA.STK_ieq) (mf_s1 sp0) CX LS CORE CELLS LOOP NP HJo HPm3 K3 ltac:(rewrite HSTK1; lia) (Z.le_refl _))
  as (CORE3 & CELLS3 & LOOP3 & NP3).
apply (KC (set_fs f3 Sc) W3 regs3 mem3 md3 Hwle3).
- destruct LS as (Ely & f & ESc). split; [exact Ely|]. exists f3. rewrite ESc. apply iq_set_fs_set_fs.
- exact CORE3.
- exact CELLS3.
- exact LOOP3.
- exact NP3.
- exact HP3.
- exact A0.
- exact K3.
Qed.
End e.
End f.
End d.
