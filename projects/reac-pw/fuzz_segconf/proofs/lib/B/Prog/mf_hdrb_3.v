(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 277 of its 298 lines of code are new or changed and 497 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3; 0x86140), the segment S_MF_HDRB (HFIND 0x865c0 ->
   TAIL 0x86820): the PREMISES OF ITS CALLEES, from the walk's mid-segment invariant. A walk lane of
   the image-B m_file-family owner's G2B. Statement and proof are about the reader `aview SEGS (w_H Wc) memc` and the journal only: no
   instruction is executed here, no symbolic state.
   ADAPTED from image A's lib/A/Prog/m_file_s_hdrb_3.v (commit d8beabc2758c): the same lemmas;
   image B's numbers where image A's file had its own: the frame 320 (image A 288) and SegInstB.STK_m_file = 8,592
   (hb3_below_win), SegInstB's gotwA / guardA / seg_litA_fz (hb3_refuse_pre), image B's call pcs in the comments.
   The call sites it serves (the neutral listing of m_file in image B):
     0x865c8 `jal m_find(c, name, |name|)`           hb3_find_pre    (m_find_c.v m_find_pre)
     0x86614 / 0x86b48 `jal m_refuse(c, line + 1)`    hb3_refuse_pre  (m_refuse_c.v m_refuse_pre, knock = false;
                                                     the walk calls m_refuse through m_file_rf.v's mf_refuse_step,
                                                     which builds these premises itself)
     0x86b88 `jal checked_memset(g, 0, 256)`        hb3_entry_addr, hb3_entry_wr, hb3_entry_dest
     0x86b98 `jal checked_memcpy(g, name, |name|)`  the same for the destination g, hb3_name_src for the source
   (g = &c->seg[j] = seg_spec.mseg_addr c j, j = c->n < 32; the runtime contract of both is the kit's
   aintrin_realizes, image B's copy lib/B/YG0d.v:331).
   Where each premise comes from (as image A's file):
   - the block c: m_file_pre's c <> 0, c mod 16 = 0 and sa_heap at the entry state, moved to the current state by
     mf_core's Permutation of the live blocks (hb3_heap_now); sa_mconf, sa_addr and sa_tail at the current reader
     from mf_core.
   - the name: the bytes [p + o, p + o + |nm|) of the text left (hb_nm), read from mf_loop's sa_str of the text
     left at the CURRENT reader; its sa_addr from mf_loop's sa_addr of the text left (hb3_addr_sub); its place: the
     text's heap block of m_file_pre, moved by hb3_heap_now (p = t + (|s| - |rest|), o + |nm| <= |rest|).
   - m_refuse's counter and line bounds: mf_loop's line + |rest| <= 65535 with rest <> [] (0 <= line + 1 <= 65536),
     and refused + |rest| < 2 ^ 32 of the model handed to m_refuse.
   - the entry g: inside the block (j < 32, 256 * 32 <= 9236), so mf_core's sa_addr of the block gives its sa_addr;
     its bytes are in M_FILE_FP's first range when j < |seg| of the final model (hb3_fp_seg) and in a live block of
     the current state, which AR keeps present and not owned (al_blocks).
   - the memcpy source is apart from g: m_file_pre's sa_disj of the text's read span (seg_spec.cstr_span) and the
     block; apart from the call's ESTACK window: the text is a heap block (below alloc_ceiling, al_blocks at the
     entry AR) and the window lies above ly_stk_lo + STK_m_file - 336 - ESTACK (afn_pre's astk_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m mf_hdrb_2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Notation MF_STK := SegInstB.STK_m_file.

Ltac hb3_pow := try change (2 ^ 63) with 9223372036854775808 in *; try change (2 ^ 64) with 18446744073709551616 in *;
  try change (2 ^ 32) with 4294967296 in *.
Ltac hb3_seg := unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE in *.

(* ================================== list facts ================================== *)
(* the line is a prefix of the text left *)
Lemma hb3_line_len : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
intros rest. unfold mf_line. induction rest as [|b r IH]; [cbn; lia|]. cbn [break_nl].
match goal with |- context [if ?c then _ else _] => destruct c end; [cbn; lia|].
destruct (break_nl r) as [l q]. cbn [fst length] in *. lia.
Qed.
Lemma hb3_nth_firstn : forall (l : list Z) k i, (i < k)%nat -> nth i (firstn k l) 0 = nth i l 0.
Proof.
induction l as [|x l IH]; intros k i Hi; destruct k as [|k].
- lia.
- destruct i; reflexivity.
- lia.
- cbn [firstn]. destruct i as [|i]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma hb3_nth_skipn : forall (l : list Z) o i, nth i (skipn o l) 0 = nth (o + i) l 0.
Proof.
induction l as [|x l IH]; intros o i; destruct o as [|o].
- reflexivity.
- cbn [skipn]. destruct i; reflexivity.
- reflexivity.
- cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma hb3_in_fs : forall (l : list Z) o k z, In z (firstn k (skipn o l)) -> In z l.
Proof.
intros l o k z Iz. rewrite <- (firstn_skipn o l). apply in_or_app. right.
rewrite <- (firstn_skipn k (skipn o l)). apply in_or_app. left. exact Iz.
Qed.

(* ================================== A. reader helpers ================================== *)
(* 4. sa_addr of a sub-range: all five conjuncts (the shadow hull of a sub-range lies in the whole range's) *)
Lemma hb3_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> 0 <= n' -> q' + n' <= q + n ->
sa_addr rd q' n'.
Proof.
intros rd q n q' n' (H0 & H63 & HM & HRA & HSV) Hq Hn' Hqn.
split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
- intros x Hx. apply HRA. lia.
- intros Hpos. assert (Hn : 0 < n) by lia. specialize (HSV Hn). intros s Hs. apply HSV.
  assert (M : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8).
  { intros x y Hxy. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
    unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  pose proof (M q q' Hq). pose proof (M (q' + n' - 1) (q + n - 1) ltac:(lia)). lia.
Qed.

(* 11 (its inFP side). The bytes of seg[i], i < |seg| of mcf, are in M_FILE_FP's first range [c, &c->seg[|seg|]).
   The statement of mf_hdrb_1.v's hb_fp_seg (image A's file kept its own copy; so does this one). *)
Lemma hb3_fp_seg : forall c k0 mcf i a, (i < length (mc_seg mcf))%nat ->
seg_spec.mseg_addr c i <= a < seg_spec.mseg_addr c i + 256 -> inFP (M_FILE_FP c k0 mcf) a.
Proof.
intros c k0 mcf i a Hi Ha. unfold inFP. exists (c, seg_spec.mseg_addr c (length (mc_seg mcf))).
split; [unfold M_FILE_FP; left; reflexivity|]. cbn [fst snd]. hb3_seg. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* 1. every byte a reader returns is in [0, 256) *)
Lemma hb3_str_bytes : forall (Wc : world SEGS) memc a z, rdW Wc memc a = Some z -> 0 <= z < 256.
Proof. intros Wc memc a z E. exact (sa_aview_rng _ _ _ _ _ E). Qed.

(* 2. the bytes of a C string read through a reader: bytes, no NUL *)
Lemma hb3_rest_bytes : forall (Wc : world SEGS) memc p rest, sa_str (rdW Wc memc) p rest ->
Forall (fun x => 0 <= x < 256) rest /\ ~ In 0 rest.
Proof.
intros Wc memc p rest [[Hzs Hn0] _]. split; [|exact Hn0].
apply Forall_forall. intros z Iz. destruct (In_nth rest z 0 Iz) as [i [Hi Hn]].
assert (Hi' : (i < length (rest ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hzs i Hi') as E. rewrite app_nth1 in E by exact Hi. rewrite Hn in E.
exact (hb3_str_bytes _ _ _ _ E).
Qed.

(* 3. the k bytes at offset o of a C string, as the byte list a runtime contract takes *)
Lemma hb3_sub_bytes : forall (Wc : world SEGS) memc p rest o k, sa_str (rdW Wc memc) p rest ->
(o + k <= length rest)%nat ->
sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn k (skipn o rest))) /\
seg_spec.zs (seg_spec.zb (firstn k (skipn o rest))) = firstn k (skipn o rest).
Proof.
intros Wc memc p rest o k HS Hk.
pose proof (hb3_rest_bytes Wc memc p rest HS) as [HF _].
assert (HFk : Forall (fun x => 0 <= x < 256) (firstn k (skipn o rest))).
{ rewrite Forall_forall in HF |- *. intros z Iz. exact (HF z (hb3_in_fs rest o k z Iz)). }
split; [|exact (sa_zs_zb _ HFk)].
destruct HS as [[Hzs _] _].
assert (Hlen : length (firstn k (skipn o rest)) = k) by (rewrite length_firstn, length_skipn; lia).
intros i Hi. unfold seg_spec.zb in Hi |- *. rewrite length_map, Hlen in Hi.
unfold ZB0. rewrite (map_nth (Z_to_bv 8) (firstn k (skipn o rest)) 0 i).
rewrite (hb3_nth_firstn _ k i Hi), hb3_nth_skipn.
assert (Hoi : (o + i < length rest)%nat) by lia.
assert (Hi' : (o + i < length (rest ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
pose proof (Hzs (o + i)%nat Hi') as E. rewrite app_nth1 in E by exact Hoi.
replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia. rewrite E. f_equal.
pose proof (hb3_str_bytes _ _ _ _ E) as R.
rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ============================ B. where the objects lie, mid-segment ============================ *)
(* 6. a heap range of the entry state is a heap range of the current state (mf_core's Permutation) *)
Lemma hb3_heap_now : forall v lyc Sc Wc memc mdc pos lowsh mcc q n,
mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> sa_heap B (mv_ly v) (mv_S v) q n -> sa_heap B lyc Sc q n.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc q n HC (b & m & Hin & H1 & H2).
destruct HC as (_ & HP & _). exists b, m. split; [|lia].
eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hin].
Qed.

(* 7. every byte of the block c is in a live block of the current state *)
Lemma hb3_blk_in : forall v lyc Sc Wc memc mdc pos lowsh mcc a,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE ->
exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc a HCX HC Ha.
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & HHc & _).
destruct (hb3_heap_now _ _ _ _ _ _ _ _ _ _ _ HC HHc) as (b & m & Hin & H1 & H2).
exists b, m. split; [exact Hin|]. unfold req_size. hb3_seg. destruct (Z.eqb_spec m 0); lia.
Qed.

(* ============================ C. m_find's premises (0x865c8) ============================
   a0 = c, a1 = p + o (the name), a2 = |nm|; l = zb nm, whose zs is nm *)
Lemma hb3_find_pre : forall v lyc Sc Wc memc mdc pos mcc cur line p rest o nm,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_loop v Wc memc mcc cur line p rest ->
hb_nm rest o nm ->
m_find_pre SEGS B lyc Sc (rdW Wc memc) (mv_c v) (p + Z.of_nat o) (Z.of_nat (length nm)) mcc (seg_spec.zb nm) /\
seg_spec.zs (seg_spec.zb nm) = nm /\ 0 <= p + Z.of_nat o < 2 ^ 64 /\ 0 <= Z.of_nat (length nm) < 2 ^ 64.
Proof.
intros v lyc Sc Wc memc mdc pos mcc cur line p rest o nm HCX HC HL HN.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (Hc0 & Hc16 & _ & HHc & _ & _ & _ & _ & _ & _ & _ & _ & HHt & HAt & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & HMC & HAD & _).
destruct HL as (HLl & _ & HLp & HLstr & HLad & _).
destruct HN as (Hnm & Hon & Hfs).
pose proof (hb3_line_len rest) as Hll.
destruct (hb3_sub_bytes Wc memc p rest o (length nm) HLstr ltac:(lia)) as [HB HZ].
rewrite Hfs in HB, HZ.
destruct HAt as (Ht0 & Ht63 & _).
split; [|split; [exact HZ|]].
- unfold m_find_pre.
  split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HMC|].
  split; [exact (hb3_heap_now _ _ _ _ _ _ _ _ _ _ _ HC HHc)|]. split; [exact HAD|].
  split; [exact HB|]. split; [unfold seg_spec.zb; rewrite length_map; reflexivity|].
  split; [apply (hb3_addr_sub _ p (Z.of_nat (length rest) + 1)); [exact HLad | lia | lia | lia]|].
  left. apply (hb3_heap_now _ _ _ _ _ _ _ _ _ _ _ HC).
  destruct HHt as (b & m & Hin & H1 & H2). exists b, m. split; [exact Hin|]. lia.
- hb3_pow. lia.
Qed.

(* ============================ D. m_refuse's premises (0x86614, 0x86b48) ============================
   a0 = c, a1 = line + 1, knock = false. mf_loop is of the model mc0 the segment started from (its text facts at
   the current reader); the counter premise is of the model mcc handed to m_refuse: on both paths of this segment
   that is the model NOT yet refused (the found path: mcc = mc0; the overflow path: mcc = mc0 with overflow + 1),
   so the caller has `mc_refused mcc + |rest| < 2 ^ 32` from mf_loop of mc0. (`mc_refused mcc <= mc_refused mc0 + 1`
   does not give `mc_refused mcc + 1 < 2 ^ 32` when |rest| = 1.) The two facts sa_ssp and the literals are of the
   current reader (a keep lemma gives them). *)
Lemma hb3_refuse_pre : forall v lyc Sc Wc memc mdc pos (mc0 mcc : mconf) cur line p rest,
mf_cx B v -> sa_frm0 -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc ->
mf_loop v Wc memc mc0 cur line p rest -> rest <> [] ->
mc_refused mcc + Z.of_nat (length rest) < 2 ^ 32 ->
sa_ssp (rdW Wc memc) SegInstB.gotwA SegInstB.guardA ->
(forall x, In x M_FILE_LITS -> sa_lit SEGS B (rdW Wc memc) (SegInstB.seg_litA_fz x) x) ->
m_refuse_pre SEGS B lyc Sc (rdW Wc memc) SegInstB.seg_litA_fz SegInstB.gotwA SegInstB.guardA (mv_c v) (line + 1)
  mcc false.
Proof.
intros v lyc Sc Wc memc mdc pos mc0 mcc cur line p rest HCX HFRM HC HL Hne Href HSSP HLITS.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (Hc0 & Hc16 & _ & HHc & _).
pose proof HC as (_ & _ & _ & _ & _ & _ & HMC & HAD & HTL).
destruct HL as (_ & _ & _ & _ & _ & _ & _ & HL0 & HLline & _).
assert (Hr1 : (1 <= length rest)%nat) by (destruct rest; [exfalso; apply Hne; reflexivity | cbn [length]; lia]).
unfold m_refuse_pre.
split; [exact Hc0|]. split; [exact Hc16|]. split; [exact (hb3_heap_now _ _ _ _ _ _ _ _ _ _ _ HC HHc)|].
split; [exact HAD|]. split; [exact HMC|]. split; [exact HTL|].
split; [lia|]. split; [hb3_pow; lia|]. split; [exact HFRM|]. split; [exact HSSP|].
intros x Hx. apply HLITS. unfold M_REFUSE_LITS in Hx. cbn [In] in Hx. unfold M_FILE_LITS.
destruct Hx as [<- | [<- | []]]; [do 11 right; left; reflexivity | do 12 right; left; reflexivity].
Qed.

(* ===================== E. the checked memset / memcpy of a new entry (0x86b88, 0x86b98) =====================
   d = g = &c->seg[j], n = 256 (memset) or |nm| (memcpy) *)
(* 10. the destination's address facts (aintrin_realizes's d conjuncts, n = 256; a smaller n by hb3_addr_sub) *)
Lemma hb3_entry_addr : forall v lyc Sc Wc memc mdc pos lowsh mcc j,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> (j < 32)%nat ->
0 <= seg_spec.mseg_addr (mv_c v) j /\ seg_spec.mseg_addr (mv_c v) j + 256 <= 2 ^ 63 /\
amem_range (seg_spec.mseg_addr (mv_c v) j) 256 /\
range_addressable (rdW Wc memc) SHADOW_OFF (seg_spec.mseg_addr (mv_c v) j) 256 /\
shadow_hull_vis (rdW Wc memc) (seg_spec.mseg_addr (mv_c v) j) 256.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc j _ HC Hj.
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & HAD & _).
assert (HS : sa_addr (rdW Wc memc) (seg_spec.mseg_addr (mv_c v) j) 256).
{ apply (hb3_addr_sub _ (mv_c v) seg_spec.SEG_M_SIZE); [exact HAD | | | ]; hb3_seg; lia. }
destruct HS as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. apply A5. lia.
Qed.

(* 11. a byte of the new entry is one the walk may write (awr_byte's second arm: in the footprint and in a live
   block) and is writable. (j < 32) is the path's test (0x86b1c `blt a0,a3`, a3 = 32; MFB_RMSET_stmt's
   `length (mc_seg mcc) < 32`): it puts the entry inside the block. *)
Lemma hb3_entry_wr : forall v lyc Sc Wc memc mdc pos lowsh mcc j a,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc ->
(j < length (mc_seg (mf_final v)))%nat -> (j < 32)%nat ->
seg_spec.mseg_addr (mv_c v) j <= a < seg_spec.mseg_addr (mv_c v) j + 256 ->
awr_byte SEGS B MF_STK (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (ablocks B (mv_ly v) (mv_S v))
  (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a /\
writable_at SEGS (mrestrict (w_H Wc) memc) a.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc j a HCX HC Hjl Hj Ha.
assert (Hblk : exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n).
{ apply (hb3_blk_in v lyc Sc Wc memc mdc pos lowsh mcc a HCX HC). hb3_seg. lia. }
split.
- unfold awr_byte. right; left. split; [exact (hb3_fp_seg (mv_c v) (mv_k0 v) (mf_final v) j a Hjl Ha)|].
  exact Hblk.
- destruct Hblk as (b & n & Hin & Hr). pose proof HC as (HJ & _). destruct HJ as (HAR & _).
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b n HAR Hin) as (_ & _ & _ & _ & Hb & _).
  destruct (Hb a Hr) as [Hp _]. eapply YCbq.apresent_writable. exact Hp.
Qed.

(* the stack window of a call made at sp = s1 lies above every heap byte *)
Lemma hb3_below_win : forall v (regsT : bvmap 5 word) b m a,
mf_cx B v -> spZ regsT = mf_s1 (mv_sp v) -> In (b, m) (ablocks B (mv_ly v) (mv_S v)) -> b <= a < b + req_size m ->
~ (spZ regsT - ESTACK <= a < spZ regsT).
Proof.
intros v regsT b m a HCX Hsp Hin Ha.
pose proof HCX as (HPRE & _). destruct HPRE as (HAR0 & _ & _ & _ & _ & HSTK & _).
destruct HSTK as (Hal16 & _ & Hceil & Hlo & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hin) as (_ & _ & Hbc & _).
unfold mf_s1, mv_sp in Hsp.
pose proof (Z.mod_pos_bound (spZ (mv_regs v) - 320) 32 ltac:(lia)).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hlo.
unfold ESTACK in *. lia.
Qed.

(* the same at the current state, for a block of the current state (mf_core's Permutation) *)
Lemma hb3_below_win_now : forall v lyc Sc Wc memc mdc pos lowsh mcc (regsT : bvmap 5 word) b m a,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> spZ regsT = mf_s1 (mv_sp v) ->
In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m ->
~ (spZ regsT - ESTACK <= a < spZ regsT).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc regsT b m a HCX HC Hsp Hin Ha.
pose proof HC as (_ & HP & _).
assert (Hin0 : In (b, m) (ablocks B (mv_ly v) (mv_S v))) by (eapply Permutation_in; [exact HP | exact Hin]).
exact (hb3_below_win v regsT b m a HCX Hsp Hin0 Ha).
Qed.

(* the destination's dest_ok (aintrin_realizes's d conjunct) at the call: the state is the current one, the call's
   sp is s1 *)
Lemma hb3_entry_dest : forall v lyc Sc Wc memc mdc pos lowsh mcc j n (regsT : bvmap 5 word),
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> (j < 32)%nat -> 0 <= n <= 256 ->
spZ regsT = mf_s1 (mv_sp v) ->
dest_ok SEGS B lyc Sc Wc regsT memc (seg_spec.mseg_addr (mv_c v) j) n.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc j n regsT HCX HC Hj Hn Hsp. unfold dest_ok. intros a Ha.
destruct (hb3_blk_in v lyc Sc Wc memc mdc pos lowsh mcc a HCX HC ltac:(hb3_seg; lia)) as (b & m & Hin & Hr).
pose proof HC as (HJ & _). destruct HJ as (HAR & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hin) as (_ & _ & _ & _ & Hb & _).
destruct (Hb a Hr) as [Hp Ho].
split; [eapply YCbq.apresent_writable; exact Hp|]. split; [exact Ho|].
exact (hb3_below_win_now v lyc Sc Wc memc mdc pos lowsh mcc regsT b m a HCX HC Hsp Hin Hr).
Qed.

(* 12. the memcpy source x = p + o, n = |nm|, at d = &c->seg[j]: aintrin_realizes OCpy's x conjunct. mf_loop is of
   any model mcl (its text facts are what is used); src_ok at the call's register bank regsT, whose sp is s1. *)
Lemma hb3_name_src : forall v lyc Sc Wc memc mdc pos lowsh mcc (mcl : mconf) line cur p rest o nm j
  (regsT : bvmap 5 word),
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcl cur line p rest ->
hb_nm rest o nm -> (j < 32)%nat -> spZ regsT = mf_s1 (mv_sp v) ->
0 <= p + Z.of_nat o /\ p + Z.of_nat o + Z.of_nat (length nm) <= 2 ^ 63 /\
src_ok SEGS Wc regsT memc (p + Z.of_nat o) (Z.of_nat (length nm)) /\
(seg_spec.mseg_addr (mv_c v) j + Z.of_nat (length nm) <= p + Z.of_nat o \/
 p + Z.of_nat o + Z.of_nat (length nm) <= seg_spec.mseg_addr (mv_c v) j) /\
amem_range (p + Z.of_nat o) (Z.of_nat (length nm)) /\
range_addressable (rdW Wc memc) SHADOW_OFF (p + Z.of_nat o) (Z.of_nat (length nm)) /\
(0 < Z.of_nat (length nm) -> shadow_hull_vis (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat (length nm))).
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc mcl line cur p rest o nm j regsT HCX HC HL HN Hj Hsp.
pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
destruct HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHt & HAt & _ & HDJ & _).
destruct HL as (HLl & _ & HLp & HLstr & HLad & _).
destruct HN as (Hnm & Hon & Hfs).
pose proof (hb3_line_len rest) as Hll.
pose proof HAt as (Ht0 & Ht63 & _).
destruct (hb3_addr_sub _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat o) (Z.of_nat (length nm)) HLad
  ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & HM & HRA & HSV).
split; [lia|]. split; [lia|]. split; [|split; [|split; [exact HM | split; [exact HRA | exact HSV]]]].
- unfold src_ok. intros a Ha. split.
  + destruct HLstr as [[Hzs _] _].
    assert (Hk : (Z.to_nat (a - p) < length (rest ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    pose proof (Hzs _ Hk) as E. rewrite Z2Nat.id in E by lia.
    replace (p + (a - p)) with a in E by lia. rewrite E. discriminate.
  + destruct HHt as (b & m & Hin & H1 & H2).
    apply (hb3_below_win v regsT b m a HCX Hsp Hin).
    assert (m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- unfold sa_disj, seg_spec.cstr_span in HDJ.
  match type of HDJ with context [?X mod 8] => pose proof (Z.mod_pos_bound X 8 ltac:(lia)) end.
  hb3_seg. lia.
Qed.

End e.
End f.
End d.

Print Assumptions hb3_find_pre.
Print Assumptions hb3_refuse_pre.
Print Assumptions hb3_entry_addr.
Print Assumptions hb3_entry_wr.
Print Assumptions hb3_entry_dest.
Print Assumptions hb3_name_src.
