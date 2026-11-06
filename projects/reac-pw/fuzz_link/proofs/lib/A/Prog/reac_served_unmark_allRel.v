(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 330 of its 385 lines of code are new or changed and 1250 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_writeSendA.v, with its module names changed; 564 of its 662 lines of code are new or changed and 287 lines of the source are left out. *)
(* reac_served_unmark_all (fuzz_link.asan 0x89ed4) on image A: THE RELEASE PIECE of its walk, `um_rel_obl` of
   lib/A/Prog/reac_served_unmark_allDefs.v. From the release cut +0x350 (0x8a224) the code
     +0x350..+0x358  stores the retired magic 0x45e0360e at F + 0 (sd a0,0(s9))
     +0x35c          `beqz s3` -> +0x378, not taken: F >= 4096 (the fact on F's atom decides it)
     +0x360..+0x368  meta_fill_f5(F's shadow, 64) (0x55f7c)
     +0x36c..+0x370  `ld a0,0x1f8(s3); sb zero,0(a0)`: the inline release of the frame's flag byte
     +0x374, +0x428..+0x464  `j`; sp := s0 - 0xa0; the thirteen restores from the saves at sp0 - 8 .. sp0 - 104;
                     sp := sp + 0xa0; `ret`
   and this file builds the whole post `um_post` (link_amem.v apost over the caller's journal) from it.

   The runs are the PLAIN gx runs of lib/A/Prog/LinkWalkSide.v (`paj_run_call_plain_x`, `paj_flag_plain_x`):
   the state's writable windows are F's first word and the flag byte. meta_fill_f5 is LinkWalkSide.v's
   `aj_gx_set_shadow_at` over the Section hypothesis `aset_shadow_realizes ... 0xf5` (discharged at the image by
   lib/A/Rt/SetShadow.v `link_set_shadow_f5`); the return is LinkPaLib.v `paj_ret_at`, the post LinkWalkSide.v
   `apost_side_gen`.

   The memory algebra is `um_apost_move`: the cut's Post survives a step that changes only bytes of the side frame,
   its shadow and its flag byte (aside_rng), and keeps the presence of bytes. g_nl's bytes are image bytes
   (`aside_rng_low`), the marks block is a byte of the write set (LinkWalkShadow.v `ajw_not_side`), and the
   interface table's strings are read-set bytes (`akb_not_side`), reached through g_nl's pointer cells, which lie
   outside the write set and outside the runtime's statics (`PcapSyms B`). The byte lemmas um_lb_inj, um_vm_unique,
   um_abytes_move, um_acstr_move, um_acstr_range, um_aiftab_keep follow the exit piece
   (lib/A/Prog/reac_link_alias_writeExit.v, the aw_ lemmas), the run tactic and the state construction follow it and
   libreac/fuzz_pcap's lib/A/Prog/PcapSourceOpenB.v `opb_epi` and PcapFrame.v (origin/ossv/recipes).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m AE7f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkShadow LinkWalkWseg.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro reac_served_unmark_allDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. The symbolic state at the release cut
   Atoms 0..31 are the registers at the cut; 32..44 the thirteen saved words (ra, s0, s1, s2..s11 of the entry);
   45 the frame's flag address (the word at F + 504). s3 = F is atom 19; s9 (25) is given atom 19's value.
   ========================================================================== *)
Definition umr_FR : YP09.region := YP09.mkRegion (Some 19%nat) 0 512 0 8 [YP09.mkChunk 504 (CVal 8 (SOff 45 0))].
Definition umr_FL0 : YP09.region := YP09.mkRegion (Some 45%nat) 0 1 0 0 [].
Definition umr_FL : YP09.region := YP09.mkRegion (Some 45%nat) 0 1 0 1 [].
Definition umr_saves_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13).
Definition umr_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0 umr_saves_chunks.
Definition umr_facts : facts := mkFacts [(19%nat, HPTR 6); (45%nat, HPTR 0)] [] [].
Definition umr_ss0 : sstate := mkSS UM_CUT_REL sr_atoms [umr_FR; umr_FL0; umr_saves] None umr_facts.

(* ==========================================================================
   1. Small helpers
   ========================================================================== *)
Lemma um_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Lemma um_wvb_fds_fs : forall l X m, m_fds (with_vm_backing l X m) = m_fds m /\ m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X []. split; reflexivity. Qed.

Lemma um_sbm_fds_fs : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply um_wvb_fds_fs. Qed.

Lemma um_apresent_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh [b Hb]]. split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply HG; [discriminate | reflexivity]].
Qed.

(* the three byte classes of the side frame (3, fpos), unfolded *)
Lemma um_side_unfold : forall ly fpos a,
  aside_rng ly 3 fpos a <->
  (frame_addr ly 3 fpos <= a < frame_addr ly 3 fpos + 512) \/
  (SHADOW_OFF + frame_addr ly 3 fpos / 8 <= a < SHADOW_OFF + frame_addr ly 3 fpos / 8 + 64) \/
  a = flag_addr ly 3 fpos.
Proof.
intros ly fpos a. unfold aside_rng, in_zr, frame_rng, shadow_addr. cbn [fst snd].
change (fs_frame_bytes 3) with 512. change (512 / 8) with 64. tauto.
Qed.

(* ==========================================================================
   2. Byte algebra (as reac_link_alias_write's exit piece)
   ========================================================================== *)
Section bytes.
Variable segs : list Segment.

Lemma um_lb_inj : forall (n : nat) (p1 p2 : Z),
  (forall k, (k < n)%nat ->
     Z_to_bv 8 (Z.shiftr (p1 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256) =
     Z_to_bv 8 (Z.shiftr (p2 mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256)) ->
  p1 mod 2 ^ (8 * Z.of_nat n) = p2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n p1 p2 H. apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i (8 * Z.of_nat n)) as [Hl|Hl].
  - pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hr.
    set (q := i / 8) in *. set (r := i mod 8) in *. clearbody q r.
    assert (Hq : 0 <= q) by lia.
    assert (Hk : (Z.to_nat q < n)%nat) by lia.
    specialize (H (Z.to_nat q) Hk).
    apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
    change (bv_modulus 8) with 256 in H. rewrite !Z.mod_mod in H by lia.
    rewrite Z2Nat.id in H by exact Hq.
    apply (f_equal (fun z => Z.testbit z r)) in H. cbv beta in H.
    change 256 with (2 ^ 8) in H. rewrite !Z.mod_pow2_bits_low in H by lia.
    rewrite !Z.shiftr_spec in H by lia.
    replace (r + 8 * q) with i in H by lia. exact H.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma um_vm_unique : forall m a (n : nat) v1 v2, val_mem segs m a n v1 -> val_mem segs m a n v2 ->
  v1 mod 2 ^ (8 * Z.of_nat n) = v2 mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v1 v2 H1 H2. apply um_lb_inj. intros k Hk.
  pose proof (eq_trans (eq_sym (H1 k Hk)) (H2 k Hk)) as E.
  exact (f_equal (fun o : option byte => match o with Some b => b | None => Z_to_bv 8 0 end) E).
Qed.

Lemma um_abytes_move : forall (m m' : word -> option byte) a bs,
  abytes segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  abytes segs m' a bs.
Proof.
  intros m m' a bs (Ha & Hl & H) Hk. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. rewrite (Hk (a + Z.of_nat i)) by lia. exact (H i Hi).
Qed.

Lemma um_acstr_move : forall m m' p s, acstr_at segs m p s ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> mbyte segs m' x = mbyte segs m x) -> acstr_at segs m' p s.
Proof.
  intros m m' p s [Bs N] Hk. split; [|exact N]. apply (um_abytes_move m m' p _ Bs).
  intros x Hx. apply Hk. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma um_acstr_range : forall m p s, acstr_at segs m p s -> 0 <= p /\ p + Z.of_nat (length s) + 1 <= 2 ^ 64.
Proof.
  intros m p s [(Ha & Hl & _) _]. rewrite length_app in Hl. cbn [length] in Hl. lia.
Qed.

Lemma um_au8arr_move : forall m m' a bs, au8arr segs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> writable_at segs m' x) -> au8arr segs m' a bs.
Proof.
  intros m m' a bs [U R] Hk Hw. split.
  - exact (um_abytes_move m m' a bs U Hk).
  - intros i Hi. apply Hw. lia.
Qed.

(* the table at m', when its cells are m's and the string each cell names at m is kept *)
Lemma um_aiftab_keep : forall m m' bs bs' tab,
  aiftab_at segs m LA_G_NL bs tab -> nk_n_if bs' = nk_n_if bs ->
  (forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_IF_NAME + 8 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall x, LA_G_NL + NK_IF_INDEX <= x < LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat (length tab) ->
     mbyte segs m' x = mbyte segs m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs m (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> mbyte segs m' x = mbyte segs m x) ->
  aiftab_at segs m' LA_G_NL bs' tab.
Proof.
  intros m m' bs bs' tab (L & L80 & E) Hn DN DI DS.
  split; [rewrite Hn; exact L|]. split; [exact L80|]. intros i n2 ix Hi.
  destruct (E i n2 ix Hi) as (R & p & P & Pz & C & I). split; [exact R|].
  assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  exists p. split; [|split; [exact Pz|split]].
  - unfold au64_at, val_mem in *. intros k Hk.
    rewrite (DN (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i + Z.of_nat k)) by lia. exact (P k Hk).
  - pose proof (um_acstr_range m p n2 C) as Rp.
    apply (um_acstr_move m m' p n2 C). exact (DS i n2 ix p Hi P ltac:(lia)).
  - unfold au32_at, val_mem in *. intros k Hk.
    rewrite (DI (LA_G_NL + NK_IF_INDEX + 4 * Z.of_nat i + Z.of_nat k)) by lia. exact (I k Hk).
Qed.
End bytes.

(* ==========================================================================
   3. The release piece
   ========================================================================== *)
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
Hypothesis LAWS : AR_laws SEGS B.
(* The runtime's symbols of image A: AF0m.v PcapSyms, instance lib/A/AD2l.v PcapB_syms. Used for the runtime's
   statics (ts_owned), to place g_nl's interface-table cells outside them, and by LinkWalkShadow.v. *)
Hypothesis TB : PcapSyms B.
(* The segments the listing is certified against (the library walks' convention): used only to place g_nl's bytes in
   the image and to make image bytes of writable segments writable at any memory (computations over tfibsegs).
   lib/A/Prog/LinkImgInst.v pi_link_segs discharges it at the link instance. *)
Hypothesis HSEGS : SEGS = tfibsegs.
(* meta_fill_f5 (0x55f7c): discharged at the image by lib/A/Rt/SetShadow.v link_set_shadow_f5. *)
Hypothesis HF5 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f5) 0xf5.

(* ---- g_nl: in the image, writable, outside the runtime's statics ---- *)
Lemma um_gnl_not_owned : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> ~ Exists (in_zr a) (as_owned_static B).
Proof.
intros a Ha Hex. rewrite (ts_owned _ TB) in Hex.
assert (C : forallb (fun r : Z * Z => (fst r + snd r <=? LA_G_NL) || (LA_G_NL + NK_SIZE <=? fst r))%bool
  Tfib_owned_static = true) by (vm_compute; reflexivity).
apply Exists_exists in Hex as (r & Hr & Hz). rewrite forallb_forall in C. specialize (C r Hr).
unfold in_zr in Hz. apply Bool.orb_true_iff in C as [C|C]; apply Z.leb_le in C; lia.
Qed.

Lemma um_gnl_img : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> in_img SEGS a.
Proof.
intros a Ha. rewrite HSEGS.
destruct (find_segment tfibsegs LA_G_NL NK_SIZE) as [sg|] eqn:Hf; [|vm_compute in Hf; discriminate Hf].
destruct (find_segment_hit _ _ _ _ Hf) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.

Lemma um_gnl_writable : forall m a, LA_G_NL <= a < LA_G_NL + NK_SIZE -> writable_at SEGS m a.
Proof. intros m a Ha. rewrite HSEGS. apply LA_G_NL_writable. unfold NK_SIZE in Ha. exact Ha. Qed.

Lemma um_jAR : forall G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly' S' W' mem' md'.
Proof. intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi). Qed.

(* A byte of the write set stays writable across a step that keeps the presence of bytes: an image byte is in a
   writable segment (the write set is off the read-only set, apre), hence writable at any memory; any other byte
   was present, hence is present after the step. *)
Lemma um_wr_writable : forall (H : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  writable_at SEGS (mrestrict H m) a ->
  (forall x, apresent H m x -> apresent H m' x) ->
  writable_at SEGS (mrestrict H m') a.
Proof.
intros H m m' a Ha Hro Hw Hp.
destruct (classic (in_img SEGS a)) as [Hi | Hni].
- rewrite HSEGS in *. destruct Hi as (sg & Hsg & Hr).
  apply wseg_writable_tfib. exists sg. split; [exact Hsg|]. split; [|exact Hr].
  destruct (seg_writable sg) eqn:Ew; [reflexivity|].
  exfalso. apply Hro. left. exists sg. split; [exact Hsg|]. split; [exact Ew | exact Hr].
- rewrite HSEGS in *. apply (YCbq.apresent_writable tfibsegs). apply Hp.
  exact (apresent_of_writable H m a Ha Hni Hw).
Qed.

(* ---- the cut's Post survives a step that changes only bytes of the side frame (3, fpos) ---- *)
Lemma um_apost_move : forall cx fpos ly3 S3 W3 ms3 md3 (regs' regs'' : bvmap 5 word) (m5 : word -> option byte),
  um_pre SK B cx -> um_base SK B cx fpos ly3 S3 W3 ms3 md3 ->
  reac_served_unmark_all_apost SEGS (um_regs cx) (um_m0 cx) regs' (rdW W3 (ms_mem ms3)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (um_lyc cx) 3 fpos a ->
     aview SEGS (w_H W3) m5 a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) m5 a) ->
  reac_served_unmark_all_apost SEGS (um_regs cx) (um_m0 cx) regs'' (rdW W3 m5).
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 regs' regs'' m5 HPRE HBASE HAP HKEEP HPRS.
unfold um_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (_ & _ & _ & _ & _ & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1)
  & Hfa3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK3 & _).
destruct HPRE as (HAPRE & HRD & HNL & HER & HTB & HBK & _ & _ & _ & _ & HGB).
destruct HAPRE as (HJ & HGX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAJW & HNRO).
destruct HER as (_ & _ & _ & _ & Herr & _ & _).
assert (HinF : In (3, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
destruct HK3 as (_ & _ & K3 & _).
pose proof (frame_facts B _ _ _ 3 fpos (proj1 HAR1) HinF) as (_ & HposF & _).
(* a byte outside the side frame is kept by the step *)
assert (HMB : forall x, 0 <= x < 2 ^ 64 -> ~ aside_rng (um_lyc cx) 3 fpos x ->
  mbyte SEGS (rdW W3 m5) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x).
{ intros x Hx Hs. apply (YCbq.mbyte_of_aview SEGS). apply HKEEP; assumption. }
(* g_nl's bytes are image bytes, hence not the side frame's *)
assert (HGS : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> ~ aside_rng (um_lyc cx) 3 fpos x).
{ intros x Hx Hs. apply (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low _ _ _ _ _ 3 fpos x HAR1 HinF Hs)).
  exact (um_gnl_img x Hx). }
assert (HGB2 : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE -> 0 <= x < 2 ^ 64)
  by (intros x Hx; unfold LA_G_NL, NK_SIZE in Hx; lia).
(* the table's cells at the cut are the call's *)
assert (HCELL : forall x, LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (um_W cx)) (um_memc cx) x).
{ intros x Hx. assert (Hx' : LA_G_NL <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME in Hx; lia).
  apply K3.
  - exact (um_gnl_img x Hx').
  - exact (um_gnl_not_owned x Hx').
  - unfold apart_gnl in Herr. lia.
  - intros [HE | Hs].
    + unfold um_E, um_wr, reac_served_unmark_all_awr, inFP in HE. destruct HE as (r & Hr & Hra).
      destruct Hr as [<- | [<- | []]]; unfold aivl in Hra; cbn [fst snd] in Hra.
      * unfold NK_IF_NAME, NK_N_SENT in *. lia.
      * fold (um_mk cx) in Hra. destruct (Z.eq_dec (um_mk cx) 0) as [E0 | N0].
        -- rewrite E0 in Hra. cbn [Z.eqb] in Hra. lia.
        -- destruct (HBK N0) as (_ & Hap & _).
           rewrite (proj2 (Z.eqb_neq _ _) N0) in Hra. unfold apart_gnl in Hap. fold (um_mk cx) in Hap. lia.
    + exact (HGS x Hx' Hs). }
(* the marks block: a byte of the write set, an application or image byte *)
assert (HMK : um_mk cx <> 0 -> forall x, um_mk cx <= x < um_mk cx + MK_SIZE ->
  0 <= x < 2 ^ 64 /\ ~ aside_rng (um_lyc cx) 3 fpos x /\ ~ in_roP SEGS PCAP_RLO PCAP_RHI x).
{ intros N0 x Hx.
  destruct (HBK N0) as ((Hp0 & Hamr & _) & _ & _ & _ & _).
  fold (um_mk cx) in Hp0, Hamr.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hw : inFP (um_wr cx) x).
  { exists (aivl (um_mk cx) MK_SIZE). split; [right; left; reflexivity|].
    unfold aivl. rewrite (proj2 (Z.eqb_neq _ _) N0). cbn [fst snd]. lia. }
  assert (Happ : x < kLowMemEnd \/ kHighMemBeg <= x)
    by (clear - Hx Hamr; unfold amem_range, MK_SIZE in *; lia).
  split; [clear - Hx Hamr Hp0 C4 C5; unfold amem_range, MK_SIZE in *; lia|]. split.
  - apply (ajw_not_side SK SEGS B LAWS pa_img_range (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx)
      (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx)
      (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) 3 fpos x HGX HJ ltac:(lia)).
    + exact HposF.
    + exact Hnin.
    + exact (HAJW x Hw).
    + exact Happ.
  - exact (HNRO x Hw). }
split.
- (* m = 0 *)
  intros Hz kbs NK. destruct HAP as (HAP0 & _). specialize (HAP0 Hz kbs NK).
  destruct HAP0 as (U & L). split; [|exact L].
  apply (um_au8arr_move SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) LA_G_NL kbs U).
  + intros x Hx. rewrite L in Hx. apply HMB; [apply HGB2 | apply HGS]; lia.
  + intros x Hx. apply um_gnl_writable. rewrite L in Hx. lia.
- (* m <> 0 *)
  intros Hn kbs tab gbs NK IT MK. destruct HAP as (_ & HAP1). specialize (HAP1 Hn kbs tab gbs NK IT MK).
  cbv zeta in HAP1 |- *.
  destruct HAP1 as ((gbs' & MK' & WF' & N0') & (kbs' & N1 & N2 & N3 & N4 & N5 & N6 & N7)).
  split.
  + exists gbs'. split; [|split; [exact WF' | exact N0']].
    destruct MK' as (U & L). split; [|exact L].
    fold (um_mk cx) in U |- *.
    apply (um_au8arr_move SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) (um_mk cx) gbs' U).
    * intros x Hx. rewrite L in Hx. destruct (HMK Hn x Hx) as (Hb & Hs & _). exact (HMB x Hb Hs).
    * intros x Hx. rewrite L in Hx. destruct (HMK Hn x Hx) as (Hb & _ & Hro).
      apply (um_wr_writable (w_H W3) (ms_mem ms3) m5 x Hb Hro); [|exact HPRS].
      destruct U as (_ & UW). unfold awrange in UW.
      replace x with (um_mk cx + (x - um_mk cx)) by lia. apply UW. rewrite L. lia.
  + exists kbs'.
    refine (conj _ (conj N2 (conj N3 (conj N4 (conj N5 (conj _ N7)))))).
    * destruct N1 as (U & L). split; [|exact L].
      apply (um_au8arr_move SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) LA_G_NL kbs' U).
      -- intros x Hx. rewrite L in Hx. apply HMB; [apply HGB2 | apply HGS]; lia.
      -- intros x Hx. apply um_gnl_writable. rewrite L in Hx. lia.
    * pose proof N6 as (Lt & L80 & _).
      assert (Hlt : Z.of_nat (length tab) <= 80) by exact L80.
      apply (um_aiftab_keep SEGS (rdW W3 (ms_mem ms3)) (rdW W3 m5) kbs' kbs' tab N6 eq_refl).
      -- intros x Hx. assert (LA_G_NL <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME, NK_SIZE in *; lia).
         apply HMB; [apply HGB2 | apply HGS]; assumption.
      -- intros x Hx. assert (LA_G_NL <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_INDEX, NK_SIZE in *; lia).
         apply HMB; [apply HGB2 | apply HGS]; assumption.
      -- intros i n2 ix p Hi Hp Hpr x Hx.
         assert (Li : (i < length tab)%nat) by (apply nth_error_Some; congruence).
         (* the cell holds the call's pointer *)
         assert (Hp0 : au64_at SEGS (um_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
         { unfold um_m0. apply (val_mem_moved SEGS (w_H W3) (w_H (um_W cx)) (ms_mem ms3) (um_memc cx)
             (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) 8 p);
             [|exact Hp].
           intros k Hk. symmetry. apply HCELL. unfold NK_IF_NAME, NK_SIZE. lia. }
         pose proof IT as (_ & _ & IT0). destruct (IT0 i n2 ix Hi) as (_ & p0 & P0 & Pz0 & C0 & _).
         pose proof (um_acstr_range SEGS _ p0 n2 C0) as Rp0.
         pose proof (um_vm_unique SEGS _ _ 8 p p0 Hp0 P0) as Ep. change (8 * Z.of_nat 8) with 64 in Ep.
         rewrite !Z.mod_small in Ep by lia. subst p0.
         apply HMB; [lia|].
         apply (akb_not_side SK SEGS B pa_img_range (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx)
           (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx)
           (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx)
           (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) 3 fpos x HJ ltac:(lia)).
         ++ exact HposF.
         ++ exact Hnin.
         ++ apply HRD. right. exists kbs, tab, i, n2, ix, p.
            split; [exact NK|]. split; [exact IT|]. split; [exact Hi|]. split; [exact Hp0|].
            split; [exact C0 | exact Hx].
Qed.

(* ---- the run tactics (PcapFrame.v paj_run_sh / paj_run_flag_sh, the call variant) ---- *)
Ltac um_run_call RUNC HS HJ :=
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
      | ?other => fail "um_run_call: the run does not stop at a call:" other
      end
    end
  end.
Ltac um_run_flag RUNF HS HJ :=
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

(* ==========================================================================
   4. um_rel
   ========================================================================== *)
Theorem um_rel : um_rel_obl SK B.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 HPRE HGI.
pose proof HPRE as HPRE0.
destruct HGI as (Hpc & HAP & HBASE).
pose proof HBASE as HBASE0.
unfold um_base in HBASE. cbv zeta in HBASE.
destruct HBASE as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ3 & Hfrs3 & Hnin & HfsS3 & Hperm
  & (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Hbl1) & Hfa3 & R2 & R9 & R8 & R18 & R19 & R25 & R20 & R3 & R4
  & Hra8 & Hsav & Hflag & HFpres & HSpres & HK3 & Hfds3 & Hfs3 & _).
destruct HPRE as ((HJ & HGX & _ & Hraok & _ & Hgp & Htp & Hsp16 & Hwlo & Hwhi & _) & HRD & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
set (regs := um_regs cx) in *. set (R := ms_regs ms3) in *. set (m3 := ms_mem ms3) in *.
set (sp := um_sp cx) in *.
change (spZ regs) with sp in Hsp16, Hwlo, Hwhi.
change UM_CID with 3 in *.
set (F := um_F cx fpos) in *. set (FL := um_FL cx fpos) in *. set (SH := um_SH cx fpos) in *.
(* ---- the journal's window and the stack ---- *)
assert (HR0 := HJ). apply ajournal_gx_row in HR0. destruct HR0 as (Hrow1 & Hrow2 & Hrow3 & Hrow4).
pose proof HJ as (HSTK0 & HXO0 & _).
assert (Hspr : 0 <= sp < 2 ^ 64)
  by (pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu; exact Hu).
assert (HKv : REAC_SERVED_UNMARK_ALL_AK = 8768) by reflexivity.
assert (HspK : alloc_ceiling <= sp - REAC_SERVED_UNMARK_ALL_AK) by lia.
assert (Hsp47 : sp <= 2 ^ 47) by lia.
(* ---- the frame, its shadow and its flag byte ---- *)
pose proof (um_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (HinF : In (3, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
assert (HinF3 : In (3, fpos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos HJ3) as (EF3 & EFL3).
destruct (aj_gx_frame_addr SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos HJ) as (EFc & EFLc).
assert (EF : frame_addr ly3 3 fpos = F) by (unfold F, um_F, UM_CID; rewrite EF3, EFc; reflexivity).
assert (EFL : flag_addr ly3 3 fpos = FL) by (unfold FL, um_FL, UM_CID; rewrite EFL3, EFLc; reflexivity).
assert (EFl : frame_addr (um_lyc cx) 3 fpos = F) by reflexivity.
assert (EFLl : flag_addr (um_lyc cx) 3 fpos = FL) by reflexivity.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (HF4096 & HFceil & HFapp).
rewrite EFl in HF4096, HFceil, HFapp. change (fs_frame_bytes 3) with 512 in HFceil, HFapp.
pose proof (frame_al64 SEGS B _ _ _ _ _ 3 fpos HAR1 HinF) as (HFal & _ & _). rewrite EFl in HFal.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (_ & _ & HFnown & HFSnown).
rewrite EFl in HFnown, HFSnown. change (fs_frame_bytes 3) with 512 in HFnown, HFSnown.
change (512 / 8) with 64 in HFSnown.
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR1 HinF) as (_ & HFLown & HFLapp & HFLceil).
rewrite EFLl in HFLown, HFLapp, HFLceil.
assert (HSHeq : SH = SHADOW_OFF + F / 8) by reflexivity.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp, HFLapp.
assert (HF8 : 0 <= F / 8 /\ F / 8 + 64 <= (F + 512) / 8).
{ split; [apply Z.div_pos; lia|]. replace (F + 512) with (F + 64 * 8) by lia. rewrite Z.div_add by lia. lia. }
assert (HF8c : (F + 512) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in HF8c.
assert (HSHb : SHADOW_OFF <= SH /\ SH + 64 <= SHADOW_OFF + 2 ^ 44) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
assert (HFLnF : ~ (F <= FL < F + 512)) by (intros Hc; exact (proj2 (HFnown FL Hc) HFLown)).
assert (HFLnS : ~ (SH <= FL < SH + 64)).
{ intros Hc. apply (proj2 (HFSnown (FL - shadow_addr F) ltac:(unfold shadow_addr; lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLown. }
assert (HFb : 0 <= F < 2 ^ 64) by lia.
assert (HFLb : 0 <= FL < 2 ^ 64) by lia.
assert (HSHr : 0 <= SH < 2 ^ 64) by (unfold SHADOW_OFF in *; lia).
assert (UF : bv_unsigned (w64 F) = F) by (unfold w64; apply unsigned_lit_small; lia).
assert (UFL : bv_unsigned (w64 FL) = FL) by (unfold w64; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (w64 sp) = sp) by (unfold w64; apply unsigned_lit_small; lia).
(* the realigned stack pointer s1 *)
destruct (sp1_facts (sp - UM_FRAME) ltac:(unfold UM_FRAME; lia)
  ltac:(unfold UM_FRAME; rewrite Zminus_mod, Hsp16; reflexivity)) as (Hsp1r & Hsp1al32 & Hsp1al16).
change (32 * ((sp - UM_FRAME) / 32)) with (um_sp1 cx) in Hsp1r, Hsp1al32, Hsp1al16.
unfold UM_FRAME in Hsp1r.
set (sp1 := um_sp1 cx) in *.
assert (Usp1 : bv_unsigned (w64 sp1) = sp1) by (unfold w64; apply unsigned_lit_small; lia).
(* ---- the environment: the registers at the cut, the saved words, the flag address ---- *)
set (extra := [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
               getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26;
               getr regs 27; w64 FL]).
set (E := Eimg (Ereg R extra)).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg R extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (EREG : forall n (r : Prelude.reg), Z.of_nat n = bv_unsigned r -> ew E n = getr R r).
{ intros n r Hr. rewrite EL; [exact (ew_Ereg_nat _ _ n r Hr)|].
  pose proof (u5_range r) as Hu. unfold A_TEXT. lia. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j extra (w64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ j)).
assert (E19 : ew E 19 = w64 F) by (rewrite (EREG 19%nat 19%bv eq_refl); exact R19).
assert (E18 : ew E 18 = w64 SH) by (rewrite (EREG 18%nat 18%bv eq_refl); exact R18).
assert (E8 : ew E 8 = w64 sp) by (rewrite (EREG 8%nat 8%bv eq_refl); exact R8).
assert (E2 : ew E 2 = w64 sp1) by (rewrite (EREG 2%nat 2%bv eq_refl); exact R2).
assert (E45 : ew E 45 = w64 FL) by (exact (EX 13%nat ltac:(lia))).
assert (U19 : bv_unsigned (ew E 19) = F) by (rewrite E19; exact UF).
assert (U8 : bv_unsigned (ew E 8) = sp) by (rewrite E8; exact Usp).
assert (U45 : bv_unsigned (ew E 45) = FL) by (rewrite E45; exact UFL).
(* the saved words, as the saves region's chunks *)
assert (HSAV : forall j, (j < 13)%nat ->
  val_mem SEGS (rdW W3 m3) (sp + (-8 - 8 * Z.of_nat j)) 8 (bv_unsigned (nth j extra (w64 0)))).
{ intros j Hj. apply (val_mem_of_rdword SEGS (w_H W3) m3).
  destruct j as [|j'].
  - replace (sp + (-8 - 8 * Z.of_nat 0)) with (sp - 8) by lia. exact Hra8.
  - replace (sp + (-8 - 8 * Z.of_nat (S j'))) with (sp - 16 - 8 * Z.of_nat j') by lia.
    rewrite (Hsav (Z.of_nat j') ltac:(lia)). f_equal.
    do 12 (destruct j' as [|j']; [reflexivity|]). lia. }
assert (HCH : forall j, (j < 13)%nat -> YP09.chunk_ok SEGS E (rdW W3 m3) sp
   (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val SEGS E _ sp (-8 - 8 * Z.of_nat j) 8 (SOff (32 + j) 0)
    (bv_unsigned (nth j extra (w64 0))));
  [ cbn [sv_denot]; rewrite (EX j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | pose proof (bv_unsigned_in_range 64 (nth j extra (w64 0))) as Hu; change (bv_modulus 64) with (2 ^ 64) in Hu;
    change (8 * Z.of_N 8) with 64; lia
  | zside
  | exact (HSAV j Hj) ]. }
(* ---- the symbolic state at the cut ---- *)
assert (HS0 : st_ok_pi SEGS VAL E umr_ss0 (restrict (w_H W3) ms3)).
{ rewrite (um_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr), Hpc, Zrom, restrict_mkst_fx.
  unfold umr_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold region_ok, umr_FR, umr_FL0, umr_saves;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (YCbq.apresent_writable SEGS); apply HFpres; unfold UM_FB; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 504 8 (SOff 45 0) FL);
      [ cbn [sv_denot]; rewrite E45, Z.add_0_r, UFL; reflexivity
      | change (8 * Z.of_N 8) with 64; lia | zside
      | exact (val_mem_of_rdword SEGS (w_H W3) m3 _ _ Hflag) ].
    + rewrite U45. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_nil.
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      unfold umr_saves_chunks. apply Forall_map, Forall_forall. intros j Hj.
      apply in_seq in Hj. apply HCH. lia.
  - apply pairwise_disjoint_of_extents.
    unfold umr_FR, umr_FL0, umr_saves, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U45, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [umr_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U19, U45. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
    repeat split; first [lia | apply Z.mod_1_r]. }
assert (HS : st_ok_pi SEGS VAL E (mkSS (ss_pc umr_ss0) (sr_set (ss_regs umr_ss0) 25%bv (SOff 19 0))
  (ss_mem umr_ss0) (ss_resv umr_ss0) (ss_facts umr_ss0)) (restrict (w_H W3) ms3)).
{ apply (ast_ok_pi_set_reg_fp E _ _ (25%bv : bv 5) (SOff 19 0) HS0 ltac:(vm_compute; reflexivity)).
  rewrite (sv_off0 E 19 F E19). cbn [ms_regs restrict]. exact (eq_sym R25). }
clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts umr_ss0] in HS.
clearbody E.
(* ---- the run +0x350 .. +0x368: the retired magic, `beqz s3` (not taken), up to meta_fill_f5 ---- *)
pose proof (paj_run_call_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNC.
um_run_call RUNC HS HJ3.
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val umr_FR umr_FL0 umr_saves] in Ha;
  [| exfalso; lia | exfalso; lia].
  rewrite U19 in Ha. left.
  apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos a HJ3
    ltac:(left; reflexivity)).
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3) with 512. lia. }
intros ms1 mat1 HS1 HJ1 _ HFr1 HG1.
(* the registers at the call *)
prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (11%bv : bv 5) Q11. prreg HS1 (1%bv : bv 5) Q1.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4.
pmkst HS1.
set (sig5 := pa_sigma LS___asan_set_shadow_f5).
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low sig5 0xf5 HF5
    _ _ _ W3 (ms_regs ms1) (ms_mem ms1) _ _ _ _ _ _ _ _ _ ly3 S3 _ _
    3 fpos SH 64 (getr (ms_regs ms1) 1) HGX HJ1 ltac:(left; reflexivity)).
  - rewrite Q10, E18. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - rewrite EF. unfold shadow_addr. lia.
  - rewrite EF. unfold shadow_addr. change (fs_frame_bytes 3 / 8) with 64. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. exact Hsp1al16.
  - unfold spZ. rewrite Q2, E2, Usp1. change ESTACK with 4096. lia.
  - unfold spZ. rewrite Q2, E2, Usp1. lia.
  - rewrite Q3, (EREG 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite Q4, (EREG 4%nat 4%bv eq_refl), R4. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hf5 & Hmf & Hpres2 & Hsbm2).
pose proof (um_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR2 HinF3) as (_ & _ & HFpres2 & _).
rewrite EF in HFpres2. change (fs_frame_bytes 3) with 512 in HFpres2.
destruct (al_flag _ _ LAWS _ _ _ _ _ 3 fpos HAR2 HinF3) as (HFLpres2 & _).
rewrite EFL in HFLpres2.
(* the state after the call *)
jafter_call_keep_pi HS1 48%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha.
  - rewrite U19 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|].
    unfold SHADOW_OFF in *; lia.
  - intros _. rewrite U19 in Ha. apply (YCbq.apresent_writable SEGS). apply (proj1 (HFpres2 a ltac:(lia))).
  - rewrite U45 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|]. intros Hc. apply HFLnS.
    replace FL with a by lia. exact Hc.
  - exfalso; lia.
  - rewrite U8 in Ha. apply (YCbq.mbyte_of_aview SEGS). apply Hmf; [lia|]. unfold SHADOW_OFF in *; lia.
  - exfalso; lia. }
rewrite <- restrict_mkst_fx in HS2.
assert (Hraw : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 32884)) by (rewrite Q1; reflexivity).
rewrite Hraw.
remember (havoc E 48 (map (getr regs2) CLOB)) as Ev2 eqn:HE2 in HS2.
assert (HEI2 : img_env VAL A_LIM Ev2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall nn, (nn < 48)%nat -> ew Ev2 nn = ew E nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
clear HE2.
assert (V19 : bv_unsigned (ew Ev2 19) = F) by (rewrite OLD2 by lia; exact U19).
assert (V45 : bv_unsigned (ew Ev2 45) = FL) by (rewrite OLD2 by lia; exact U45).
assert (V8 : bv_unsigned (ew Ev2 8) = sp) by (rewrite OLD2 by lia; exact U8).
(* the flag byte becomes writable *)
lazymatch type of HS2 with st_ok_pi _ _ _ ?ssx ?msx =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) umr_FL0) in
  pose proof (st_ok_pi_region_nth Ev2 ssx msx 1 r1 HS2 ltac:(vm_compute; reflexivity)) as HR1;
  pose proof (ast_ok_pi_set_region Ev2 ssx msx 1 r1 (set_window r1 0 1) HS2 ltac:(vm_compute; reflexivity)
    ltac:(reflexivity) ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS Ev2 _ r1 0 1 HR1 ltac:(intros o Ho; cbn [YP09.r_base base_val];
       rewrite V45; replace (FL + o) with FL by lia; cbn [ms_mem restrict mkst];
       apply (YCbq.apresent_writable SEGS); exact HFLpres2))) as HS3
end.
clear HS2 HR1. norm_pi HS3.
(* ---- the run +0x36c .. +0x464: the inline release, the restores, up to `ret` ---- *)
pose proof (paj_flag_plain_x SK B LAWS (um_G cx) HGX (um_XO cx) (um_OUT cx)) as RUNF.
um_run_flag RUNF HS3 HJ2.
{ try unfold UM_CID; lia. }
{ intros a (r & Hr & Ha). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - rewrite V19 in Ha. left.
    apply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 3 fpos a HJ2
      ltac:(left; reflexivity)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3) with 512. lia.
  - rewrite V45 in Ha. right. right. right. rewrite EFL. lia.
  - exfalso; lia. }
{ intros msr HSr.
  lazymatch type of HSr with st_ok_pi _ _ _ ?ssx _ =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) umr_FL) in
    pose proof (st_ok_pi_region_nth Ev2 ssx msr 1 r1 HSr ltac:(vm_compute; reflexivity)) as HR1;
    pose proof (field_of_region Ev2 (ms_mem msr) 45 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR1 V45
      ltac:(cbn; tauto) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as Vfl;
    change (N.to_nat 1) with 1%nat in Vfl; specialize (Vfl 0%nat ltac:(lia));
    replace (FL + 0 + Z.of_nat 0) with FL in Vfl by lia;
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
(* the model and the post are named before the side condition is computed (an evar under vm_compute loops) *)
pose proof (paj_ret_at (L := link_listing) (PL := PL_link) (PI := PI) W3 Ev2 _ ms5
  (with_vm_backing (m_vm_lazy md2) mat5 md2) (um_post SK B cx) HS5 eq_refl) as RET5.
apply RET5; [vm_compute; reflexivity|]. clear RET5.
intros mat6.
assert (Era : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite P1, OLD2 by lia. exact (EX 0%nat ltac:(lia)). }
unfold YK0s.ret_ok in Hraok. rewrite Era, Hraok.
pose proof (ajournal_gx_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat6 HJ5) as HJ6.
(* ---- what the release changed: only bytes of the side frame ---- *)
assert (HWR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hn. apply (YCbq.aview_eq_of SEGS). apply HFr1.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val umr_FR umr_FL0 umr_saves] in Hra;
  [rewrite U19 in Hra | |]; lia. }
assert (HWR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 8) -> a <> FL ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha Hn Hfl. apply (YCbq.aview_eq_of SEGS). apply HFr5.
  rewrite unsigned_lit_small by lia.
  intros (r & Hr & Hra). cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra;
  [rewrite V19 in Hra | rewrite V45 in Hra |]; lia. }
assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ aside_rng (um_lyc cx) 3 fpos a ->
  aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H W3) m3 a).
{ intros a Ha Hs. rewrite um_side_unfold, EFl, EFLl in Hs.
  assert (N1 : ~ (F <= a < F + 8)) by (intros ?; apply Hs; left; lia).
  assert (N2 : a <> FL) by (intros ?; apply Hs; right; right; assumption).
  assert (N3 : ~ (SH <= a < SH + 64)) by (intros ?; apply Hs; right; left; lia).
  rewrite (HWR5 a Ha N1 N2), (Hmf a Ha N3). exact (HWR1 a Ha N1). }
assert (HPRS : forall a, apresent (w_H W3) m3 a -> apresent (w_H W3) (ms_mem ms5) a).
{ intros a Ha. apply (um_apresent_grows (w_H W3) mem2); [exact HG5|]. apply Hpres2.
  exact (um_apresent_grows (w_H W3) m3 (ms_mem ms1) a HG1 Ha). }
(* ---- the post ---- *)
unfold um_post.
eapply (apost_side_gen SK SEGS B LAWS pa_segs_low REAC_SERVED_UNMARK_ALL_AK 0 (um_E cx)
  (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx) (um_ly cx) (um_S cx) (um_W0 cx)
  (um_mem0 cx) (um_md0 cx) (um_own cx) (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx)
  regs (ms_regs ms5) ly3 (stack_free_state 3 fpos S3) W3 (ms_mem ms5) _ (um_k cx) 3 fpos S1 W1 mem1 md1 _
  HJ HJ6 ltac:(lia)).
- destruct (um_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (A1 & _).
  destruct (um_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (A2 & _).
  destruct (um_sbm_fds_fs _ _ Hsbm2) as (A3 & _).
  destruct (um_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (A4 & _).
  rewrite A1, A2, A3, A4. exact Hfds3.
- destruct (um_wvb_fds_fs (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat6
    (with_vm_backing (m_vm_lazy md2) mat5 md2)) as (_ & A1).
  destruct (um_wvb_fds_fs (m_vm_lazy md2) mat5 md2) as (_ & A2).
  destruct (um_sbm_fds_fs _ _ Hsbm2) as (_ & A3).
  destruct (um_wvb_fds_fs (m_vm_lazy md3) mat1 md3) as (_ & A4).
  rewrite A1, A2, A3, A4. exact Hfs3.
- apply aregs_preserved_eqs.
  + rewrite P2, OLD2, E8 by lia. unfold w64, sp, um_sp, spZ. apply Z_to_bv_bv_unsigned.
  + rewrite P3, OLD2, (EREG 3%nat 3%bv eq_refl) by lia. exact R3.
  + rewrite P4, OLD2, (EREG 4%nat 4%bv eq_refl) by lia. exact R4.
  + rewrite P8, OLD2 by lia. exact (EX 1%nat ltac:(lia)).
  + rewrite P9, OLD2 by lia. exact (EX 2%nat ltac:(lia)).
  + rewrite P18, OLD2 by lia. exact (EX 3%nat ltac:(lia)).
  + rewrite P19, OLD2 by lia. exact (EX 4%nat ltac:(lia)).
  + rewrite P20, OLD2 by lia. exact (EX 5%nat ltac:(lia)).
  + rewrite P21, OLD2 by lia. exact (EX 6%nat ltac:(lia)).
  + rewrite P22, OLD2 by lia. exact (EX 7%nat ltac:(lia)).
  + rewrite P23, OLD2 by lia. exact (EX 8%nat ltac:(lia)).
  + rewrite P24, OLD2 by lia. exact (EX 9%nat ltac:(lia)).
  + rewrite P25, OLD2 by lia. exact (EX 10%nat ltac:(lia)).
  + rewrite P26, OLD2 by lia. exact (EX 11%nat ltac:(lia)).
  + rewrite P27, OLD2 by lia. exact (EX 12%nat ltac:(lia)).
- exact HAR1.
- exact Hfrs1.
- exact Hbl1.
- apply (akept_step SK SEGS B LAWS pa_segs_low (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx)
    W3 m3 W3 (ms_mem ms5) (sp - REAC_SERVED_UNMARK_ALL_AK) sp _ _ (aside_rng (um_lyc cx) 3 fpos)
    (um_jAR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) HspK ltac:(lia) HK3 HKEEP).
  + intros a _ Hp. exact (HPRS a Hp).
  + intros a Ha. exact Ha.
  + intros a Ha. left. right. exact Ha.
- cbv beta. split; [|split].
  + apply (set_fs_trans S3 (stack_free_state 3 fpos S3) (um_Sc cx)).
    * apply set_fs_of_exists. exact HfsS3.
    * apply stack_free_state_set_fs.
  + rewrite stack_free_state_set_fs, ablocks_set_fs. exact Hperm.
  + exact (um_apost_move cx fpos ly3 S3 W3 ms3 md3 R (ms_regs ms5) (ms_mem ms5) HPRE0 HBASE0 HAP HKEEP HPRS).
Qed.

End b.
End a.

About um_rel.
Print Assumptions um_rel.
