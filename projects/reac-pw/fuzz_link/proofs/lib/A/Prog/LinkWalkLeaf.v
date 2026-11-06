(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v; 146 of its 199 lines of code are new or changed and 1252 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: walk-kit lemmas for a LEAF walk of one of link's own functions, beside the kit of
   lib/A/Prog/LinkWalk.v. Each is generic in the segments (no address of link).

   - apost_leaf_app: LinkWalk.v's apost_leaf for a leaf whose write set E may lie anywhere outside the shadow band
     [SHADOW_OFF, kHighMemBeg): a caller's buffer in a heap block, in a side frame or on the real stack, not only an
     image global below SHADOW_OFF. ashadow_kept_app is its shadow clause: the shadow byte of a heap byte is in the
     band, so a run that writes its own window and E keeps it.
   - st_ok_pi_keep: a symbolic state keeps any sublist of its regions (submem). A walk drops the .got regions once
     the shadow base is in its register, before it adds the region of a pointer argument that may overlap them.
   - st_ok_pi_add_alias: an alias fact over st_ok_pi (Reusable/YP03.v st_ok_add_alias). The runner names an address
     only as an atom plus a constant; an alias `x + y = SOff n d` lets it name an address the code forms with an
     `add` of two registers (copy_attr's out + s3).
   - val_mem_of_rdword_g and the presence / byte helpers: Reusable/StackFree8.v's val_mem_of_rdword,
     apresent_writable, mbyte_of_aview over any segments (StackFree8.v states them inside its own image section).
   (aj_gx_strnlen_atS, the strnlen lift that keeps the model relation, is in lib/A/Prog/LinkWalkStrS.v.)

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   Section m: bytes, presence and the view, over any segments
   ========================================================================== *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

Lemma lw_apresent_writable : forall H (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

Lemma lw_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a a' E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a') as [b'|] eqn:E1; destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E2;
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* a byte the view shows is a byte the memory holds *)
Lemma lw_aview_mbyte : forall H (m : word -> option byte) a v,
  aview segs H m a = Some v -> exists b : byte, mbyte segs (mrestrict H m) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
  intros H m a v Hv. unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [b|]; [|discriminate].
  cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
  pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn in Hr. lia.
Qed.

(* a byte present at the start is present later, and its memory byte stays defined *)
Lemma lw_mbyte_some_kept : forall H (m m' : word -> option byte) a b,
  (forall x, apresent H m x -> apresent H m' x) -> mbyte segs (mrestrict H m) a = Some b ->
  exists b', mbyte segs (mrestrict H m') a = Some b'.
Proof.
  intros H m m' a b Hp Hb. unfold mbyte, mrestrict in *.
  destruct (H (Z_to_bv 64 a)) eqn:Eh.
  - exists b. exact Hb.
  - destruct (m (Z_to_bv 64 a)) as [c|] eqn:Ec.
    + assert (Hpa : apresent H m (bv_unsigned (Z_to_bv 64 a))).
      { unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Eh | exists c; exact Ec]. }
      destruct (Hp _ Hpa) as [_ [c' Hc']]. rewrite Z_to_bv_bv_unsigned in Hc'. rewrite Hc'. exists c'. reflexivity.
    + destruct (m' (Z_to_bv 64 a)) as [c'|]; [exists c'; reflexivity | exists b; exact Hb].
Qed.

Lemma val_mem_of_rdword_g : forall H mem a v,
  rdword (aview segs H mem) a = Some v -> val_mem segs (mrestrict H mem) a 8 v.
Proof.
  intros H mem a v Hw. unfold rdword in Hw.
  destruct (aview segs H mem a) as [b0|] eqn:E0; [|discriminate].
  destruct (aview segs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
  destruct (aview segs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
  destruct (aview segs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
  destruct (aview segs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
  destruct (aview segs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
  destruct (aview segs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
  destruct (aview segs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
  injection Hw as <-.
  apply lw_aview_mbyte in E0 as (c0 & M0 & -> & R0). apply lw_aview_mbyte in E1 as (c1 & M1 & -> & R1).
  apply lw_aview_mbyte in E2 as (c2 & M2 & -> & R2). apply lw_aview_mbyte in E3 as (c3 & M3 & -> & R3).
  apply lw_aview_mbyte in E4 as (c4 & M4 & -> & R4). apply lw_aview_mbyte in E5 as (c5 & M5 & -> & R5).
  apply lw_aview_mbyte in E6 as (c6 & M6 & -> & R6). apply lw_aview_mbyte in E7 as (c7 & M7 & -> & R7).
  rewrite ?Z.add_0_r in M0.
  set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
    256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
  assert (Hv : 0 <= v < 2 ^ 64) by (subst v; lia).
  assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
    v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
    Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
  { intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
    replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
    2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
    replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
    2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
    apply Z_to_bv_bv_unsigned. }
  intros k Hk.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia];
  [ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
  | change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
  | change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
  - rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
      256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; lia.
  - rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
      256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; lia.
  - rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
      256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; lia.
  - rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
      (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; lia.
  - rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
      (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; lia.
  - rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
      (bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; lia.
  - rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
      (bv_unsigned c7)); cbn; subst v; lia.
  - rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
      0); cbn; subst v; lia.
Qed.
End m.

(* ==========================================================================
   Section s: the symbolic state (regions dropped, an alias added)
   ========================================================================== *)
Section s. Context {fx : YK11.FPState}.
Variable segs : list Segment.
Variable val : nat -> Z.

Lemma st_ok_keep : forall E ss ms rs,
  st_ok segs E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok segs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hsub Hwf.
  unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  repeat (split; [assumption|]). split; [|exact H9].
  exact (mem_ok_sub segs E (ms_mem ms) (ss_mem ss) rs Hsub Hwf H8).
Qed.

Lemma st_ok_pi_keep : forall E ss ms rs,
  st_ok_pi segs val E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs val E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
  intros E ss ms rs HS Hsub Hwf. exact (st_ok_keep E (abs_ss val ss) ms rs HS Hsub Hwf).
Qed.

Lemma st_ok_pi_add_alias : forall E ss ms (a b : sv),
  st_ok_pi segs val E ss ms -> sv_denot E a = sv_denot E b -> st_ok_pi segs val E (add_alias ss a b) ms.
Proof.
  intros E ss ms a b HS Hab. exact (st_ok_add_alias segs E (abs_ss val ss) ms a b HS Hab).
Qed.
End s.

(* ==========================================================================
   Section j: the apost of a leaf whose write set lies outside the shadow band
   ========================================================================== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The shadow of every heap block the call keeps: the run writes only its window (above the ceiling) and E (outside
   the shadow band), and the shadow byte of a heap byte lies in the band, below the ceiling. *)
Lemma ashadow_kept_app : forall lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi (E : Z -> Prop),
  AR segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall x, E x -> ~ (SHADOW_OFF <= x < kHighMemBeg)) ->
  ashadow_kept segs B lyc Sc ly2 S2 W memc W2 mem2.
Proof.
  intros lyc Sc ly2 S2 W memc mdc W2 mem2 slo shi E HAR Hceil UN HE b m a Hin _ Ha.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
  assert (Ha0 : 0 <= a < kHighMemEnd) by lia.
  assert (Ha1 : a <= alloc_ceiling) by lia.
  pose proof (shadow_addr_bounds a Ha0) as Hsb.
  pose proof (shadow_mono a alloc_ceiling Ha1) as Hsle.
  assert (Hsh : shadow_addr alloc_ceiling < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF; lia).
  assert (Hlo : SHADOW_OFF <= shadow_addr a) by (unfold shadow_addr; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)); lia).
  apply UN; [unfold kHighShadowEnd in Hsb; lia | lia |].
  intros HEa. apply (HE _ HEa). split; [exact Hlo | lia].
Qed.

(* THE WHOLE POST of a leaf that reaches no allocator and writes, beside its window, a set E of bytes outside the
   shadow band (LinkWalk.v apost_leaf, whose E lies below SHADOW_OFF). *)
Lemma apost_leaf_app : forall (K EV : Z) (E : Z -> Prop) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs regs2 : bvmap 5 word) mem2 md2
    (Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  0 <= EV -> sp0 - STK <= spZ regs - K -> spZ regs - K <= spZ regs ->
  m_fds md2 = m_fds mdc -> m_fs md2 = m_fs mdc ->
  aregs_preserved regs regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) -> ~ E a ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) ->
  (forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem2 a) ->
  (forall x, E x -> ~ (SHADOW_OFF <= x < kHighMemBeg)) ->
  Q lyc Sc W regs2 mem2 md2 ->
  apost SK segs B K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Q
    W (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom segs)) md2).
Proof.
  intros K EV E G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs2 mem2 md2 Q
    HJ HJ2 HEV Hlo Hwin Hfds Hfs HP UN Hgrow Hpw HE HQ.
  pose proof (aj_stk_ceiling SK segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as Hceil.
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  exists lyc, Sc, regs2, mem2, md2.
  split; [reflexivity|].
  split; [eapply (ajournal_gx_mono_k SK segs B); [exact HJ2 | lia]|].
  split; [exact HP|]. split; [reflexivity|].
  split; [exact Hfds|]. split; [exact Hfs|].
  split; [eapply akept_run; [exact LAWS | exact segs_low | exact HAR | lia | exact Hwin | exact UN | exact Hgrow | exact Hpw]|].
  split; [exact (ashadow_kept_app lyc Sc lyc Sc W memc mdc W mem2 (spZ regs - K) (spZ regs) E HAR ltac:(lia) UN HE)|].
  exact HQ.
Qed.

End j.
End a.
