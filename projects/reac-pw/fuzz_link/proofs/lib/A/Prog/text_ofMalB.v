(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 354 of its 401 lines of code are new or changed and 544 lines of the source are left out. *)
(* text_of on image A: the copy arm from wrapper_malloc's return (+0x230, THE BLOCK CUT to_gi_230) to THE NUL CUT
   (lib/A/Prog/text_ofMalT.v to_gi_24c, then to_tail):
     +0x230 `beqz a0` (refuted: the block is at least 4096), +0x234 s3 := the block, +0x238 `beqz s1`:
     - k = 0: to +0x24c;
     - k > 0: +0x23c .. +0x248 checked_memcpy(block, c0 + adv, k) (link_ajkit.v aj_gx_intrin_at, OCpy), back at +0x24c.
   The token engine, restarted at +0x230 from the registers (atom 10 the block, atom 9 the count k, its range a fact).
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkSide LinkWalkAlloc text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkNoWrite LinkWalkLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs text_ofKit text_ofMalKit LinkWalkShadow LinkWalkCall text_ofMalT PaJournalFs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition TO_AT230 : Z := AF_text_of + 0x230.
Definition tb_ss (f9 : afact) : sstate := mkSS TO_AT230 sr_atoms [] None
  (mkFacts [(10%nat, mkAF 4096 (2 ^ 47 - 2) 0); (9%nat, f9); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).

Lemma tm_mbyte2 : forall segs (H H' : word -> bool) (m m' : word -> option byte) a b,
  aview segs H m a = aview segs H' m' b -> mbyte segs (mrestrict H m) a = mbyte segs (mrestrict H' m') b.
Proof.
  intros segs H H' m m' a b E. unfold aview in E.
  destruct (mbyte segs (mrestrict H m) a) as [x|], (mbyte segs (mrestrict H' m') b) as [y|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).

(* ---- THE BLOCK CUT (+0x230): wrapper_malloc returned the block res of k + 1 bytes ---- *)
Definition to_gi_230 (cx : tocx) (c0 c1 : Z) (inp : list byte) (adv n k res : Z)
    (ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
    : Prop :=
  let regs := to_regs cx in
  let sp := to_sp cx in
  let m2 := rdW W2 mem2 in
  let rd2 := aview SEGS (w_H W2) mem2 in
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx) ly2 S2 W2 mem2 md2 (to_k cx + 1) /\
  m_fds md2 = m_fds (to_mdc cx) /\ m_fs md2 = m_fs (to_mdc cx) /\
  getr regs2 2 = w64 (sp - TO_FRAME) /\ getr regs2 8 = w64 (to_o cx) /\ getr regs2 9 = w64 k /\
  getr regs2 10 = w64 res /\ getr regs2 18 = w64 (c0 + adv) /\ getr regs2 20 = w64 SHADOW_OFF /\
  getr regs2 21 = w64 (SHADOW_OFF + to_o cx / 8) /\
  (forall r, In r TO_UNTOUCHED -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
  (forall j, (j < 7)%nat ->
     rdword rd2 (sp - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))) /\
  ablocks B ly2 S2 = ablocks B (to_lyc cx) (to_Sc cx) ++ [(res, k + 1)] /\ frames S2 = frames (to_Sc cx) /\
  (forall c q, frame_addr ly2 c q = frame_addr (to_lyc cx) c q) /\ 4096 <= res /\
  akept SEGS B (to_lyc cx) (to_Sc cx) (to_W cx) (to_memc cx) W2 mem2 (sp - TEXT_OF_AK) sp
    (fun a => to_E cx a \/ res <= a < res + req_size (k + 1)) /\
  (forall a, sp - TEXT_OF_AK <= a < sp -> apresent (w_H W2) mem2 a) /\
  mo_le MT (to_Sc cx) S2 (mo_malloc MT (k + 1)) /\ text_of_ledpost B (to_Sc cx) S2 /\
  to_inp cx c0 c1 inp /\ 1 <= adv <= 3 /\ adv + n <= c1 /\ 0 <= k <= n /\ n <= 319 /\
  ~ In (zb 0) (to_t inp adv k) /\
  (* the k bytes the code copies *)
  (forall i, 0 <= i < k -> mbyte SEGS m2 (c0 + adv + i) = nth_error inp (Z.to_nat (adv + i))) /\
  (0 < k -> range_addressable rd2 SHADOW_OFF (c0 + adv) k /\ shadow_hull_vis rd2 (c0 + adv) k /\
     amem_range (c0 + adv) k /\ (res + k <= c0 + adv \/ c0 + adv + k <= res) /\
     (forall a, c0 + adv <= a < c0 + adv + k -> ~ (sp - TEXT_OF_AK <= a < sp))) /\
  (* the cursor and *own *)
  au64_at SEGS m2 (to_p cx) (c0 + adv + n) /\ au64_at SEGS m2 (to_p cx + 8) (c1 - adv - n) /\
  abuf SEGS m2 (to_p cx) 16 /\
  (forall i, 0 <= i < 8 -> writable_at SEGS m2 (to_o cx + i)) /\ range_addressable rd2 SHADOW_OFF (to_o cx) 8.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
(* checked_memcpy (0x52d78): lib/A/AE2q.v asan_memcpy_realizes *)
Hypothesis AMCPY : aintrin_realizes SEGS B OCpy (pa_sigma LS___asan_memcpy).

(* the NUL cut from the block cut, after a stretch that wrote at most the first k bytes of the block *)
Lemma to_24c_of : forall cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 (R : bvmap 5 word) m md,
  to_pre SK B MT CTX cx -> to_gi_230 cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 ->
  getr R 2 = getr regs2 2 -> getr R 8 = getr regs2 8 -> getr R 9 = getr regs2 9 -> getr R 19 = w64 res ->
  getr R 20 = getr regs2 20 -> getr R 21 = getr regs2 21 ->
  (forall r, In r TO_UNTOUCHED -> getr R (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
  ajournal_gx SEGS B (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx)
    (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx) (to_own cx) ly2 S2 W2 m md (to_k cx + 1) ->
  m_fds md = m_fds md2 -> m_fs md = m_fs md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + k) -> ~ (to_sp cx - 64 - ESTACK <= a < to_sp cx - 64) ->
     aview SEGS (w_H W2) m a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m a) ->
  (forall i, 0 <= i < k -> aview SEGS (w_H W2) m (res + i) = aview SEGS (w_H W2) mem2 (c0 + adv + i)) ->
  to_gi_24c SK B MT cx c0 c1 inp adv n k res ly2 S2 W2 (mkst R (Z_to_bv 64 (BASE + TO_AT24C)) m (seg_rom SEGS)) md.
Proof.
  intros cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 R m md HPX HGI Q2 Q8 Q9 Q19 Q20 Q21 QUT HJm Hfdm Hfsm
    UNm GRm CPm.
  pose proof HPX as (HPRE & HRD & Hlive & Hmo & Hch & Hctx & Hled & HP).
  pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
  destruct (to_pre_happ SK B MT CTX cx HPX) as (AMp & AMo).
  pose proof (to_pre_P SK B MT CTX cx HPX) as HP0.
  destruct HP0 as (c0' & c1' & inp' & _ & _ & _ & _ & _ & _ & _ & _ & HAFp & _ & _ & _ & _ & HAFo & HAPop & _).
  unfold to_gi_230 in HGI. cbv zeta in HGI.
  destruct HGI as (HJ2 & Hfd2 & Hfs2 & R2 & R8 & R9 & R10 & R18 & R20 & R21 & RUT & RSV & Hbl & Hfrs & Hfa & H4096 & KAB
    & HPW & MLE & HLED & HINP & Hadv & Hadvn & Hkn & Hn319 & HNZ & HSRC & HSRC2 & Pp & Pp8 & HBP & HOW & HRAo).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs.
  pose proof (to_win SK B MT CTX cx HPX) as (Wce & W47 & W16 & Wlo & Whi).
  pose proof (ajournal_gx_row SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (Hrow & _ & _ & _).
  change (aarg (to_regs cx) 0) with (to_p cx) in *. change (aarg (to_regs cx) 1) with (to_o cx) in *.
  change (spZ (to_regs cx)) with (to_sp cx) in *.
  set (regs := to_regs cx) in *. set (W := to_W cx) in *. set (sp := to_sp cx) in *.
  set (p := to_p cx) in *. set (o := to_o cx) in *.
  assert (HKv : TEXT_OF_AK = 16448) by reflexivity.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (Ho0 : 0 <= o < 2 ^ 64) by (unfold o, to_o, aarg, argZ; apply u64_range).
  assert (Hp0 : 0 <= p < 2 ^ 64) by (unfold p, to_p, aarg, argZ; apply u64_range).
  assert (Ho64 : o + 8 <= 2 ^ 47) by (unfold amem_range in AMo; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Hp64 : p + 16 <= 2 ^ 47) by (unfold amem_range in AMp; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (HoS : o + 8 <= sp - TEXT_OF_AK \/ sp + 16 <= o) by (revert HAFo; unfold apart_frame, o, sp, to_o, to_sp, regs; clear; intros; lia).
  assert (HpS : p + 16 <= sp - TEXT_OF_AK \/ sp <= p) by (revert HAFp; unfold apart_frame, p, sp, to_p, to_sp, regs; clear; intros; lia).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (HinP : In (res, k + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (k + 1) HAR2 HinP) as (_ & _ & Hbc & Hiapp & _ & _ & _).
  assert (Hrq : req_size (k + 1) = k + 1)
    by (unfold req_size; replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  rewrite Hrq in Hbc, Hiapp. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hiapp.
  (* the write set's bytes are no bytes of the block *)
  assert (EnF : forall a, to_E cx a -> ~ (res <= a < res + (k + 1))).
  { intros a Ha. rewrite <- Hrq. apply (to_fresh_not_sclass SEGS B LAWS (to_lyc cx) (to_Sc cx) ly2 S2 W2 _ md2 res (k + 1)
      a HAR2 Hbl Hfrs Hfa Hrow).
    eapply (sclass_of_ajw SK SEGS B LAWS); [exact HGok | exact HJ | exact (Hajw a Ha) |].
    destruct (to_E_app cx a (conj AMp AMo) Ha) as [H | H]; [left; exact H | right; lia]. }
  assert (HoE : forall i, 0 <= i < 8 -> to_E cx (o + i)).
  { intros i Hi. exists (o, o + 8). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  assert (HpE : forall i, 0 <= i < 16 -> to_E cx (p + i)).
  { intros i Hi. exists (p, p + 16). split; [left; reflexivity | cbn [fst snd]; lia]. }
  (* a byte off the block and off the copy's window shows its value at the block cut *)
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + (k + 1)) -> ~ (sp - TEXT_OF_AK <= a < sp) ->
            mbyte SEGS (rdW W2 m) a = mbyte SEGS (rdW W2 mem2) a).
  { intros a Ha Hb Hw. apply (mbyte_of_aview SEGS). apply UNm; [exact Ha | lia | lia]. }
  unfold to_gi_24c. cbv zeta. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem mkst].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact HJm|].
  split; [rewrite Hfdm; exact Hfd2|]. split; [rewrite Hfsm; exact Hfs2|].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|].
  split; [exact Q19|]. split; [rewrite Q20; exact R20|]. split; [rewrite Q21; exact R21|].
  split; [intros r Hr; rewrite (QUT r Hr); exact (RUT r Hr)|].
  split.
  { intros j Hj. refine (eq_trans _ (RSV j Hj)). apply rdword_ext. intros i Hi. apply UNm; [lia | lia | lia]. }
  split; [exact Hbl|]. split; [exact Hfrs|]. split; [exact Hfa|]. split; [exact H4096|].
  split.
  { set (EF := fun a => to_E cx a \/ res <= a < res + req_size (k + 1)) in *.
    assert (KC : akept SEGS B ly2 S2 W2 mem2 W2 m (sp - TEXT_OF_AK) sp EF).
    { apply (akept_run SEGS B LAWS pa_segs_low ly2 S2 W2 mem2 md2 W2 m (sp - TEXT_OF_AK) sp EF HAR2); [lia | lia | | | ].
      - intros a Ha Hw HnE. apply UNm; [exact Ha | | lia]. intros Hq. apply HnE. unfold EF. right. rewrite Hrq. lia.
      - exact GRm.
      - intros a Ha. apply GRm. exact (HPW a Ha). }
    exact (akept_trans_ly SK SEGS B LAWS pa_segs_low (to_lyc cx) (to_Sc cx) W (to_memc cx) ly2 S2 W2 mem2
      W2 m (sp - TEXT_OF_AK) sp (sp - TEXT_OF_AK) sp EF EF EF ltac:(lia) ltac:(lia) KAB KC ltac:(lia) ltac:(lia)
      (fun b m0 Hb => ltac:(rewrite Hbl; apply in_or_app; left; exact Hb))
      (fun f Hf => ltac:(rewrite Hfrs; exact Hf)) Hfa (fun a H => H) (fun a H => H)). }
  split; [intros a Ha; apply GRm; exact (HPW a Ha)|].
  split; [exact MLE|]. split; [exact HLED|]. split; [exact HINP|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HNZ|].
  destruct HINP as (Ic0 & Ic1 & Ic0r & Ic1r & Iinp & Ilen).
  assert (Ht : Z.of_nat (length (to_t inp adv k)) = k) by (unfold to_t; rewrite length_firstn, length_skipn; lia).
  split.
  { split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hik : 0 <= Z.of_nat i < k) by lia.
    rewrite (tm_mbyte2 SEGS _ _ _ _ _ _ (CPm (Z.of_nat i) Hik)).
    rewrite (HSRC (Z.of_nat i) Hik). unfold to_t. rewrite tm_nth_firstn_skipn by lia. f_equal. lia. }
  split.
  { apply (tm_val_mem_move SEGS _ _ p 8 _ Pp). intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KM; [lia | | lia].
    intros Hq. apply (EnF x); [replace x with (p + (x - p)) by lia; apply HpE; lia | exact Hq]. }
  split.
  { apply (tm_val_mem_move SEGS _ _ (p + 8) 8 _ Pp8). intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply KM; [lia | | lia].
    intros Hq. apply (EnF x); [replace x with (p + (x - p)) by lia; apply HpE; lia | exact Hq]. }
  split.
  { destruct HBP as (junk & Hl & (Hjb & Hjw)). exists junk. split; [exact Hl|]. split.
    - apply (tm_abytes_move SEGS _ _ p junk Hjb). intros x Hx. apply KM; [lia | | lia].
      intros Hq. apply (EnF x); [replace x with (p + (x - p)) by lia; apply HpE; lia | exact Hq].
    - intros i Hi. exact (writable_kept (segs := SEGS) (w_H W2) mem2 m (p + i) (GRm (p + i)) (Hjw i Hi)). }
  split.
  { intros i Hi. exact (writable_kept (segs := SEGS) (w_H W2) mem2 m (o + i) (GRm (o + i)) (HOW i Hi)). }
  apply (tm_ra_move (aview SEGS (w_H W2) mem2) (aview SEGS (w_H W2) m) o 8 ltac:(lia) ltac:(lia)); [|exact HRAo].
  intros s Hs. apply UNm; [unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia].
Qed.

Lemma to_aft : forall cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2,
  to_pre SK B MT CTX cx -> to_gi_230 cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + TO_AT230)) mem2 (seg_rom SEGS)) md2) (to_post SK B MT cx).
Proof.
  intros cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 HPX HGI.
  pose proof HGI as HGI0.
  pose proof HPX as (HPRE & HRD & Hlive & Hmo & Hch & Hctx & Hled & HP).
  pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
  unfold to_gi_230 in HGI. cbv zeta in HGI.
  destruct HGI as (HJ2 & Hfd2 & Hfs2 & R2 & R8 & R9 & R10 & R18 & R20 & R21 & RUT & RSV & Hbl & Hfrs & Hfa & H4096 & KAB
    & HPW & MLE & HLED & HINP & Hadv & Hadvn & Hkn & Hn319 & HNZ & HSRC & HSRC2 & Pp & Pp8 & HBP & HOW & HRAo).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as (HB0' & HB1' & HB2').
  pose proof pa_segs_low as Hsegs.
  pose proof (to_win SK B MT CTX cx HPX) as (Wce & W47 & W16 & Wlo & Whi).
  assert (VB : BASE = 0x821cc) by exact (lv_text LV).
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (HKv : TEXT_OF_AK = 16448) by reflexivity.
  set (sp := to_sp cx) in *.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (HinP : In (res, k + 1) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res (k + 1) HAR2 HinP) as (_ & _ & Hbc & _ & _ & _ & _).
  assert (Hrq : req_size (k + 1) = k + 1)
    by (unfold req_size; replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  rewrite Hrq in Hbc.
  (* ---- the restart at +0x230 ---- *)
  set (xs := [Z_to_bv 64 SHADOW_OFF]).
  remember (Eimg (Ereg regs2 xs)) as E4 eqn:HE4.
  assert (HEI4 : img_env VAL A_LIM E4) by (subst E4; apply Eimg_env).
  assert (ER4 : forall (n0 : nat) (r : bv 5), Z.of_nat n0 = bv_unsigned r -> (n0 < A_TEXT)%nat -> ew E4 n0 = getr regs2 r)
    by (intros n0 r Hr Hn; subst E4; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n0 r Hr)).
  assert (HRO4 : regs_ok E4 sr_atoms regs2) by (subst E4; apply regs_ok_Eimg_Ereg).
  clear HE4.
  assert (U9 : bv_unsigned (ew E4 9) = k)
    by (rewrite (ER4 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E4 10) = res)
    by (rewrite (ER4 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)), R10; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E4 20) = SHADOW_OFF)
    by (rewrite (ER4 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)), R20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (HSA : forall f9, afact_ok E4 9 f9 ->
            st_ok_pi SEGS VAL E4 (tb_ss f9)
              (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + TO_AT230)) mem2 (seg_rom SEGS)))).
  { intros f9 Hf9. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - exact HRO4.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok tb_ss ss_facts].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U10; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
      split; [exact Hf9|].
      split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20; rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I]. }
  assert (SHOK : sh_ok SEGS (SOff 20 0) [] E4 (mrestrict (w_H W2) mem2)) by constructor.
  pose (RUN := paj_run_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
  pose proof (paj_branch (PI := PI)) as BR.
  destruct (Z.eq_dec k 0) as [K0 | K0].
  - (* ==== k = 0: +0x238 taken, to +0x24c ==== *)
    pose proof (HSA (mkAF 0 0 0) ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9, Z.pow_0_r, Z.mod_1_r; lia))
      as HS.
    pose (RUNTO := paj_run_to_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
    paj_run_tok RUN HS HJ2 SHOK tt_span; [cbn [ss_mem tb_ss]; apply awr_ok_x_nil|].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
      assert (HM1 : ms_mem msX = mem2)
        by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hin & _); cbn [ss_mem tb_ss In] in Hin;
            destruct Hin) end.
    clear HF HFr HG.
    psrr_branch_tok RUN BR HS SHOK tt_span.
    2: { exfalso. rewrite branch_eq_U, lf_U_reg, U_SLit in Hc. rewrite ?ew_ewset_other in Hc by lia.
         rewrite U9 in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_neq in Hc. lia. }
    paj_run_to_tok RUNTO HS HJ2 SHOK tt_span TO_AT24C; [cbn [ss_mem add_cond]; apply awr_ok_x_nil|].
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msX) =>
      assert (HM2 : ms_mem msX = mem2)
        by (rewrite <- HM1; apply functional_extensionality; intros x; apply HF; intros (r0 & Hin & _);
            cbn [ss_mem add_cond tb_ss In] in Hin; destruct Hin) end.
    prreg HS (2%bv : bv 5) P2. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
    prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
    rewrite ?ew_ewset_other in P2, P8, P9, P19, P20, P21 by lia.
    assert (QUT : forall r, In r TO_UNTOUCHED ->
              getr (ms_regs ms0) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
    { intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
           let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; rewrite Q; rewrite ?ew_ewset_other by lia;
           apply ER4; [vm_compute; reflexivity | unfold A_TEXT; lia] end |]).
      destruct Hr. }
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Hms. cbn [ss_pc] in Hms.
    change 24128 with TO_AT24C in Hms.
    rewrite HM2 in Hms, HJ2. rewrite Hms.
    apply (to_tail SK B MT CTX LAWS MTL cx c0 c1 inp adv n k res ly2 S2 W2 _ _ HPX).
    apply (to_24c_of cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 (ms_regs ms0) mem2 _ HPX HGI0).
    + rewrite P2. exact (ER4 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)).
    + rewrite P8. exact (ER4 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)).
    + rewrite P9. exact (ER4 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)).
    + rewrite P19. rewrite (ER4 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)). exact R10.
    + rewrite P20. exact (ER4 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)).
    + rewrite P21. exact (ER4 21%nat 21%bv eq_refl ltac:(unfold A_TEXT; lia)).
    + exact QUT.
    + exact HJ2.
    + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    + intros a _ _ _. reflexivity.
    + intros a H. exact H.
    + intros i Hi. lia.
  - (* ==== k > 0: checked_memcpy ==== *)
    pose proof (HSA (mkAF 1 319 0) ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U9, Z.pow_0_r, Z.mod_1_r; lia))
      as HS.
    paj_run_tok RUN HS HJ2 SHOK tt_span; [cbn [ss_mem tb_ss]; apply awr_ok_x_nil|].
    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
      assert (HMc : ms_mem msX = mem2)
        by (apply functional_extensionality; intros x; apply HF; intros (r0 & Hin & _);
            cbn [ss_mem tb_ss In] in Hin; destruct Hin) end.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
    rewrite ?ew_ewset_other in P1, P2, P3, P4, P10, P11, P12 by lia.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (19%bv : bv 5) P19.
    prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
    rewrite ?ew_ewset_other in P8, P9, P19, P20, P21 by lia.
    assert (QUTc : forall r, In r TO_UNTOUCHED -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)).
    { intros r Hr. unfold TO_UNTOUCHED in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr];
        [lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
           let Q := fresh "Q" in prreg HS (Z_to_bv 5 c) Q; rewrite Q; rewrite ?ew_ewset_other by lia;
           apply ER4; [vm_compute; reflexivity | unfold A_TEXT; lia] end |]).
      destruct Hr. }
    assert (Usp : spZ (ms_regs ms) = sp - 64).
    { unfold spZ. rewrite P2, (ER4 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)), R2. unfold TO_FRAME.
      apply unsigned_lit_small. lia. }
    pmkst HS. rewrite HMc. rewrite HMc in HJ2.
    destruct HINP as (Ic0 & Ic1 & Ic0r & Ic1r & Iinp & Ilen).
    destruct (HSRC2 ltac:(lia)) as (RAs & HUs & AMs & APs & WNs).
    (* the block is no block of the call's state *)
    assert (HnotSc : ~ In (res, k + 1) (ablocks B (to_lyc cx) (to_Sc cx))).
    { intros Hin. apply in_split in Hin as (l1 & l2 & El).
      pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 _ md2 (res, k + 1) (res, k + 1) l1 l2 [] HAR2
        ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as Hd.
      unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia. }
    pose proof HJ as (_ & _ & (memSA2 & HJAi2 & _) & _).
    pose proof HJAi2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
    eapply SRr_bind.
    { eapply (aj_gx_intrin_at SK SEGS B LAWS pa_segs_low OCpy _ AMCPY (to_G cx) (to_XO cx) (to_OUT cx) W2
        (ms_regs ms) mem2 (to_STK cx) (to_sp0 cx) (to_FP cx) (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx) (to_md0 cx)
        (to_own cx) ly2 S2 _ (to_k cx + 1) res (c0 + adv) k _ HGok HJ2).
      - rewrite P10, (ER4 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)). exact R10.
      - rewrite P11, (ER4 18%nat 18%bv eq_refl ltac:(unfold A_TEXT; lia)). exact R18.
      - rewrite P12, (ER4 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)). exact R9.
      - lia.
      - lia.
      - lia.
      - rewrite Usp. replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact W16.
      - rewrite Usp, HES. lia.
      - rewrite Usp. lia.
      - rewrite P3, (ER4 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)).
        exact (eq_trans (RUT 3 ltac:(unfold TO_UNTOUCHED; cbn; tauto)) Hgp).
      - rewrite P4, (ER4 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)).
        exact (eq_trans (RUT 4 ltac:(unfold TO_UNTOUCHED; cbn; tauto)) Htp).
      - exact P1.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. left. split; [|split; [lia | rewrite Usp, HES; lia]].
        unfold awr_byte. right.
        destruct (in_dec tm_dec (res, k + 1) (ablocks B (to_ly cx) (to_S cx))) as [Hin0|Hin0].
        + left. split.
          * replace a with (res + (a - res)) by lia. apply (Hgone res (k + 1) (a - res) Hin0 HnotSc). rewrite Hrq. lia.
          * exists res, (k + 1). split; [exact HinP | rewrite Hrq; lia].
        + right. left. exists res, (k + 1). split; [exact HinP|]. split; [exact Hin0 | rewrite Hrq; lia].
      - exact (amem_range_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 res (k + 1) res k HAR2 HinP ltac:(lia)
          ltac:(rewrite Hrq; lia)).
      - exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 res (k + 1) res k HAR2 HinP ltac:(lia)
          ltac:(rewrite Hrq; lia)).
      - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 res (k + 1) res k HAR2 HinP
          ltac:(lia) ltac:(rewrite Hrq; lia) ltac:(lia)).
      - split; [lia|]. split; [unfold amem_range in AMs; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
        split.
        { intros a Ha. split.
          - pose proof (HSRC (a - (c0 + adv)) ltac:(lia)) as Hm.
            replace (c0 + adv + (a - (c0 + adv))) with a in Hm by lia.
            unfold aview. rewrite Hm. destruct (nth_error inp _) eqn:En; [discriminate|].
            apply nth_error_None in En. lia.
          - rewrite Usp, HES. pose proof (WNs a Ha). lia. }
        split; [exact APs|]. split; [exact AMs|]. split; [exact RAs|]. intros _. exact HUs. }
    cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & H10c & Hcpy & Hun5 & Hpr5 & Hsm5).
    change (Z_to_bv 64 (BASE + 24128)) with (Z_to_bv 64 (BASE + TO_AT24C)).
    apply (to_tail SK B MT CTX LAWS MTL cx c0 c1 inp adv n k res ly2 S2 W2 _ _ HPX).
    apply (to_24c_of cx c0 c1 inp adv n k res ly2 S2 W2 regs2 mem2 md2 regs5 mem5 md5 HPX HGI0).
    + exact (eq_trans (HP5 2 ltac:(unfold acallee_saved; lia))
        (eq_trans P2 (ER4 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)))).
    + exact (eq_trans (HP5 8 ltac:(unfold acallee_saved; lia))
        (eq_trans P8 (ER4 8%nat 8%bv eq_refl ltac:(unfold A_TEXT; lia)))).
    + exact (eq_trans (HP5 9 ltac:(unfold acallee_saved; lia))
        (eq_trans P9 (ER4 9%nat 9%bv eq_refl ltac:(unfold A_TEXT; lia)))).
    + exact (eq_trans (HP5 19 ltac:(unfold acallee_saved; lia))
        (eq_trans P19 (eq_trans (ER4 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)) R10))).
    + exact (eq_trans (HP5 20 ltac:(unfold acallee_saved; lia))
        (eq_trans P20 (ER4 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)))).
    + exact (eq_trans (HP5 21 ltac:(unfold acallee_saved; lia))
        (eq_trans P21 (ER4 21%nat 21%bv eq_refl ltac:(unfold A_TEXT; lia)))).
    + intros r Hr. exact (eq_trans (HP5 r ltac:(unfold TO_UNTOUCHED in Hr; cbn [In] in Hr; unfold acallee_saved; lia))
        (QUTc r Hr)).
    + exact HJ5.
    + rewrite (proj1 (same_but_materialized_fs _ _ Hsm5)). repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    + rewrite (proj2 (same_but_materialized_fs _ _ Hsm5)). repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
    + intros a Ha Hb Hw. apply Hun5; [exact Ha | exact Hb | rewrite Usp; exact Hw].
    + exact Hpr5.
    + intros i Hi. exact (Hcpy i Hi).
Qed.

End b.
End a.
