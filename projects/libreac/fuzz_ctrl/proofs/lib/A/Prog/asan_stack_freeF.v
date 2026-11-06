(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 1441 of its 1505 lines of code are new or changed and 947 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTail.v, with its module paths and module names changed; 534 of its 819 lines of code are new or changed and 1220 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/YTailF.v, with its module paths and module names changed; 465 of its 503 lines of code are new or changed and 781 lines of the source are left out. *)
(* asan_stack_free_6_contract_F (asan_stack_free_cF.v) by route 1 (ROUTE1.md (a working note, not in this delivery)), as asan_set_shadowF.v
   proves asan_set_shadow_contract_F: the walk runs UNCHANGED on the restricted memory normalize_P m, where P
   keeps only the four regions the footprint names -- the image [IMG_LO, IMG_HI), the callee's stack window
   [sp - 32, sp), the side stack [FS, FS + FS_SIZE) and the frame's 512 shadow bytes [SA, SA + 512) with
   SA = shadow_addr fr.  MemNormP.evtF_normalize_P turns that run into a footprint run on m with footprint RNG_P;
   the rng premises weaken RNG_P to RNG (MemNormP.evtF_RNG_P_weaken_top).  The post comes back to m by the _rel_P
   transfer lemmas.

   WHAT DIFFERS FROM asan_set_shadowF.v, and why.
   1. The input walk is Tk/AW/Sf6L.stack_free_6_L, not the frozen Tk/AW/Sf6.stack_free_6: the frozen one asks
      `shadow_rw m` (EVERY shadow byte readable and writable), which no restricted memory satisfies.  Sf6L is
      that same walk with the premise localized to the 512 shadow bytes it touches, and without the post's
      shadow_rw conjunct (asan_stack_free_cF.v states both forms; Sf6L.v's header lists the four edits).
   2. `shadow_rw m'` of the real post is re-established HERE, on the full memory, where shadow_rw does hold:
      shadow_rw_write_L below is Sf6.shadow_rw_write restated in this (Lib) world -- a shadow byte outside
      [SA, SA + 512) is outside the run's write set, and one inside is readable because the run left 0xf5 there.
   3. The run is given lo := sp - 32, not the caller's lo: only [sp - 32, sp) is in the footprint, so only that
      part of the stack can be carried into the restricted memory.  `stk rsegs m' lo sp` of the real post is
      rebuilt by stk_after below: below sp - 32 the run changed nothing except the flag byte, which it left
      readable, and the shadow window is apart from [lo, sp) (shadow vs app).
   Helpers taken from asan_memsetF.v and asan_set_shadowF.v, not restated here: in_rngb / in_rngb_true (the kept
   byte set), in_seg_img (every loaded segment lies in the image), stk_rel_P (stk back to the full memory),
   asan_cells_P (the runtime cells into the restricted memory).
   The shadow arithmetic (app_in_shadow, shadow_addr_add, shadow_range_in, shadow_stk) is Tk/AW/SmLib.v's; it is
   restated below over this world's `stk` rather than that file's, so this file does not pull the walk engine. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
(* MemNorm by its full logical path: lib/, lib/A/, lib/B/ and lib/U/ each carry a MemNorm.v, so the partial
   `From ...fuzz_ctrl.lib Require MemNorm` can bind any of them; this file means the core one, which MemNormP
   is stated over. *)
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c asan_stack_free_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_free_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memsetF asan_set_shadowF.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Sf6L.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require asan_stack_free_c_on.
Import ListNotations.
Open Scope Z_scope.

(* `Require Sf6L` pulls in lib/A/Tk/UL/LiaTuning.v, whose global `Ltac lia ::=` is the walk engine's tuned one.
   It is what this file's `lia` means below, and it is right for goals with variables; on the two CLOSED
   contradictions about the top byte 2^64 - 1 it gives "No applicable tactic", so those two are proved HERE, in
   a context of three hypotheses, with the plain tactic named in full (pinning `lia` to the plain one for the
   whole file instead makes it run out of 120 GB in this file's 40-hypothesis contexts: measured, build
   20261029T045951Z, 602 s and 125 GB, killed). *)

(* ---------------------------------------------------------------- the kept byte set *)

Definition PSF (S0 FS SA : Z) (a : word) : bool :=
  in_rngb IMG_LO (IMG_HI - IMG_LO) (bv_unsigned a) || in_rngb (S0 - 32) 32 (bv_unsigned a)
  || in_rngb FS FS_SIZE (bv_unsigned a) || in_rngb SA 512 (bv_unsigned a).

Lemma PSF_or : forall S0 FS SA x, 0 <= x < 2^64 ->
  (IMG_LO <= x < IMG_HI \/ S0 - 32 <= x < S0 \/ FS <= x < FS + FS_SIZE \/ SA <= x < SA + 512) ->
  PSF S0 FS SA (wa x) = true.
Proof.
  intros S0 FS SA x Hx H. unfold PSF. rewrite wa_unsigned by exact Hx.
  destruct H as [H|[H|[H|H]]].
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left. apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; right. apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; right. apply in_rngb_true. lia.
  - apply orb_true_iff; right. apply in_rngb_true. lia.
Qed.

Lemma PSF_inv : forall S0 FS SA x, 0 <= x < 2^64 -> PSF S0 FS SA (wa x) = true ->
  IMG_LO <= x < IMG_HI \/ S0 - 32 <= x < S0 \/ FS <= x < FS + FS_SIZE \/ SA <= x < SA + 512.
Proof.
  intros S0 FS SA x Hx H. unfold PSF in H. rewrite wa_unsigned in H by exact Hx.
  apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]; [apply orb_true_iff in H as [H|H]|]|];
    apply in_rngb_true in H; [left | right; left | right; right; left | right; right; right]; lia.
Qed.

(* The top byte of the address space is in no kept region: the image ends at IMG_HI, and the other three lie
   under HIGHMEM_BEG / APPMEM_END. *)
Lemma PSF_top : forall S0 FS SA, S0 <= APPMEM_END -> FS + FS_SIZE <= S0 - 32 -> SA + 512 <= HIGHMEM_BEG ->
  PSF S0 FS SA (wa (2^64 - 1)) = false.
Proof.
  intros S0 FS SA H1 H2 H3.
  destruct (PSF S0 FS SA (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
  destruct (PSF_inv S0 FS SA (2^64 - 1) ltac:(Stdlib.micromega.Lia.lia) E) as [X|[X|[X|X]]];
    unfold IMG_LO, IMG_HI, FS_SIZE, HIGHMEM_BEG, APPMEM_END in *; Stdlib.micromega.Lia.lia.
Qed.

Lemma in_seg_top : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa (2^64 - 1)) = false.
Proof.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
  pose proof (in_seg_img (2^64 - 1) ltac:(Stdlib.micromega.Lia.lia) E) as X.
  unfold IMG_LO, IMG_HI in X. Stdlib.micromega.Lia.lia.
Qed.

(* ---------------------------------------------------------------- the shadow arithmetic (SmLib's, restated) *)

Lemma shadow_addr_add_L : forall a x, shadow_addr (a + 8 * x) = shadow_addr a + x.
Proof. intros a x. unfold shadow_addr. rewrite (Z.mul_comm 8 x), Z.div_add by lia. lia. Qed.

Lemma app_in_shadow_L : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END.
  intros a [H|H]; [left|right]; Z.div_mod_to_equations; lia.
Qed.

Lemma shadow_range_in_L : forall A n, 0 <= A -> A mod 8 = 0 -> 0 < n ->
  (forall x, A <= x < A + 8 * n -> app_mem x) ->
  forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y.
Proof.
  intros A n HA HM Hn APP y Hy.
  replace y with (shadow_addr (A + 8 * (y - shadow_addr A))) by (rewrite shadow_addr_add_L; lia).
  apply app_in_shadow_L, APP. lia.
Qed.

Lemma shadow_stk_L : forall m A n, shadow_rw m -> 0 <= A -> A mod 8 = 0 -> 0 < n ->
  (forall x, A <= x < A + 8 * n -> app_mem x) -> stk rsegs m (shadow_addr A) (shadow_addr A + n).
Proof.
  intros m A n SRW HA HM Hn APP.
  assert (SH : forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y)
    by (apply shadow_range_in_L; assumption).
  pose proof (app_in_shadow_L _ (APP (A + 8 * (n - 1)) ltac:(lia))) as SL. rewrite shadow_addr_add_L in SL.
  assert (SA0 : 0 <= shadow_addr A)
    by (unfold shadow_addr, ASAN_K; pose proof (Z.div_pos A 8 HA ltac:(lia)); lia).
  split; [exact SA0|]. split.
  - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in SL.
    change (2 ^ 64) with 18446744073709551616. lia.
  - intros y Hy. exact (SRW y (SH y Hy)).
Qed.

(* ---------------------------------------------------------------- into and out of the restricted memory *)

Lemma bytes_at_P_keep : forall (P : word -> bool) m a bs, ro_agree rsegs m ->
  a + Z.of_nat (length bs) <= TASK_SIZE ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> P (wa x) = true) ->
  bytes_at rsegs m a bs -> bytes_at rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) a bs.
Proof.
  intros P m a bs RO Hl HP H. apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.bytes_at_P_of_cj rsegs P m a bs).
  - intros i Hi. left. apply HP. lia.
  - apply bytes_normalize_low; [exact RO | exact Hl | exact H].
Qed.

Lemma stk_P_keep : forall (P : word -> bool) m lo hi, mem_inv rsegs m -> hi <= TASK_SIZE ->
  (forall x, lo <= x < hi -> P (wa x) = true) ->
  stk rsegs m lo hi -> stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) lo hi.
Proof.
  intros P m lo hi HMI Hhi HP H.
  refine (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.stk_P_of_cj rsegs P m lo hi _ (stk_normalize m lo hi HMI H Hhi)).
  intros a Ha. left. apply HP. exact Ha.
Qed.

(* ---------------------------------------------------------------- stk and shadow_rw across the run (Sf6's) *)

Lemma bytes_at_some_L : forall (m : word -> option byte) A bs a, bytes_at rsegs m A bs ->
  A <= a < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m A bs a (H0 & H1 & H) Ha. assert (LT : (Z.to_nat (a - A) < length bs)%nat) by lia.
  specialize (H _ LT). rewrite Z2Nat.id in H by lia. replace (A + (a - A)) with a in H by lia.
  destruct (nth_error bs (Z.to_nat (a - A))) as [b|] eqn:E; [exists b; exact H|].
  apply nth_error_None in E. lia.
Qed.

Lemma stk_after : forall (m m' : word -> option byte) W lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall a, lo <= a < hi -> outside W a \/ (exists b, mrd rsegs m' (wa a) = Some b)) ->
  stk rsegs m' lo hi.
Proof.
  intros m m' W lo hi (H0 & H1 & H) MU WM HC. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [apply WM; exact Hw|].
  destruct (HC a Ha) as [Ho | (b' & Hb')]; [|exists b'; exact Hb'].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma shadow_rw_write_L : forall (m m' : word -> option byte) W A n,
  shadow_rw m -> munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> a < A \/ A + n <= a -> outside W a) ->
  (forall a, A <= a < A + n -> exists b, mrd rsegs m' (wa a) = Some b) -> shadow_rw m'.
Proof.
  intros m m' W A n SRW MU WM OUT IN a Ha. destruct (SRW a Ha) as [Hw [b Hb]].
  split; [apply WM; exact Hw|].
  destruct (in_shadow_range a Ha) as [R1 R2].
  destruct (Z_lt_le_dec a A) as [L1|L1]; [| destruct (Z_lt_le_dec a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. apply OUT; [exact Ha| left; exact L1].
  - apply IN. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. apply OUT; [exact Ha| right; exact L2].
Qed.

(* ---------------------------------------------------------------- the footprint contract *)

Theorem asan_stack_free_6_holds_F : forall RNG, asan_stack_free_6_contract_F RNG.
Proof.
  intros RNG. unfold asan_stack_free_6_contract_F.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS j.
  cbv zeta. intros HJ EFR HL HL8 PL FLGB FLWB AC SRW MI ST LOK ROOM HLO HHI RB RI RW RF RS.
  pose proof PL as (FS0 & FS4K & FSGT & FAPP & FSTK).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RA0.
  assert (EN : fs_shadow_n 6 (bv_unsigned a1) = 512) by reflexivity.
  change (fs_M 6) with 256 in HJ.
  assert (EFA : bv_unsigned a0 = FS + 6328320 + j * 4096).
  { rewrite EFR. unfold fs_frame, fs_B.
    change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + j * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + j * (64 * 64)).
    lia. }
  assert (EFG : fs_flag FS 6 j = FS + 36352 + j).
  { unfold fs_flag.
    change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + j) with (FS + 4096 + 32768 - 512 + j). lia. }
  unfold FS_SIZE, ASAN_GT in *.
  unfold HIGHMEM_BEG, APPMEM_END in HLO, HHI.
  rewrite EN in RS.
  remember (shadow_addr (bv_unsigned a0)) as SA eqn:ESA.
  rewrite <- ?ESA in RS.
  assert (ESAF : shadow_addr (fs_frame FS 6 j) = SA) by (rewrite <- EFR; symmetry; exact ESA).
  assert (FA8 : bv_unsigned a0 mod 8 = 0) by (rewrite EFA; lia).
  assert (SHI : forall y, SA <= y < SA + 512 -> in_shadow y).
  { rewrite ESA. apply shadow_range_in_L; [lia| exact FA8| lia|]. intros x Hx. apply FAPP. lia. }
  assert (SAL : 0x5fe000 <= SA).
  { pose proof (SHI SA ltac:(lia)) as X.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (SAU : SA + 512 <= 0x10007fff8000).
  { pose proof (SHI (SA + 511) ltac:(lia)) as X.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  (* ---- the kept set and the weakening of RNG_P to RNG ---- *)
  pose (P := PSF (bv_unsigned sp) FS SA).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [unfold IMG_LO, IMG_HI in Hx; lia| left; exact Hx]. }
  assert (PW : forall x, bv_unsigned sp - 32 <= x < bv_unsigned sp -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; left; exact Hx]. }
  assert (PF : forall x, FS <= x < FS + 11571200 -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; right; left; exact Hx]. }
  assert (PS : forall x, SA <= x < SA + 512 -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; right; right; exact Hx]. }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { apply PSF_top; unfold APPMEM_END, HIGHMEM_BEG, FS_SIZE; lia. }
  assert (SEG0 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa (2^64 - 1)) = false) by exact in_seg_top.
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PSF_inv (bv_unsigned sp) FS SA x Hx Hp) as [X|[X|[X|X]]].
      + destruct RI as (_ & _ & R). apply R; unfold IMG_LO, IMG_HI in X; lia.
      + destruct RW as (_ & _ & R). apply R; lia.
      + destruct RF as (_ & _ & R). unfold FS_SIZE in X. apply R; lia.
      + destruct RS as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs) as X.
      unfold IMG_LO, IMG_HI in X. apply R; lia. }
  apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 SEG0 HB).
  clear HB P0 SEG0.
  (* ---- the premises of the walk, in the restricted memory ---- *)
  pose proof (ro_agree_of_mem_inv m MI) as RO.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  assert (MI0 : mem_inv rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m)).
  { intros x b Hx. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P in Hx.
    destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP rsegs P x); [exact (MI x b Hx) | discriminate Hx]. }
  assert (ST32 : stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp)).
  { destruct (stk_split rsegs m lo (bv_unsigned sp - 32) (bv_unsigned sp) ST ltac:(lia)) as [_ H]. exact H. }
  assert (SHSTK : stk rsegs m SA (SA + 512)).
  { rewrite ESA. apply shadow_stk_L; [exact SRW| lia| exact FA8| lia|]. intros x Hx. apply FAPP. lia. }
  assert (STF0 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) FS (FS + 11571200))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PF; lia| exact FSTK]).
  assert (ST320 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned sp - 32) (bv_unsigned sp))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PW; lia| exact ST32]).
  assert (SHSTK0 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) SA (SA + 512))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PS; lia| exact SHSTK]).
  assert (SHSTK0' : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (shadow_addr (bv_unsigned a0))
                      (shadow_addr (bv_unsigned a0) + fs_shadow_n 6 (bv_unsigned a1)))
    by (rewrite <- ESA, EN; exact SHSTK0).
  assert (FLG0 : bytes_at rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (fs_flag FS 6 j) [Z_to_bv 8 1]).
  { apply (bytes_at_P_keep P m _ _ RO); [| | exact FLGB].
    - cbn [length]. rewrite EFG. unfold TASK_SIZE. lia.
    - intros x Hx. cbn [length] in Hx. rewrite EFG in Hx. apply PF. lia. }
  assert (FLW0 : bytes_at rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned a0 + fs_B 6 - 8)
                   (le8 (Z_to_bv 64 (fs_flag FS 6 j)))).
  { apply (bytes_at_P_keep P m _ _ RO); [| | exact FLWB].
    - rewrite length_le8. change (fs_B 6) with 4096. unfold TASK_SIZE. lia.
    - intros x Hx. rewrite length_le8 in Hx. change (fs_B 6) with 4096 in Hx. apply PF. lia. }
  assert (AC0 : asan_cells (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m)) by exact (asan_cells_P P m PI MI AC).
  assert (PL0 : fs_place (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) FS).
  { unfold fs_place. split; [exact FS0|]. split; [exact FS4K|]. split; [exact FSGT|].
    split; [exact FAPP| exact STF0]. }
  (* ---- the run on the restricted memory, lifted ---- *)
  pose proof Sf6L.stack_free_6_L as HL6.
  unfold asan_stack_free_6_contract_L, asan_stack_free_contract_L, ASAN_STACK_FREE_6, ASAN_STACK_FREE_K in HL6.
  cbv zeta in HL6.
  apply (ExecF.evtF_mono rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.RNG_P rsegs P) (fun st => exists st0,
            asan_stack_free_post_L 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (bv_unsigned a1) FS j (bv_unsigned sp - 32) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) st0
            /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.ms_rel_P rsegs P st st0 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    exact (HL6 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned sp - 32) FS j
             HJ EFR HL HL8 PL0 FLG0 FLW0 AC0 SHSTK0' MI0 ST320 ltac:(lia) ROOM ltac:(unfold HIGHMEM_BEG; lia) HHI).
  - intros st (st0 & HQ & REL & SAME).
    cbv zeta in HQ.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU0 & WM0 & MI0' & ST0' & PL0' & FLGZ & SHB & AC0').
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    assert (MUr : munch [(fs_flag FS 6 j, fs_flag FS 6 j + 1);
                         (shadow_addr (fs_frame FS 6 j), shadow_addr (fs_frame FS 6 j) + fs_shadow_n 6 (bv_unsigned a1));
                         (bv_unsigned sp - 32, bv_unsigned sp)] m (ms_mem st))
      by (eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.munch_rel_P rsegs P); [exact REL0| exact E8| exact SAME| exact MU0]).
    assert (WMr : wmono rsegs m (ms_mem st))
      by (eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.wmono_rel_P rsegs P); [exact REL0| exact E8| exact SAME| exact WM0]).
    assert (FLGr : bytes_at rsegs (ms_mem st) (fs_flag FS 6 j) [Z_to_bv 8 0])
      by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 FLGZ).
    assert (SHBr : bytes_at rsegs (ms_mem st) (shadow_addr (fs_frame FS 6 j))
                     (repeat (Z_to_bv 8 0xf5) (Z.to_nat (fs_shadow_n 6 (bv_unsigned a1)))))
      by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 SHB).
    assert (STmid : stk rsegs (ms_mem st) (bv_unsigned sp - 32) (bv_unsigned sp))
      by exact (stk_rel_P P (ms_mem st) m0' _ _ E8 ST0').
    unfold asan_stack_free_post. cbv zeta.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MUr.
    + exact WMr.
    + intros x b Hx. destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (MI x b Hx).
    + (* stk rsegs (ms_mem st) lo sp: below sp - 32 only the flag byte moved, and it is readable *)
      apply (stk_after m (ms_mem st) _ lo (bv_unsigned sp) ST MUr WMr).
      intros a Ha.
      destruct (Z_le_gt_dec (bv_unsigned sp - 32) a) as [C1|C1].
      * right. destruct STmid as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb.
      * destruct (Z.eq_dec a (fs_flag FS 6 j)) as [C2|C2].
        -- right. rewrite C2. apply (bytes_at_some_L (ms_mem st) (fs_flag FS 6 j) [Z_to_bv 8 0] _ FLGr).
           cbn [length]. lia.
        -- left. cbn [outside]. rewrite ESAF, EN.
           split; [lia|]. split; [lia|]. split; [lia| exact I].
    + (* fs_place *)
      destruct PL0' as (_ & _ & _ & _ & STF').
      unfold fs_place. split; [exact FS0|]. split; [exact FS4K|]. split; [exact FSGT|]. split; [exact FAPP|].
      exact (stk_rel_P P (ms_mem st) m0' _ _ E8 STF').
    + exact FLGr.
    + exact SHBr.
    + apply (asan_cells_kept [(fs_flag FS 6 j, fs_flag FS 6 j + 1);
                              (shadow_addr (fs_frame FS 6 j), shadow_addr (fs_frame FS 6 j) + fs_shadow_n 6 (bv_unsigned a1));
                              (bv_unsigned sp - 32, bv_unsigned sp)] m (ms_mem st) AC MUr).
      cbn [disjoint_from]. rewrite ?ESAF, ?EFG. unfold RT_LO, RT_HI. lia.
    + (* shadow_rw: outside [SA, SA + 512) the run wrote no shadow byte, inside it left 0xf5 *)
      apply (shadow_rw_write_L m (ms_mem st) _ SA 512 SRW MUr WMr).
      * intros a Hin Hout. cbn [outside]. rewrite ESAF, EN.
        split; [|split; [lia|]].
        -- intros X. apply (app_not_shadow a); [|exact Hin].
           replace a with (fs_flag FS 6 j) by lia. apply FAPP. rewrite EFG. lia.
        -- split; [|exact I].
           unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia.
      * intros a Ha. apply (bytes_at_some_L (ms_mem st) (shadow_addr (fs_frame FS 6 j)) _ a SHBr).
        rewrite repeat_length, EN. rewrite Z2Nat.id by lia. rewrite ESAF. lia.
Qed.

(* ---------------------------------------------------------------- route (C): the _on twin *)

(* Route (C) (a Theorem Labs lane 09:20Z; frozen form a Theorem Labs lane's ASSIGN.md (a working note, not in this delivery); ADDITIVE: every proof line above is unchanged).
   asan_stack_free_6_holds_F_on is asan_stack_free_6_holds_F with
     - the universal shadow premise (AsanRT.shadow_rw: every shadow byte) narrowed to `shadow_rw_on R m`,
       R = SFO.asan_stack_free_shadow_R 6 L FS j of
       a Theorem Labs lane's leaf lib/A/Prog/asan_stack_free_c_on.v: the frame's 512 shadow bytes
       [shadow_addr fr, shadow_addr fr + 512). The run needs exactly those PRESENT: its 64 sd stores fill them with
       0xf5 and it reads no shadow byte (Tk/AW/Sf6.v stack_free_6_on, the plain run, takes the same R). The proof
       reads the premise only there: shadow_stk_on_L below at A = fr, n = 512 gives the stk window SHSTK, as
       shadow_stk_L does from shadow_rw in the old proof;
     - the post SFO.asan_stack_free_post_on, whose last conjunct is `forall P, shadow_rw_on P m -> shadow_rw_on P m'`
       in place of the universal post conjunct, from shadow_rw_write_on_L below (the old proof's shadow_rw_write_L step).
   Every other premise (mem_inv included) and the rest of the proof are the old ones. The statement is
   Seg/YTailF.v's stack_free_6_F_on, word for word, so YTailF.v's stack_free_6_F_on_gen is `exact` of it.
   shadow_stk_on_L / shadow_rw_write_on_L are SmLib.shadow_stk_on / Sf6.shadow_rw_write_on restated in this world,
   as shadow_stk_L / shadow_rw_write_L above restate SmLib.shadow_stk / Sf6.shadow_rw_write. *)
Module SFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_free_c_on.

Lemma shadow_stk_on_L : forall m A n,
  A.ShadowRwOn.shadow_rw_on (fun y => shadow_addr A <= y < shadow_addr A + n) m -> 0 <= A -> A mod 8 = 0 -> 0 < n ->
  (forall x, A <= x < A + 8 * n -> app_mem x) -> stk rsegs m (shadow_addr A) (shadow_addr A + n).
Proof.
  intros m A n SRW HA HM Hn APP.
  assert (SH : forall y, shadow_addr A <= y < shadow_addr A + n -> in_shadow y)
    by (apply shadow_range_in_L; assumption).
  pose proof (app_in_shadow_L _ (APP (A + 8 * (n - 1)) ltac:(lia))) as SL. rewrite shadow_addr_add_L in SL.
  assert (SA0 : 0 <= shadow_addr A)
    by (unfold shadow_addr, ASAN_K; pose proof (Z.div_pos A 8 HA ltac:(lia)); lia).
  split; [exact SA0|]. split.
  - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in SL.
    change (2 ^ 64) with 18446744073709551616. lia.
  - intros y Hy. exact (SRW y Hy (SH y Hy)).
Qed.

Lemma shadow_rw_write_on_L : forall (m m' : word -> option byte) W A n,
  munch W m m' -> wmono rsegs m m' ->
  (forall a, in_shadow a -> a < A \/ A + n <= a -> outside W a) ->
  (forall a, A <= a < A + n -> exists b, mrd rsegs m' (wa a) = Some b) ->
  forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros m m' W A n MU WM OUT IN P SRW a Hp Ha. destruct (SRW a Hp Ha) as [Hw [b Hb]].
  split; [apply WM; exact Hw|].
  destruct (in_shadow_range a Ha) as [R1 R2].
  destruct (Z_lt_le_dec a A) as [L1|L1]; [| destruct (Z_lt_le_dec a (A + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. apply OUT; [exact Ha| left; exact L1].
  - apply IN. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
    rewrite wa_unsigned by lia. apply OUT; [exact Ha| right; exact L2].
Qed.

Theorem asan_stack_free_6_holds_F_on : forall RNG : ExecF.footprint,
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS j : Z),
  let fr := bv_unsigned a0 in let L := bv_unsigned a1 in let S0 := bv_unsigned sp in
  0 <= j < fs_M 6 -> fr = fs_frame FS 6 j ->
  1 <= L <= fs_B 6 -> L mod 8 = 0 ->
  fs_place m FS ->
  bytes_at rsegs m (fs_flag FS 6 j) [Z_to_bv 8 1] ->
  bytes_at rsegs m (fr + fs_B 6 - 8) (le8 (Z_to_bv 64 (fs_flag FS 6 j))) ->
  asan_cells m -> A.ShadowRwOn.shadow_rw_on (SFO.asan_stack_free_shadow_R 6 L FS j) m -> mem_inv rsegs m ->
  stk rsegs m lo S0 -> lo + 32 <= S0 -> FS + FS_SIZE <= S0 - 32 ->
  HIGHMEM_BEG <= lo -> S0 <= APPMEM_END ->
  RngBytes.rng_bytes RNG ->
  ExecF.rng RNG 0x10000 0x5ee000 ->
  ExecF.rng RNG (S0 - 32) 32 ->
  ExecF.rng RNG FS FS_SIZE ->
  ExecF.rng RNG (shadow_addr fr) (fs_shadow_n 6 L) ->
  ExecF.evtF rsegs RNG
    (SFO.asan_stack_free_post_on 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS j lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASAN_STACK_FREE_6) fc None m (seg_rom rsegs)).
Proof.
  intros RNG.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS j.
  cbv zeta. intros HJ EFR HL HL8 PL FLGB FLWB AC SRW MI ST LOK ROOM HLO HHI RB RI RW RF RS.
  pose proof PL as (FS0 & FS4K & FSGT & FAPP & FSTK).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RA0.
  assert (EN : fs_shadow_n 6 (bv_unsigned a1) = 512) by reflexivity.
  change (fs_M 6) with 256 in HJ.
  assert (EFA : bv_unsigned a0 = FS + 6328320 + j * 4096).
  { rewrite EFR. unfold fs_frame, fs_B.
    change (FS + 36864 + Z.of_nat 6 * 2 ^ 20 + j * (64 * 2 ^ Z.of_nat 6)) with (FS + 36864 + 6 * 1048576 + j * (64 * 64)).
    lia. }
  assert (EFG : fs_flag FS 6 j = FS + 36352 + j).
  { unfold fs_flag.
    change (FS + 4096 + 2 ^ 15 - 2 ^ (15 - Z.of_nat 6) + j) with (FS + 4096 + 32768 - 512 + j). lia. }
  unfold FS_SIZE, ASAN_GT in *.
  unfold HIGHMEM_BEG, APPMEM_END in HLO, HHI.
  rewrite EN in RS.
  remember (shadow_addr (bv_unsigned a0)) as SA eqn:ESA.
  rewrite <- ?ESA in RS.
  assert (ESAF : shadow_addr (fs_frame FS 6 j) = SA) by (rewrite <- EFR; symmetry; exact ESA).
  assert (FA8 : bv_unsigned a0 mod 8 = 0) by (rewrite EFA; lia).
  assert (SHI : forall y, SA <= y < SA + 512 -> in_shadow y).
  { rewrite ESA. apply shadow_range_in_L; [lia| exact FA8| lia|]. intros x Hx. apply FAPP. lia. }
  assert (SAL : 0x5fe000 <= SA).
  { pose proof (SHI SA ltac:(lia)) as X.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  assert (SAU : SA + 512 <= 0x10007fff8000).
  { pose proof (SHI (SA + 511) ltac:(lia)) as X.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in X. lia. }
  (* ---- the kept set and the weakening of RNG_P to RNG ---- *)
  pose (P := PSF (bv_unsigned sp) FS SA).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [unfold IMG_LO, IMG_HI in Hx; lia| left; exact Hx]. }
  assert (PW : forall x, bv_unsigned sp - 32 <= x < bv_unsigned sp -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; left; exact Hx]. }
  assert (PF : forall x, FS <= x < FS + 11571200 -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; right; left; exact Hx]. }
  assert (PS : forall x, SA <= x < SA + 512 -> P (wa x) = true).
  { intros x Hx. apply PSF_or; [lia| right; right; right; exact Hx]. }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { apply PSF_top; unfold APPMEM_END, HIGHMEM_BEG, FS_SIZE; lia. }
  assert (SEG0 : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa (2^64 - 1)) = false) by exact in_seg_top.
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PSF_inv (bv_unsigned sp) FS SA x Hx Hp) as [X|[X|[X|X]]].
      + destruct RI as (_ & _ & R). apply R; unfold IMG_LO, IMG_HI in X; lia.
      + destruct RW as (_ & _ & R). apply R; lia.
      + destruct RF as (_ & _ & R). unfold FS_SIZE in X. apply R; lia.
      + destruct RS as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs) as X.
      unfold IMG_LO, IMG_HI in X. apply R; lia. }
  apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 SEG0 HB).
  clear HB P0 SEG0.
  (* ---- the premises of the walk, in the restricted memory ---- *)
  pose proof (ro_agree_of_mem_inv m MI) as RO.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  assert (MI0 : mem_inv rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m)).
  { intros x b Hx. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P in Hx.
    destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP rsegs P x); [exact (MI x b Hx) | discriminate Hx]. }
  assert (ST32 : stk rsegs m (bv_unsigned sp - 32) (bv_unsigned sp)).
  { destruct (stk_split rsegs m lo (bv_unsigned sp - 32) (bv_unsigned sp) ST ltac:(lia)) as [_ H]. exact H. }
  (* the one read of the narrowed premise: the frame's 512 shadow bytes, R itself *)
  assert (SHSTK : stk rsegs m SA (SA + 512)).
  { rewrite ESA. apply shadow_stk_on_L; [| lia| exact FA8| lia|].
    - refine (A.ShadowRwOn.shadow_rw_on_mono _ _ m _ SRW). intros y Hy.
      unfold SFO.asan_stack_free_shadow_R. rewrite <- EFR, EN. exact Hy.
    - intros x Hx. apply FAPP. lia. }
  assert (STF0 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) FS (FS + 11571200))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PF; lia| exact FSTK]).
  assert (ST320 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned sp - 32) (bv_unsigned sp))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PW; lia| exact ST32]).
  assert (SHSTK0 : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) SA (SA + 512))
    by (apply stk_P_keep; [exact MI| unfold TASK_SIZE; lia| intros x Hx; apply PS; lia| exact SHSTK]).
  assert (SHSTK0' : stk rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (shadow_addr (bv_unsigned a0))
                      (shadow_addr (bv_unsigned a0) + fs_shadow_n 6 (bv_unsigned a1)))
    by (rewrite <- ESA, EN; exact SHSTK0).
  assert (FLG0 : bytes_at rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (fs_flag FS 6 j) [Z_to_bv 8 1]).
  { apply (bytes_at_P_keep P m _ _ RO); [| | exact FLGB].
    - cbn [length]. rewrite EFG. unfold TASK_SIZE. lia.
    - intros x Hx. cbn [length] in Hx. rewrite EFG in Hx. apply PF. lia. }
  assert (FLW0 : bytes_at rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned a0 + fs_B 6 - 8)
                   (le8 (Z_to_bv 64 (fs_flag FS 6 j)))).
  { apply (bytes_at_P_keep P m _ _ RO); [| | exact FLWB].
    - rewrite length_le8. change (fs_B 6) with 4096. unfold TASK_SIZE. lia.
    - intros x Hx. rewrite length_le8 in Hx. change (fs_B 6) with 4096 in Hx. apply PF. lia. }
  assert (AC0 : asan_cells (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m)) by exact (asan_cells_P P m PI MI AC).
  assert (PL0 : fs_place (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) FS).
  { unfold fs_place. split; [exact FS0|]. split; [exact FS4K|]. split; [exact FSGT|].
    split; [exact FAPP| exact STF0]. }
  (* ---- the run on the restricted memory, lifted ---- *)
  pose proof Sf6L.stack_free_6_L as HL6.
  unfold asan_stack_free_6_contract_L, asan_stack_free_contract_L, ASAN_STACK_FREE_6, ASAN_STACK_FREE_K in HL6.
  cbv zeta in HL6.
  apply (ExecF.evtF_mono rsegs (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.RNG_P rsegs P) (fun st => exists st0,
            asan_stack_free_post_L 6 32 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (bv_unsigned a1) FS j (bv_unsigned sp - 32) (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) st0
            /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.ms_rel_P rsegs P st st0 /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    exact (HL6 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.normalize_P rsegs P m) (bv_unsigned sp - 32) FS j
             HJ EFR HL HL8 PL0 FLG0 FLW0 AC0 SHSTK0' MI0 ST320 ltac:(lia) ROOM ltac:(unfold HIGHMEM_BEG; lia) HHI).
  - intros st (st0 & HQ & REL & SAME).
    cbv zeta in HQ.
    destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU0 & WM0 & MI0' & ST0' & PL0' & FLGZ & SHB & AC0').
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    assert (MUr : munch [(fs_flag FS 6 j, fs_flag FS 6 j + 1);
                         (shadow_addr (fs_frame FS 6 j), shadow_addr (fs_frame FS 6 j) + fs_shadow_n 6 (bv_unsigned a1));
                         (bv_unsigned sp - 32, bv_unsigned sp)] m (ms_mem st))
      by (eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.munch_rel_P rsegs P); [exact REL0| exact E8| exact SAME| exact MU0]).
    assert (WMr : wmono rsegs m (ms_mem st))
      by (eapply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.wmono_rel_P rsegs P); [exact REL0| exact E8| exact SAME| exact WM0]).
    assert (FLGr : bytes_at rsegs (ms_mem st) (fs_flag FS 6 j) [Z_to_bv 8 0])
      by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 FLGZ).
    assert (SHBr : bytes_at rsegs (ms_mem st) (shadow_addr (fs_frame FS 6 j))
                     (repeat (Z_to_bv 8 0xf5) (Z.to_nat (fs_shadow_n 6 (bv_unsigned a1)))))
      by exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 SHB).
    assert (STmid : stk rsegs (ms_mem st) (bv_unsigned sp - 32) (bv_unsigned sp))
      by exact (stk_rel_P P (ms_mem st) m0' _ _ E8 ST0').
    unfold SFO.asan_stack_free_post_on. cbv zeta.
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MUr.
    + exact WMr.
    + intros x b Hx. destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (MI x b Hx).
    + (* stk rsegs (ms_mem st) lo sp: below sp - 32 only the flag byte moved, and it is readable *)
      apply (stk_after m (ms_mem st) _ lo (bv_unsigned sp) ST MUr WMr).
      intros a Ha.
      destruct (Z_le_gt_dec (bv_unsigned sp - 32) a) as [C1|C1].
      * right. destruct STmid as (_ & _ & Hs). destruct (Hs a ltac:(lia)) as (_ & b & Hb). exists b. exact Hb.
      * destruct (Z.eq_dec a (fs_flag FS 6 j)) as [C2|C2].
        -- right. rewrite C2. apply (bytes_at_some_L (ms_mem st) (fs_flag FS 6 j) [Z_to_bv 8 0] _ FLGr).
           cbn [length]. lia.
        -- left. cbn [outside]. rewrite ESAF, EN.
           split; [lia|]. split; [lia|]. split; [lia| exact I].
    + (* fs_place *)
      destruct PL0' as (_ & _ & _ & _ & STF').
      unfold fs_place. split; [exact FS0|]. split; [exact FS4K|]. split; [exact FSGT|]. split; [exact FAPP|].
      exact (stk_rel_P P (ms_mem st) m0' _ _ E8 STF').
    + exact FLGr.
    + exact SHBr.
    + apply (asan_cells_kept [(fs_flag FS 6 j, fs_flag FS 6 j + 1);
                              (shadow_addr (fs_frame FS 6 j), shadow_addr (fs_frame FS 6 j) + fs_shadow_n 6 (bv_unsigned a1));
                              (bv_unsigned sp - 32, bv_unsigned sp)] m (ms_mem st) AC MUr).
      cbn [disjoint_from]. rewrite ?ESAF, ?EFG. unfold RT_LO, RT_HI. lia.
    + (* the POST form: outside [SA, SA + 512) the run wrote no shadow byte, inside it left 0xf5 *)
      refine (shadow_rw_write_on_L m (ms_mem st) _ SA 512 MUr WMr _ _).
      * intros a Hin Hout. cbn [outside]. rewrite ESAF, EN.
        split; [|split; [lia|]].
        -- intros X. apply (app_not_shadow a); [|exact Hin].
           replace a with (fs_flag FS 6 j) by lia. apply FAPP. rewrite EFG. lia.
        -- split; [|exact I].
           unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia.
      * intros a Ha. apply (bytes_at_some_L (ms_mem st) (shadow_addr (fs_frame FS 6 j)) _ a SHBr).
        rewrite repeat_length, EN. rewrite Z2Nat.id by lia. rewrite ESAF. lia.
Qed.
