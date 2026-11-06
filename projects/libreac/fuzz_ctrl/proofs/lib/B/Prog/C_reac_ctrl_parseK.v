(* lib/B/Prog/C_reac_ctrl_parseK.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): memory plumbing for the glue
   pb_reac_ctrl_parse (no C_reac_ctrl_parseLib dependency).
     rcpK_raw_SA     a run on the normalized memory that writes only [lo, hi), moved to the real memory
                     (lib.B.MemNorm.mem_rel + ro_same + munch): the real end memory equals the start memory off [lo, hi).
     rcpK_aview_eq / rcpK_apresent_eq   the view and the presence of one address read only that address.
     rcpK_compose    the call's acall_kept (YCbq.v:824) from the caller memory to the return memory of
                     reac_ctrl_parse: the prologue's raw keep off [S - 128, S), the fake-stack call's acall_kept
                     over its window [A - ESTACK, A), and the re-based stretch's raw munch WR.
     rcpK_rw_cells_tr   cells that keep their bytes and stay writable keep rw_cells.
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YA0n YM05 YI16 YG0f YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0n YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

(* The prologue's run on normalize memc writes only [lo, hi): off it the real end memory m1 is memc. *)
Lemma rcpK_raw_SA : forall (memc m1 m1n : word -> option byte) (lo hi : Z),
  lib.B.MemNorm.mem_rel rsegs m1 m1n -> lib.B.MemNorm.ro_same rsegs memc m1 ->
  munch [(lo, hi)] (lib.B.MemNorm.normalize rsegs memc) m1n ->
  forall x : word, ~ (lo <= bv_unsigned x < hi) -> m1 x = memc x.
Proof.
  intros memc m1 m1n lo hi [REL1 _] ROS MU x Hx.
  destruct (ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
  pose proof (REL1 x) as E1. unfold lib.B.MemNorm.normalize in E1. rewrite R in E1.
  assert (Ho : outside [(lo, hi)] (bv_unsigned x)) by (cbn [outside]; split; [exact Hx | exact I]).
  pose proof (MU x Ho) as E2. unfold lib.B.MemNorm.normalize in E2. rewrite R in E2.
  rewrite <- E1, E2. reflexivity.
Qed.

(* outside is decidable (no classical axiom). *)
Lemma rcpK_outside_dec : forall (WR : list ivl) (x : Z), outside WR x \/ ~ outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z_lt_le_dec x lo) as [L|L]; destruct (Z_lt_le_dec x hi) as [M|M];
    try (left; split; [lia | exact H]); right; intros [H1 H2]; try (apply H; exact H2); lia.
Qed.

Section K.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma rcpK_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.aview rsegs H m' a = lib.Reusable.YG0n.aview rsegs H m a.
Proof.
  intros H m m' a E. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  rewrite E. reflexivity.
Qed.

Lemma rcpK_apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.apresent H m a -> lib.Reusable.YG0n.apresent H m' a.
Proof. intros H m m' a E [Hh (b & Hb)]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

Lemma rcpK_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Ha.
Qed.

(* The acall_kept of reac_ctrl_parse from the caller memory memc to its return memory m'. *)
Lemma rcpK_compose : forall lyc Sc (W : lib.Reusable.YA0n.world rsegs) (memc m1 mem2 m' : word -> option byte)
    (S A o : Z) (WR : list ivl),
  lib.Reusable.YM05.alloc_ceiling <= S - 8800 -> S - 8800 <= A - lib.Reusable.YG0d.ESTACK -> A <= S - 128 -> S <= 2 ^ 64 ->
  (forall x : word, ~ (S - 128 <= bv_unsigned x < S) -> m1 x = memc x) ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2 (A - lib.Reusable.YG0d.ESTACK) A (fun _ => False) ->
  munch WR mem2 m' ->
  (* the caller's blocks, frames (and their shadow) and the image lie below the window *)
  (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
     0 <= b + i < S - 8800) ->
  (forall cid pos a, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
     (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
      lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                 lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> 0 <= a < S - 8800) ->
  (forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < S - 8800) ->
  (* every byte WR names outside the window: below alloc_ceiling, not an image byte, and inside the output object
     if it is a byte of a caller's block or of a caller's frame or its shadow *)
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside WR a -> ~ (S - 8800 <= a < S) ->
     a < lib.Reusable.YM05.alloc_ceiling /\ ~ lib.Reusable.YG0d.in_img rsegs a /\
     (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
        a = b + i -> o <= a < o + 36) /\
     (forall cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
        (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
         lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                    lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> o <= a < o + 36)) ->
  (forall a, S - 8800 <= a < S -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m' a) ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W m' (S - 8800) S (fun a => o <= a < o + 36).
Proof.
  intros lyc Sc W memc m1 mem2 m' S A o WR Hceil HA1 HA2 HS RA (K1 & K2 & K3 & K4 & K5 & K6) MU
    Hblk Hfrm Himg HWR HPR.
  pose proof (lib.Reusable.YCbq.asan_consts) as (C1 & _).
  assert (ES : lib.Reusable.YG0d.ESTACK = 4096) by reflexivity.
  (* the three raw steps at one address a in [0, 2^64) that WR does not name, outside [S - 128, S) *)
  assert (RAW : forall a, 0 <= a < 2 ^ 64 -> outside WR a -> ~ (S - 128 <= a < S) ->
                  m' (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a) /\ m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { intros a Ha Ho Hw. split.
    - apply MU. rewrite rcpK_u64 by lia. exact Ho.
    - apply RA. rewrite rcpK_u64 by lia. exact Hw. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* (1) above alloc_ceiling, off the window *)
    intros a Ha Hw.
    assert (Ho : outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _). lia. }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K1 a Ha ltac:(unfold lib.Reusable.YG0d.ESTACK in *; lia)).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (2) the caller's blocks, off the output object *)
    intros b m i Hb Hi HE.
    pose proof (Hblk b m i Hb Hi) as Hlo.
    assert (Ho : outside WR (b + i)).
    { destruct (rcpK_outside_dec WR (b + i)) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR (b + i) ltac:(lia) Hx ltac:(lia)) as (_ & _ & Hbk & _).
      exact (HE (Hbk b m i Hb Hi eq_refl)). }
    destruct (RAW (b + i) ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' (b + i) E2).
    rewrite (K2 b m i Hb Hi ltac:(intros [])).
    exact (rcpK_aview_eq _ memc m1 (b + i) E1).
  - (* (3) the image *)
    intros a Hi Hst Her.
    pose proof (Himg a Hi) as Hlo.
    assert (Ho : outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & Hni & _). exact (Hni Hi). }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K3 a Hi Hst Her).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (4) the caller's frames and their shadow, off the output object *)
    intros cid pos a Hin Hr HE.
    pose proof (Hfrm cid pos a Hin Hr) as Hlo.
    assert (Ho : outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & _ & _ & Hfk).
      exact (HE (Hfk cid pos Hin Hr)). }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    rewrite (rcpK_aview_eq _ mem2 m' a E2).
    rewrite (K4 cid pos a Hin Hr ltac:(intros [])).
    exact (rcpK_aview_eq _ memc m1 a E1).
  - (* (5) presence above alloc_ceiling, off the window *)
    intros a Ha Hw Hp.
    assert (Ho : outside WR a).
    { destruct (rcpK_outside_dec WR a) as [Hx|Hx]; [exact Hx|].
      exfalso. destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _). lia. }
    destruct (RAW a ltac:(lia) Ho ltac:(lia)) as [E2 E1].
    apply (rcpK_apresent_eq _ mem2 m' a E2).
    apply (K5 a Ha ltac:(unfold lib.Reusable.YG0d.ESTACK in *; lia)).
    apply (rcpK_apresent_eq _ memc m1 a E1). exact Hp.
  - (* (6) the window is present at the end *)
    exact HPR.
Qed.

(* Cells that keep their bytes (mrd) and stay writable (stk) keep rw_cells. *)
Lemma rcpK_rw_cells_tr : forall (m m' : word -> option byte) p cs,
  rw_cells rsegs m p cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mrd rsegs m' (wa (p + i)) = mrd rsegs m (wa (p + i))) ->
  stk rsegs m' p (p + Z.of_nat (cells_size cs)) ->
  rw_cells rsegs m' p cs.
Proof.
  intros m m' p cs [[Hwf (H0 & H1 & Hb)] _] Hm (S0 & S1 & Hs).
  split; [split; [exact Hwf|]|].
  - split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hb i Hi). pose proof (cells_bytes_length cs Hwf) as EL.
    apply Hm. lia.
  - split; [exact S0|]. split; [lia|]. intros i Hi. destruct (Hs (p + i) ltac:(lia)) as [Hw _]. exact Hw.
Qed.
End K.
