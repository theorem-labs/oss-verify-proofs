(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3501 of its 3539 lines of code are new or changed and 210 lines of the source are left out. *)
(* The footprint twin of reac_ctrl_parse_x_holds (reac_ctrl_parse.v, not in this delivery; RECIPE.md step 1 (a working note, not in this delivery)): the same run as
   an ExecF.evtF under a footprint RNG (reac_ctrl_parse_contract_x_F of reac_ctrl_parse_c.v), by the script of
   lib/B/Prog/reac_ctrl_parse.v (not in this delivery) over StepF's step.  Every data access closes from one rng premise of that statement:
   the image (the GOT words, the runtime's cells, the literal addresses), the window [S - K, S) and its shadow, the
   50 input bytes at f and the 36 record bytes at o with their shadow, the 6 compare bytes at BC with their shadow,
   the side stack's header and the class-1 hint word, flag bytes, frames and frame shadow, and the thread cells of
   asan_tls_cells.  Four of the five callees are taken in their footprint form in the same places where
   reac_ctrl_parse.v's theorem takes their old contracts; the fifth, kind_of_link1, is proved in footprint form on
   this branch (kind_of_link1F.v), so it is used, not assumed.  reac_ctrl_parse.v and its theorems are unchanged. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLib RcParse RcParseLib
  RcAsan RcAsanLib RcBoxLib RcClassifyLib.
(* asan_memset_cF / asan_memcpy_cF before reac_ctrl_parse_c: the unqualified IMG_LO, IMG_LEN, sh_lo and sh_len stay
   reac_ctrl_parse_c's (the statement's), not those of ImgBounds / rng_asan, which the shared texts Export (rng_asan's
   sh_len is a different text: it has an n = 0 guard). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c asan_memset_cF asan_memcpy_cF memcmp_c bcmp_wrap_c
  kind_of_link1_c kind_of_link1F reac_ctrl_parse_c.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The footprint forms of the four callees this proof assumes.  __asan_memset and __asan_memcpy: a Theorem Labs lane's one     *)
(* shared statement each, asan_memset_contract_F of lib/B/Prog/asan_memset_cF.v and asan_memcpy_contract_F of        *)
(* lib/B/Prog/asan_memcpy_cF.v (a Theorem Labs lane proves them: asan_memset_holds_F, asan_memcpy_holds_F).  The bcmp          *)
(* wrapper's bcmp_wrap_contract_F comes from bcmp_wrap_c.v.  __asan_stack_malloc_1's footprint form follows.           *)

(* __asan_stack_malloc_c in footprint form: the NARROW text, asan_stack_malloc_contract_F_narrow at lines 694-721 of
     git show 062bf770c5b:proofs/libreac/fuzz_knock/lib/A/Prog/asan_stack_malloc_F.v
   (the canonical wide text of 31a0b55aa13 fuzz_scene asan_stack_malloc_cF.v with its one side-stack premise
   rng RNG FS FS_SIZE replaced by two pieces), in a Theorem Labs lane's premise order, with fuzz_knock's names replaced by fuzz_ctrl
   image B's: the module paths, IMG_LO (reac_ctrl_parse_c.v) and IMG_HI (below) for asan_stack_malloc_cF's, and image
   B's ASAN_STACK_MALLOC_1 and ASAN_STACK_MALLOC_K (asan_stack_malloc_c.v).  The premises of
   asan_stack_malloc_contract are unchanged, then one rng premise per region the call reads or writes: the image
   [IMG_LO, IMG_HI); the stack window [S0 - K, S0); the five runtime pointer cells read through DT, TS, C, T and DB;
   the side stack's header [FS, fs_frame FS 0 0) (hint words, the words at FS + 88 and FS + 96, flag bytes of every
   class); the class-c frame area [fs_frame FS c 0, fs_frame FS c 0 + 2^20); the shadow of that frame area (fs_M c
   frames of fs_B c bytes, so fs_shadow_area c shadow bytes from its shadow_addr); the thread-pointer cells
   [TP - 88, TP - 80) and [TP - 8, TP + 16).  The form speaks only of the classes 0..10 (its first premise).  It is a
   local copy for this proof, the Section hypothesis SMAL below: a Theorem Labs lane publishes this unit's own. *)
Definition fs_shadow_area (c : nat) : Z := fs_M c * fs_B c / 8.

(* The end of image B: IMG_LO + IMG_LEN of reac_ctrl_parse_c.v (= ASAN_GT). *)
Definition IMG_HI : Z := 0x5fe000.

Definition asan_stack_malloc_contract_F (c : nat) (entry K : Z) : Prop :=
  (c <= 10)%nat ->
  forall (RNG : footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= c)%nat -> bytes_at rsegs m (CF + 120) (le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs m (fs_hint FS c) (le8 h) ->
  bytes_at rsegs m (fs_flag FS c 0) flags -> Z.of_nat (length flags) = fs_M c ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K -> (forall a, S0 - K <= a < S0 -> app_mem a) ->
  disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)] (S0 - K) K ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (S0 - K) K ->
  rng RNG (bv_unsigned DT + 8) 8 -> rng RNG (bv_unsigned TS + 8 * k) 8 -> rng RNG (bv_unsigned C + 152) 8 ->
  rng RNG (bv_unsigned T + 48) 16 -> rng RNG (bv_unsigned DB + 24) 8 ->
  rng RNG FS (fs_frame FS 0 0 - FS) -> rng RNG (fs_frame FS c 0) (2 ^ 20) ->
  rng RNG (shadow_addr (fs_frame FS c 0)) (fs_shadow_area c) ->
  rng RNG (TP - 88) 8 -> rng RNG (TP - 8) 24 ->
  evtF rsegs RNG (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).

Definition asan_stack_malloc_1_contract_F : Prop :=
  asan_stack_malloc_contract_F 1 ASAN_STACK_MALLOC_1 ASAN_STACK_MALLOC_K.

(* The old contract at class 1 is the footprint form at RNG_all: the bounds of every rng premise come from the
   premises the old contract already carries (the window, fs_place for the side stack's header, its class-1 frame area
   and that area's shadow, the bytes_at of asan_tls_cells for the thread cells), so the _F form asks for nothing new. *)
Lemma asan_stack_malloc_1_contract_of_F :
  asan_stack_malloc_1_contract_F -> asan_stack_malloc_1_contract.
Proof.
  unfold asan_stack_malloc_1_contract_F, asan_stack_malloc_contract_F,
    asan_stack_malloc_1_contract, asan_stack_malloc_contract. cbv zeta.
  intros HF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo FS h DT TS C T DB k flags HL HL8 HC HSW MI HT H7 HTP HP H88 H96 HH HFl HFln HFb ST HLK HFS HAPP HDJ.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5. unfold ASAN_STACK_MALLOC_K in HFS.
  pose proof HT as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
                    & A18 & A19).
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (E1 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; change (Z.of_nat 1) with 1; lia).
  apply (evtF_evt rsegs RNG_all).
  apply (HF (proj1 (Nat.leb_le 1 10) eq_refl) RNG_all ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
           s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FS h DT TS C T DB k flags); try assumption.
  - (* image *) apply rng_all; unfold IMG_LO, IMG_HI; lia.
  - (* stack window *) apply rng_all; unfold ASAN_STACK_MALLOC_K; lia.
  - (* DT + 8 *) destruct A4 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* TS + 8 k *) destruct A9 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* C + 152 *) destruct A10 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* T + 48 *) destruct A11 as (tb & te & (Ha & Hb & _)).
    rewrite length_app, !length_le8 in Hb. apply rng_all; lia.
  - (* DB + 24 *) destruct A19 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* side-stack header *) apply rng_all; rewrite ?E0; lia.
  - (* class-1 frame area *) apply rng_all; rewrite ?E1; lia.
  - (* shadow of the class-1 frame area *)
    change (fs_shadow_area 1) with 131072. rewrite E1. unfold shadow_addr, ASAN_K.
    pose proof (Z.div_mod (FS + 1085440) 8 ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound (FS + 1085440) 8 ltac:(lia)) as M.
    apply rng_all; lia.
  - (* TS cell at TP - 88 *) destruct A8 as (Ha & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
  - (* DT, side-stack and DB cells at TP - 8 .. TP + 16 *)
    destruct A3 as (Ha & _). destruct A17 as (_ & Hb & _). rewrite length_le8 in Hb. apply rng_all; lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The shadow covers, carried through the proof as quantified facts.  Z.div is opaque to lia, and a GROUND rng
   premise whose bounds hold a division makes every later lia pay for that division's Euclidean equations, so the
   consequences of the statement's 8-aligned shadow word covers are drawn once here, each in a context with no other
   division, and used through shcov (the shadow byte of one checked byte), shblk (the i-th shadow byte of an
   8-aligned block) and shkov (the aligned cover a callee's _F contract names). *)
Definition shcov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> ExecF.rng RG (x / 8 + ASAN_K) 1.
Definition shblk (RG : ExecF.footprint) (p k : Z) : Prop :=
  forall i, 0 <= i <= k -> ExecF.rng RG (p / 8 + ASAN_K + i) 1.
Definition shkov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    ExecF.rng RG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

Lemma shcov_sub : forall RG p n p' n', shcov RG p n -> p <= p' -> p' + n' <= p + n -> shcov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma shkov_sub : forall RG p n p' n', shkov RG p n -> p <= p' -> p' + n' <= p + n -> shkov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 a b H3 H4 H5. apply H; lia. Qed.

Lemma rcpF_floor8 : forall y, y / 8 * 8 <= y <= y / 8 * 8 + 7.
Proof. intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

(* The statement's aligned shadow word cover of [p, p + n) gives the shadow byte of each of its bytes. *)
Lemma rcpF_cov : forall RG p n,
  ExecF.rng RG (sh_lo p) (sh_len p n) -> shcov RG p n.
Proof.
  intros RG p n H x Hx. unfold sh_len, sh_lo in H.
  eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)). pose proof (rcpF_floor8 (p / 8 + ASAN_K)). lia.
  - pose proof (Z.div_le_mono x (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (rcpF_floor8 ((p + n - 1) / 8 + ASAN_K)). lia.
Qed.

(* and the aligned cover of each of its sub-ranges. *)
Lemma rcpF_kov : forall RG p n,
  ExecF.rng RG (sh_lo p) (sh_len p n) -> shkov RG p n.
Proof.
  intros RG p n H a b H1 H2 H3. unfold sh_len, sh_lo in H.
  eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p / 8 + ASAN_K) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono b (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The EXACT metadata of the window [S - 8800, S) (the statement's window premise) gives the shadow byte of each byte
   of the window, and the aligned cover of each sub-range of [S - 2560, S - 128): it holds the real-stack frame
   [A - 128, A) (S - 160 < A <= S - 128; rngF_frame_kov) and the windows [spc - K, spc) of __asan_memset (K = 2208)
   and __asan_memcpy (K = 2224) below the body's sp spc (S - 288 <= spc <= S - 128), whose aligned shadow word span
   a Theorem Labs lane's shared _F texts name (sh_word_rng (sp - K) K). *)
Lemma rcpF_win_cov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 8800)) (shadow_addr S - shadow_addr (S - 8800)) -> shcov RG (S - 8800) 8800.
Proof.
  intros RG S H16 H x Hx. eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr; Z.div_mod_to_equations; lia.
Qed.

Lemma rcpF_win_kov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 8800)) (shadow_addr S - shadow_addr (S - 8800)) -> shkov RG (S - 2560) 2432.
Proof.
  intros RG S H16 H a b H1 H2 H3.
  eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

Lemma rcpF_div8 : forall z, (8 * z) / 8 = z.
Proof. intros z. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

(* The class-1 frames' shadow comes as the BYTE-exact span [shadow_addr F0, shadow_addr F1) of fp_w.  Both ends are
   the shadow byte of a 64-aligned address, so that span is a whole number of aligned shadow words and it gives the
   same two consequences.  p0 and p1 below are F0 / 64 and F1 / 64. *)
Lemma rcpF_span_cov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shcov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H x Hx.
  assert (L1 : 8 * p0 <= x / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) x 8 ltac:(lia) ltac:(lia)) as D. rewrite rcpF_div8 in D. lia. }
  assert (L2 : x / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono x ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma rcpF_span_kov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shkov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H a b H1 H2 H3.
  assert (KA : ASAN_K = 8 * 268431360) by reflexivity.
  assert (L1 : 8 * p0 <= a / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) a 8 ltac:(lia) ltac:(lia)) as D. rewrite rcpF_div8 in D. lia. }
  assert (L2 : b / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono b ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  assert (M1 : p0 + 268431360 <= (a / 8 + ASAN_K) / 8).
  { pose proof (Z.div_le_mono (8 * (p0 + 268431360)) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite rcpF_div8 in D. lia. }
  assert (M2 : (b / 8 + ASAN_K) / 8 <= p1 + 268431360 - 1).
  { pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p1 + 268431360 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* A shadow access: its address holds a division, which StepF's [alia] does not reason about, so it goes through
   StepF's acc_hint hook and closes from one of the quantified covers above. *)
Ltac rcpF_has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac rcpF_rng1 :=
  lazymatch goal with
  | |- ExecF.rng ?RG ?E 1 =>
      first
        [ (* the i-th shadow byte of the 8-aligned block at p *)
          match goal with H : shblk RG _ _ |- _ => apply H; lia end
        | (* the shadow byte of X, a byte of a shcov range *)
          lazymatch E with ?X / 8 + ASAN_K =>
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end
        | (* the same two, with the address written another way *)
          match goal with H : shblk RG ?p _ |- _ =>
            replace E with (p / 8 + ASAN_K + (E - (p / 8 + ASAN_K))) by lia;
            apply H; unfold ASAN_K in *; lia end
        | lazymatch E with ?X / 8 + ?c =>
            replace E with (X / 8 + ASAN_K) by (unfold ASAN_K in *; lia);
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end ]
  end.

(* The hook also puts two access shapes into the one StepF's literal branch matches: an address written
   [wa E] (a pointer the run loaded from a GOT word) becomes [Z_to_bv 64 E], and a closed address written with
   named constants (GOT_UAR, CELL_K, ...) becomes its literal value. *)
Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RG (wa ?E, ?nn) => change (acc_in RG (Z_to_bv 64 E, nn)); solve_acc1
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?nn) =>
      tryif rcpF_has_div E then
        (let nz := eval cbv in (Z.of_nat nn) in
         refine (rng_acc_litZ' RG E nz E nn nz _ (@eq_refl Z nz) (@eq_refl bool true)
                   (conj (Z.le_refl E) (Z.le_refl (E + nz))));
         rcpF_rng1)
      else
        (tryif is_closed_lits E then fail else
           (let E' := eval vm_compute in E in
            is_Zlit E'; change (acc_in RG (Z_to_bv 64 E', nn)); solve_acc1))
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* The store hook of this file: Tac.v's mem_after_store_opt (the hook reac_ctrl_parse.v runs under) on evtF goals.
   It folds Z_to_le_bytes of a literal into le8 / le4 / le2 / le1 as Tac's fix_lit_store does, and it does not run
   StepF's norm_lit_store_bytes, whose le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z] folding would leave nothing for the
   script's own `rewrite rc_le1_lit` (sstep, the flag clear of the exit). *)
Ltac rcpF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac rcpF_store_opt :=
  try rcpF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= rcpF_store_opt.

(* briefs/common.md Proof speed (2): lia case-splits on every disjunction, implication and <> it can read, so each
   heavy proof below hides the hypotheses its lia calls do not need (rs_hold, by conversion, so a Section hypothesis
   stays usable by the Section's lemmas); a use site unfolds rs_hold.  The disjunctions the store and call
   transports need (record or input apart from the saved registers and from each other) stay visible. *)
Local Definition rs_hold (A : Prop) : Prop := A.
Local Ltac rs_hide H := let T := type of H in change (rs_hold T) in H.

(* ------------------------------------------------------------------------------------------------------------ *)

(* Every byte readable in m is readable in m'. *)
Definition rd_mono (m m' : word -> option byte) : Prop :=
  forall x : word, (exists b, mrd rsegs m x = Some b) -> exists b, mrd rsegs m' x = Some b.

Lemma rd_mono_refl : forall m, rd_mono m m.
Proof. intros m x H. exact H. Qed.

Lemma rd_mono_trans : forall m1 m2 m3, rd_mono m1 m2 -> rd_mono m2 m3 -> rd_mono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma wtm_cases : forall bs m (a x : word), write_to_mem m a bs x = m x \/ exists v, write_to_mem m a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

Lemma rd_mono_write : forall m0 m a bs, rd_mono m0 m -> rd_mono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. destruct (H x Hx) as [v Hv]. unfold mrd in *.
  destruct (wtm_cases bs m a x) as [E|[w E]]; rewrite E; [exists v; exact Hv | exists w; reflexivity].
Qed.

Lemma rd_mono_munch : forall W m m', munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> exists b, mrd rsegs m' x = Some b) -> rd_mono m m'.
Proof.
  intros W m m' Hm H x Hx. destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd in *. rewrite (Hm x Ho). exact Hx.
  - exact (H x Ho).
Qed.

Lemma stk_mono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> rd_mono m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw Hr. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma shadow_rw_mono : forall m m', shadow_rw m -> wmono rsegs m m' -> rd_mono m m' -> shadow_rw m'.
Proof.
  intros m m' H Hw Hr a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma fs_place_mono : forall m m' FS, fs_place m FS -> wmono rsegs m m' -> rd_mono m m' -> fs_place m' FS.
Proof.
  intros m m' FS (P1 & P2 & P3 & P4 & P5) Hw Hr. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (stk_mono m m' _ _ P5 Hw Hr).
Qed.

Lemma wv_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma stk_wv : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> wview rsegs m (wa a) <> None.
Proof. intros m lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma bytes_keep : forall m m' A bs, bytes_at rsegs m A bs ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) -> bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (Ha & Hl & H) Hk. split; [lia|]. split; [lia|]. intros i Hi. rewrite Hk by lia. apply H, Hi.
Qed.

Lemma addr_keep : forall m m' p n, addressable m p n ->
  (forall i, 0 <= i < n -> mrd rsegs m' (wa (shadow_addr (p + i))) = mrd rsegs m (wa (shadow_addr (p + i)))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) Hk. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. rewrite Hk by exact Hi.
  split; [exact Hb | exact Hok].
Qed.

Lemma app_not_shadow : forall x y, app_mem x -> in_shadow y -> x <> y.
Proof.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia.
Qed.

Lemma sh_range : forall L H x, L mod 8 = 0 -> H mod 8 = 0 ->
  (shadow_addr L <= shadow_addr x < shadow_addr H <-> L <= x < H).
Proof. intros L H x HL HH. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_range8 : forall fr x, fr mod 8 = 0 ->
  (shadow_addr fr <= shadow_addr x < shadow_addr fr + 8 <-> fr <= x < fr + 64).
Proof. intros fr x Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma sh_add8 : forall fr i, fr mod 8 = 0 -> shadow_addr (fr + 8 * i) = shadow_addr fr + i.
Proof. intros fr i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma bytes_le_to_Z_nonneg' : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma bytes_le_to_Z_cons' : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons'.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_nonneg' bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

Lemma rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (Z_to_le_bytes_to_Z' [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

Lemma rd_of_bytes : forall m A bs, bytes_at rsegs m A bs ->
  forall y, A <= y < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa y) = Some b.
Proof.
  intros m A bs (Ha & Hl & H) y Hy. pose proof (H (Z.to_nat (y - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (y - A))) with y in E by lia.
  destruct (nth_error bs (Z.to_nat (y - A))) as [v|] eqn:En; [exists v; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma rd_of_stk : forall m lo hi, stk rsegs m lo hi -> forall y, lo <= y < hi -> exists b, mrd rsegs m (wa y) = Some b.
Proof. intros m lo hi (_ & _ & H) y Hy. exact (proj2 (H y Hy)). Qed.

Lemma not_outside_in : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
Qed.

Lemma rd_mono_list : forall W m m', munch W m m' ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs m' (wa y) = Some b) W -> rd_mono m m'.
Proof.
  intros W m m' Hm HF. apply (rd_mono_munch W m m' Hm). intros x Hx.
  destruct (not_outside_in W _ Hx) as (r & Hr & Hin). rewrite Forall_forall in HF.
  pose proof (HF r Hr (bv_unsigned x) Hin) as R. unfold wa in R. rewrite Z_to_bv_lit_self in R. exact R.
Qed.


Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Lemma bytes_ro : forall m A c, bytes_at rsegs m A (cbytes c) -> cell_wf c -> ro_cells rsegs m A [c].
Proof. intros m A c H Hw. split; [split; [exact Hw | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H]. Qed.
Lemma bytes_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. exact (bytes_ro m A (C8 v) H I). Qed.
Lemma bytes_ro4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v H. exact (bytes_ro m A (C4 v) H I). Qed.

(* ----- generic shadow helpers (as in reac_ctrl_classify_box_frame.v) ----- *)

Lemma acl_app_in : forall m p nn i, addressable m p nn -> 0 <= i < nn -> app_mem (p + i).
Proof. intros m p nn i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma acl_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma acl_addr_sub : forall m p nn p' n', addressable m p nn -> p <= p' -> 0 <= n' -> p' + n' <= p + nn ->
  addressable m p' n'.
Proof.
  intros m p nn p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma acl_addr_join : forall m p nn n', addressable m p nn -> addressable m (p + nn) n' -> 0 <= n' ->
  addressable m p (nn + n').
Proof.
  intros m p nn n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i nn) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + nn + (i - nn)) by lia. apply HA'. lia.
Qed.

Lemma acl_addr_munch : forall W m m' p nn, addressable m p nn -> munch W m m' ->
  (forall i, 0 <= i < nn -> outside W (shadow_addr (p + i))) -> addressable m' p nn.
Proof.
  intros W m m' p nn (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma acl_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma acl_shadow : forall mc p nn j w X, addressable mc p nn -> 0 <= j -> 1 <= w -> j + w <= nn ->
  X mod 8 + w <= 8 -> X = p + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc p nn j w X HA Hj Hw Hjw Hm ->.
  pose proof (rt_shadow_rd mc p nn [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc p nn HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K p nn [] j HSR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  exact (asan_check_lt rsegs mc ASAN_K p nn j w k HAD Hj Hw Hjw Hm BK).
Qed.

Lemma acl_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma acl_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma acl_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma acl_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma acl_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (acl_sh_lt x lo Hm L). lia.
  - pose proof (acl_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma acl_frame_mod8 : forall FS, FS mod 4096 = 0 -> fs_frame FS 1 0 mod 8 = 0.
Proof.
  intros FS H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Lemma acl_S_mod8 : forall S j, S mod 16 = 0 -> j mod 8 = 0 -> (S - j) mod 8 = 0.
Proof. intros S j H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al0 : forall x, x mod 4 = 0 -> x mod 8 + 4 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma acl_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

Ltac steps_to P :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
  | _ => step; steps_to P
  end.

(* ----- shadow-check tactics (as in reac_ctrl_classify_box_frame.v / declaration_of.v) ----- *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* A shadow check of the access of w bytes at X (RX : 0 <= X < 2^64): SH gives the shadow byte k, its read at
   X / 8 + ASAN_K and the check fact (k = 0, or X mod 8 + (w - 1) < k); `pre` steps to the shadow address,
   then the load of k and `bnez` go on when k = 0; else the slow path `andi r, X, 7` (and `addi r, r, w - 1` by
   `extra`) and `blt r, k` go on as the check passes. The register r is generalized at the join, and the call of
   __asan_report_* is not reached. *)
Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?rgq ?Q (MS ?R ?Fm (if _ then _ else ?B) ?fcc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) Fm B fcc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac pre_no X RX := idtac.
Ltac no_extra X := idtac.
Ltac add1 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.
Ltac add3 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.

(* The 16 shadow bytes of the frame [shadow_addr fra, + 16) are in the shadow region: the frame is low or high
   application memory, so its shadow is in the low or high shadow. *)
Lemma frame_shadow_in : forall fra i,
  0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  0 <= i < 16 -> in_shadow (fra / 8 + ASAN_K + i).
Proof.
  intros fra i H0 HFRA SHlo SHhi Hi.
  unfold in_shadow, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
  destruct HFRA as [L|H]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

(* shadow_rw gives a writable+readable stk over the frame's 16-byte shadow region. *)
Lemma shadow16_stk : forall mc fra,
  shadow_rw mc -> 0 <= fra -> (fra + 128 <= 2147450880 \/ 17594333495296 <= fra) ->
  2147450880 <= fra / 8 + ASAN_K -> fra / 8 + ASAN_K + 16 <= 17594333495296 ->
  stk rsegs mc (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16).
Proof.
  intros mc fra SR H0 HFRA SHlo SHhi. split; [lia|]. split; [lia|].
  intros a Ha. apply SR. replace a with (fra / 8 + ASAN_K + (a - (fra / 8 + ASAN_K))) by lia.
  apply frame_shadow_in; [exact H0 | exact HFRA | exact SHlo | exact SHhi | lia].
Qed.

(* The box of the class-1 frame lives at fra + 32; its 36 bytes are addressable from the shadow bytes the frame
   poisoning wrote: granules 4..7 (fra + 32 .. fra + 64) are zero, granule 8 (fra + 64 .. fra + 72) is 4, so the
   first 4 bytes of it are addressable. *)
Lemma frame_shadow_addr : forall mc fra,
  0 <= fra -> fra mod 8 = 0 -> fra + 68 <= APPMEM_END ->
  (forall i, 0 <= i < 36 -> app_mem (fra + 32 + i)) ->
  (forall g, 4 <= g <= 7 -> exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) ->
  (exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + 8)) = Some b /\ bv_signed b = 4) ->
  addressable mc (fra + 32) 36.
Proof.
  intros mc fra Hfra0 Hmod Hend Hap Hz H8.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. unfold addr_byte. split; [apply Hap; exact Hi|].
  assert (ESH : shadow_addr (fra + 32 + i) = fra / 8 + ASAN_K + (32 + i) / 8).
  { unfold shadow_addr.
    replace (fra + 32 + i) with ((32 + i) + fra / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  destruct (Z_lt_le_dec i 32) as [L|L].
  - assert (Hg : 4 <= (32 + i) / 8 <= 7) by (Z.div_mod_to_equations; lia).
    destruct (Hz ((32 + i) / 8) Hg) as (b & Hb & Hs).
    exists b. rewrite ESH. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
  - assert (Eg : (32 + i) / 8 = 8) by (Z.div_mod_to_equations; lia).
    destruct H8 as (b & Hb & Hs). exists b. rewrite ESH, Eg. split; [exact Hb|].
    unfold shadow_ok. right. split; [|lia].
    assert (Em : (fra + 32 + i) mod 8 = i - 32)
      by (replace (fra + 32 + i) with ((32 + i) + fra / 8 * 8) by (Z.div_mod_to_equations; lia);
          rewrite Z.mod_add by lia; Z.div_mod_to_equations; lia).
    rewrite Em, Hs. lia.
Qed.

(* After the release un-poisons the whole frame to shadow 0, its 128 bytes are addressable. *)
Lemma frame_all_addr : forall mc fra,
  0 <= fra -> fra mod 8 = 0 -> fra + 128 <= APPMEM_END ->
  (forall i, 0 <= i < 128 -> app_mem (fra + i)) ->
  (forall g, 0 <= g <= 15 -> exists b, mrd rsegs mc (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) ->
  addressable mc fra 128.
Proof.
  intros mc fra Hf0 Hmod Hend Hap Hz.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. unfold addr_byte. split; [apply Hap; exact Hi|].
  assert (ESH : shadow_addr (fra + i) = fra / 8 + ASAN_K + i / 8).
  { unfold shadow_addr. replace (fra + i) with (i + fra / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (Hg : 0 <= i / 8 <= 15) by (Z.div_mod_to_equations; lia).
  destruct (Hz (i / 8) Hg) as (b & Hb & Hs).
  exists b. rewrite ESH. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
Qed.

(* The tls premise at the frame release: the run wrote only W, fp_w cs FS and Y (the thread cells are apart from the
   last two), so the thread cells and the pointers read from them are those of m (as in fl_fp_ret). *)
Lemma acl_tls_ret : forall cs m m' TP FS lo hi W D Y Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y).
Proof.
  intros cs m0 m' TP FS lo hi W D Y Wm (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Htls Hm Hs DT TS C T DB k HT.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m0 m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls _ _ _ _ _ _ HT0).
Qed.

(* ----- the free-frame side-stack premise (fpx): fp with no data ranges, plus the data ranges apart from fp_wx ----- *)

Lemma fpx_fp_nil : forall cs m TP FS lo hi W D X, fpx cs m TP FS lo hi W D X -> fp cs m TP FS lo hi W [].
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & _).
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|].
  split; [exact H96|]. split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd|].
  apply Forall_nil.
Qed.

Lemma fpx_dj : forall cs m TP FS lo hi W D X, fpx cs m TP FS lo hi W D X -> fp_dj D (fp_wx cs FS X).
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD). exact HD.
Qed.

Lemma fpx_of_fp_nil : forall cs m TP FS lo hi W D X,
  fp cs m TP FS lo hi W [] -> fp_dj D (fp_wx cs FS X) -> fpx cs m TP FS lo hi W D X.
Proof.
  intros cs m TP FS lo hi W D X (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & _) HD.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|].
  split; [exact H96|]. split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HD].
Qed.

(* A point of [lo, hi) in none of the holes is inside one of the pieces that cut_ivls keeps. *)
Lemma cut_ivls0_cover : forall holes lo hi x, lo <= x < hi ->
  Forall (fun h => ~ (fst h <= x < snd h)) holes ->
  exists r, In r (cut_ivls0 lo hi holes) /\ fst r <= x < snd r.
Proof.
  induction holes as [|[a b] hs IH]; intros lo hi x Hx Hh; cbn [cut_ivls0].
  - exists (lo, hi). split; [left; reflexivity | cbn [fst snd]; lia].
  - apply Forall_cons_iff in Hh as [Hab Hhs]. cbn [fst snd] in Hab.
    destruct (Z_lt_le_dec x a) as [L|L].
    + exists (lo, Z.min a hi). split; [left; reflexivity | cbn [fst snd]; lia].
    + destruct (IH (Z.max b lo) hi x ltac:(lia) Hhs) as (r & Hr & Hrx).
      exists r. split; [right; exact Hr | exact Hrx].
Qed.

Lemma cut_ivls_cover : forall holes lo hi x, lo <= x < hi ->
  Forall (fun h => ~ (fst h <= x < snd h)) holes ->
  exists r, In r (cut_ivls lo hi holes) /\ fst r <= x < snd r.
Proof.
  intros holes lo hi x Hx Hh. destruct (cut_ivls0_cover holes lo hi x Hx Hh) as (r & Hr & Hrx).
  exists r. split; [|exact Hrx]. unfold cut_ivls, nonempty. apply filter_In. split; [exact Hr|].
  apply Z.ltb_lt. lia.
Qed.

Lemma len_le_M : forall (fl : list byte), (length fl <= Z.to_nat (fs_M 1))%nat -> Z.of_nat (length fl) <= fs_M 1.
Proof.
  intros fl H. apply Nat2Z.inj_le in H. rewrite Z2Nat.id in H by (unfold fs_M; apply Z.pow_nonneg; lia). exact H.
Qed.

Lemma fs_flag1 : forall FS i, fs_flag FS 1 i = FS + 20480 + i.
Proof. intros FS i. unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. lia. Qed.

Lemma fs_frame1 : forall FS j, fs_frame FS 1 j = FS + 1085440 + j * 128.
Proof.
  intros FS j. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. lia.
Qed.

Lemma sh_frame1 : forall FS j, shadow_addr (fs_frame FS 1 j) = shadow_addr (fs_frame FS 1 0) + 16 * j.
Proof. intros FS j. rewrite !fs_frame1. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The class-1 hint word and flag array are ranges of fp_wx [1] FS X, whatever X is. *)
Lemma fp_wx_hint_flag_in : forall FS X,
  In (fs_hint FS 1, fs_hint FS 1 + 8) (fp_wx [1%nat] FS X) /\
  In (fs_flag FS 1 0, fs_flag FS 1 0 + fs_M 1) (fp_wx [1%nat] FS X).
Proof.
  intros FS X. destruct X as [|p X'].
  - change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
    split; [left; reflexivity | right; left; reflexivity].
  - change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta.
    split; apply in_or_app; left; [left; reflexivity | right; left; reflexivity].
Qed.

(* A frame named by the class-1 filter of fp_wx1 is a frame of X. *)
Lemma wx_filter_in : forall (l : list (nat * Z)) ci,
  In ci (filter (fun ci => Nat.eqb (fst ci) 1) l) -> In ci l.
Proof.
  induction l as [|a l IH]; intros ci H; [exact H|].
  cbn in H.
  repeat match type of H with context [if ?b then _ else _] => destruct b end;
    first [ destruct H as [H|H]; [left; exact H | right; exact (IH ci H)] | right; exact (IH ci H) ].
Qed.

(* A byte of a class-1 frame j that X does not name is inside fp_wx [1] FS X (the frame is not a hole). *)
Lemma fp_wx_frame_in : forall FS X j x, 0 <= j < fs_M 1 -> Forall (fun ci => snd ci <> j) X ->
  fs_frame FS 1 j <= x < fs_frame FS 1 (j + 1) -> ~ outside (fp_wx [1%nat] FS X) x.
Proof.
  intros FS X j x Hj HX Hx Hout.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  rewrite !fs_frame1 in Hx.
  destruct X as [|p X'].
  - apply (outside_In _ x (fs_frame FS 1 0, fs_frame FS 1 (fs_M 1)) Hout).
    + change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
      right; right; left; reflexivity.
    + cbn [fst snd]. rewrite !fs_frame1. lia.
  - assert (Hcut : exists r, In r (cut_ivls (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1))
                    (map (fun j0 => (fs_frame FS 1 j0, fs_frame FS 1 (j0 + 1)))
                       (map snd (filter (fun ci => Nat.eqb (fst ci) 1) (p :: X'))))) /\ fst r <= x < snd r).
    { apply cut_ivls_cover; [rewrite !fs_frame1; lia|].
      apply Forall_forall. intros h Hh. apply in_map_iff in Hh as (j0 & <- & Hj0).
      apply in_map_iff in Hj0 as (ci & <- & Hci). apply wx_filter_in in Hci.
      rewrite Forall_forall in HX. pose proof (HX ci Hci) as Hne. cbn [fst snd]. rewrite !fs_frame1. lia. }
    destruct Hcut as (r & Hr & Hrx).
    apply (outside_In _ x r Hout); [|exact Hrx].
    change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta. apply in_or_app. right. apply in_or_app. left. exact Hr.
Qed.

(* A shadow byte of a class-1 frame j that X does not name is inside fp_wx [1] FS X. *)
Lemma fp_wx_frame_sh_in : forall FS X j x, 0 <= j < fs_M 1 -> Forall (fun ci => snd ci <> j) X ->
  shadow_addr (fs_frame FS 1 j) <= x < shadow_addr (fs_frame FS 1 (j + 1)) -> ~ outside (fp_wx [1%nat] FS X) x.
Proof.
  intros FS X j x Hj HX Hx Hout.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  rewrite (sh_frame1 FS j), (sh_frame1 FS (j + 1)) in Hx.
  destruct X as [|p X'].
  - apply (outside_In _ x (shadow_addr (fs_frame FS 1 0), shadow_addr (fs_frame FS 1 (fs_M 1))) Hout).
    + change (fp_wx [1%nat] FS []) with (fp_w1 FS 1 ++ []). rewrite app_nil_r. unfold fp_w1.
      right; right; right; left; reflexivity.
    + cbn [fst snd]. rewrite (sh_frame1 FS (fs_M 1)). lia.
  - assert (Hcut : exists r, In r (cut_ivls (shadow_addr (fs_frame FS 1 0)) (shadow_addr (fs_frame FS 1 (fs_M 1)))
                    (map (fun j0 => (shadow_addr (fs_frame FS 1 j0), shadow_addr (fs_frame FS 1 (j0 + 1))))
                       (map snd (filter (fun ci => Nat.eqb (fst ci) 1) (p :: X'))))) /\ fst r <= x < snd r).
    { apply cut_ivls_cover; [rewrite (sh_frame1 FS (fs_M 1)); lia|].
      apply Forall_forall. intros h Hh. apply in_map_iff in Hh as (j0 & <- & Hj0).
      apply in_map_iff in Hj0 as (ci & <- & Hci). apply wx_filter_in in Hci.
      rewrite Forall_forall in HX. pose proof (HX ci Hci) as Hne. cbn [fst snd].
      rewrite (sh_frame1 FS (snd ci)), (sh_frame1 FS (snd ci + 1)). lia. }
    destruct Hcut as (r & Hr & Hrx).
    apply (outside_In _ x r Hout); [|exact Hrx].
    change (fp_wx [1%nat] FS (p :: X')) with (fp_wx1 FS (p :: X') 1 ++ []). rewrite app_nil_r.
    unfold fp_wx1. cbv zeta. apply in_or_app. right. apply in_or_app. right. exact Hr.
Qed.

(* The narrow __asan_stack_malloc_1 form's premises on the five runtime pointer cells and the two thread-pointer
   cells, from the statement's one rng fact per cell of fp_tls. *)
Lemma rcpF_tls_rng : forall RG TP DT TS C T DB k,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls TP DT TS C T DB k) ->
  rng RG (bv_unsigned DT + 8) 8 /\ rng RG (bv_unsigned TS + 8 * k) 8 /\ rng RG (bv_unsigned C + 152) 8 /\
  rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8 /\ rng RG (TP - 88) 8 /\ rng RG (TP - 8) 24.
Proof.
  intros RG TP DT TS C T DB k H. unfold fp_tls in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R3 H]. apply Forall_cons_iff in H as [R4 H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R7 H]. apply Forall_cons_iff in H as [R8 H].
  apply Forall_cons_iff in H as [R9 H]. apply Forall_cons_iff in H as [R10 H].
  do 5 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [R16 _].
  cbn [fst snd] in R3, R4, R7, R8, R9, R10, R16.
  split; [eapply rng_sub; [exact R4 | lia | lia]|].
  split; [eapply rng_sub; [exact R8 | lia | lia]|].
  split; [eapply rng_sub; [exact R9 | lia | lia]|].
  split; [eapply rng_sub; [exact R10 | lia | lia]|].
  split; [eapply rng_sub; [exact R16 | lia | lia]|].
  split; [eapply rng_sub; [exact R7 | lia | lia]|].
  eapply rng_sub; [exact R3 | lia | lia].
Qed.

(* The narrow form's premise on the shadow of the class-1 frame area, from the statement's rng fact on the frames'
   byte-exact shadow span in fp_w [1%nat] FS: the frames span 2^20 bytes, so their shadow is fs_shadow_area 1 bytes. *)
Lemma rcpF_frame_sh : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (shadow_addr (fs_frame FS 1 0)) (fs_shadow_area 1).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (fs_shadow_area 1) with (shadow_addr (fs_frame FS 1 (fs_M 1)) - shadow_addr (fs_frame FS 1 0));
    [exact H|].
  rewrite (fs_frame1 FS (fs_M 1)), (fs_frame1 FS 0). change (fs_M 1) with 8192.
  change (fs_shadow_area 1) with 131072. unfold shadow_addr.
  replace (FS + 1085440 + 0 * 128) with (FS + 1085440) by lia.
  replace (FS + 1085440 + 8192 * 128) with (FS + 1085440 + 131072 * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* The narrow form's premise on the class-1 frame area, from the statement's rng fact on the frames' span in
   fp_w [1%nat] FS: fs_M 1 = 8192 frames of fs_B 1 = 128 bytes, 2^20 bytes from fs_frame FS 1 0. *)
Lemma rcpF_frame_area : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (fs_frame FS 1 0) (2 ^ 20).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (2 ^ 20) with (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0); [exact H|].
  rewrite (fs_frame1 FS (fs_M 1)), (fs_frame1 FS 0). change (fs_M 1) with 8192. lia.
Qed.

(* ================= the prologue, the class-1 frame request and poisoning ================= *)

Section SetupF.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S FS : Z) (fr junk : list byte) (RNG : ExecF.footprint).
  Hypothesis SMAL : asan_stack_malloc_1_contract_F.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  (* The free frames X (class-1 frames in use by the caller, flag 1 at m) and the side-stack premise in the free-frame
     form (fpx: the data ranges are apart from fp_wx [1] FS X, which leaves out X's frames and their shadow). XB0 is
     not in reac_ctrl_parse_contract_x: without it an index of X may name a "flag" byte the run writes (the saved ra
     at S - 8, the class-1 hint), and the post's X flags at m' fail. *)
  Variable X : list (nat * Z).
  Hypothesis XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X.
  Hypothesis XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X.
  Hypothesis FP0 : fpx [1%nat] m (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X.
  Hypothesis TLS0 : reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - 8800) S.

  (* ---- The footprint premises of the run.  The shadow covers are QUANTIFIED (shcov / shblk / shkov): a ground
     rng premise whose bounds hold a division would make every later lia pay for that division's Euclidean
     equations.  The ranges without a division stay ground, since StepF's solve_acc1 matches them in the
     context. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 2560) 2432.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

  (* The implications among the Section hypotheses: no lia of the heavy proofs below needs them. *)
  Local Ltac rs_hide_sec :=
    rs_hide HF; rs_hide HOK; rs_hide AO0; rs_hide AF0; rs_hide RINF; rs_hide SCF; rs_hide SKF;
    rs_hide ROUT; rs_hide SCO; rs_hide SKO.

  (* the aligned sp (s1 after andi) *)
  Definition A : Z := (S - 128) / 32 * 32.

  Lemma HA1 : A mod 32 = 0 /\ S - 160 < A <= S - 128.
  Proof. unfold A. Z.div_mod_to_equations. lia. Qed.

  Lemma STW0 : forall a, S - 8800 <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  (* The 12 saved registers, lowest address (S-96, s10) first. *)
  Definition SAVES : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* the writes of the run outside o: the window, the class-1 hint word, flag j, the frame and its shadow *)
  Definition Wf (fr j nn : Z) : list ivl :=
    [(S - 8800, S); (fs_hint FS 1, fs_hint FS 1 + 8); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (fr, fr + 128); (shadow_addr fr, shadow_addr fr + 16)].

  (* The frame: real (fv = 0, fr = A - 128, sp = A - 128) or fake (fv = fr the side frame j, sp = A, the flag-byte
     address w120 at fr + 120, and frame j's flag byte 0 at m: __asan_stack_malloc_1 took a free frame, so j is not a
     frame of X and frame j's flag is back to its value at m once the exit clears it). *)
  Definition FK (fr fv spc j nn : Z) (w120 : word) : Prop :=
    (fv = 0 /\ fr = A - 128 /\ spc = A - 128 /\ j = 0 /\ nn = 0) \/
    (0 <= j < fs_M 1 /\ fr = fs_frame FS 1 j /\ fv = fr /\ spc = A /\ w120 = Z_to_bv 64 (fs_flag FS 1 j) /\ nn = 1 /\
     bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0]).

  Lemma app_range : forall Y nn, 0 < nn -> (forall i, 0 <= i < nn -> app_mem (Y + i)) ->
    Y + nn <= 2147450880 \/ 17594333495296 <= Y.
  Proof.
    intros Y nn Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (nn - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (Y + nn) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 Y) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - Y) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma fk_facts : forall fr fv spc j nn w120, FK fr fv spc j nn w120 ->
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 128 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 128 -> app_mem (fr + i)) /\
    (fr + 128 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 16 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
    2147450880 <= fr / 8 + ASAN_K /\ fr / 8 + ASAN_K + 16 <= 17594333495296.
  Proof.
    intros fr0 fv spc j nn w120 HK.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & HAPP & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : fr0 mod 8 = 0 /\ FS + 36864 <= fr0 /\ fr0 + 128 <= A /\ (spc = A \/ spc = fr0) /\
                (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr0 + i)) <> None) /\
                (forall i, 0 <= i < 128 -> app_mem (fr0 + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & Ew & En & Hf0)]; subst fr0.
      - split; [unfold A; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ ST0); lia|].
        intros i Hi. unfold app_mem. right. lia.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ (14 - 1)) with 8192 in Hj. change (2 ^ 1) with 2 in *. change (2 ^ 20) with 1048576 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range fr0 128 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 16 -> fr0 / 8 + ASAN_K + i = shadow_addr (fr0 + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi. apply (proj1 (SR0 _ (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* ---- The footprint of the frame __asan_stack_malloc_1 gave: its 128 bytes and its 16 shadow bytes are in RNG
     whether it is the real-stack frame (inside the window) or a side frame (inside the class-1 frames). ---- *)
  Lemma rngF_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> rng RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply rng_sub; [exact RWIN | lia | lia].
    - eapply rng_sub; [exact RFRM | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_cov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shcov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shcov_sub; [exact SCW | lia | lia].
    - eapply shcov_sub; [exact SCFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  Lemma rngF_frame_kov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shkov RNG fra 128.
  Proof.
    intros fra fv spc j nn w120 HK. pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & Efra & Espc & Ej & En) | (Hj & Efra & Efvs & Espc & Ew & En & Hf0)]; subst fra.
    - eapply shkov_sub; [exact SKW | lia | lia].
    - eapply shkov_sub; [exact SKFR | rewrite !fs_frame1; lia | rewrite !fs_frame1; lia].
  Qed.

  (* The 16 shadow bytes of the frame, at the addresses the run forms: fra / 8 + ASAN_K + i. *)
  Lemma rngF_frame_blk : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shblk RNG fra 15.
  Proof.
    intros fra fv spc j nn w120 HK.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & _).
    pose proof (rngF_frame_cov fra fv spc j nn w120 HK) as HC.
    intros i Hi. pose proof (sh_add8 fra i FR8) as Hs. unfold shadow_addr in Hs.
    replace (fra / 8 + ASAN_K + i) with ((fra + 8 * i) / 8 + ASAN_K) by lia.
    apply HC. lia.
  Qed.

  Definition BI (W : list ivl) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES.

  (* The continuation at 0x83f28: the body. The last premise is the side frame's flag-pointer word at fr + 120
     (written by __asan_stack_malloc_1, read back by the release at the exit); the body never writes there. *)
  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fr fv spc j nn w120 -> BI (Wf fr j nn) mc -> addressable mc (fr + 32) 36 ->
      (fv <> 0 -> bytes_at rsegs mc (fr + 120) (le8 w120)) ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fr / 8 + ASAN_K)) (Z_to_bv 64 fr) (wa ASAN_K)
                         (Z_to_bv 64 (fr + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x83f28) fc None mc (seg_rom rsegs)).

  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* 0x83ea8 .. 0x83f28: the stack slot, the 3 frame words and the 16 shadow bytes of the frame. *)
  Lemma fwords : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) Q,
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) -> KB Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x83ea8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q
      HK HB H120 K.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSpos & _) & _).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf, shadow_addr in MU.
    (* the writes of this block: the stack slot, the 3 frame words and the 16 shadow bytes; fra + 120 is apart *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24);
                            (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUw.
    rs_hide_sec. rs_hide H120. rs_hide Fsp. rs_hide FRA.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83ed0.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_mono m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk mcur fra SRmc ltac:(lia) FRA ltac:(lia) ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    eapply K.
    - exact HK.
    - unfold BI, Wf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
    - (* fra + 120 is apart from this block's writes, so the flag-pointer word is still there *)
      intros Hfv. eapply (bytes_at_transport rsegs _ mc _ (fra + 120) (le8 w120) (H120 Hfv) MUw).
      cbn [disjoint_from]. rewrite length_le8. unfold rs_hold in FRA. lia.
  Qed.

  (* 0x83e04 .. 0x83ea8: the prologue, the class-1 frame request __asan_stack_malloc_1(128) and the choice of a
     side-stack frame or the real-stack fallback with its page probe. *)
  Lemma entry : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KB Q ->
    evtF rsegs RNG Q (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    unfold REAC_CTRL_PARSE.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPm. unfold reac_ctrl_parse_W in FPm.
    assert (MU : munch [(S - 8800, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 96) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    rs_hide_sec.
    carve_frame 96%nat STs.
    carve_frame 32%nat STz.
    step.
    steps_to 0x83e40.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
    rewrite EA.
    steps_to 0x83e6c.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (fl_fp [1%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HFl & HFln & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ A _ STzc ltac:(lia)) as [STA _].
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd0 & _).
    pose proof (fl_cols (reac_ctrl_parse_W o S) [(S - 8800, S)] _ HWd0
                  ltac:(unfold sub_fp, reac_ctrl_parse_W; intros xq Hxq; cbn [outside] in Hxq |- *;
                        split; [exact (proj1 Hxq) | exact I])) as HCOLa.
    assert (HCOL0 : Forall (fun d => forall x, fst d <= x < snd d -> outside [(S - 8800, S)] x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0))
      by (rewrite Forall_forall in HCOLa |- *; intros dq Hdq; apply HCOLa, in_or_app; left; exact Hdq).
    destruct (fl_tls_same m m1 [(S - 8800, S)] (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k
                HT0 HT MU HCOL0) as (EDT & ETS & EC & ET & EDB & Ekq).
    subst DT0 TS0 C0 T0 DB0 k0.
    pose proof SMAL as HM. unfold asan_stack_malloc_1_contract_F, asan_stack_malloc_contract_F in HM. cbv zeta in HM.
    specialize (HM (proj1 (Nat.leb_le 1 10) eq_refl)).
    eapply evtF_cut.
    { destruct (rcpF_tls_rng RNG _ DT TS C T DB k (RTLS DT TS C T DB k HT0))
        as (RTdt & RTts & RTc & RTt & RTdb & RTp88 & RTp8).
      eapply HM with (lo := S - 8800) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m m1 SR0 WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HFl.
      - exact HFln.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
          match goal with Hd : RcLay.ly_dj _ _ lo hi |- _ => unfold RcLay.ly_dj in Hd; lia end end.
      - (* the image *) unfold IMG_LO, IMG_HI. exact RIMG.
      - (* the callee's window [A - 208, A) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - (* the runtime pointer cell at DT + 8 *) exact RTdt.
      - (* the runtime pointer cell at TS + 8 k *) exact RTts.
      - (* the runtime pointer cell at C + 152 *) exact RTc.
      - (* the runtime pointer cells at T + 48 *) exact RTt.
      - (* the runtime pointer cell at DB + 24 *) exact RTdb.
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 frame area, from the frames' range in fp_w [1%nat] FS *) exact (rcpF_frame_area RNG FS RW1).
      - (* the shadow of the class-1 frame area *) exact (rcpF_frame_sh RNG FS RW1).
      - (* the thread-pointer cell at TP - 88 *) exact RTp88.
      - (* the thread-pointer cells at TP - 8 .. TP + 16 *) exact RTp8. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x83e78)) with (Z_to_bv 64 0x83e78) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 128, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf (A - 128) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 128)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step.
      assert (HSp : store_ok rsegs m2 (wa (A - 4096)) 8 = true)
        by (eapply wv_store_ok with (m := m2);
              [ intros i Hi; apply (stk_wv m2 (S - 8800) A); [exact ST2 | lia] | apply wmono_refl | lia | lia ]).
      rewrite (unsigned_lit A) by lia.
      step. store_done.
      step.
      rewrite (rc_lts_signed (A - 128) (A - 4096)) by lia.
      replace (A - 128 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (fwords (A - 128) 0 (A - 128) 0 0 (Z_to_bv 64 0));
        [left; repeat split; lia | | intros Hc; exfalso; exact (Hc eq_refl) | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
    - (* the side-stack frame fs_frame FS 1 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      change (bv_unsigned (Z_to_bv 64 128)) with 128 in FRM.
      replace (fs_shadow_n 1 128) with 16 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 1 jj) as fra eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hjj.
      assert (SHb : shadow_addr fra + 16 <= S - 8800)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (EFl : fs_flag FS 1 jj = FS + 20480 + jj)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      (* flag jj was 0 at m1 (the frame __asan_stack_malloc_1 took was free), and the prologue wrote only the window *)
      assert (HFj0 : bytes_at rsegs m (fs_flag FS 1 jj) [Z_to_bv 8 0]).
      { pose proof HFl as (Ba & Bl & BH).
        assert (HJ : (Z.to_nat jj < length flags)%nat) by (rewrite EM1 in HFln; lia).
        pose proof (BH (Z.to_nat jj) HJ) as E1. rewrite Hnth in E1. rewrite Z2Nat.id in E1 by lia.
        replace (fs_flag FS 1 0 + jj) with (fs_flag FS 1 jj) in E1 by (unfold fs_flag; lia).
        split; [rewrite EFl; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; rewrite EFl; lia|].
        intros i0 Hi0. cbn [length] in Hi0. destruct i0 as [|i0]; [|lia].
        cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. rewrite <- E1.
        unfold mrd. rewrite (MU (wa (fs_flag FS 1 jj))); [reflexivity|].
        rewrite wa_unsigned by (rewrite EFl; lia). cbn [outside]. rewrite EFl. split; [lia | exact I]. }
      assert (HKj : FK fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj))).
      { right. split; [rewrite EM1; exact Hjj|]. split; [exact Efr|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact HFj0]. }
      pose proof HFS' as HFSw.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFLg). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H120). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf fra jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi RS; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
        ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES]; rewrite EFl;
              clear -HFS' FShi Hjj SHb HAlo HAhi RS; lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STw STs STz STw2 STzc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fra) by lia. cbn [negb]. cbv iota.
      eapply (fwords fra fra A jj 1 (Z_to_bv 64 (fs_flag FS 1 jj)));
        [exact HKj | | intros _; replace (fra + 120) with (fra + 128 - 8) by lia; exact H120
         | exact K].
      refine (conj _ (conj WM3 (conj RM3 (conj MI2 FR2)))). unfold Wf, shadow_addr. exact MU3.
  Qed.

  (* ================= the body (0x83f28 .. 0x84314) ================= *)

  (* The runtime state the post names: the runtime's cells and shadow, the window addressable, the side-stack premise
     in the free-frame form, X's flags still 1, the class-1 flag array as at m (rcp_flag_kept), the tls premise. *)
  Definition aJ (mc : word -> option byte) : Prop :=
    asan_cells mc /\ shadow_rw mc /\ addressable mc (S - 8800) 8800 /\
    fpx [1%nat] mc (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    Forall (fun ci => bytes_at rsegs mc (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
    (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat ->
       bytes_at rsegs m (fs_flag FS 1%nat 0) fl -> bytes_at rsegs mc (fs_flag FS 1%nat 0) fl) /\
    reac_ctrl_parse_tls mc (bv_unsigned tp) FS (S - 8800) S.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

  (* The contract's post (reac_ctrl_parse_contract_x of reac_ctrl_parse_c.v, with K = 8800 and sp = S). *)
  Definition Qp : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8800) S /\
      (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
      asan_cells m' /\ shadow_rw m' /\ addressable m' (S - 8800) 8800 /\
      fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
      Forall (fun ci => bytes_at rsegs m' (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X /\
      (forall fl, (length fl <= Z.to_nat (fs_M 1))%nat ->
         bytes_at rsegs m (fs_flag FS 1%nat 0) fl -> bytes_at rsegs m' (fs_flag FS 1%nat 0) fl) /\
      reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.

  (* Every flag byte X names is a byte of the class-1 flag array. *)
  Lemma x_flag_in : forall ci, In ci X ->
    fs_flag FS (fst ci) (snd ci) = fs_flag FS 1 (snd ci) /\
    fs_flag FS 1 0 <= fs_flag FS 1 (snd ci) /\ fs_flag FS 1 (snd ci) + 1 <= fs_flag FS 1 0 + fs_M 1.
  Proof.
    intros ci Hin.
    destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (Hc & _).
    pose proof (proj1 (Forall_forall _ _) XB0 ci Hin) as Hb.
    rewrite Hc. split; [reflexivity|].
    assert (EM : fs_M 1 = 8192) by reflexivity.
    rewrite !fs_flag1, EM. rewrite EM in Hb. clear -Hb. lia.
  Qed.

  Lemma aJ_m : aJ m.
  Proof.
    split; [exact AC0|]. split; [exact SR0|]. split; [exact AW0|]. split; [exact FP0|].
    split; [eapply Forall_impl; [|exact XF0]; intros ci (_ & H); exact H|].
    split; [intros fl _ H; exact H | exact TLS0].
  Qed.

  (* aJ survives writes inside the function's window [S - 8800, S). *)
  Lemma jr_win : forall W' m1 m2, aJ m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 ->
    sub_fp W' [(S - 8800, S)] -> aJ m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW & FP & XF & FL & TL) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (S - 8800) S x Hs HHM Hx)).
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP) as FPn.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    (* the class-1 flag array is on the side stack, below the window *)
    assert (FLo : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> outside W' x).
    { intros x Hx. apply (fl_out_lo W' (S - 8800) S x Hs). left.
      unfold fs_flag, fs_M in Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx.
      change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 1)) with 16384 in Hx. change (2 ^ (14 - 1)) with 8192 in Hx.
      clear -Hx HFSb. lia. }
    split; [|split; [|split; [|split; [|split; [|split]]]]].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (S - 8800) S x Hs).
      left. clear -Hx HHM. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - exact (fl_shadow_rw W' m1 m2 SW MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
    - apply fpx_of_fp_nil; [|exact (fpx_dj _ _ _ _ _ _ _ _ _ FP)].
      exact (fl_fp [1%nat] m1 m2 (bv_unsigned tp) FS (S - 8800) S (if o =? 0 then [] else [(o, o + 36)])
               [] W' FPn MU WM Hs).
    - apply Forall_forall. intros ci Hin. pose proof (proj1 (Forall_forall _ _) XF ci Hin) as Hb.
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (fl_bytes W' m1 m2 _ _ Hb MU). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply FLo. clear -Hx L1 L2. lia.
    - intros fl Hl Hb. apply (fl_bytes W' m1 m2 _ _ (FL fl Hl Hb) MU). intros x Hx. apply FLo.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
    - exact (fl_tls [1%nat] m1 m2 (bv_unsigned tp) FS (S - 8800) S (if o =? 0 then [] else [(o, o + 36)])
               [] W' (fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) FPn MU Hs TL).
  Qed.

  (* 0x842dc .. 0x84314: sp = s0 - 128, the saved registers restored from [S - 96, S), the frame popped, ret. *)
  Lemma L_restore : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]) m m' ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) -> aJ m' ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x842dc) fc None m' (seg_rom rsegs)).
  Proof.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM MI ST HBox HaJ.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. unfold Qp. destruct HaJ as (AC & SW & AW & FP & XF & FL & TL).
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AC|]. split; [exact SW|]. split; [exact AW|].
    split; [exact FP|]. split; [exact XF|]. split; [exact FL | exact TL].
  Qed.

  (* The full body footprint stays apart from the runtime's cells [RT_LO, RT_HI): the window and the side stack are
     above them, o is apart (AO0 via the CF cells), and every shadow byte is apart from application memory. *)
  Lemma aout_rt : forall Wm x,
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    RT_LO <= x < RT_HI -> outside Wm x.
  Proof.
    intros Wm x Hs Hx.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold HIGHMEM_BEG, APPMEM_END in HHM'. unfold RT_LO, RT_HI in Hx. unfold ASAN_GT in P3.
    unfold FS_SIZE in HFSb.
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    apply Hs. apply fl_out_app.
    - unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K. cbn [outside]. split; [lia|].
      destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO0 Eo) as (_ & _ & DRT). unfold GOT_CF, CF in DRT. split; [lia | exact I].
    - assert (F0 : 0 <= fs_frame FS 1 0) by (rewrite EFR0; lia).
      assert (FM : fs_frame FS 1 (fs_M 1) <= APPMEM_END) by (rewrite EFM; clear -HFSb HAE; lia).
      assert (W0 : 0 <= S - 8800) by lia.
      apply fl_out_app.
      + unfold fp_w, fp_w1; cbn [flat_map app outside].
        split; [unfold fs_hint; cbn [Z.of_nat]; lia|].
        split; [unfold fs_flag, fs_M; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
        split; [rewrite EFR0; lia|].
        split; [exact (acl_sh_out x (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) Hap F0 FM)|].
        exact I.
      + cbn [outside]. split; [|exact I].
        exact (acl_sh_out x (S - 8800) S Hap W0 HAE).
  Qed.

  (* The post's asan runtime state (asan_cells, shadow_rw, fp, tls) once the run wrote only within the window+o
     (fp's W), the class-1 side-stack bytes (fp_w [1] FS) and the window's shadow, with the hint and flag bytes read
     back as 0/1 at m'. fp is rebuilt by fl_fp_free, the tls premise by acl_tls_ret. *)
  Lemma aJ_free : forall Wm m',
    munch Wm m m' -> wmono rsegs m m' -> rd_mono m m' ->
    sub_fp Wm (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]) ->
    (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
    (forall x, FS <= x < FS + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
    (exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')) ->
    (exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags') ->
    asan_cells m' /\ shadow_rw m' /\
    fpx [1%nat] m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f n o) X /\
    reac_ctrl_parse_tls m' (bv_unsigned tp) FS (S - 8800) S.
  Proof.
    intros Wm m' MU WM RM Hs O88 HRD Hint Hflags.
    pose proof (fpx_fp_nil _ _ _ _ _ _ _ _ _ FP0) as FPn.
    split; [|split; [|split]].
    - apply (fl_asan_cells Wm m m' AC0 MU). intros x Hx. exact (aout_rt Wm x Hs Hx).
    - exact (shadow_rw_mono m m' SR0 WM RM).
    - apply fpx_of_fp_nil; [|exact (fpx_dj _ _ _ _ _ _ _ _ _ FP0)].
      eapply (fl_fp_free [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] Wm FPn TLS0 MU WM Hs O88 HRD).
      intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split; [exact Hint | exact Hflags].
    - exact (acl_tls_ret [1%nat] m m' (bv_unsigned tp) FS (S - 8800) S (reac_ctrl_parse_W o S)
               [] [(shadow_addr (S - 8800), shadow_addr S)] Wm FPn TLS0 MU Hs).
  Qed.

  (* ================= the body (0x83f28 .. 0x842dc) ================= *)

  (* The record buffer the body fills: the caller's o when given, else the frame's 32-byte scratch at fra + 32. *)
  Definition REC (fra : Z) : Z := if o =? 0 then fra + 32 else o.

  (* The body's write footprint: the frame footprint Wf plus the record at o (when o <> 0). *)
  Definition Wb (fra j nn : Z) : list ivl :=
    Wf fra j nn ++ (if o =? 0 then [] else [(o, o + 36)]).

  (* The invariant carried through the body: the writes stay inside Wb, the window's saved registers are intact, and
     the record buffer is addressable (so the instrumented checks before each record access pass). *)
  Definition aJb (fra j nn : Z) (mc : word -> option byte) : Prop :=
    munch (Wb fra j nn) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES /\ addressable mc (REC fra) 36.

  (* Wb is apart from everything the full footprint (reac_ctrl_parse_W, the class-1 side-stack bytes and the window's
     shadow) is apart from: so the body's munch feeds aJ_free and aout_rt at the exit. *)
  Lemma Wb_sub : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wb fra j nn)
      (reac_ctrl_parse_W o S ++ fp_w [1%nat] FS ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof.
    intros fra fv spc j nn w120 HK x Hout.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFSb & _ & _ & _).
    unfold ASAN_GT in P3. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    apply acl_out_app_inv in Hout. destruct Hout as [HoutW Hout1].
    apply acl_out_app_inv in Hout1. destruct Hout1 as [HoutF HoutS].
    unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K in HoutW. cbn [outside] in HoutW. destruct HoutW as [HW0 HWo].
    unfold fp_w in HoutF. cbn [flat_map app] in HoutF. unfold fp_w1 in HoutF. cbn [outside] in HoutF.
    destruct HoutF as (Hhint & Hflag & Hframe & Hsframe & _).
    cbn [outside] in HoutS. destruct HoutS as [HSwin _].
    assert (EFR0 : fs_frame FS 1 0 = FS + 1085440) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016)
      by (unfold fs_frame, fs_B, fs_M; cbn [Z.of_nat Pos.of_succ_nat];
          change (2 ^ (14 - 1)) with 8192; change (2 ^ 1) with 2; change (2 ^ 20) with 1048576; lia).
    rewrite EFR0, EFM in Hframe, Hsframe.
    unfold Wb. apply fl_out_app; [unfold Wf | exact HWo]. cbn [outside].
    split; [exact HW0|].
    split; [exact Hhint|].
    split.
    { destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hf0)].
      - subst nn j. cbn [Z.mul Z.add]. intros [A1 A2]. clear -A1 A2. lia.
      - subst nn. unfold fs_flag, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 1)) with 16384 in *.
        change (2 ^ (14 - 1)) with 8192 in *. clear -Hflag Hj. lia. }
    destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hf0)].
    - subst fra.
      assert (M8 : (A - 128) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
      split.
      + clear -HW0 HAlo HAhi RS. lia.
      + split; [|exact I]. intros [A1 A2].
        pose proof (sh_add8 (A - 128) 16 M8) as E. replace (A - 128 + 8 * 16) with A in E by lia.
        apply HSwin. split.
        * pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(clear -HAlo RS; lia)). lia.
        * pose proof (acl_sh_ge S A ltac:(clear -HAhi RS; lia)). lia.
    - subst fra.
      assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
        by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576; lia).
      assert (Hjb : 0 <= j < 8192)
        by (unfold fs_M in Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj; change (2 ^ (14 - 1)) with 8192 in Hj; exact Hj).
      rewrite EFRj in FR8 |- *.
      split.
      + clear -Hframe Hjb. lia.
      + split; [|exact I]. intros [A1 A2].
        pose proof (sh_add8 (FS + 1085440 + j * 128) 16 FR8) as E.
        replace (FS + 1085440 + j * 128 + 8 * 16) with (FS + 1085440 + j * 128 + 128) in E by lia.
        apply Hsframe. split.
        * pose proof (acl_sh_ge (FS + 1085440 + j * 128) (FS + 1085440) ltac:(clear -Hjb; lia)). lia.
        * pose proof (acl_sh_ge (FS + 2134016) (FS + 1085440 + j * 128 + 128) ltac:(clear -Hjb; lia)). lia.
  Qed.

  (* The runtime's cells and shadow survive the body's writes. *)
  Lemma jb_sw : forall fra j nn mc, aJb fra j nn mc -> shadow_rw mc.
  Proof. intros fra j nn mc (MU & WM & RM & _). exact (shadow_rw_mono m mc SR0 WM RM). Qed.

  Lemma jb_ac : forall fra fv spc j nn w120 mc, FK fra fv spc j nn w120 -> aJb fra j nn mc -> asan_cells mc.
  Proof.
    intros fra fv spc j nn w120 mc HK (MU & WM & RM & _).
    apply (fl_asan_cells (Wb fra j nn) m mc AC0 MU).
    intros y Hy. exact (aout_rt (Wb fra j nn) y (Wb_sub fra fv spc j nn w120 HK) Hy).
  Qed.

  (* A frame index whose flag byte is 0 at m is not an index of X: X's flags are 1 at m. *)
  Lemma x_ne_j : forall j, bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] -> Forall (fun ci => snd ci <> j) X.
  Proof.
    intros j (_ & _ & H0). eapply Forall_impl; [|exact XF0].
    intros [c i] (Hc & (_ & _ & H1)) E. cbn [fst snd] in Hc, E, H1. subst c i.
    pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0. pose proof (H1 0%nat ltac:(cbn [length]; lia)) as A1.
    cbn [nth_error] in A0, A1. rewrite A0 in A1. injection A1 as A1.
    vm_compute in A1. discriminate.
  Qed.

  (* A data range of the caller (D: f's 50 bytes, o's record) is apart from a class-1 frame j whose flag is 0 at m:
     j is not in X, so the frame is inside fpx's footprint fp_wx [1] FS X, which D is apart from. *)
  Lemma D_apart_frame : forall a b j, In (a, b) (reac_ctrl_parse_D f n o) -> a < b ->
    0 <= j < fs_M 1 -> bytes_at rsegs m (fs_flag FS 1 j) [Z_to_bv 8 0] ->
    b <= fs_frame FS 1 j \/ fs_frame FS 1 j + 128 <= a.
  Proof.
    intros a b j Hin Hab Hj Hfl0.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd.
    assert (E1 : fs_frame FS 1 (j + 1) = fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
    destruct (Z_le_gt_dec b (fs_frame FS 1 j)) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (fs_frame FS 1 j + 128) a) as [R|R]; [right; exact R|].
    exfalso. apply (fp_wx_frame_in FS X j (Z.max a (fs_frame FS 1 j)) Hj (x_ne_j j Hfl0)); [lia|].
    apply (fl_dj_out_r _ _ a b (Z.max a (fs_frame FS 1 j)) HDd Hin). lia.
  Qed.

  (* A data range of the caller is apart from the class-1 hint word and flag array (both stay in fp_wx [1] FS X). *)
  Lemma D_apart_hint_flag : forall a b, In (a, b) (reac_ctrl_parse_D f n o) ->
    RcLay.ly_dj a b (fs_hint FS 1) (fs_hint FS 1 + 8) /\ RcLay.ly_dj a b (fs_flag FS 1 0) (fs_flag FS 1 0 + fs_M 1).
  Proof.
    intros a b Hin.
    pose proof (fpx_dj _ _ _ _ _ _ _ _ _ FP0) as HDd. unfold fp_dj in HDd.
    pose proof (proj1 (Forall_forall _ _) HDd (a, b) Hin) as Hab. cbn beta in Hab. rewrite Forall_forall in Hab.
    destruct (fp_wx_hint_flag_in FS X) as (Hh & Hf).
    split; [exact (Hab _ Hh) | exact (Hab _ Hf)].
  Qed.

  (* The input buffer f is apart from the frame: inside the window apart from it (real frame) or apart from the
     side frame j by fpx's data-range disjointness (side frame, D_apart_frame). *)
  Lemma f_apart_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> 50 <= n ->
    f + 50 <= fra \/ fra + 128 <= f.
  Proof.
    intros fra fv spc j nn w120 HK HN.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hfl0)].
    - subst fra. destruct HfW as [L|R]; [left; clear -L HAlo HAhi RS; lia | right; clear -R HAlo HAhi RS; lia].
    - subst fra.
      assert (HinD : In (f, f + 50) (reac_ctrl_parse_D f n o)).
      { unfold reac_ctrl_parse_D. replace (n <? 50) with false by (symmetry; apply Z.ltb_ge; lia).
        apply in_or_app. left. left. reflexivity. }
      exact (D_apart_frame f (f + 50) j HinD ltac:(lia) Hj Hfl0).
  Qed.

  (* The shadow byte of an application byte apart from the frame is apart from every range the body writes. *)
  Lemma jb_sh_out : forall fra fv spc j nn w120 y, FK fra fv spc j nn w120 ->
    app_mem y -> (y + 1 <= fra \/ fra + 128 <= y) -> outside (Wb fra j nn) (shadow_addr y).
  Proof.
    intros fra fv spc j nn w120 y HK Hap Hfr.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & HP & _ & _ & _ & _ & _ & _ & _).
    destruct HP as (_ & _ & HGT & Hfsapp & _). unfold ASAN_GT in HGT.
    pose proof (rt_app_shadow y Hap) as Hs. set (z := shadow_addr y) in *.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    assert (Hzlt : z < 0x10007fff8000)
      by (clear -Hs; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs; lia).
    assert (NF : forall a b, FS <= a -> b <= FS + 11571200 -> ~ (a <= z < b)).
    { intros a b Ha Hb [c1 c2]. apply (acl_app_not_shadow z); [apply Hfsapp; unfold FS_SIZE; lia | exact Hs]. }
    assert (H4 : ~ (fra <= z < fra + 128)).
    { destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hfl0)]; subst fra.
      - intros [c1 c2]. clear -c1 Hzlt HHM' HAlo HAhi RS. lia.
      - assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576; lia).
        assert (Hjb : 0 <= j < 8192)
          by (unfold fs_M in Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj; change (2 ^ (14 - 1)) with 8192 in Hj; exact Hj).
        rewrite EFRj. apply NF; clear -Hjb; lia. }
    assert (H5 : ~ (shadow_addr fra <= z < shadow_addr fra + 16)).
    { pose proof (sh_add8 fra 16 FR8) as E. replace (fra + 8 * 16) with (fra + 128) in E by lia.
      pose proof (acl_win_sh y fra (fra + 128) FR8 ltac:(clear -Hfr; lia)) as HW. rewrite E in HW. exact HW. }
    unfold Wb. apply fl_out_app; [unfold Wf; cbn [outside] | ].
    - split; [clear -Hzlt HHM'; lia|].
      split; [apply NF; [unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -HGT; lia | unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -HGT; lia]|].
      split.
      { destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hfl0)].
        - subst nn j. cbn [Z.add]. intros [c1 c2]. clear -c1 c2. lia.
        - subst nn. apply NF; unfold fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
            change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 1)) with 16384 in *;
            change (2 ^ (14 - 1)) with 8192 in Hj; clear -Hj HGT; lia. }
      split; [exact H4|].
      split; [exact H5 | exact I].
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside].
      + exact I.
      + split; [|exact I]. destruct (AO0 Eo) as (AOa & _ & _). intros [c1 c2].
        apply (acl_app_not_shadow z); [replace z with (o + (z - o)) by lia; apply (acl_app_in m o 36); [exact AOa | clear -c1 c2; lia] | exact Hs].
  Qed.

  (* The 50 input bytes at f stay addressable through the body's writes. *)
  Lemma jb_af : forall fra fv spc j nn w120 mc, FK fra fv spc j nn w120 -> aJb fra j nn mc -> 50 <= n ->
    addressable mc f 50.
  Proof.
    intros fra fv spc j nn w120 mc HK (MU & _) HN.
    apply (acl_addr_munch (Wb fra j nn) m mc f 50 (AF0 HN) MU). intros i Hi.
    pose proof (acl_app_in m f 50 i (AF0 HN) Hi) as Hap.
    apply (jb_sh_out fra fv spc j nn w120 (f + i) HK Hap).
    destruct (f_apart_frame fra fv spc j nn w120 HK HN) as [L|R]; [left; clear -L Hi; lia | right; clear -R Hi; lia].
  Qed.

  (* The 6 bytes of the .str.4 compare literal stay addressable through the body's writes. *)
  Lemma jb_bc : forall fra fv spc j nn w120 mc, FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    addressable mc REAC_CTRL_PARSE_BC 6.
  Proof.
    intros fra fv spc j nn w120 mc HK (MU & _).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & HP & _ & _ & _ & _ & _ & _ & _).
    destruct HP as (_ & _ & HGT & _ & _). unfold ASAN_GT in HGT.
    destruct (fk_facts fra fv spc j nn w120 HK) as (_ & FRlo & _ & _ & _ & _ & _ & _ & _ & _).
    apply (acl_addr_munch (Wb fra j nn) m mc REAC_CTRL_PARSE_BC 6 ABC MU). intros i Hi.
    pose proof (acl_app_in m REAC_CTRL_PARSE_BC 6 i ABC Hi) as Hap.
    apply (jb_sh_out fra fv spc j nn w120 (REAC_CTRL_PARSE_BC + i) HK Hap).
    left. unfold REAC_CTRL_PARSE_BC. clear -FRlo HGT Hi. lia.
  Qed.

  (* ================= the frame-free exit (0x84224 .. 0x842dc) ================= *)

  (* The window stays addressable at the exit's memory. Side frame: the frame is on the side stack, apart from the
     window, so the window's shadow bytes are untouched (acl_addr_munch of AW0). *)
  Lemma epi_win_side : forall fra fv spc j nn w120 m',
    FK fra fv spc j nn w120 -> fv <> 0 -> munch (Wb fra j nn) m m' -> addressable m' (S - 8800) 8800.
  Proof.
    intros fra fv spc j nn w120 m' HK Hfv MU.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & _ & _ & _ & _ & HFSb & _ & _ & _). unfold FS_SIZE in HFSb.
    assert (Efra128 : fra + 128 <= S - 8800).
    { destruct HK as [(Ef & _ & _ & _ & _)|(Hj & Efr & _)]; [subst fv; contradiction|].
      subst fra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576.
      unfold fs_M in Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. change (2 ^ (14 - 1)) with 8192 in Hj.
      clear -Hj HFSb. lia. }
    apply (acl_addr_munch (Wb fra j nn) m m' (S - 8800) 8800 AW0 MU). intros i Hi.
    assert (Hap : app_mem (S - 8800 + i)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    apply (jb_sh_out fra fv spc j nn w120 (S - 8800 + i) HK Hap). right. clear -Efra128 Hi. lia.
  Qed.

  (* Real frame: the frame [A - 128, A) is inside the window; its 128 bytes are addressable from the 16 shadow bytes
     the exit set to 0 (frame_all_addr), the non-frame window parts from AW0 (acl_addr_munch), joined. *)
  Lemma epi_win_real : forall fra fv spc j nn w120 m',
    FK fra fv spc j nn w120 -> fv = 0 -> munch (Wb fra j nn) m m' ->
    (forall g, 0 <= g <= 15 -> exists b, mrd rsegs m' (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) ->
    addressable m' (S - 8800) 8800.
  Proof.
    intros fra fv spc j nn w120 m' HK Hfv MU HSH.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Efra : fra = A - 128).
    { destruct HK as [(_ & Efr & _)|(Hj & Efr & Ef & _)]; [exact Efr|].
      exfalso. rewrite Ef in Hfv. rewrite Efr in Hfv.
      pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp & _) & _).
      unfold fs_frame, fs_B in Hfv. cbn [Z.of_nat Pos.of_succ_nat] in Hfv. change (2 ^ 20) with 1048576 in Hfv.
      unfold fs_M in Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. change (2 ^ (14 - 1)) with 8192 in Hj.
      clear -Hfv FSp Hj. lia. }
    assert (M8 : (A - 128) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
    assert (Apos : 0 <= A - 128) by (clear -HAlo RS; lia).
    (* part1 : [S - 8800, A - 128) *)
    assert (P1 : addressable m' (S - 8800) (A - 128 - (S - 8800))).
    { apply (acl_addr_munch (Wb fra j nn) m m' (S - 8800) (A - 128 - (S - 8800))
               (acl_addr_sub m (S - 8800) 8800 (S - 8800) (A - 128 - (S - 8800)) AW0 ltac:(lia) ltac:(lia) ltac:(lia)) MU).
      intros i Hi. assert (Hap : app_mem (S - 8800 + i)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
      apply (jb_sh_out fra fv spc j nn w120 (S - 8800 + i) HK Hap). left. rewrite Efra. clear -Hi; lia. }
    (* part3 : [A, S) *)
    assert (P3 : addressable m' A (S - A)).
    { apply (acl_addr_munch (Wb fra j nn) m m' A (S - A)
               (acl_addr_sub m (S - 8800) 8800 A (S - A) AW0 ltac:(lia) ltac:(lia) ltac:(lia)) MU).
      intros i Hi. assert (Hap : app_mem (A + i)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
      apply (jb_sh_out fra fv spc j nn w120 (A + i) HK Hap). right. rewrite Efra. clear -Hi; lia. }
    (* frame : [A - 128, A) via frame_all_addr *)
    assert (PF : addressable m' (A - 128) 128).
    { apply frame_all_addr.
      - exact Apos.
      - exact M8.
      - unfold APPMEM_END in *; clear -HAhi HAE'; lia.
      - intros i Hi. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; clear -Hi HAlo HAhi HHM' HAE' RS; lia.
      - intros g Hg. rewrite <- Efra. exact (HSH g Hg). }
    assert (P3' : addressable m' (A - 128 + 128) (S - A)) by (replace (A - 128 + 128) with A by lia; exact P3).
    pose proof (acl_addr_join m' (A - 128) 128 (S - A) PF P3' ltac:(lia)) as PFR.
    assert (EJ : addressable m' (S - 8800) ((A - 128 - (S - 8800)) + (128 + (S - A)))).
    { apply (acl_addr_join m' (S - 8800) (A - 128 - (S - 8800)) (128 + (S - A)) P1); [|clear -HAlo HAhi RS; lia].
      replace (S - 8800 + (A - 128 - (S - 8800))) with (A - 128) by lia. exact PFR. }
    replace (A - 128 - (S - 8800) + (128 + (S - A))) with 8800 in EJ by lia. exact EJ.
  Qed.

  (* The side frame's flag array at the exit: m's array with index j cleared to 0 (the exit's flag-byte store), still
     every byte 0 or 1. Feeds aJ_free's Hflags premise. *)
  Lemma epi_flags : forall (m' : word -> option byte) (j : Z) (flags : list byte),
    0 <= j < fs_M 1 ->
    bytes_at rsegs m (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
    mrd rsegs m' (wa (fs_flag FS 1 j)) = Some (Z_to_bv 8 0) ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> x <> fs_flag FS 1 j ->
       mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros m' j flags Hj (Ba & Bl & BH) Hlen HFl Hvj Hoth.
    set (J := Z.to_nat j).
    assert (HJlt : (J < length flags)%nat) by (unfold J; lia).
    assert (EjZ : Z.of_nat J = j) by (unfold J; rewrite Z2Nat.id; lia).
    assert (Ej : fs_flag FS 1 j = fs_flag FS 1 0 + Z.of_nat J)
      by (rewrite EjZ; unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (HLfir : length (firstn J flags) = J) by (apply firstn_length_le; lia).
    assert (HLsk : length (skipn (Datatypes.S J) flags) = (length flags - Datatypes.S J)%nat) by (apply length_skipn).
    exists (firstn J flags ++ Z_to_bv 8 0 :: skipn (Datatypes.S J) flags).
    assert (HL : length (firstn J flags ++ Z_to_bv 8 0 :: skipn (Datatypes.S J) flags) = length flags).
    { rewrite length_app. cbn [length]. rewrite HLfir, HLsk. clear -HJlt. lia. }
    split; [|split].
    - split; [exact Ba|]. split; [rewrite HL; exact Bl|].
      intros i Hi. rewrite HL in Hi.
      assert (HiZ : Z.of_nat i < fs_M 1) by (rewrite <- Hlen; lia).
      destruct (lt_eq_lt_dec i J) as [[Hlt|Heq]|Hgt].
      + rewrite nth_error_app1 by (rewrite HLfir; lia).
        rewrite nth_error_firstn. replace (Nat.ltb i J) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
        rewrite Hoth.
        * apply BH. lia.
        * unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; clear -HiZ; lia.
        * rewrite Ej. clear -Hlt EjZ. lia.
      + subst i. rewrite nth_error_app2 by (rewrite HLfir; lia).
        rewrite HLfir, Nat.sub_diag. cbn [nth_error].
        replace (fs_flag FS 1 0 + Z.of_nat J) with (fs_flag FS 1 j) by (rewrite Ej; reflexivity). exact Hvj.
      + rewrite nth_error_app2 by (rewrite HLfir; lia). rewrite HLfir.
        destruct (i - J)%nat as [|d] eqn:Ed; [exfalso; clear -Hgt Ed; lia|].
        cbn [nth_error]. rewrite nth_error_skipn. replace (Datatypes.S J + d)%nat with i by lia.
        rewrite Hoth.
        * apply BH. lia.
        * unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; clear -HiZ; lia.
        * rewrite Ej. clear -Hgt EjZ. lia.
    - rewrite HL; exact Hlen.
    - apply Forall_app. split.
      + pose proof (firstn_skipn J flags) as Esp. rewrite <- Esp in HFl. apply Forall_app in HFl.
        exact (proj1 HFl).
      + apply Forall_cons; [left; reflexivity|].
        pose proof (firstn_skipn (Datatypes.S J) flags) as Esp. rewrite <- Esp in HFl. apply Forall_app in HFl.
        exact (proj2 HFl).
  Qed.

  (* A byte apart from the run's writes keeps its value at the exit memory. *)
  Lemma munch_mrd_out : forall W m1 m2 x, munch W m1 m2 -> 0 <= x < 2^64 -> outside W x ->
    mrd rsegs m2 (wa x) = mrd rsegs m1 (wa x).
  Proof.
    intros W m1 m2 x MU Hx Hout. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
    rewrite wa_unsigned by lia. exact Hout.
  Qed.

  (* The caller's record o is apart from the class-1 flag array [FS + 20480, FS + 28672) (fpx's D-disjointness). *)
  Lemma o_apart_flag : o <> 0 -> o + 36 <= FS + 20480 \/ FS + 28672 <= o.
  Proof.
    intros Ho.
    assert (HinD : In (o, o + 36) (reac_ctrl_parse_D f n o)).
    { unfold reac_ctrl_parse_D. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq o 0) Ho). left. reflexivity. }
    destruct (D_apart_hint_flag o (o + 36) HinD) as (_ & Ho2).
    unfold RcLay.ly_dj in Ho2. destruct Ho2 as [L|R].
    - left. unfold fs_flag in L; cbn [Z.of_nat Pos.of_succ_nat] in L; clear -L; lia.
    - right. unfold fs_flag, fs_M in R; cbn [Z.of_nat Pos.of_succ_nat] in R;
        change (2 ^ 15) with 32768 in R; change (2 ^ (15 - 1)) with 16384 in R; change (2 ^ (14 - 1)) with 8192 in R;
        clear -R; lia.
  Qed.

  (* A flag byte not in the single range the exit writes (fs_flag FS 1 j, + nn) is apart from the body+exit writes. *)
  Lemma flag_out_Wb : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    FS + 20480 <= x < FS + 28672 -> ~ (fs_flag FS 1 j <= x < fs_flag FS 1 j + nn) ->
    outside (Wb fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx Hnotj.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _ & _ & FSp4 & _) & _ & _ & _ & HFSb & _ & _ & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & _ & _).
    assert (Hxapp : app_mem x) by (apply FSp4; clear -Hx HFSb; unfold FS_SIZE; lia).
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1; lia).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    unfold Wb. apply fl_out_app.
    - unfold Wf. cbn [outside].
      split; [clear -Hx HFSb; lia|].
      split; [unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -Hx; lia|].
      split; [exact Hnotj|].
      split; [clear -Hx FRlo; lia|].
      split; [|exact I].
      pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
      rewrite <- Esh. exact (acl_sh_out x fra (fra + 128) Hxapp Efra0 Efra128).
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      split; [|exact I]. destruct (o_apart_flag Eo) as [L|R]; [clear -Hx L | clear -Hx R]; lia.
  Qed.

  (* The exit's class-1 flag array is m's, byte for byte (feeds epi_aJ): the real frame writes no flag byte; the side
     frame's exit clears flag j, which was 0 at m (FK), and no other flag byte is written. *)
  Lemma epi_flags_real : forall fra fv spc j nn w120 m', FK fra fv spc j nn w120 -> fv = 0 ->
    munch (Wb fra j nn) m m' ->
    forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x).
  Proof.
    intros fra fv spc j nn w120 m' HK Hfv MU x Hx.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    assert (Hnn0 : nn = 0).
    { destruct HK as [(_ & _ & _ & _ & E)|(Hjj & Efr & Ef & _)]; [exact E|].
      exfalso. rewrite Ef in Hfv. rewrite Efr in Hfv.
      unfold fs_frame, fs_B in Hfv. cbn [Z.of_nat Pos.of_succ_nat] in Hfv. change (2 ^ 20) with 1048576 in Hfv.
      unfold fs_M in Hjj. cbn [Z.of_nat Pos.of_succ_nat] in Hjj. change (2 ^ (14 - 1)) with 8192 in Hjj.
      clear -Hfv FSp1 Hjj. lia. }
    assert (Ex : FS + 20480 <= x < FS + 28672).
    { unfold fs_flag, fs_M in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
        change (2 ^ 15) with 32768 in Hx; change (2 ^ (15 - 1)) with 16384 in Hx; change (2 ^ (14 - 1)) with 8192 in Hx;
        clear -Hx; lia. }
    assert (Hout : outside (Wb fra j nn) x).
    { apply (flag_out_Wb fra fv spc j nn w120 x HK Ex). rewrite Hnn0. clear; lia. }
    assert (Hbd : 0 <= x < 2^64) by (clear -Ex HFSb FSp1 RS; lia).
    exact (munch_mrd_out (Wb fra j nn) m m' x MU Hbd Hout).
  Qed.

  Lemma epi_flags_side : forall fra fv spc j nn w120 m', FK fra fv spc j nn w120 -> fv <> 0 ->
    munch (Wb fra j nn) m m' -> mrd rsegs m' (wa (fs_flag FS 1 j)) = Some (Z_to_bv 8 0) ->
    forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x).
  Proof.
    intros fra fv spc j nn w120 m' HK Hfv MU Hclr x Hx.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    pose proof HK as HK0.
    destruct HK0 as [(Ef & _)|(Hj & _ & _ & _ & _ & Hnn1 & Hfl0)]; [exfalso; apply Hfv; exact Ef|].
    assert (Ex : FS + 20480 <= x < FS + 28672).
    { unfold fs_flag, fs_M in Hx; cbn [Z.of_nat Pos.of_succ_nat] in Hx;
        change (2 ^ 15) with 32768 in Hx; change (2 ^ (15 - 1)) with 16384 in Hx; change (2 ^ (14 - 1)) with 8192 in Hx;
        clear -Hx; lia. }
    assert (Hbd : 0 <= x < 2^64) by (clear -Ex HFSb FSp1 RS; lia).
    destruct (Z.eq_dec x (fs_flag FS 1 j)) as [Exj|Exj].
    - subst x. rewrite Hclr. destruct Hfl0 as (_ & _ & H0).
      pose proof (H0 0%nat ltac:(cbn [length]; lia)) as A0. cbn [Z.of_nat nth_error] in A0.
      rewrite Z.add_0_r in A0. symmetry. exact A0.
    - apply (munch_mrd_out (Wb fra j nn) m m' x MU Hbd).
      apply (flag_out_Wb fra fv spc j nn w120 x HK Ex). rewrite Hnn1. clear -Exj; lia.
  Qed.

  (* The caller's record o is apart from the side stack's header [FS, FS + 36864) (fp's W-disjointness RT4.3). *)
  Lemma o_apart_FS : o <> 0 -> o + 36 <= FS \/ FS + 36864 <= o.
  Proof.
    intros Ho. pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    unfold reac_ctrl_parse_W, fp_dj in HWd.
    rewrite (proj2 (Z.eqb_neq o 0) Ho) in HWd.
    apply Forall_inv_tail in HWd. apply Forall_inv in HWd. cbn [fst snd] in HWd.
    rewrite Forall_app in HWd. destruct HWd as [_ HWd]. apply Forall_inv in HWd. cbn [fst snd] in HWd.
    assert (EFF : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    unfold RcLay.ly_dj in HWd. destruct HWd as [HWd|HWd]; [left; clear -HWd; lia | right; rewrite EFF in HWd; clear -HWd; lia].
  Qed.

  (* The runtime state the post names (aJ m') once the body+exit wrote only within Wb, the window is addressable, and
     the class-1 flag array at m' is m's (epi_flags_real / epi_flags_side): fpx and tls by aJ_free (with the header
     fields FS+80..104 and the side stack kept, the hint readable), X's flags and rcp_flag_kept from the array. *)
  Lemma epi_aJ : forall fra fv spc j nn w120 m',
    FK fra fv spc j nn w120 ->
    munch (Wb fra j nn) m m' -> wmono rsegs m m' -> rd_mono m m' ->
    addressable m' (S - 8800) 8800 ->
    (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> mrd rsegs m' (wa x) = mrd rsegs m (wa x)) ->
    aJ m'.
  Proof.
    intros fra fv spc j nn w120 m' HK MU WM RM AW Hfl.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & FSp2 & FSp3 & FSp4 & FSp5) & _ & _ & HCL & HFSb
                       & _ & _ & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & FAPP & FRA & _ & _ & _).
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1; lia).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    assert (Hj0 : 0 <= j) by (destruct HK as [(_ & _ & _ & Ejj & _)|(Hjj & _)]; lia).
    assert (O88 : forall x, FS + 80 <= x < FS + 104 -> outside (Wb fra j nn) x).
    { intros x Hx.
      assert (Hxapp : app_mem x) by (apply FSp4; clear -Hx HFSb; unfold FS_SIZE; lia).
      unfold Wb. apply fl_out_app.
      - unfold Wf. cbn [outside].
        split; [clear -Hx HFSb; lia|].
        split; [unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; clear -Hx; lia|].
        split; [unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; clear -Hx Hj0; lia|].
        split; [clear -Hx FRlo; lia|].
        split; [|exact I].
        pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
        rewrite <- Esh. exact (acl_sh_out x fra (fra + 128) Hxapp Efra0 Efra128).
      - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
        split; [|exact I]. destruct (o_apart_FS Eo) as [L|R]; [clear -Hx L | clear -Hx R]; lia. }
    pose proof (stk_mono m m' FS (FS + FS_SIZE) FSp5 WM RM) as STFS.
    assert (HRD : forall x, FS <= x < FS + FS_SIZE -> outside (Wb fra j nn) x \/ exists b, mrd rsegs m' (wa x) = Some b).
    { intros x Hx. right. exact (rd_of_stk m' FS (FS + FS_SIZE) STFS x Hx). }
    assert (Hint : exists h', bytes_at rsegs m' (fs_hint FS 1) (le8 h')).
    { apply (rd8_le8 m' (fs_hint FS 1)).
      - unfold fs_hint; cbn [Z.of_nat]; clear -FSp1; lia.
      - unfold fs_hint; cbn [Z.of_nat]; clear -HFSb HAE' FSp1; unfold FS_SIZE in *; lia.
      - intros i Hi. apply (rd_of_stk m' FS (FS + FS_SIZE) STFS).
        unfold fs_hint; cbn [Z.of_nat]; unfold FS_SIZE; clear -Hi HFSb FSp1; lia. }
    (* m's flag array, 0/1 bytes (fp_cls of FP0), reads back at m' *)
    apply Forall_inv in HCL. destruct HCL as (_ & h & flags & _ & Bflag & Lflag & Fflag).
    assert (Hflags : exists flags', bytes_at rsegs m' (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
                       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags').
    { exists flags. split; [|split; [exact Lflag | exact Fflag]].
      apply (bytes_keep m m' _ _ Bflag). intros x Hx. apply Hfl. rewrite Lflag in Hx. exact Hx. }
    destruct (aJ_free (Wb fra j nn) m' MU WM RM (Wb_sub fra fv spc j nn w120 HK) O88 HRD Hint Hflags)
      as (ACm & SWm & Hfp & Htls).
    split; [exact ACm|]. split; [exact SWm|]. split; [exact AW|]. split; [exact Hfp|].
    split.
    - apply Forall_forall. intros ci Hin. destruct (proj1 (Forall_forall _ _) XF0 ci Hin) as (_ & Hb).
      destruct (x_flag_in ci Hin) as (E & L1 & L2).
      apply (bytes_keep m m' _ _ Hb). intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      rewrite E in Hx. apply Hfl. clear -Hx L1 L2. lia.
    - split; [|exact Htls].
      intros fl Hl Hb. apply (bytes_keep m m' _ _ Hb). intros x Hx. apply Hfl.
      pose proof (len_le_M fl Hl) as Hl'. clear -Hx Hl'. lia.
  Qed.

  (* The caller's record o is apart from the frame: the window keeps o out of the real frame (HOK), and fpx's
     data-range disjointness keeps it out of the side frame j (D_apart_frame; o may be inside a frame of X). *)
  Lemma o_apart_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> o <> 0 ->
    o + 36 <= fra \/ fra + 128 <= o.
  Proof.
    intros fra fv spc j nn w120 HK Ho.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct HK as [(_ & Efr & _)|(Hj & Efr & _ & _ & _ & _ & Hfl0)]; subst fra.
    - destruct (HOK Ho) as (_ & _ & _ & HoS & _). destruct HoS as [L|R];
        [left; clear -L HAlo HAhi RS; lia | right; clear -R HAlo HAhi RS; lia].
    - assert (HinD : In (o, o + 36) (reac_ctrl_parse_D f n o)).
      { unfold reac_ctrl_parse_D. apply in_or_app. right. rewrite (proj2 (Z.eqb_neq o 0) Ho). left. reflexivity. }
      exact (D_apart_frame o (o + 36) j HinD ltac:(lia) Hj Hfl0).
  Qed.

  (* The exit's own writes (the frame's cookie, its 16 shadow bytes, and the flag byte): a tight footprint apart from
     the saved registers [S - 96, S) and the caller's record o, so both survive the exit and reach L_restore. *)
  Definition Wtight (fra j nn : Z) : list ivl :=
    [(fra, fra + 128); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (fs_flag FS 1 j, fs_flag FS 1 j + nn)].

  Lemma tight_out : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    (S - 96 <= x < S \/ (o <> 0 /\ o <= x < o + 36)) -> outside (Wtight fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (FSp1 & _ & _ & FSp4 & _) & _ & _ & _ & HFSb & _).
    unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & FRA & _ & SH2a & SH2b).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1; lia).
    assert (Hfl : FS + 20480 <= fs_flag FS 1 j /\ fs_flag FS 1 j + nn <= FS + 28672).
    { destruct HK as [(_ & _ & _ & Ejj & Enn)|(Hjj & _ & _ & _ & _ & Enn & _)];
        [subst j nn; unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia|].
      unfold fs_M in Hjj; cbn [Z.of_nat Pos.of_succ_nat] in Hjj; change (2 ^ (14 - 1)) with 8192 in Hjj.
      subst nn; unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia. }
    unfold Wtight. cbn [outside].
    destruct Hx as [Hs | [Ho Hr]].
    - split; [clear -Hs FRhi HAhi RS; lia|].
      split; [clear -Hs SH2b HHM' RS; lia|].
      split; [|exact I]. clear -Hs Hfl HFSb RS; lia.
    - pose proof (AO0 Ho) as (AOa & _ & _).
      pose proof (acl_app_in m o 36 (x - o) AOa ltac:(clear -Hr; lia)) as Hoapp.
      replace (o + (x - o)) with x in Hoapp by lia.
      pose proof (o_apart_frame fra fv spc j nn w120 HK Ho) as Hofr.
      split; [clear -Hr Hofr; lia|].
      split.
      + intro Hq. apply (acl_app_not_shadow x Hoapp).
        replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
        apply frame_shadow_in; [exact Efra0 | exact FRA | exact SH2a | exact SH2b | clear -Hq; lia].
      + split; [|exact I]. destruct (o_apart_flag Ho) as [L|R]; [clear -L Hr Hfl | clear -R Hr Hfl]; lia.
  Qed.

  (* The body+exit footprint lies inside the post's munch list: the window and o (reac_ctrl_parse_fp), the class-1
     hint and flag array and the side frame j with its shadow (fp_wx [1] FS X: j is not in X, FK), and the real
     frame's shadow inside the window's shadow. *)
  Lemma wb_sub_fp : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    sub_fp (Wb fra j nn)
      (reac_ctrl_parse_fp o S ++ fp_wx [1%nat] FS X ++ [(shadow_addr (S - 8800), shadow_addr S)]).
  Proof.
    intros fra fv spc j nn w120 HK x Hout.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    apply acl_out_app_inv in Hout. destruct Hout as [Hfp Hout1].
    apply acl_out_app_inv in Hout1. destruct Hout1 as [HoutF HoutS].
    unfold reac_ctrl_parse_fp in Hfp. apply acl_out_app_inv in Hfp. destruct Hfp as [Htail Hwin].
    cbn [outside] in Hwin. destruct Hwin as [Hwin _]. unfold REAC_CTRL_PARSE_K in Hwin.
    cbn [outside] in HoutS. destruct HoutS as [HSwin _].
    destruct (fp_wx_hint_flag_in FS X) as (Ihint & Iflag).
    pose proof (outside_In _ x _ HoutF Ihint) as Hhint. pose proof (outside_In _ x _ HoutF Iflag) as Hflag.
    cbn [fst snd] in Hhint, Hflag.
    unfold Wb. apply fl_out_app; [unfold Wf; cbn [outside] | exact Htail].
    split; [exact Hwin|].
    split; [exact Hhint|].
    split.
    { destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hfl0)].
      - subst nn j. cbn [Z.mul Z.add]. intros [A1 A2]. clear -A1 A2. lia.
      - subst nn. assert (EFj : fs_flag FS 1 j = fs_flag FS 1 0 + j)
          by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
        intros [A1 A2]. apply Hflag. rewrite EFj in A1, A2. clear -A1 A2 Hj. lia. }
    destruct HK as [(Ef & Efr & Esp & Ej & Enn)|(Hj & Efr & Ef & Esp & Ew & Enn & Hfl0)].
    - subst fra.
      assert (M8 : (A - 128) mod 8 = 0) by (clear -HA32; Z.div_mod_to_equations; lia).
      split.
      + clear -Hwin HAlo HAhi RS. lia.
      + split; [|exact I]. intros [A1 A2].
        pose proof (sh_add8 (A - 128) 16 M8) as E. replace (A - 128 + 8 * 16) with A in E by lia.
        apply HSwin. split.
        * pose proof (acl_sh_ge (A - 128) (S - 8800) ltac:(clear -HAlo RS; lia)). lia.
        * pose proof (acl_sh_ge S A ltac:(clear -HAhi RS; lia)). lia.
    - subst fra. pose proof (x_ne_j j Hfl0) as HXj.
      assert (E1 : fs_frame FS 1 (j + 1) = fs_frame FS 1 j + 128) by (rewrite !fs_frame1; lia).
      assert (E2 : shadow_addr (fs_frame FS 1 (j + 1)) = shadow_addr (fs_frame FS 1 j) + 16)
        by (rewrite (sh_frame1 FS (j + 1)), (sh_frame1 FS j); lia).
      split.
      + intros Hx. exact (fp_wx_frame_in FS X j x Hj HXj ltac:(lia) HoutF).
      + split; [|exact I]. intros Hx. exact (fp_wx_frame_sh_in FS X j x Hj HXj ltac:(lia) HoutF).
  Qed.

  (* The exit's tight footprint is inside the body+exit footprint (so the composed munch stays over Wb). *)
  Lemma wtight_sub_wb : forall fra j nn, sub_fp (Wtight fra j nn) (Wb fra j nn).
  Proof.
    intros fra j nn x Hout. unfold Wb in Hout. apply acl_out_app_inv in Hout. destruct Hout as [HoutWf _].
    unfold Wf in HoutWf. cbn [outside] in HoutWf.
    destruct HoutWf as (_ & _ & Hflag & Hframe & Hshadow & _).
    unfold Wtight, shadow_addr in *. cbn [outside].
    split; [exact Hframe | split; [exact Hshadow | split; [exact Hflag | exact I]]].
  Qed.

  (* 0x84224 .. 0x842dc: the frame-free exit. The 5 unused poison bytes and the frame cookie, then (real frame)
     un-poison the 16 shadow bytes to 0, or (side frame) set them to 0xf5 (released) and clear the frame's flag byte;
     the record and the saved registers survive; the post's runtime state is rebuilt and L_restore returns. *)
  Lemma L_epi : forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK HJb Hrec Hw120.
    pose proof HJb as HJbc. destruct HJbc as (_ & WM & RM & MI & SV & AREC).
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHMx. pose proof HAE as HAEx. unfold HIGHMEM_BEG, APPMEM_END in HHMx, HAEx.
    pose proof FP0 as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (FSp1q & _) & _). 
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAPP & FRA & SWsh & SH2a & SH2b).
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    assert (Efra0 : 0 <= fra) by (clear -FRlo FSp1q; lia).
    pose proof (jb_sw fra j nn mc HJb) as SRmc.
    pose proof (munch_refl (Wtight fra j nn) mc) as MUc.
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof (rd_mono_refl mc) as RMc.
    unfold Wtight, shadow_addr in MUc.
    rs_hide_sec. rs_hide Hrec. rs_hide Hw120. rs_hide Fsp. rs_hide FRA.
    pose proof HK as HK0.
    destruct HK0 as [(Efv & Efra & Espc & Ej & Enn) | (Hjb & Efra & Efvs & Espc & Ew120 & Enn & Hfl0)].
    - (* real frame: fv = 0, j = 0, nn = 0 *)
      subst j nn.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      step. step.
      wstb fra 8%nat fra FW. step. store_done.
      step. if_cases Eb; cbv iota.
      2:{ exfalso. rewrite Efv in Eb. vm_compute in Eb. discriminate. }
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (shadow_rw_mono mc mcur SRmc WMc RMc) as SRcur;
        pose proof (shadow16_stk mcur fra SRcur Efra0 FRA SH2a SH2b) as STsh end.
      pose proof (stk_carve rsegs _ (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia)) as [STsh' [junkS SHC]].
      replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
      sstep (fra / 8 + ASAN_K) 4 4%nat SWsh.
      sstep (fra / 8 + ASAN_K) 5 5%nat SWsh.
      sstep (fra / 8 + ASAN_K) 6 6%nat SWsh.
      sstep (fra / 8 + ASAN_K) 7 7%nat SWsh.
      sstep (fra / 8 + ASAN_K) 0 0%nat SWsh.
      sstep (fra / 8 + ASAN_K) 1 1%nat SWsh.
      sstep (fra / 8 + ASAN_K) 2 2%nat SWsh.
      sstep (fra / 8 + ASAN_K) 3 3%nat SWsh.
      sstep (fra / 8 + ASAN_K) 12 12%nat SWsh.
      sstep (fra / 8 + ASAN_K) 13 13%nat SWsh.
      sstep (fra / 8 + ASAN_K) 14 14%nat SWsh.
      sstep (fra / 8 + ASAN_K) 15 15%nat SWsh.
      sstep (fra / 8 + ASAN_K) 8 8%nat SWsh.
      sstep (fra / 8 + ASAN_K) 9 9%nat SWsh.
      sstep (fra / 8 + ASAN_K) 10 10%nat SWsh.
      sstep (fra / 8 + ASAN_K) 11 11%nat SWsh.
      destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
      match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mfin _) =>
        assert (HSH : forall g, 0 <= g <= 15 ->
                  exists b, mrd rsegs mfin (wa (fra / 8 + ASAN_K + g)) = Some b /\ bv_signed b = 0) end.
      { destruct HB16 as (_ & _ & Hr). intros g Hg. exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 0 \/ g = 1 \/ g = 2 \/ g = 3 \/ g = 4 \/ g = 5 \/ g = 6 \/ g = 7 \/ g = 8 \/ g = 9 \/
                     g = 10 \/ g = 11 \/ g = 12 \/ g = 13 \/ g = 14 \/ g = 15) by lia.
        destruct Hc as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 0) with (fra / 8 + ASAN_K + Z.of_nat 0) by lia; rewrite (Hr 0%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 1) with (fra / 8 + ASAN_K + Z.of_nat 1) by lia; rewrite (Hr 1%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 2) with (fra / 8 + ASAN_K + Z.of_nat 2) by lia; rewrite (Hr 2%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 3) with (fra / 8 + ASAN_K + Z.of_nat 3) by lia; rewrite (Hr 3%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia; rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia; rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia; rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia; rewrite (Hr 7%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia; rewrite (Hr 8%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 9) with (fra / 8 + ASAN_K + Z.of_nat 9) by lia; rewrite (Hr 9%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 10) with (fra / 8 + ASAN_K + Z.of_nat 10) by lia; rewrite (Hr 10%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 11) with (fra / 8 + ASAN_K + Z.of_nat 11) by lia; rewrite (Hr 11%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 12) with (fra / 8 + ASAN_K + Z.of_nat 12) by lia; rewrite (Hr 12%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 13) with (fra / 8 + ASAN_K + Z.of_nat 13) by lia; rewrite (Hr 13%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 14) with (fra / 8 + ASAN_K + Z.of_nat 14) by lia; rewrite (Hr 14%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 15) with (fra / 8 + ASAN_K + Z.of_nat 15) by lia; rewrite (Hr 15%nat ltac:(cbn [length]; lia)) ];
          reflexivity. }
      destruct HJb as (MUbody & _).
      pose proof (munch_trans _ m mc _ MUbody (munch_weaken _ _ mc _ (wtight_sub_wb fra 0 0) MUc)) as MUfin.
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (wb_sub_fp fra fv spc 0 0 w120 HK) | exact MUfin].
      + exact WM.
      + exact MI.
      + exact (stk_mono m _ _ _ ST0 WM RM).
      + intros Ho. apply (acl_rw (Wtight fra 0 0) mc _ o [CB 36 (snd (ctrlparse n fr))] (Hrec Ho) MUc WMc).
        intros y Hy. apply (tight_out fra fv spc 0 0 w120 y HK). right. split; [exact Ho|].
        cbn [cells_size csize Nat.add] in Hy. lia.
      + apply (epi_aJ fra fv spc 0 0 w120 _ HK MUfin WM RM).
        * apply (epi_win_real fra fv spc 0 0 w120 _ HK Efv MUfin HSH).
        * exact (epi_flags_real fra fv spc 0 0 w120 _ HK Efv MUfin).
    - (* side frame: fv = fra <> 0, nn = 1 *)
      subst nn.
      assert (Hfrapos : 0 < fra) by (clear -FRlo FSp1q; lia).
      assert (Hfvne : fv <> 0) by (rewrite Efvs; clear -Hfrapos; lia).
      pose proof (Hw120 Hfvne) as HW120. rewrite Ew120 in HW120. apply bytes_ro8 in HW120. unfold rs_hold in FRA.
      pose proof FP0 as (DTw & TSw & Cw & Tw & DBw & kw & _ & _ & (_ & _ & _ & _ & FSp5w) & _ & _ & _ & HFSbw & _).
      unfold FS_SIZE in HFSbw, FSp5w.
      assert (Hjb8 : 0 <= j < 8192)
        by (unfold fs_M in Hjb; cbn [Z.of_nat Pos.of_succ_nat] in Hjb; change (2 ^ (14 - 1)) with 8192 in Hjb; exact Hjb).
      assert (EFl : fs_flag FS 1 j = FS + 20480 + j)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      rewrite Efvs.
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      step. step.
      wstb fra 8%nat fra FW. step. store_done.
      step. if_cases Eb; cbv iota.
      { exfalso. rewrite (rc_neq0_64 fra) in Eb by (clear -Hfrapos FRhi HAhi RS; lia). discriminate. }
      step.
      wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
      step. (* ld a1, 120(s2): the frame's flag-byte address w120 *)
      (* sb zero, 0(a1): the flag byte, carved from the side stack as a 1-byte cell so its new value 0 is kept *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (stk_mono m mcur FS (FS + 11571200) FSp5w WM RM) as STF end.
      destruct (stk_split rsegs _ FS (fs_flag FS 1 j + 1) (FS + 11571200) STF ltac:(rewrite EFl; lia)) as [STF1 _].
      clear STF.
      destruct (stk_carve rsegs _ FS (fs_flag FS 1 j + 1) 1%nat STF1 ltac:(rewrite EFl; lia)) as [STF2 [junkF FLC]].
      clear STF1 STF2.
      replace (fs_flag FS 1 j + 1 - Z.of_nat 1) with (fs_flag FS 1 j) in FLC by lia.
      assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
      { assert (EMj : fs_M 1 = 8192) by reflexivity.
        eapply rng_sub; [exact RFLG | rewrite !fs_flag1; lia | rewrite !fs_flag1; lia]. }
      wst (fs_flag FS 1 j) 1%nat ltac:(apply (stk_wv m FS (FS + 11571200)); [exact FSp5w | rewrite EFl; clear -Hi Hjb8; lia]).
      step.
      change (Z_to_bv 64 (fs_flag FS 1 j)) with (wa (fs_flag FS 1 j)).
      replace (wa (fs_flag FS 1 j)) with (wa (fs_flag FS 1 j + Z.of_nat 0)) by (f_equal; lia).
      rewrite rc_le1_lit. mem_after_store.
      step.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mfin _) =>
        assert (Hclr : mrd rsegs mfin (wa (fs_flag FS 1 j)) = Some (Z_to_bv 8 0)) end.
      { destruct FLC as [[_ HBF] _]. cbn [cells_bytes cbytes app] in HBF.
        destruct HBF as (_ & _ & Hr). pose proof (Hr 0%nat ltac:(cbn [length]; lia)) as H0.
        cbn [Z.of_nat nth_error] in H0. rewrite Z.add_0_r in H0. exact H0. }
      destruct HJb as (MUbody & _).
      pose proof (munch_trans _ m mc _ MUbody (munch_weaken _ _ mc _ (wtight_sub_wb fra j 1) MUc)) as MUfin.
      eapply L_restore.
      + exact SV.
      + eapply munch_weaken; [exact (wb_sub_fp fra fv spc j 1 w120 HK) | exact MUfin].
      + exact WM.
      + exact MI.
      + exact (stk_mono m _ _ _ ST0 WM RM).
      + intros Ho. apply (acl_rw (Wtight fra j 1) mc _ o [CB 36 (snd (ctrlparse n fr))] (Hrec Ho) MUc WMc).
        intros y Hy. apply (tight_out fra fv spc j 1 w120 y HK). right. split; [exact Ho|].
        cbn [cells_size csize Nat.add] in Hy. lia.
      + apply (epi_aJ fra fv spc j 1 w120 _ HK MUfin WM RM).
        * apply (epi_win_side fra fv spc j 1 w120 _ HK Hfvne MUfin).
        * exact (epi_flags_side fra fv spc j 1 w120 _ HK Hfvne MUfin Hclr).
  Qed.


  (* ================= the body walk (0x83f28 .. 0x84224) ================= *)

  (* The callees of the body. *)
  Hypothesis MSET : asan_memset_contract_F.
  Hypothesis MCPY : asan_memcpy_contract_F.
  Hypothesis BWRP : bcmp_wrap_contract_F.
  Hypothesis KOL : kind_of_link1_contract_F.

  (* The record buffer the body fills, named R (as o' in the plain proof): the caller's o when given, else the
     frame's 32-byte scratch at fra + 32. *)
  Definition RF (fra R : Z) : Prop := (o = 0 /\ R = fra + 32) \/ (o <> 0 /\ R = o).

  Lemma rf_rec : forall fra R, RF fra R -> REC fra = R.
  Proof.
    intros fra R [(Ho & ER)|(Ho & ER)]; unfold REC.
    - rewrite (proj2 (Z.eqb_eq o 0) Ho). lia.
    - rewrite (proj2 (Z.eqb_neq o 0) Ho). lia.
  Qed.

  (* What the body itself writes: the record and the window (the callees' frames). *)
  Definition Wr (R : Z) : list ivl := [(R, R + 36); (S - 8800, S)].

  (* The memory state carried from 0x83f28 (mc0) to the current memory mc. *)
  Definition BJ (R : Z) (mc0 mc : word -> option byte) : Prop :=
    munch (Wr R) mc0 mc /\ wmono rsegs mc0 mc /\ rd_mono mc0 mc /\ mem_inv rsegs mc /\
    stk rsegs mc (S - 8800) S /\ rw_cells rsegs mc (S - 96) SAVES.

  Lemma bj_refl : forall R mc0, mem_inv rsegs mc0 -> stk rsegs mc0 (S - 8800) S ->
    rw_cells rsegs mc0 (S - 96) SAVES -> BJ R mc0 mc0.
  Proof.
    intros R mc0 MI ST SV. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [apply rd_mono_refl|]. split; [exact MI|]. split; [exact ST | exact SV].
  Qed.

  (* A side-stack frame is below the window. *)
  Lemma side_frame_lo : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> fv <> 0 ->
    fra + 128 <= S - 8800.
  Proof.
    intros fra fv spc j nn w120 HK Hfv.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & _ & _ & _ & _ & HFSb & _ & _ & _).
    unfold FS_SIZE in HFSb.
    destruct HK as [(Ef & _ & _ & _ & _)|(Hj & Efr & _)]; [subst fv; contradiction|].
    subst fra. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576.
    unfold fs_M in Hj. cbn [Z.of_nat Pos.of_succ_nat] in Hj. change (2 ^ (14 - 1)) with 8192 in Hj.
    clear -Hj HFSb. lia.
  Qed.

  (* The record's place: alignment, bounds, application memory, and apartness from the runtime's cells, the saved
     registers, the callees' frames, the input buffer and the frame's flag-pointer word. *)
  Lemma rf_facts : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R ->
    0 < R /\ R mod 4 = 0 /\ R + 36 <= 2^64 /\ (forall i, 0 <= i <= 36 -> app_mem (R + i)) /\
    (R + 36 <= RT_LO \/ RT_HI <= R) /\ (R + 36 <= S - 96 \/ S <= R) /\
    (forall KK, 0 <= KK <= 4560 -> R + 36 <= spc - KK \/ spc <= R) /\
    (50 <= n -> R + 36 <= f \/ f + 50 <= R) /\
    (fv <> 0 -> R + 36 <= fra + 120 \/ fra + 128 <= R).
  Proof.
    intros fra fv spc j nn w120 R HK HR.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (Pfs0 & Pfs1 & Pfs2 & _ & _) & _ & _ & _ & HFSb
                       & _ & _ & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hsp : spc = A /\ fra + 128 <= S - 8800 \/ spc = fra /\ fra = A - 128).
    { pose proof HK as HK2. destruct HK2 as [(Ef & Efr & Esp & _)|(Hj & Efr & Ef & Esp & _)].
      - right. split; [lia | exact Efr].
      - left. split; [exact Esp|]. apply (side_frame_lo fra fv spc j nn w120 HK).
        rewrite Ef, Efr. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. clear -Pfs0 Hj. lia. }
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - (* the frame's scratch *)
      split; [clear -FRlo Pfs0 Pfs2; lia|].
      split; [clear -FR8; Z.div_mod_to_equations; lia|].
      split; [clear -FRhi HAhi RS HAE'; lia|].
      split; [intros i Hi; replace (fra + 32 + i) with (fra + (32 + i)) by lia; apply FAP; lia|].
      split; [right; unfold RT_HI; clear -FRlo Pfs0 Pfs2; lia|].
      split; [left; clear -FRhi HAhi RS; lia|].
      split; [intros KK HKK; clear -Hsp FRhi HAlo HAhi RS HKK;
               destruct Hsp as [[E1 E2]|[E1 E2]]; lia|].
      split.
      + intros HN. destruct (f_apart_frame fra fv spc j nn w120 HK HN) as [L|Rr];
          [right; clear -L; lia | left; clear -Rr; lia].
      + intros _. left. lia.
    - (* the caller's record *)
      destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
      destruct (AO0 Ho) as (AOa & AOe & AOc). unfold GOT_CF, CF in AOc.
      split; [clear -Ho Ro; lia|]. split; [exact Ho4|]. split; [exact Ho36|].
      split.
      { intros i Hi. destruct (Z.eq_dec i 36) as [E36|E36]; [subst i; exact AOe|].
        exact (acl_app_in m o 36 i AOa ltac:(lia)). }
      split; [unfold RT_LO, RT_HI; clear -AOc; lia|].
      split; [clear -HoS RS; lia|].
      split; [intros KK HKK; destruct Hsp as [[E1 E2]|[E1 E2]];
               clear -HoS E1 E2 HAlo HAhi RS HKK; lia|].
      split; [intros HN; destruct (Hof HN) as [L|Rr]; [left; exact L | right; exact Rr]|].
      intros _. destruct (o_apart_frame fra fv spc j nn w120 HK Ho) as [Hx|Hx];
        [left; clear -Hx; lia | right; clear -Hx; lia].
  Qed.

  (* Every byte the body writes is application memory, so no shadow byte is inside its footprint. *)

  (* ---- The footprint of the record R: the caller's buffer at o, or the frame's 32-byte scratch at fra + 32. ---- *)
  Lemma rngF_rec : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> rng RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply rng_sub; [exact (rngF_frame fra fv spc j nn w120 HK) | lia | lia].
    - exact (ROUT Ho).
  Qed.

  Lemma rngF_rec_cov : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> shcov RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply shcov_sub; [exact (rngF_frame_cov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SCO Ho).
  Qed.

  Lemma rngF_rec_kov : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> shkov RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply shkov_sub; [exact (rngF_frame_kov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SKO Ho).
  Qed.
  Lemma wr_app : forall fra fv spc j nn w120 R x, FK fra fv spc j nn w120 -> RF fra R ->
    ~ outside (Wr R) x -> app_mem x.
  Proof.
    intros fra fv spc j nn w120 R x HK HR Hin.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (_ & _ & _ & HRap & _).
    assert (D : (R <= x < R + 36) \/ (S - 8800 <= x < S)).
    { destruct (Z_le_dec R x) as [A1|A1]; destruct (Z_lt_dec x (R + 36)) as [A2|A2];
        destruct (Z_le_dec (S - 8800) x) as [A3|A3]; destruct (Z_lt_dec x S) as [A4|A4];
        first [ left; lia | right; lia
              | exfalso; apply Hin; unfold Wr; cbn [outside]; split; [lia | split; [lia | exact I]] ]. }
    destruct D as [D|D].
    - replace x with (R + (x - R)) by lia. apply HRap. lia.
    - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. right. lia.
  Qed.

  (* The body writes no shadow byte, so every addressable range stays addressable. *)
  Lemma bj_addr : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) p q,
    FK fra fv spc j nn w120 -> RF fra R -> addressable mc0 p q -> munch (Wr R) mc0 mc ->
    addressable mc p q.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc p q HK HR AD MU.
    apply (acl_addr_munch (Wr R) mc0 mc p q AD MU). intros i Hi.
    destruct (rc_outside_dec (Wr R) (shadow_addr (p + i))) as [Hou|Hou]; [exact Hou|].
    exfalso. apply (acl_app_not_shadow (shadow_addr (p + i))).
    - exact (wr_app fra fv spc j nn w120 R _ HK HR Hou).
    - apply rt_app_shadow. exact (acl_app_in mc0 p q i AD Hi).
  Qed.

  Lemma Wr_sub : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R ->
    sub_fp (Wr R) (Wb fra j nn).
  Proof.
    intros fra fv spc j nn w120 R HK HR x Hout.
    unfold Wb in Hout. apply acl_out_app_inv in Hout. destruct Hout as [HoutF HoutO].
    unfold Wf in HoutF. cbn [outside] in HoutF. destruct HoutF as (HW & _ & _ & HFr & _).
    unfold Wr. cbn [outside]. split; [|split; [exact HW | exact I]].
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - clear -HFr. lia.
    - rewrite (proj2 (Z.eqb_neq o 0) Ho) in HoutO. cbn [outside] in HoutO. exact (proj1 HoutO).
  Qed.

  (* The body's invariant, read back as the exit lemma's aJb. *)
  Lemma bj_aJb : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    BJ R mc0 mc -> aJb fra j nn mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR (MU0 & WM0 & RM0 & _ & _) AD0 (MU & WM & RM & MI & ST & SV).
    unfold aJb. rewrite (rf_rec fra R HR).
    split.
    { apply (munch_trans _ m mc0 mc).
      - eapply munch_weaken; [|exact MU0]. unfold Wb. intros x Hx.
        exact (proj1 (acl_out_app_inv _ _ _ Hx)).
      - eapply munch_weaken; [|exact MU]. exact (Wr_sub fra fv spc j nn w120 R HK HR). }
    split; [exact (wmono_trans rsegs _ _ _ WM0 WM)|].
    split; [exact (rd_mono_trans _ _ _ RM0 RM)|].
    split; [exact MI|]. split; [exact SV|].
    exact (bj_addr fra fv spc j nn w120 R mc0 mc R 36 HK HR AD0 MU).
  Qed.

  (* The side frame's flag-pointer word survives the body. *)
  Lemma w120_bj : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> munch (Wr R) mc0 mc ->
    fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR H0 MU Hfv.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfr).
    pose proof (side_frame_lo fra fv spc j nn w120 HK Hfv) as Hlo.
    eapply (bytes_at_transport rsegs (Wr R) mc0 mc _ _ (H0 Hfv) MU).
    unfold Wr. cbn [disjoint_from]. rewrite length_le8.
    destruct (Hfr Hfv) as [Hx|Hx]; repeat split; try exact I; clear -Hx Hlo; lia.
  Qed.

  (* The input buffer is apart from every range the body's footprint names. *)
  Lemma f_dj_Wb : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> 50 <= n ->
    forall a len, f <= a -> 0 <= len -> a + len <= f + 50 -> disjoint_from (Wb fra j nn) a len.
  Proof.
    intros fra fv spc j nn w120 HK HN a len Ha Hlen Hae.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    assert (HinD : In (f, f + 50) (reac_ctrl_parse_D f n o)).
    { unfold reac_ctrl_parse_D. replace (n <? 50) with false by (symmetry; apply Z.ltb_ge; lia).
      apply in_or_app. left. left. reflexivity. }
    destruct (D_apart_hint_flag f (f + 50) HinD) as (Hhint & Hflag).
    unfold RcLay.ly_dj in Hhint, Hflag.
    assert (Hjb : 0 <= j /\ j + 1 <= fs_M 1).
    { destruct HK as [(_ & _ & _ & Ej & _)|(Hj & _)]; [subst j; unfold fs_M; cbn; lia | lia]. }
    assert (Hnn : nn = 0 \/ nn = 1) by (destruct HK as [(_ & _ & _ & _ & En)|(_ & _ & _ & _ & _ & En)]; lia).
    assert (EFL : fs_flag FS 1 j = fs_flag FS 1 0 + j)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    pose proof (f_apart_frame fra fv spc j nn w120 HK HN) as Hfr.
    assert (Hap : f + 50 <= 2147450880 \/ 17594333495296 <= f).
    { apply (app_range f 50 ltac:(lia)). intros i Hi. exact (acl_app_in m f 50 i (AF0 HN) Hi). }
    unfold Wb, Wf, shadow_addr. cbn [app disjoint_from].
    repeat split; try exact I.
    - clear -HfW Ha Hae Hlen; lia.
    - clear -Hhint Ha Hae Hlen; lia.
    - rewrite EFL. clear -Hflag Ha Hae Hlen Hjb Hnn EFL; lia.
    - clear -Hfr Ha Hae Hlen; lia.
    - clear -Hap SH1 SH2 Ha Hae Hlen; lia.
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [disjoint_from]; [exact I|].
      destruct (HOK Eo) as (_ & _ & _ & _ & Hof). destruct (Hof HN) as [Hx|Hx];
        split; try exact I; clear -Hx Ha Hae Hlen; lia.
  Qed.

  (* The munch the input-byte reads (rc_ro_now) need: from the entry memory m through the body. *)
  Lemma bj_mub : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> munch (Wr R) mc0 mc ->
    munch (Wb fra j nn) m mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR (MU0 & _) MU.
    apply (munch_trans _ m mc0 mc).
    - eapply munch_weaken; [|exact MU0]. unfold Wb. intros x Hx. exact (proj1 (acl_out_app_inv _ _ _ Hx)).
    - eapply munch_weaken; [|exact MU]. exact (Wr_sub fra fv spc j nn w120 R HK HR).
  Qed.

  (* The runtime's compare cells, between GOT_CF and CF + 256, are apart from the body's footprint. *)
  Lemma low_out_Wb : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    GOT_CF <= x < CF + 256 -> outside (Wb fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx. unfold GOT_CF, CF in Hx.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (Pfs0 & Pfs1 & Pfs2 & _ & _) & _ & _ & _ & HFSb
                       & _ & _ & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    assert (EFL : fs_flag FS 1 j <= FS + 28672 /\ FS <= fs_flag FS 1 j).
    { assert (Hjb : 0 <= j /\ j <= fs_M 1).
      { destruct HK as [(_ & _ & _ & Ej & _)|(Hj & _)]; [subst j; unfold fs_M; cbn; lia | lia]. }
      unfold fs_flag, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
      change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 1)) with 16384 in *.
      change (2 ^ (14 - 1)) with 8192 in Hjb. lia. }
    assert (Hnn : nn = 0 \/ nn = 1)
      by (destruct HK as [(_ & _ & _ & _ & En)|(_ & _ & _ & _ & _ & En)]; lia).
    unfold Wb, Wf. apply fl_out_app; cbn [outside].
    - split; [clear -Hx HHM'; lia|].
      split; [unfold fs_hint; cbn [Z.of_nat]; clear -Hx Pfs0 Pfs2; lia|].
      split; [clear -Hx EFL Hnn Pfs0 Pfs2; lia|].
      split; [clear -Hx FRlo Pfs0 Pfs2; lia|].
      split; [clear -Hx SH1; unfold shadow_addr; lia | exact I].
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO0 Eo) as (_ & _ & AOc). unfold GOT_CF, CF in AOc.
      split; [clear -Hx AOc; lia | exact I].
  Qed.

  (* A byte of the caller's record is apart from everything the frame block writes. *)
  Lemma o_out_Wf : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 -> o <> 0 ->
    o <= x < o + 36 -> outside (Wf fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Ho Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (Pfs0 & Pfs1 & Pfs2 & _ & _) & _ & _ & _ & HFSb
                       & _ & _ & _).
    unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
    destruct (AO0 Ho) as (AOa & AOe & AOc).
    pose proof (o_apart_FS Ho) as HoFS.
    assert (Hap : app_mem x)
      by (replace x with (o + (x - o)) by lia; exact (acl_app_in m o 36 (x - o) AOa ltac:(lia))).
    assert (EFL : FS <= fs_flag FS 1 j /\ fs_flag FS 1 j + nn <= FS + 28672).
    { assert (Hjb : 0 <= j /\ j + nn <= fs_M 1).
      { destruct HK as [(_ & _ & _ & Ej & En)|(Hj & _ & _ & _ & _ & En)];
          [clear -Ej En; subst j nn; unfold fs_M; cbn; lia | clear -Hj En; lia]. }
      unfold fs_flag, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
      change (2 ^ 15) with 32768 in *. change (2 ^ (15 - 1)) with 16384 in *.
      change (2 ^ (14 - 1)) with 8192 in Hjb. lia. }
    unfold Wf. cbn [outside].
    split; [clear -HoS Hx; lia|].
    split; [unfold fs_hint; cbn [Z.of_nat]; clear -HoFS Hx; lia|].
    split; [clear -HoFS Hx EFL; lia|].
    split; [pose proof (o_apart_frame fra fv spc j nn w120 HK Ho) as Hofr; clear -Hofr Hx; lia|].
    split; [|exact I].
    pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
    rewrite <- Esh.
    apply (acl_sh_out x fra (fra + 128) Hap);
      [clear -FRlo Pfs0 Pfs2; lia | unfold APPMEM_END; clear -FRhi HAhi RS HAE'; lia].
  Qed.

  (* The record buffer is writable and readable at the body's entry memory. *)
  Lemma rec_rw : forall fra fv spc j nn w120 R (mc0 : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 ->
    exists junk', rw_cells rsegs mc0 R [CB 36 junk'].
  Proof.
    intros fra fv spc j nn w120 R mc0 HK HR HB.
    pose proof HB as (MU & WM & RM & MI & SV).
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & HP & _ & _ & _ & HFSb & _ & _ & _).
    pose proof HP as (Pfs0 & Pfs1 & Pfs2 & Pfsapp & STfs). unfold ASAN_GT in Pfs2. unfold FS_SIZE in HFSb, STfs.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - assert (STf : stk rsegs m fra (fra + 128)).
      { pose proof HK as HK2. destruct HK2 as [(Ef & Efr & _)|(Hjj & Efr & _)].
        - subst fra. destruct (stk_split rsegs m (S - 8800) (A - 128) S ST0 ltac:(lia)) as [_ STx].
          destruct (stk_split rsegs m (A - 128) (A - 128 + 128) S STx ltac:(lia)) as [STy _]. exact STy.
        - assert (EFRj : fs_frame FS 1 j = FS + 1085440 + j * 128)
            by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576; lia).
          assert (Hjb : 0 <= j < 8192)
            by (unfold fs_M in Hjj; cbn [Z.of_nat Pos.of_succ_nat] in Hjj;
                change (2 ^ (14 - 1)) with 8192 in Hjj; exact Hjj).
          subst fra. rewrite EFRj in *.
          destruct (stk_split rsegs m FS (FS + 1085440 + j * 128) (FS + 11571200) STfs ltac:(lia)) as [_ STx].
          destruct (stk_split rsegs m (FS + 1085440 + j * 128) (FS + 1085440 + j * 128 + 128)
                      (FS + 11571200) STx ltac:(lia)) as [STy _]. exact STy. }
      pose proof (stk_mono m mc0 fra (fra + 128) STf WM RM) as STf0.
      destruct (stk_split rsegs mc0 fra (fra + 68) (fra + 128) STf0 ltac:(lia)) as [STa _].
      destruct (stk_carve rsegs mc0 fra (fra + 68) 36 STa ltac:(lia)) as [_ [junk' HRW]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in HRW by lia.
      exists junk'. exact HRW.
    - destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
      exists junk. apply (acl_rw (Wf fra j nn) m mc0 o [CB 36 junk] Horw MU WM).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      exact (o_out_Wf fra fv spc j nn w120 x HK Ho Hx).
  Qed.

  (* The cells the bcmp wrapper reads, at a body memory. *)
  Lemma jb_cl : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> munch (Wr R) mc0 mc -> aCL mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR HB MU.
    pose proof (bj_mub fra fv spc j nn w120 R mc0 mc HK HR HB MU) as MUb.
    pose proof (fun x Hx => low_out_Wb fra fv spc j nn w120 x HK Hx) as LO.
    unfold aCL.
    split; [eapply fl_bytes; [exact HBCMP | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold REAL_BCMP, GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HMEMCMP | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold REAL_MEMCMP, GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HGCF | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HCF254 | exact MUb |]|].
    { intros x Hx. cbn [length] in Hx. apply LO. unfold GOT_CF, CF in *. lia. }
    eapply fl_bytes; [exact HCF255 | exact MUb |].
    intros x Hx. cbn [length] in Hx. apply LO. unfold GOT_CF, CF in *. lia.
  Qed.

  (* The shadow fact of a 1-byte access at p + jj. *)
  Lemma sh1 : forall (mq : word -> option byte) p q jj Y, addressable mq p q -> 0 <= jj -> jj + 1 <= q ->
    Y = p + jj ->
    exists kk : byte, ov_read_bytes rsegs mq (wa (Y / 8 + ASAN_K)) 1 = Some [kk]
      /\ (bv_signed kk = 0 \/ Y mod 8 + (1 - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128.
  Proof.
    intros mq p q jj Y AD H1 H2 HY.
    apply (acl_shadow mq p q jj 1 Y AD H1 ltac:(lia) ltac:(lia)); [|exact HY].
    pose proof (Z.mod_pos_bound Y 8 ltac:(lia)). lia.
  Qed.

  (* The shadow fact of a w-byte access at p + jj, p 4-aligned. *)
  Lemma shw : forall (mq : word -> option byte) p q jj w Y, addressable mq p q -> p mod 4 = 0 -> 0 <= jj ->
    jj mod 4 + w <= 4 -> 1 <= w -> jj + w <= q -> Y = p + jj ->
    exists kk : byte, ov_read_bytes rsegs mq (wa (Y / 8 + ASAN_K)) 1 = Some [kk]
      /\ (bv_signed kk = 0 \/ Y mod 8 + (w - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128.
  Proof.
    intros mq p q jj w Y AD Hp Hj Hjw Hw Hq HY.
    apply (acl_shadow mq p q jj w Y AD Hj Hw Hq); [|exact HY].
    rewrite HY. exact (acl_mod_al p jj w Hp Hj Hjw).
  Qed.

  (* The record's bytes 4..27, as in the plain proof. *)
  Definition P1 : list byte :=
    [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
     cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
     (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
     cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z].

  (* ----- the body's branch and record tactics (as in lib/U/Prog/reac_ctrl_parse.v) ----- *)

  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by zlitr;
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* A pointer-overflow guard of the ubsan build that cannot fire. *)
  Ltac ub_false :=
    rc_wrap_lits;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; unfold bv_eqb, bv_ltu; rewrite ?unsigned_lit by lia; cbn [negb];
          first [ reflexivity | apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply negb_false_iff, Z.ltb_lt; lia ] ]
    end.

  Ltac kfact :=
    match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.

  Ltac bfact :=
    match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, P1; zeval; zeval; reflexivity.

  Ltac kbound :=
    first [ zlitr
          | match goal with
            | KR : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear - KR; lia
            | KR : rs_hold (2 <= KL1 ?x <= 13 /\ _) |- _ => unfold rs_hold in KR; clear - KR; lia
            end ].

  (* The len input bytes at f + lo, readable at the current memory (MUq : munch (Wb ..) m _, DJ : f_dj_Wb ..). *)
  Ltac rdbb lo len MUq DJ tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jj, (jj < len)%nat -> In (lo + jj)%nat (cp_rd n fr)) by tac;
    let RR := fresh "RO" in
    pose proof (rc_ro_now rsegs _ m _ f fr lo len (cp_rd n fr) Hrd HIN ltac:(lia) ltac:(lia) ltac:(lia)
                  MUq ltac:(apply DJ; lia)) as RR;
    cbn [map seq] in RR;
    let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in RR;
    rewrite ?Z.add_0_r in RR;
    clear HIN.

  (* The exit lemma (0x84224 -> Qp), proved in the other lane; the body's lemmas take it as their continuation. *)
  Definition EPI : Prop :=
    forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).

  (* 0x84224 with the record complete: hand it to the exit lemma. *)
  Lemma b_done : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HRec.
    apply HEPI with (fra := fra) (fv := fv) (j := j) (nn := nn) (w120 := w120).
    - exact HK.
    - exact (bj_aJb fra fv spc j nn w120 R mc0 mc HK HR HB AD0 HJ).
    - intros Ho. destruct HR as [(Ho0 & _)|(_ & ER)]; [contradiction|]. rewrite <- ER. exact HRec.
    - exact (w120_bj fra fv spc j nn w120 R mc0 mc HK HR H120 (proj1 HJ)).
  Qed.

  (* 0x843d0: store the kind word and leave through 0x84224. *)
  Lemma b_kind : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ repeat cp_z 6 ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 k)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x843d0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HKc HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    step. step.
    match goal with H : rw_cells rsegs ?mm R [C4 _] |- _ => rename H into HK' end.
    pose proof (rc_rw_join rsegs _ R (R + 4) _ _ HK' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ R (R + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HT) as J2.
    pose proof (rc_rw_join rsegs _ R (R + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HG) as J3.
    apply (rc_rw_flat rsegs _ R _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (b_done fra fv spc j nn w120 R mc0 _); try eassumption.
      refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x845e8: the kind word is in the record; read it back (checked) and leave through 0x84224. *)
  Lemma b_fin4 : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg amp
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x845e8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg amp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HK' HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    assert (RX : 0 <= R < 2^64) by lia.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    assert (RD4 : ov_read_bytes rsegs mc (wa (R + 0)) 4 = Some (le4 (Z_to_bv 64 k))).
    { apply (cl_rd rsegs mc R (le4 (Z_to_bv 64 k)) _ 0 4);
        [ exact (proj2 (proj1 (cl_rw_c4 rsegs mc R (Z_to_bv 64 k) HK')))
        | rewrite length_le4; lia | reflexivity ]. }
    assert (SH : exists kk : byte, ov_read_bytes rsegs mc (wa (R / 8 + ASAN_K)) 1 = Some [kk]
                   /\ (bv_signed kk = 0 \/ R mod 8 + (4 - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128).
    { apply (acl_shadow mc R 36 0 4 R); [ | lia | lia | lia | exact (acl_mod_al0 R R4) | lia ].
      exact (bj_addr fra fv spc j nn w120 R mc0 mc R 36 HK HR AD0 MU). }
    chk_core R RX (Z_to_bv 5 11) SH pre_sr add3.
    step. rewrite (cl_sx32 k) by lia.
    step.
    apply cl_rw_c4 in HK'.
    pose proof (rc_rw_join rsegs _ R (R + 4) _ _ HK' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ R (R + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HT) as J2.
    pose proof (rc_rw_join rsegs _ R (R + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HG) as J3.
    apply (rc_rw_flat rsegs _ R _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (b_done fra fv spc j nn w120 R mc0 _); try eassumption.
      refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x845e4: store the kind word, then 0x845e8. *)
  Lemma b_kind2 : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ repeat cp_z 6 ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 k)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x845e4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HKc HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    step.
    match goal with H : rw_cells rsegs ?mm R [C4 _] |- _ => rename H into HK' end.
    eapply (b_fin4 fra fv spc j nn w120 R mc0 _ k tg (repeat cp_z 6)); try eassumption.
    refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
  Qed.

  (* The o-join `addi r, s10, 0; beqz s4, L; addi r, s4, 0`, stepped to its beqz (or `beqz s4, L; addi s10, s4, 0`
     with r = s10): at L the register r holds R whichever way the branch goes (HO: R = fra + 32 when o = 0, else o);
     only r is generalized, so s10 keeps fra + 32. *)
  Ltac ojoin HO R r :=
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        let G := fresh "G" in let Hz := fresh "Hz" in let Hq := fresh "Hq" in
        enough (G : forall w, w = Z_to_bv 64 R -> evtF sg rgq Qq (MS (bvmap_set r w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.

  (* The kind tree walks to one of these: the three 4-byte-store checks, the link-1 call, the record branch. *)
  Ltac drive2 :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84328) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84350) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843bc) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843d8) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x845a0) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* 0x84318 .. 0x84600: the kind tree, the record's tail fields (the link-1 and the head-amp records). *)
  Lemma b_tree : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    addressable mc0 f 50 -> (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = true -> ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0))%bool = false ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 (repeat cp_z 2)] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 (f + 18)) (zxb (cp_b fr 22)) (zxb (cp_b fr 17)) (zxb (cp_b fr 18)) (zxb (cp_b fr 19))
               (zxb (cp_b fr 16)) x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 (R + 16)) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84318) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x16 x17 x28 x29 x30 x31
      HEPI HK HR HB AD0 ADf0 H120 HJ HE T0 HKc HP HT HG.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct (proj1 (cp_hdr_spec n fr) HE) as (HN & E12 & E13).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    pose proof (RFF HN) as RFf.
    pose proof (RINF HN) as RGINF. pose proof (SCF HN) as SCINF. pose proof (SKF HN) as SKINF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof HR as HO. unfold RF in HO.
    pose proof (cp_v_range fr 16). pose proof (cp_v_range fr 17). pose proof (cp_v_range fr 18).
    pose proof (cp_v_range fr 19). pose proof (cp_v_range fr 22).
    pose proof (cp_v_range fr 32). pose proof (cp_v_range fr 33). pose proof (cp_v_range fr 34).
    pose proof (cp_v_range fr 35).
    pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR ADf0 MUq) as ADF.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_mub fra fv spc j nn w120 R mc0 mq HK HR HB MUq) as MUB.
    pose proof (f_dj_Wb fra fv spc j nn w120 HK HN) as DJF.
    pose proof (shw mc R 36 0 4 R (ADR mc MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SHR.
    clear RFF RW120.
    rs_hide_sec. rs_hide KR. rs_hide HO. rs_hide H120.
    drive2.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84328) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 4 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84350) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 8 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843bc) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 13 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843d8) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 12 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x845a0) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 13 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) => idtac
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => idtac
         end.
    (* the two blocks the tree leaves open *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) =>
             (* 0x84390: kind_of_link1 (byte 22), then the checked store at 0x845e4 *)
             step; step;
             eapply evtF_cut; [eapply KOL | intros ? [? ->]];
             rewrite rc_signed_zxb;
             change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22);
             replace (ret_pc (Z_to_bv 64 0x84398)) with (Z_to_bv 64 0x84398)
               by (symmetry; apply ret_pc_even; [lia | reflexivity]);
             destruct SHR as (kk & RK & OK & KR0);
             pre_sr R RXr; steps_until_if; clear RK;
             unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR0; lia);
             destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
             [ eapply (b_kind2 fra fv spc j nn w120 R mc0 _ (KL1 (cp_v fr 22)) (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
             | step; rewrite ?(unsigned_lit R) by (clear -RXr; lia); rewrite rc_land7;
               step;
               (let MB := fresh "MB" in pose proof (Z.mod_pos_bound R 8 eq_refl) as MB;
                rewrite ?(unsigned_lit (R mod 8)) by (clear -MB; lia); clear MB);
               step;
               (let MB := fresh "MB" in pose proof (Z.mod_pos_bound R 8 eq_refl) as MB;
                rewrite (rc_lts_signed (R mod 8 + 3) (bv_signed kk)) by (clear -MB KR0; lia);
                replace (R mod 8 + 3 <? bv_signed kk) with true
                  by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                      [exfalso; exact (K0 OK) | clear -OK; lia]);
                clear MB);
               cbv iota;
               eapply (b_kind2 fra fv spc j nn w120 R mc0 _ (KL1 (cp_v fr 22)) (repeat cp_z 2));
                 [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
                 | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
                 | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ] ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => idtac
         end.
    (* 0x843f0: byte 18 = 4; byte 19 decides kind 11 / the record *)
    step. step. br.
    2:{ chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 11 (repeat cp_z 2));
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdbb 34%nat 2%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdbb 32%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (32 + jj)%nat with 32%nat by lia; apply cp_rd_rec;
            [exact HE | exact HRC | lia]).
    step. step. ub_false. step. step. ub_false. step.
    pose proof (sh1 _ f 50 34 (f + 34) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH34.
    chk_core (f + 34) RXf (Z_to_bv 5 13) SH34 pre_sr no_extra.
    step.
    pose proof (sh1 _ f 50 35 (f + 35) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH35.
    chk_core (f + 35) RXf (Z_to_bv 5 12) SH35 pre_sr no_extra.
    step. step. ojoin HO R (Z_to_bv 5 12).
    step.
    pose proof (shw _ R 36 28 2 (R + 28) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH28.
    chk_core (R + 28) RXr (Z_to_bv 5 15) SH28 pre_sr add1.
    step. step. step. step. step. ub_false.
    match goal with H : rw_cells rsegs _ (R + 28) [C2 _] |- _ => rename H into HT' end.
    apply (rc_rw_flat rsegs _ (R + 28) _ [cp_b fr 35; cp_b fr 34]) in HT';
      [|cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity].
    cbn [length] in HT'.
    step.
    pose proof (sh1 _ f 50 32 (f + 32) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH32.
    chk_core (f + 32) RXf (Z_to_bv 5 14) SH32 pre_sr no_extra.
    step. step. step. br.
    2:{ pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as SHRa;
        chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    step. step. ub_false. step.
    rdbb 33%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (33 + jj)%nat with 33%nat by lia; apply cp_rd_33;
            [exact HE | exact HRC | lia]).
    pose proof (sh1 _ f 50 33 (f + 33) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH33.
    chk_core (f + 33) RXf (Z_to_bv 5 14) SH33 pre_sr no_extra.
    step. step. step. br.
    2:{ pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as SHRa;
        chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    step. step.
    rewrite rc_pack_eqb by zlitr.
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34). change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    zdec (cp_v fr 34 * 256 + cp_v fr 35) 257.
    2:{ destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34n|E34n];
          [assert (E35n : cp_v fr 35 <> 1) by lia|].
        - pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as SHRa.
          chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3. step.
          eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
            [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
            | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
            | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ].
        - pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as SHRa.
          chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3. step.
          eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
            [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
            | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
            | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    assert (E34 : cp_v fr 34 = 1) by lia. assert (E35 : cp_v fr 35 = 1) by lia.
    assert (K6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdbb 36%nat 3%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; apply cp_rd_amp; [exact HE | exact HRC | exact K6 | lia]).
    pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SHR6.
    chk_core R RXr (Z_to_bv 5 12) SHR6 pre_sr add3.
    step. step. step. step. ub_false. step.
    step. step. ojoin HO R (Z_to_bv 5 12).
    pose proof (sh1 _ f 50 36 (f + 36) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH36.
    chk_core (f + 36) RXf (Z_to_bv 5 14) SH36 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 30 (R + 30) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH30.
    chk_core (R + 30) RXr (Z_to_bv 5 14) SH30 pre_sr no_extra.
    step. step. rewrite rc_le1_zxb. mem_after_store. step. ub_false. step.
    step. step. ojoin HO R (Z_to_bv 5 12).
    pose proof (sh1 _ f 50 37 (f + 37) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH37.
    chk_core (f + 37) RXf (Z_to_bv 5 14) SH37 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 31 (R + 31) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH31.
    chk_core (R + 31) RXr (Z_to_bv 5 14) SH31 pre_sr no_extra.
    step. step. rewrite rc_le1_zxb. mem_after_store. step. ub_false. step.
    step. ojoin HO R (Z_to_bv 5 26).
    pose proof (sh1 _ f 50 38 (f + 38) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH38.
    chk_core (f + 38) RXf (Z_to_bv 5 12) SH38 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 32 (R + 32) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH32r.
    chk_core (R + 32) RXr (Z_to_bv 5 13) SH32r pre_sr no_extra.
    step. rewrite rc_le1_zxb. mem_after_store. step.
    match goal with H : rw_cells rsegs _ R [C4 _] |- _ => rename H into HK6 end.
    match goal with H : rw_cells rsegs _ (R + 30) _ |- _ => rename H into HG6 end.
    eapply (rc_rw_flat rsegs _ (R + 30)) in HG6; [|reflexivity].
    cbn [cells_bytes cbytes app length] in HG6.
    eapply (b_fin4 fra fv spc j nn w120 R mc0 _ 6 [cp_b fr 35; cp_b fr 34] _);
      [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
      | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
      | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ].
  Qed.

  (* 0x84010 .. 0x84200: the broadcast word and the per-field stores, then the kind-1 leaf or the kind tree. *)
  Lemma b_fields : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) v
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    addressable mc0 f 50 -> (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = true -> -256 < v < 256 -> (v =? 0) = cp_bcast fr ->
    ro_cells rsegs mc f (map C1 (map (cp_b fr) (seq 0 23))) ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] ->
    rw_cells rsegs mc (R + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11]] ->
    rw_cells rsegs mc (R + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5]] ->
    rw_cells rsegs mc (R + 16) [CB 12 (repeat cp_z 12)] ->
    rw_cells rsegs mc (R + 28) [CB 2 (repeat cp_z 2)] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) (Z_to_bv 64 o)
               (Z_to_bv 64 f) (Z_to_bv 64 (R + 16)) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra)
               (wa ASAN_K) (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84010) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc v x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HEPI HK HR HB AD0 ADf0 H120 HJ HE Hvr Hvb RO HKc HSRC HDST HMID HT HG.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct (proj1 (cp_hdr_spec n fr) HE) as (HN & E12 & E13).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    pose proof (RFF HN) as RFf.
    pose proof (RINF HN) as RGINF. pose proof (SCF HN) as SCINF. pose proof (SKF HN) as SKINF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof HR as HO. unfold RF in HO.
    pose proof (cp_v_range fr 16). pose proof (cp_v_range fr 17).
    cbn [map seq] in RO.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR ADf0 MUq) as ADF.
    rs_hide_sec. rs_hide H120. rs_hide RFF. rs_hide RW120. rs_hide HO.
    (* 0x84010 .. 0x84024: the broadcast word at R + 16, the overflow guards of f + 14 and f + 15 *)
    do 4 step. ub_false. do 2 step. ub_false.
    (* 0x84028: the check of byte 14 *)
    step.
    pose proof (sh1 _ f 50 14 (f + 14) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH14.
    chk_core (f + 14) RXf (Z_to_bv 5 12) SH14 pre_sr no_extra.
    (* 0x8403c .. 0x84048: a0 = f + 15; the o-join a3 = R (s10 keeps fra + 32) *)
    do 3 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 13) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8404c: the check of byte 15 (and the load of byte 14) *)
    pose proof (sh1 _ f 50 15 (f + 15) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH15.
    chk_core (f + 15) RXf (Z_to_bv 5 11) SH15 pre_sr no_extra.
    (* 0x84060: the check of the 2-byte store at R + 20 (and the load of byte 15) *)
    step.
    pose proof (shw _ R 36 20 2 (R + 20) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH20.
    chk_core (R + 20) RXr (Z_to_bv 5 14) SH20 pre_sr add1.
    (* 0x84078 .. 0x84088: the store at R + 20, the overflow guard of f + 18 *)
    do 5 step. ub_false.
    (* 0x8408c: the check of byte 18 *)
    step.
    pose proof (sh1 _ f 50 18 (f + 18) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH18.
    chk_core (f + 18) RXf (Z_to_bv 5 12) SH18 pre_sr no_extra.
    (* 0x840a0 .. 0x840a8: the o-join a1 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 11) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x840ac: the check of the store at R + 22 (and the load of byte 18) *)
    step.
    pose proof (sh1 _ R 36 22 (R + 22) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH22.
    chk_core (R + 22) RXr (Z_to_bv 5 14) SH22 pre_sr no_extra.
    (* 0x840c4 .. 0x840cc: the store at R + 22 (le1 (zxb b) folded to [b] so it joins the record's cells), the
       overflow guard of f + 19 *)
    do 2 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x840d0: the check of byte 19 *)
    step.
    pose proof (sh1 _ f 50 19 (f + 19) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH19.
    chk_core (f + 19) RXf (Z_to_bv 5 14) SH19 pre_sr no_extra.
    (* 0x840e4 .. 0x840ec: the o-join a2 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 12) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x840f0: the check of the store at R + 23 (and the load of byte 19) *)
    step.
    pose proof (sh1 _ R 36 23 (R + 23) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH23.
    chk_core (R + 23) RXr (Z_to_bv 5 11) SH23 pre_sr no_extra.
    (* 0x84108 .. 0x84114: the store at R + 23, the overflow guard of f + 21 *)
    do 3 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x84118: the check of byte 20 *)
    step.
    pose proof (sh1 _ f 50 20 (f + 20) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH20f.
    chk_core (f + 20) RXf (Z_to_bv 5 15) SH20f pre_sr no_extra.
    (* 0x8412c .. 0x84138: a1 = f + 21; the o-join a6 = R *)
    do 3 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 16) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8413c: the check of byte 21 (and the load of byte 20) *)
    pose proof (sh1 _ f 50 21 (f + 21) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH21.
    chk_core (f + 21) RXf (Z_to_bv 5 12) SH21 pre_sr no_extra.
    (* 0x84150: the check of the 2-byte store at R + 24 (and the load of byte 21) *)
    step.
    pose proof (shw _ R 36 24 2 (R + 24) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH24.
    chk_core (R + 24) RXr (Z_to_bv 5 17) SH24 pre_sr add1.
    (* 0x84168 .. 0x84178: the store at R + 24, the overflow guard of f + 22 *)
    do 5 step. ub_false.
    (* 0x8417c: the check of byte 22 *)
    step.
    pose proof (sh1 _ f 50 22 (f + 22) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH22f.
    chk_core (f + 22) RXf (Z_to_bv 5 15) SH22f pre_sr no_extra.
    (* 0x84190 .. 0x84198: the o-join a2 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 12) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8419c: the check of the store at R + 26 (and the load of byte 22) *)
    step.
    pose proof (sh1 _ R 36 26 (R + 26) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH26.
    chk_core (R + 26) RXr (Z_to_bv 5 16) SH26 pre_sr no_extra.
    (* 0x841b4 .. 0x841bc: the store at R + 26, the overflow guard of f + 16 *)
    do 2 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x841c0: the check of byte 16 *)
    step.
    pose proof (sh1 _ f 50 16 (f + 16) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH16.
    chk_core (f + 16) RXf (Z_to_bv 5 16) SH16 pre_sr no_extra.
    (* 0x841d4 .. 0x841d8: the overflow guard of f + 17 *)
    do 2 step. ub_false.
    (* 0x841dc: the check of byte 17 (and the load of byte 16) *)
    step.
    pose proof (sh1 _ f 50 17 (f + 17) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH17.
    chk_core (f + 17) RXf (Z_to_bv 5 17) SH17 pre_sr no_extra.
    (* 0x841f4 .. 0x84200: the load of byte 17, the or of bytes 16 and 17, the branch *)
    step. step. rewrite ?rc_zextb. step. step.
    (* the record's bytes 4..27 are complete *)
    match goal with H : rw_cells rsegs _ (R + 4) [CB 6 _] |- _ => rename H into HSRC' end.
    match goal with H : rw_cells rsegs _ (R + 10) [CB 6 _] |- _ => rename H into HDST' end.
    pose proof (rc_rw_join rsegs _ (R + 4) (R + 10) _ _ HSRC' ltac:(cbn [cells_size csize app]; lia) HDST')
      as J1.
    pose proof (rc_rw_join rsegs _ (R + 4) (R + 16) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HMID) as J2.
    clear HSRC' HDST' HMID J1.
    apply (rc_rw_flat rsegs _ (R + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn firstn repeat app]. reflexivity. }
    change (length P1) with 24%nat in J2. rename J2 into HP.
    cond_norm.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0))%bool eqn:T0; cbn [negb]; cbv iota.
    - (* 0x84204 .. 0x84218: kind 1: the check of the kind word at R, then 0x843d0 *)
      rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
      pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia)) as SHR.
      chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3.
      step. step.
      eapply (b_kind fra fv spc j nn w120 R mc0 _ 1 (repeat cp_z 2));
        [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
        | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
        | exact HKc | exact HP | exact HT | exact HG | kfact | lia | bfact ].
    - (* 0x84318: the kind tree *)
      eapply (b_tree fra fv spc j nn w120 R mc0);
        [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact ADf0 | exact H120
        | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV))))) | exact HE | exact T0
        | exact HKc | exact HP | exact HT | exact HG ].
  Qed.

  Lemma rc_land3 : forall x, x mod 4 = 0 -> 0 <= x < 2^64 ->
    Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
  Proof.
    intros x H Rx. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    change (2^2) with 4. rewrite H. reflexivity.
  Qed.

  (* 0x8421c: a failed header guard; the record keeps the 36 zero bytes of ctrlparse. *)
  Lemma b_none : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = false -> rw_cells rsegs mc R [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra)
               x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8421c) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HH HZ.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    assert (EK0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite HH; reflexivity).
    step. rewrite rc_land3 by lia. step. ub_false.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite EK0; reflexivity).
    eapply (b_done fra fv spc j nn w120 R mc0 mc); try eassumption.
    rewrite (ctrlparse_bytes_none n fr HH). exact HZ.
  Qed.

  (* 0x83f28 .. 0x84010: the record's zeroing, the header guards, the two input copies and the compare. *)
  Lemma L_body_k :
    (forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs))) ->
    KB Qp.
  Proof.
    intros HEPI. unfold KB.
    intros fra fv spc j nn w120 mc0 rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB AD32 H120.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hspc : S - 288 <= spc <= S - 128).
    { pose proof HK as HK2. destruct HK2 as [(_ & _ & Esp & _)|(_ & _ & _ & Esp & _)]; subst spc; lia. }
    remember (REC fra) as R eqn:ER.
    assert (HR : RF fra R).
    { unfold RF. subst R. unfold REC. destruct (Z.eqb_spec o 0) as [Eo|Eo];
        [left; split; [exact Eo | reflexivity] | right; split; [exact Eo | reflexivity]]. }
    clear ER.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    (* the record is apart from each callee's frame, as plain disjunctions for the transport tactics *)
    pose proof (RSP 2208 ltac:(lia)) as RSPa.
    pose proof (RSP 2224 ltac:(lia)) as RSPb.
    pose proof (RSP 4560 ltac:(lia)) as RSPc.
    pose proof HB as HB'. destruct HB' as (MU0 & WM0 & RM0 & MIb & SV0).
    assert (AD0 : addressable mc0 R 36).
    { pose proof HR as HR2. destruct HR2 as [(Ho & ER2)|(Ho & ER2)]; subst R; [exact AD32|].
      destruct (AO0 Ho) as (AOa & _ & _).
      apply (acl_addr_munch (Wf fra j nn) m mc0 o 36 AOa MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _ (jb_sh_out fra fv spc j nn w120 (o + i) HK _ _)));
        [exact (acl_app_in m o 36 i AOa Hi)|].
      destruct (o_apart_frame fra fv spc j nn w120 HK Ho) as [Hx|Hx]; [left | right]; lia. }
    assert (ADf0 : 50 <= n -> addressable mc0 f 50).
    { intros HN. apply (acl_addr_munch (Wf fra j nn) m mc0 f 50 (AF0 HN) MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _ (jb_sh_out fra fv spc j nn w120 (f + i) HK _ _)));
        [exact (acl_app_in m f 50 i (AF0 HN) Hi)|].
      destruct (f_apart_frame fra fv spc j nn w120 HK HN) as [Hx|Hx]; [left | right]; lia. }
    assert (ADbc0 : addressable mc0 REAC_CTRL_PARSE_BC 6).
    { apply (acl_addr_munch (Wf fra j nn) m mc0 REAC_CTRL_PARSE_BC 6 ABC MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _
                (jb_sh_out fra fv spc j nn w120 (REAC_CTRL_PARSE_BC + i) HK _ _)));
        [exact (acl_app_in m REAC_CTRL_PARSE_BC 6 i ABC Hi)|].
      left. destruct (fk_facts fra fv spc j nn w120 HK) as (_ & FRlo & _).
      pose proof FP0 as (DT & TS & C & T & DB & k0 & _ & _ & (Pfs0 & _ & Pfs2 & _) & _).
      unfold ASAN_GT in Pfs2. unfold REAC_CTRL_PARSE_BC. lia. }
    assert (ST0' : stk rsegs mc0 (S - 8800) S) by exact (stk_mono m mc0 _ _ ST0 WM0 RM0).
    destruct (rec_rw fra fv spc j nn w120 R mc0 HK HR HB) as [junk0 HRW0].
    pose proof HR as HO. unfold RF in HO.
    pose proof (f_dj_Wb fra fv spc j nn w120 HK) as DJF0.
    pose proof (bj_refl R mc0 MIb ST0' SV0) as HJ0. clear MU0 WM0 SV0 ST0'.
    destruct HJ0 as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_mub fra fv spc j nn w120 R mc0 mq HK HR HB MUq) as MUB.
    assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; lia).
    rs_hide_sec. rs_hide H120. rs_hide RFF. rs_hide RW120. rs_hide HO. rs_hide ADf0. rs_hide DJF0. rs_hide RRT.
    (* 0x83f28: s3 = the record *)
    step. step. ojoin HO R (Z_to_bv 5 19). step. step. step. step.
    (* 0x83f40: asan_memset(R, 0, 36) *)
    pose proof MSET as HM.
    unfold asan_memset_contract_F, ASAN_MEMSET_K, rng_asan.sh_word_rng, rng_asan.sh_al8_lo,
      rng_asan.sh_al8_hi in HM.
    cbv zeta in HM.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ;
      eapply evtF_cut; [ eapply (HM) with (junk := junk0) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m1 & Ems & MUc & WMc & MIc & STc & RWc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?UR, ?U36, ?U0, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?UR, ?U36, ?U0 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m1) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m1 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m1 RM RMd) as RMn;
          transport_after_call rsegs mm m1 MUc WMc;
          assert (STn : stk rsegs m1 (S - 8800) S) by
            (apply (stk_mono m m1 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m1 WMb WM)
             | apply (rd_mono_trans m mc0 m1 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc ACc SRc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?UR, ?U36, ?U0, ?Uspc.
    { change (Z.to_nat 36) with 36%nat. exact HRW0. }
    { lia. }
    { exact (ADR _ MU). }
    { right. apply RAP. lia. }
    { right. apply RAP. lia. }
    { exact RRT. }
    { apply RSP. lia. }
    { exact (proj1 (stk_split rsegs mc0 (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ). }
    { exact (jb_sw fra j nn _ AJ). }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memset's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the 36 bytes at R *) exact RGREC. }
    { (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the aligned shadow word span of __asan_memset's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?UR, ?U36, ?U0 in *. change (Z.to_nat 36) with 36%nat in *.
    change (Z_to_bv 8 (0 mod 256)) with cp_z in *.
    match goal with H : rw_cells rsegs m1 R [CB 36 (repeat cp_z 36)] |- _ => rename H into HZ end.
    try clear HRW0.
    (* 0x83f44: n < 50 *)
    step. step. rewrite (rc_ltu64 n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    { assert (HH : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    destruct (HF Hge) as (Hf0 & Hf50 & HfW).
    pose proof (RFF Hge) as RFf.
    pose proof (RINF Hge) as RGINF. pose proof (SCF Hge) as SCINF. pose proof (SKF Hge) as SKINF.
    pose proof (DJF0 Hge) as DJF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR (ADf0 Hge) MUq) as ADF.
    (* 0x83f4c .. 0x83f74: the first header byte *)
    step. ub_false. step. step. ub_false. step.
    rdbb 12%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (12 + jj)%nat with 12%nat by lia; apply cp_rd_12; lia).
    pose proof (sh1 _ f 50 12 (f + 12) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH12.
    chk_core (f + 12) RXf (Z_to_bv 5 12) SH12 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by lia.
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (HH : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    (* 0x83f78 .. 0x83f9c: the second header byte *)
    step. step. ub_false. step.
    rdbb 13%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (13 + jj)%nat with 13%nat by lia; apply cp_rd_13; lia).
    pose proof (sh1 _ f 50 13 (f + 13) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH13.
    chk_core (f + 13) RXf (Z_to_bv 5 12) SH13 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by lia.
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (HH : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; lia).
    clear RO RO0.
    rdbb 0%nat 23%nat (MUB _ MU) DJF ltac:(intros jj Hjj; apply cp_rd_e; [exact HE | lia]).
    (* 0x83fa0: the record is 4-aligned *)
    step. rewrite rc_land3 by lia. step. ub_false.
    (* the record's pieces *)
    destruct (rc_rw_cut_at rsegs _ R cp_z 36 4 (R + 4) HZ ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (R + 4) cp_z 32 6 (R + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (R + 10) cp_z 26 6 (R + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (R + 16) cp_z 20 12 (R + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (R + 28) cp_z 8 2 (R + 30) HZ4 ltac:(lia) ltac:(lia)) as [HT HG];
      cbn [Nat.sub] in HG.
    clear HZ HZ1 HZ2 HZ3 HZ4.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
    assert (U10 : bv_unsigned (Z_to_bv 64 (R + 10)) = R + 10) by (apply unsigned_lit; lia).
    (* 0x83fa8: asan_memcpy(R + 10, f, 6) *)
    step. step. ojoin HO R (Z_to_bv 5 10).
    step. step. step. step.
    pose proof MCPY as HMC.
    unfold asan_memcpy_contract_F, ASAN_MEMCPY_K, rng_asan.sh_word_rng, rng_asan.sh_al8_lo,
      rng_asan.sh_al8_hi in HMC.
    cbv zeta in HMC.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ1;
      eapply evtF_cut;
        [ eapply (HMC) with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
            (junk := repeat cp_z 6) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m2 & Ems & MUc & WMc & MIc & STc & RWc & BAc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?U10, ?U6, ?Uf, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?U10, ?U6 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m2) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m2 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m2 RM RMd) as RMn;
          transport_after_call rsegs mm m2 MUc WMc;
          assert (STn : stk rsegs m2 (S - 8800) S) by
            (apply (stk_mono m m2 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m2 WMb WM)
             | apply (rd_mono_trans m mc0 m2 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc BAc ACc SRc; rename RWc into HDSTc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U10, ?U6, ?Uf, ?Uspc.
    { exact BD0. }
    { reflexivity. }
    { change (Z.to_nat 6) with 6%nat. exact HDST. }
    { right. destruct RFf as [Hx|Hx]; [right | left]; lia. }
    { lia. }
    { exact (acl_addr_sub _ f 50 f 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (acl_addr_sub _ R 36 (R + 10) 6 (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { right. exact (acl_app_in mc0 f 50 6 (ADf0 Hge) ltac:(lia)). }
    { right. replace (R + 10 + 6) with (R + 16) by lia. apply RAP. lia. }
    { right. split; [exact (acl_app_in mc0 f 50 7 (ADf0 Hge) ltac:(lia))|].
      replace (R + 10 + 7) with (R + 17) by lia. apply RAP. lia. }
    { destruct RRT as [Hx|Hx]; [left | right]; unfold RT_LO, RT_HI in *; lia. }
    { destruct (RSP 2224 ltac:(lia)) as [Hx|Hx]; [left | right]; lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ1). }
    { exact (jb_sw fra j nn _ AJ1). }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memcpy's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the destination bytes in the record *) eapply rng_sub; [exact RGREC | lia | lia]. }
    { (* the source bytes in the input *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; lia. }
    { (* the aligned shadow word span of __asan_memcpy's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?U10, ?U6, ?Uf in *. change (Z.to_nat 6) with 6%nat in *.
    (* 0x83fc4 .. 0x83fe4: asan_memcpy(R + 4, f + 6, 6) *)
    step. step. step. ub_false. step. step. ojoin HO R (Z_to_bv 5 22). step. step. step.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    assert (U4 : bv_unsigned (Z_to_bv 64 (R + 4)) = R + 4) by (apply unsigned_lit; lia).
    assert (Uf6 : bv_unsigned (Z_to_bv 64 (f + 6)) = f + 6) by (apply unsigned_lit; lia).
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ2;
      eapply evtF_cut;
        [ eapply (HMC) with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
            (junk := repeat cp_z 6) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m3 & Ems & MUc & WMc & MIc & STc & RWc & BAc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?U4, ?U6, ?Uf6, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?U4, ?U6 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m3) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m3 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m3 RM RMd) as RMn;
          transport_after_call rsegs mm m3 MUc WMc;
          assert (STn : stk rsegs m3 (S - 8800) S) by
            (apply (stk_mono m m3 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m3 WMb WM)
             | apply (rd_mono_trans m mc0 m3 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc BAc ACc SRc; rename RWc into HSRCc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U4, ?U6, ?Uf6, ?Uspc.
    { exact BD1. }
    { reflexivity. }
    { change (Z.to_nat 6) with 6%nat. exact HSRC. }
    { right. destruct RFf as [Hx|Hx]; [right | left]; lia. }
    { lia. }
    { exact (acl_addr_sub _ f 50 (f + 6) 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (acl_addr_sub _ R 36 (R + 4) 6 (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { right. replace (f + 6 + 6) with (f + 12) by lia.
      exact (acl_app_in mc0 f 50 12 (ADf0 Hge) ltac:(lia)). }
    { right. replace (R + 4 + 6) with (R + 10) by lia. apply RAP. lia. }
    { right. split.
      - replace (f + 6 + 7) with (f + 13) by lia. exact (acl_app_in mc0 f 50 13 (ADf0 Hge) ltac:(lia)).
      - replace (R + 4 + 7) with (R + 11) by lia. apply RAP. lia. }
    { destruct RRT as [Hx|Hx]; [left | right]; unfold RT_LO, RT_HI in *; lia. }
    { destruct (RSP 2224 ltac:(lia)) as [Hx|Hx]; [left | right]; lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ2). }
    { exact (jb_sw fra j nn _ AJ2). }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memcpy's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the destination bytes in the record *) eapply rng_sub; [exact RGREC | lia | lia]. }
    { (* the source bytes in the input *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; lia. }
    { (* the aligned shadow word span of __asan_memcpy's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?U4, ?U6, ?Uf6 in *. change (Z.to_nat 6) with 6%nat in *.
    (* 0x83fe8 .. 0x83ffc: the compare with .str.4 *)
    step. step. step. step. step. step.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof BWRP as HBC. unfold bcmp_wrap_contract_F, BCMP_WRAP_K in HBC. cbv zeta in HBC.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ3;
      pose proof (jb_cl fra fv spc j nn w120 R mc0 mm HK HR HB MU) as (CL1 & CL2 & CL3 & CL4 & CL5);
      eapply evtF_cut;
        [ eapply (HBC) with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
            (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m4 & Ems & MUc & WMc & MIc & STc & ACc & SRc & BA1 & BA2);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?Uspc in MUc;
          rewrite ?Uspc in STc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m4) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_nil];
             cbn [fst snd]; intros y Hy; apply (rd_of_stk _ _ _ STc); lia);
          pose proof (rd_mono_trans mc0 mm m4 RM RMd) as RMn;
          transport_after_call rsegs mm m4 MUc WMc;
          assert (STn : stk rsegs m4 (S - 8800) S) by
            (apply (stk_mono m m4 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m4 WMb WM)
             | apply (rd_mono_trans m mc0 m4 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc ACc SRc BA1 BA2;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U6, ?Uf, ?Uspc.
    all: try change (bv_unsigned (Z_to_bv 64 135680)) with 135680.
    { exact BD0. }
    { apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MI | vm_compute; reflexivity]. }
    { change (Z.to_nat 6) with 6%nat. exact Hv. }
    { exact MI. }
    { lia. }
    { exact (acl_addr_sub _ f 50 f 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (bj_addr fra fv spc j nn w120 R mc0 _ REAC_CTRL_PARSE_BC 6 HK HR ADbc0 MU). }
    { right. exact (acl_app_in mc0 f 50 6 (ADf0 Hge) ltac:(lia)). }
    { right. unfold app_mem, LOWMEM_END. left. lia. }
    { right. exact (acl_app_in mc0 f 50 7 (ADf0 Hge) ltac:(lia)). }
    { right. unfold app_mem, LOWMEM_END. left. lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { left. lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ3). }
    { exact (jb_sw fra j nn _ AJ3). }
    { exact CL1. }
    { exact CL2. }
    { exact CL3. }
    { exact CL4. }
    { exact CL5. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *) exact RIMG. }
    { (* the bcmp wrapper's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the 6 input bytes *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; lia. }
    { (* the 6 bytes at .str.4 *)
      eapply rng_sub; [exact RBC | unfold REAC_CTRL_PARSE_BC; lia | unfold REAC_CTRL_PARSE_BC; lia]. }
    { (* their aligned shadow word cover *)
      right. unfold shadow_addr. apply SKBC; unfold REAC_CTRL_PARSE_BC; lia. }
    (* 0x84000: the check of the 4-byte store at R + 16, then the field stores *)
    pose proof (shw _ R 36 16 4 (R + 16) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH16r.
    chk_core (R + 16) RXr (Z_to_bv 5 12) SH16r pre_sr add3.
    eapply b_fields;
      first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV))))) | exact (ADf0 Hge) | exact Hvr | exact Hvb].
  Qed.

  (* The whole run: the entry (0x83e04 .. 0x83f28), the body walk, the exit. *)
  Lemma parse_x_run : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    evtF rsegs RNG Qp (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
                     a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
    exact (entry t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Qp m eq_refl (L_body_k L_epi)).
  Qed.

End SetupF.

(* The free-frame contract in footprint form: the Section's run at the contract's state.  The Section's X premises
   are the contract's leading Forall split into the flag bytes (XF0) and the frame indices (XB0); its shadow
   premises are the statement's exact window shadow and aligned covers, turned here into the quantified covers the
   run uses. *)
Theorem reac_ctrl_parse_x_F_holds :
  asan_stack_malloc_1_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F -> bcmp_wrap_contract_F ->
  reac_ctrl_parse_contract_x_F.
Proof.
  intros SMAL MSET MCPY BWRP. unfold reac_ctrl_parse_contract_x_F.
  intros RNG X ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f n o S FS fr junk HXF Ha0 Ha1 Ha2 Hsp Hf Hn Ho HS HS16 HKS Hstk Hmi Hfr Hn50 Hrd Ho36 Hac Hsw Hhm Hae
    Haddr Hfa Hoa Hbc Hrb Hrm Hcf Hcf1 Hcf2 Hfp Htls
    RBY RIMG0 RWIN RWSHA RINF RFSHA ROUT ROSHA RBC RBCSHA RFSS RW1 RTLS.
  subst a0 a1 a2 sp. unfold REAC_CTRL_PARSE_K in *.
  assert (RS : 8800 <= S < 2^64) by lia.
  assert (XF0 : Forall (fun ci => fst ci = 1%nat /\ bytes_at rsegs m (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (H1 & _ & H3); exact (conj H1 H3)).
  assert (XB0 : Forall (fun ci => 0 <= snd ci < fs_M 1) X)
    by (eapply Forall_impl; [|exact HXF]; intros ci (_ & H2 & _); exact H2).
  pose proof kind_of_link1_F_holds as KOL.
  (* the image, as the literal range the step tactics match *)
  assert (RIMG : rng RNG 0x10000 0x5ee000) by (unfold IMG_LO, IMG_LEN in RIMG0; exact RIMG0).
  (* the quantified shadow covers of the window, of f, of o and of the compare bytes *)
  assert (SCW : shcov RNG (S - 8800) 8800) by exact (rcpF_win_cov RNG S HS16 RWSHA).
  assert (SKW : shkov RNG (S - 2560) 2432) by exact (rcpF_win_kov RNG S HS16 RWSHA).
  assert (SCF : 50 <= n -> shcov RNG f 50) by (intros H50; apply rcpF_cov; exact (RFSHA H50)).
  assert (SKF : 50 <= n -> shkov RNG f 50) by (intros H50; apply rcpF_kov; exact (RFSHA H50)).
  assert (SCO : o <> 0 -> shcov RNG o 36) by (intros H0; apply rcpF_cov; exact (ROSHA H0)).
  assert (SKO : o <> 0 -> shkov RNG o 36) by (intros H0; apply rcpF_kov; exact (ROSHA H0)).
  assert (SKBC : shkov RNG REAC_CTRL_PARSE_BC 6) by (apply rcpF_kov; exact RBCSHA).
  (* the class-1 side-stack bytes of fp_w, one rng fact per range *)
  pose proof RW1 as RWc. unfold fp_w, fp_w1 in RWc. cbn [flat_map app] in RWc.
  apply Forall_cons_iff in RWc as [_ RWc].
  apply Forall_cons_iff in RWc as [RFLG RWc].
  apply Forall_cons_iff in RWc as [RFRM RWc].
  apply Forall_cons_iff in RWc as [RFRS _].
  cbn [fst snd] in RFLG, RFRM, RFRS.
  replace (fs_flag FS 1 0 + fs_M 1 - fs_flag FS 1 0) with (fs_M 1) in RFLG by lia.
  (* the frames' shadow comes byte-exact; both of its ends are the shadow byte of a 64-aligned address *)
  pose proof Hfp as (DTq & TSq & Cq & Tq & DBq & kq & _ & _ & (HFSp & HFS4 & _) & _).
  assert (EQ : FS = 4096 * (FS / 4096)) by (pose proof (Z.div_mod FS 4096 ltac:(lia)); lia).
  set (q := FS / 4096) in EQ. clearbody q.
  assert (EF0 : fs_frame FS 1 0 = 64 * (64 * q + 16960)) by (rewrite fs_frame1; lia).
  assert (EF1 : fs_frame FS 1 (fs_M 1) = 64 * (64 * q + 33344))
    by (rewrite fs_frame1; change (fs_M 1) with 8192; lia).
  assert (ES0 : shadow_addr (fs_frame FS 1 0) = 8 * (64 * q + 16960) + ASAN_K).
  { unfold shadow_addr. rewrite EF0.
    replace (64 * (64 * q + 16960)) with (8 * (8 * (64 * q + 16960))) by lia. rewrite rcpF_div8. lia. }
  assert (ES1 : shadow_addr (fs_frame FS 1 (fs_M 1)) = 8 * (64 * q + 33344) + ASAN_K).
  { unfold shadow_addr. rewrite EF1.
    replace (64 * (64 * q + 33344)) with (8 * (8 * (64 * q + 33344))) by lia. rewrite rcpF_div8. lia. }
  rewrite ES0, ES1 in RFRS.
  assert (SCFR : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_cov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  assert (SKFR : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0))
    by (rewrite EF0, EF1; exact (rcpF_span_kov RNG (64 * q + 16960) (64 * q + 33344) RFRS)).
  eapply parse_x_run; eassumption.
Qed.

(* RECIPE step 1: the old statement, back from the footprint form at ExecF.RNG_all, from the same callee contracts
   (in footprint form) as reac_ctrl_parse.v's reac_ctrl_parse_x_holds takes in the same places. *)
Theorem reac_ctrl_parse_x_holds_of_F :
  asan_stack_malloc_1_contract_F -> asan_memset_contract_F -> asan_memcpy_contract_F -> bcmp_wrap_contract_F ->
  reac_ctrl_parse_contract_x.
Proof.
  intros SMAL MSET MCPY BWRP.
  exact (reac_ctrl_parse_contract_x_of_F (reac_ctrl_parse_x_F_holds SMAL MSET MCPY BWRP)).
Qed.
