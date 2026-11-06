(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 278 of its 317 lines of code are new or changed and 215 lines of the source are left out. *)
(* trim (reac_segconf.c:51-59, static) on the ASan+UBSan image B of reac-pw/fuzz_segconf (fuzz_segconf.asan-ubsan,
   pin c3796c0b38f3; entry BASE + AF_trim = 0x89640, 324 bytes, 81 instructions, frame 32 bytes, no side-stack
   frame): the kit of its walk. ADAPTED for the image-B G3 walk owner's image-B trim walk lane from the image-A G3 walk owner's image-A kit
   lib/A/Prog/trim_k.v (commit 07dedd5b93c6: its pure lemmas, tr_cx / tr_mid / tr_post and the
   cut-statement form) and the unit owner's UBSan walk lib/U/Prog/trim.v (commit 523c6a205596: the
   three trap discharges), re-derived on image B's code (the
   neutral excerpt trim.fuzz_segconf.asan-ubsan.s; listing lib/B/Prog/SegList.v,
   AF_trim = 0x4880). The contract is trim_c.v (the image-A owner's text, G3 FINAL 6f783602b5e3).
   Image B's code differs from image A's in three ways that matter here: the shadow base lives in s1 (x9; A: s2),
   s2 (x18) holds 1 - s (it counts down with the leading loop and feeds the s + |s1| trap), and three UBSan trap
   branches go to the `unimp` at 0x89770:
     0x896a4 `beq s0,a3` (a3 = -1): s + 1 would wrap. Not taken: s0 = p + i <= p + |s| < 2 ^ 47 (trim_pre's sa_addr
             p (|s| + 1)), the LEAD seed's range fact on s0, decided by the executor.
     0x896d0 `bltu a1,a0` (a1 = s2 - 2 = 2^64 - 1 - s0, a0 = |s1|): s0 + |s1| would wrap. Not taken:
             s0 + |s1| = p + |s| < 2 ^ 47 (trim_s.v, tr_trap_ltu).
     0x896f4 `beq a2,a3` (a2 = e, a3 = 1): e - 1 would be 0. Not taken: e >= s0 + 1 >= 4097 (p >= 4096: a live object
             lies at or above 4096), the TRAIL seed's range fact on e, decided by the executor.
   Cut points (listing offsets from BASE = image B's text base 0x84dc0):
     LEAD  0x48c0 = 0x89680  the leading-blank loop's head (s0 = a0 = p + i, s2 = 1 - (p + i))
     AFTER 0x4904 = 0x896c4  the loop's exit (s0 = p + trim_lead s), before `jal strlen` at 0x896c8
     TRAIL 0x4934 = 0x896f4  the trailing-blank loop's head (a2 = e = p + lead + j, a0 = e - 1)
     FIN   0x4980 = 0x89740  the store's inline check (a1 = e = trim_end_addr p s), then `sb zero,0(a1)` and the
                             return; 0x8973c `mv a1,a2` is the entry the non-blank exits take, one step before. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase trim_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the plain walk's pure lemmas (the unit owner's lib/Prog/trim.v TrimSpine at db8c4beebf62, the image-free part, as
   the image-A G3 walk owner's lib/A/Prog/trim_k.v TrimA copies them) ---- *)
Module TrimB.
Import SegModel.

Lemma cut_nul_nz : forall s, ~ In 0 s -> cut_nul s = s.
Proof.
  induction s as [|x s IH]; intros H; cbn; [reflexivity|].
  destruct (x =? 0) eqn:E.
  - apply Z.eqb_eq in E. subst. exfalso. apply H. left. reflexivity.
  - f_equal. apply IH. intros Hi. apply H. right. exact Hi.
Qed.

Lemma tw_nth : forall P l i, (i < length (takewhile P l))%nat -> P (nth i l 0) = true.
Proof.
  intros P. induction l as [|x l IH]; intros i H; cbn in *; [lia|].
  destruct (P x) eqn:E; cbn in H; [|lia]. destruct i; [exact E|]. apply IH. lia.
Qed.

Lemma tw_len : forall P l, (length (takewhile P l) <= length l)%nat.
Proof. intros P. induction l as [|x l IH]; cbn; [lia|]. destruct (P x); cbn; lia. Qed.

Lemma tw_stop : forall P l, P 0 = false -> P (nth (length (takewhile P l)) l 0) = false.
Proof.
  intros P. induction l as [|x l IH]; intros H0; cbn; [exact H0|].
  destruct (P x) eqn:E; cbn; [apply IH; exact H0 | exact E].
Qed.

Lemma skipn_tw : forall P l, skipn (length (takewhile P l)) l = dropwhile P l.
Proof. intros P. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (P x); cbn; [exact IH | reflexivity]. Qed.

Lemma trim_end_le : forall s f e, (trim_end s e f <= e)%nat.
Proof.
  intros s f. induction f as [|f IH]; intros [|e].
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - apply Nat.le_refl.
  - change (trim_end s (S e) (S f)) with (if blank (nth e s 0) then trim_end s e f else S e).
    destruct (blank (nth e s 0)); [specialize (IH e); lia | apply Nat.le_refl].
Qed.

Definition s1_of (s : list Z) : list Z := dropwhile blank s.
Definition te (s : list Z) (j : nat) : nat := trim_end (s1_of s) j j.

Lemma te_S : forall s j, te s (S j) = if blank (nth j (s1_of s) 0) then te s j else S j.
Proof. reflexivity. Qed.

Lemma te_0 : forall s, te s 0 = 0%nat.
Proof. reflexivity. Qed.

Lemma te_le : forall s j, (te s j <= j)%nat.
Proof. intros. apply trim_end_le. Qed.

Lemma lead_eq : forall s, ~ In 0 s -> seg_spec.trim_lead s = length (takewhile blank s).
Proof. intros s H. unfold seg_spec.trim_lead. rewrite cut_nul_nz by exact H. reflexivity. Qed.

Lemma lead_le : forall s, ~ In 0 s -> (seg_spec.trim_lead s <= length s)%nat.
Proof. intros s H. rewrite lead_eq by exact H. apply tw_len. Qed.

Lemma lead_blank : forall s i, ~ In 0 s -> (i < seg_spec.trim_lead s)%nat -> blank (nth i s 0) = true.
Proof. intros s i H Hi. rewrite lead_eq in Hi by exact H. apply tw_nth. exact Hi. Qed.

Lemma lead_stop : forall s, ~ In 0 s -> blank (nth (seg_spec.trim_lead s) s 0) = false.
Proof. intros s H. rewrite lead_eq by exact H. apply tw_stop. reflexivity. Qed.

Lemma s1_skipn : forall s, ~ In 0 s -> s1_of s = skipn (seg_spec.trim_lead s) s.
Proof. intros s H. rewrite lead_eq by exact H. unfold s1_of. symmetry. apply skipn_tw. Qed.

Lemma s1_len : forall s, ~ In 0 s -> length (s1_of s) = (length s - seg_spec.trim_lead s)%nat.
Proof. intros s H. rewrite s1_skipn by exact H. apply length_skipn. Qed.

Lemma nth_skipn0 : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
  induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity.
  - destruct j; reflexivity.
  - apply IH.
Qed.

Lemma s1_nth : forall s j, ~ In 0 s -> nth j (s1_of s) 0 = nth (seg_spec.trim_lead s + j) s 0.
Proof. intros s j H. rewrite s1_skipn by exact H. apply nth_skipn0. Qed.

Lemma rtrim_len : forall s, ~ In 0 s -> length (r_trim s) = te s (length (s1_of s)).
Proof.
  intros s H. unfold r_trim. rewrite cut_nul_nz by exact H. fold (s1_of s). fold (te s (length (s1_of s))).
  rewrite length_firstn. pose proof (te_le s (length (s1_of s))). lia.
Qed.

(* trim's blank test: `bltu 0x20, c` (out when c > 32), then bit c of 0x100002200 = 2^32 + 2^13 + 2^9 *)
Lemma blank_le32 : forall c, blank c = true -> c <= 32.
Proof.
  intros c H. unfold blank in H.
  destruct (c =? 32) eqn:E1; [apply Z.eqb_eq in E1; lia|].
  destruct (c =? 9) eqn:E2; [apply Z.eqb_eq in E2; lia|].
  destruct (c =? 13) eqn:E3; [apply Z.eqb_eq in E3; lia|]. discriminate.
Qed.

Lemma blank_mask_b : forall c, 0 <= c <= 32 ->
  (Z.land (Z.shiftr 4294976000 (Z.land c 63)) 1 =? 0) = negb (blank c).
Proof.
  intros c Hc. destruct (Z_of_nat_complete c ltac:(lia)) as [n ->].
  assert (Hn : (n <= 32)%nat) by lia. clear Hc.
  do 33 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Lemma blank0 : blank 0 = false.
Proof. reflexivity. Qed.

End TrimB.
Import TrimB.

(* ---- the bytes of a C string through a reader ---- *)
Lemma sa_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i <= length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
  intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia).
  destruct (Nat.lt_ge_cases i (length s)) as [Hl|Hg].
  - rewrite app_nth1 by exact Hl. reflexivity.
  - assert (i = length s) as -> by lia. rewrite app_nth2, Nat.sub_diag by lia. cbn [nth].
    rewrite nth_overflow by lia. reflexivity.
Qed.

Lemma bv8_small : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  replace (2 ^ Z.of_N 8) with 256 by reflexivity. lia.
Qed.

(* ---- 64-bit words as the executor's terms leave them ---- *)
Lemma w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H.
Qed.
Lemma w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. apply w64_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma alu64_add_lit : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma alu64_sub_lit : forall a b, alu64 ALU_SUB (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma md_mul_lit : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. rewrite m_mul. unfold v_mul. apply w64_mod. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.

(* the listing offsets of trim's cut points (BASE + AF_trim = 0x89640, AF_trim = 0x4880, lib/B/Prog/SegList.v) *)
Definition TR_LEAD : Z := 0x48c0.   (* 0x89680 srli a4,a0,3: the leading loop's head *)
Definition TR_AFTER : Z := 0x4904.  (* 0x896c4 mv a0,s0: the leading loop's exit *)
Definition TR_CALL : Z := 0x4908.   (* 0x896c8 jal strlen (the trampoline 0x43a98) *)
Definition TR_RET : Z := 0x490c.    (* 0x896cc addi a1,s2,-2: strlen's return *)
Definition TR_TRAIL : Z := 0x4934.  (* 0x896f4 beq a2,a3: the trailing loop's head (its trap test first) *)
Definition TR_FIN : Z := 0x4980.    (* 0x89740 srli a0,a1,3: the store's inline check *)
(* the blank mask of 0x8966c-0x89674 and 0x896e8-0x896f0: lui 0x800; addiw 0x11; slli 9 *)
Definition TR_MASK : Z := 4294976000.
(* a3 at the leading loop: `li a3,-1` (0x89678), the word 2 ^ 64 - 1 *)
Definition TR_M1 : Z := 18446744073709551615.
(* the callee-saved registers trim never writes *)
Definition TR_KEPT : list (bv 5) := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* image B's values of the contract's pure parameters come from the image-B harness owner's lib/B/Prog/SegInstB.v (1f771e2f2066,
   the image-A owner's SegInstA names): STK_trim = 32 + ESTACK = 4128 (trim's 32-byte frame, 0x89640 `addi sp,sp,-32`, and below it
   the strlen wrapper's ESTACK window, called at sp0 - 32), RLO_A / RHI_A = SegGlob.SEG_RLO / SEG_RHI = 0xa1c60 /
   0xa3f08. The entry stays the listing term BASE + AF_trim (SegInstB's ruling; A_trim_A_AF ties it to 0x89640). *)

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

(* the contract's footprint and post (trim_c.v:92-98), word for word *)
Definition tr_FP (p : Z) (s : list Z) : list (Z * Z) := [(trim_end_addr p s, trim_end_addr p s + 1)].
Definition tr_Q (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (regs : bvmap 5 word)
  (p : Z) (s : list Z)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) /\
 sa_bytes (aview SEGS (w_H W') mem') p
   (seg_spec.zb (firstn (seg_spec.trim_lead s + length (SegModel.r_trim s)) s) ++ [seg_spec.ZERO]) /\
 sa_kept SEGS W mem W' mem' regs STK_trim (fun a => a = trim_end_addr p s) /\
 sa_noalloc B ly S ly' S'.
Definition tr_post (regs : bvmap 5 word) ly S W mem md (p : Z) (s : list Z) : world SEGS -> config -> Prop :=
apost_base SEGS B STK_trim (tr_FP p s) regs ly S W mem md EV_trim (tr_Q ly S W mem regs p s).

(* the contract's premises (trim_c.v:86-90) at image B *)
Definition tr_cx ly S W (regs : bvmap 5 word) mem md ch (p : Z) (s : list Z) : Prop :=
afn_pre SEGS B STK_trim ly S W regs mem md ch /\
arodata_okP SEGS RLO_A RHI_A B (rdW W mem) /\
getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
trim_pre SEGS B ly S W mem regs p s /\
st_nev S + EV_trim <= EV_MAX.

(* the invariant at every cut: the journal from the entry (no side-stack frame, no event, the layout, the state and
   the world of the entry); every byte outside the stack window [sp0 - STK_trim, sp0) as at the entry (trim writes
   only its frame before the store, and strlen only its scratch window); every byte outside the image present at
   the entry present; the prologue's four slots (ra at sp0 - 8, s0 at - 16, s1 at - 24, s2 at - 32) *)
Definition tr_mid ly S W (regs : bvmap 5 word) mem md (p : Z) (s : list Z) memc mdc : Prop :=
ajournal SEGS B STK_trim (spZ regs) (tr_FP p s) ly S W mem md [] ly S W memc mdc 0 /\
kept_out (rdW W mem) (rdW W memc) (spZ regs - STK_trim) (spZ regs) /\
(forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) mem a -> ~ in_img SEGS a -> apresent (w_H W) memc a) /\
rdword (rdW W memc) (spZ regs - 8) = Some (bv_unsigned (getr regs 1)) /\
rdword (rdW W memc) (spZ regs - 16) = Some (bv_unsigned (getr regs 8)) /\
rdword (rdW W memc) (spZ regs - 24) = Some (bv_unsigned (getr regs 9)) /\
rdword (rdW W memc) (spZ regs - 32) = Some (bv_unsigned (getr regs 18)).

(* the registers between the prologue and the epilogue: sp = sp0 - 32, s1 = the shadow base (0x89668
   `ld s1,0(a2)`), gp, tp and s3..s11 the entry's *)
Definition tr_regs (regs regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (spZ regs - 32) /\ getr regs1 9 = w64 SB /\
(forall r, In r TR_KEPT -> getr regs1 r = getr regs r).

Definition tr_at (regs : bvmap 5 word) ly S W mem md p s (regs1 : bvmap 5 word) memc mdc (pc : Z) : Prop :=
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)) mdc) (tr_post regs ly S W mem md p s).

(* ---- the four cut points ---- *)
Definition TR_FIN_stmt : Prop :=
forall ly S W regs mem md ch p s regs1 memc mdc,
tr_cx ly S W regs mem md ch p s -> tr_mid ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
getr regs1 8 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) ->
getr regs1 11 = w64 (trim_end_addr p s) ->
tr_at regs ly S W mem md p s regs1 memc mdc TR_FIN.

Definition TR_TRAIL_stmt : Prop :=
forall ly S W regs mem md ch p s regs1 memc mdc j,
tr_cx ly S W regs mem md ch p s -> tr_mid ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
(1 <= j <= length (s1_of s))%nat -> te s j = te s (length (s1_of s)) ->
getr regs1 8 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) ->
getr regs1 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat j - 1) ->
getr regs1 12 = w64 (p + Z.of_nat (seg_spec.trim_lead s) + Z.of_nat j) ->
getr regs1 13 = w64 1 -> getr regs1 14 = w64 32 -> getr regs1 15 = w64 TR_MASK ->
tr_at regs ly S W mem md p s regs1 memc mdc TR_TRAIL.

Definition TR_AFTER_stmt : Prop :=
forall ly S W regs mem md ch p s regs1 memc mdc,
tr_cx ly S W regs mem md ch p s -> tr_mid ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
getr regs1 8 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) ->
getr regs1 18 = w64 (1 - (p + Z.of_nat (seg_spec.trim_lead s))) ->
tr_at regs ly S W mem md p s regs1 memc mdc TR_AFTER.

Definition TR_LEAD_stmt : Prop :=
forall ly S W regs mem md ch p s regs1 memc mdc i,
tr_cx ly S W regs mem md ch p s -> tr_mid ly S W regs mem md p s memc mdc -> tr_regs regs regs1 ->
(i <= seg_spec.trim_lead s)%nat ->
getr regs1 8 = w64 (p + Z.of_nat i) -> getr regs1 10 = w64 (p + Z.of_nat i) ->
getr regs1 18 = w64 (1 - (p + Z.of_nat i)) ->
getr regs1 11 = w64 32 -> getr regs1 12 = w64 TR_MASK -> getr regs1 13 = w64 TR_M1 ->
tr_at regs ly S W mem md p s regs1 memc mdc TR_LEAD.

Lemma tr_regs_kept : forall regs regs1 regs1',
tr_regs regs regs1 -> (forall r, In r (2%bv :: 9%bv :: TR_KEPT) -> getr regs1' r = getr regs1 r) ->
tr_regs regs regs1'.
Proof.
intros regs regs1 regs1' (R2 & R9 & RK) K. split; [rewrite K by (cbn; tauto); exact R2|].
split; [rewrite K by (cbn; tauto); exact R9|]. intros r Hr. rewrite K by (right; right; exact Hr). exact (RK r Hr).
Qed.

(* ---- what the entry context gives ---- *)
Hypothesis LAWS : AR_laws SEGS B.

(* where the string lies: below the stack window (a side-stack frame or a heap block, both below alloc_ceiling) or
   above the entry sp (the caller's real stack) *)
Definition tr_zone ly S (W : world SEGS) (mem : word -> option byte) (regs : bvmap 5 word) (p n : Z) : Prop :=
((sa_fframe ly S p n \/ sa_heap B ly S p n) /\ p + n <= alloc_ceiling) \/
(spZ regs <= p /\ p + n <= ly_top ly /\ (forall i, 0 <= i < n -> apresent (w_H W) mem (p + i))).

Lemma tr_cx_facts : forall ly S W regs mem md ch p s,
tr_cx ly S W regs mem md ch p s ->
let n := Z.of_nat (length s) + 1 in
sa_str (rdW W mem) p s /\ sa_addr (rdW W mem) p n /\ tr_zone ly S W mem regs p n /\
(forall i, 0 <= i < n -> apresent (w_H W) mem (p + i) /\ ~ in_img SEGS (p + i)) /\
(forall i, 0 <= i < n -> ~ (SHADOW_OFF <= p + i < SHADOW_OFF + 17592186044416)) /\
4096 <= p /\ p + n <= 2 ^ 47 /\ n < 2 ^ 32 /\
(p + n <= spZ regs - STK_trim \/ spZ regs <= p) /\
spZ regs mod 16 = 0 /\ alloc_ceiling + STK_trim <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
intros ly S W regs mem md ch p s (HPRE & HROD & H10 & Hp64 & (Hp0 & HSTR & HADDR & HDST & HL32) & HEV). cbv zeta.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HS : STK_trim = 4128) by reflexivity.
assert (HZ : tr_zone ly S W mem regs p (Z.of_nat (length s) + 1) /\
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> apresent (w_H W) mem (p + i) /\ ~ in_img SEGS (p + i)) /\
  (forall i, 0 <= i < Z.of_nat (length s) + 1 -> ~ (SHADOW_OFF <= p + i < SHADOW_OFF + 17592186044416)) /\
  4096 <= p /\ p + (Z.of_nat (length s) + 1) <= 2 ^ 47).
{ destruct HDST as [(Hfr & _) | [(Hhp & _) | (Hsp & Htp' & Hpr & _)]].
  - destruct Hfr as (cid & pos & Hin & Hcid & Hf1 & Hf2).
    destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hb1 & Hb2 & Hb3).
    destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (_ & _ & Hfp & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hb3.
    split; [left; split; [left; exists cid, pos; repeat split; assumption | lia]|].
    split; [intros i Hi; split; [exact (proj1 (Hfp (p + i) ltac:(lia))) | exact (frm_img SEGS B LAWS ly S W mem md cid pos (p + i) HAR Hin ltac:(lia))]|].
    split; [intros i Hi; unfold SHADOW_OFF; lia|]. lia.
  - destruct Hhp as (b & m & Hin & Hb1 & Hb2).
    destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & Hbp & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrk].
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
    split; [left; split; [right; exists b, m; repeat split; assumption | lia]|].
    split; [intros i Hi; split; [exact (proj1 (Hbp (p + i) ltac:(lia))) | exact (blk_img SEGS B LAWS ly S W mem md b m (p + i) HAR Hin ltac:(lia))]|].
    split; [intros i Hi; unfold SHADOW_OFF; lia|]. lia.
  - split; [right; exact (conj Hsp (conj Htp' Hpr))|].
    split; [intros i Hi; split; [exact (Hpr i Hi) | intros Himg; pose proof (pa_segs_low (p + i) Himg); unfold kLowMemEnd in *; lia]|].
    split; [intros i Hi; unfold SHADOW_OFF; lia|]. lia. }
destruct HZ as (HZ & HPR & HSB & H4096 & H47p).
split; [exact HSTR|]. split; [exact HADDR|]. split; [exact HZ|]. split; [exact HPR|]. split; [exact HSB|].
split; [exact H4096|]. split; [exact H47p|].
split; [lia|].
split.
{ destruct HZ as [(_ & Hc) | (Hsp & _)]; [left; lia | right; exact Hsp]. }
split; [exact Hal16|]. split; [lia|]. lia.
Qed.

(* the NUL lands inside the string: trim_lead s + |r_trim s| <= |s| *)
Lemma tr_e_range : forall s, ~ In 0 s -> (seg_spec.trim_lead s + length (SegModel.r_trim s) <= length s)%nat.
Proof.
intros s NZ. rewrite (rtrim_len s NZ). pose proof (te_le s (length (s1_of s))). rewrite (s1_len s NZ) in *.
pose proof (lead_le s NZ). lia.
Qed.

(* tr_mid survives a step that keeps every byte outside the stack window as it was at the last cut, and every
   present byte outside the image present *)
Lemma tr_mid_step : forall ly S W regs mem md p s memc mdc memc' mdc',
tr_mid ly S W regs mem md p s memc mdc -> 32 <= spZ regs <= 2 ^ 47 ->
ajournal SEGS B STK_trim (spZ regs) (tr_FP p s) ly S W mem md [] ly S W memc' mdc' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_trim <= a < spZ regs - 32) -> rdW W memc' a = rdW W memc a) ->
(forall a, 0 <= a < 2 ^ 64 -> apresent (w_H W) memc a -> ~ in_img SEGS a -> apresent (w_H W) memc' a) ->
tr_mid ly S W regs mem md p s memc' mdc'.
Proof.
intros ly S W regs mem md p s memc mdc memc' mdc' (HJ & KEEP & KPR & K8 & K16 & K24 & K32) Hsp HJ' KM KP.
assert (HS : STK_trim = 4128) by reflexivity.
split; [exact HJ'|].
split; [intros a Ha Hn; rewrite KM by (exact Ha || lia); exact (KEEP a Ha Hn)|].
split; [intros a Hb Ha Hi; exact (KP a Hb (KPR a Hb Ha Hi) Hi)|].
split; [rewrite (rdword_ext (rdW W memc) (rdW W memc')); [exact K8 | intros k Hk; apply KM; lia]|].
split; [rewrite (rdword_ext (rdW W memc) (rdW W memc')); [exact K16 | intros k Hk; apply KM; lia]|].
split; [rewrite (rdword_ext (rdW W memc) (rdW W memc')); [exact K24 | intros k Hk; apply KM; lia]|].
rewrite (rdword_ext (rdW W memc) (rdW W memc')); [exact K32 | intros k Hk; apply KM; lia].
Qed.

Lemma tr_ag32 : forall (regs1 : bvmap 5 word) extra E0 E (k : nat), (32 <= k)%nat ->
env_agree 32 (Ereg regs1 extra) E0 -> env_agree k E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E k Hk H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma tr_ag_ew : forall E0 E (k n : nat) v, env_agree k E0 E -> (n < k)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E k n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.

End e.
End f.
End d.
