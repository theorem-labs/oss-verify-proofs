(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ASan's strcmp interceptor, proved over the run's segment list (the binary's segments followed by the vDSO pair): its address block, the contract astrcmp_contract, and its proofs astrcmp_ok (from the interceptor's entry) and astrcmp_thunk_ok (from the slot __vdsosym's two calls reach). *)

(* WHAT THE INTERCEPTOR DOES, read whole from the disassembly (every instruction from the entry to
   both returns, and the two functions it calls on the path proved here):

   1. Prologue: a 0x7f0-byte frame holding ra and s0..s11 in its top 104 bytes, then 0xa0 more bytes.
   2. A call to the init-once test.  It pushes 16 bytes, loads the asan_inited byte with `lb` and
      `fence r,rw`, and returns 1 when that byte is 1.  On any other answer the interceptor
      tail-calls the real strcmp instead (not proved here: the byte is a premise).
   3. The compare loop: byte i of each string, until the first difference or a NUL of the first
      string.  It leaves i + 1 in s4 and the two bytes in s9 and s10.
   4. `lbu a0, 0xfa(flags)` where flags is the sanitizer common-flags struct (its address is in a
      GOT cell).  On 0 it skips to step 6.
   5. On non-zero, COMMON_INTERCEPTOR_READ_STRING of each string: `lbu 0xf5(flags)`
      (strict_string_checks) picks the size, strlen + 1 when set and i + 1 when clear; an overflow
      test; size - 1 >= 64 goes to the slow check (__asan_region_is_poisoned); otherwise the quick
      check loads the two aligned 8-byte shadow words holding the shadow bytes of the first and of
      the last byte read, and goes on only when both are 0 (else a byte-exact check and a report).
   6. The result (c2 < c1) - (c1 < c2) (a sign, not the byte difference musl's strcmp returns),
      a call to the weak hook (a bare `ret`), the epilogue.

   THE BYTE AT flags + 0xfa IS intercept_strcmp, NOT strict_string_checks.  Evidence:
   - LLVM compiler-rt's sanitizer_flags.inc declares the common flags as consecutive fields in the
     order ... strict_string_checks, intercept_strstr, intercept_strspn, intercept_strtok,
     intercept_strpbrk, intercept_strcmp, intercept_strlen, intercept_strndup, intercept_strchr ...
     (all bool, one byte each).
   - AsConst.v of this directory names cells of this struct: ACF_STRICT_CELL = flags + 0xf5 (value 0),
     ACF_ISTRSPN_CELL = flags + 0xf7, ACF_ISTRLEN_CELL = flags + 0xfb (value 1), ACF_ISTRCHR_CELL =
     flags + 0xfd (value 1).  In that order flags + 0xf5 .. flags + 0xfd are strict_string_checks,
     intercept_strstr, intercept_strspn, intercept_strtok, intercept_strpbrk, intercept_strcmp,
     intercept_strlen, intercept_strndup, intercept_strchr, so flags + 0xfa is intercept_strcmp.
   - The code agrees: behind the byte at 0xfa it reads 0xf5 and, when that is set, calls strlen to
     size the range, which is COMMON_INTERCEPTOR_READ_STRING, and the strcmp interceptor runs that
     only under `if (common_flags()->intercept_strcmp)`.
   - intercept_strcmp defaults to true.  The struct is in .bss, so every flag is 0 at load, and the
     runtime's init writes the defaults; at a compare __vdsosym makes the byte is 1, so the shadow
     check RUNS on every call.  That is why this contract has shadow premises.

   THE PATH PROVED: asan_inited = 1, intercept_strcmp = 1, strict_string_checks = 0, i < 64, and the
   four shadow words the quick check reads all 0.  [astrcmp_shz] states the last one per string: every
   shadow byte from the aligned word holding the shadow of the string's first byte to the aligned
   word holding the shadow of its NUL reads 0.  The read size is i + 1 with i at most either
   string's length, so both words of each string lie in that span.  [astrcmp_cells] states the
   flag cells and the two pointer cells the code loads.  The frame is 0x7f0 + 0xa0 + 0x10 bytes, the
   last 16 the init test's.

   THE RESULT is a sign; the post states only `r = 0 <-> sx = sy`, which is all __vdsosym reads of it
   (right after each of its two calls it tests a0 with beqz or bnez).

   NAMING: `asegs` is ASegs.v's segment list of this directory's image. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr ZBridge TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------ *)
(* THE ADDRESS BLOCK: every address of the image (echconfiglist_parser.asan-ubsan) this file uses,
   measured from its disassembly and its data.  Nothing else in this file is specific to the
   image.  Call sites in __vdsosym: auipc ra,0xffc3a at 0x56e7ac and 0x56e818, each with a jalr
   to ASTRCMP_THUNK. *)
Definition ASTRCMP_THUNK        : Z := 0x1a8700.  (* `j 0x624`, to ASTRCMP                       *)
Definition ASTRCMP              : Z := 0x1a8d24.  (* entry: addi sp,sp,-0x7f0                    *)
Definition ASTRCMP_LOOP         : Z := 0x1a8d84.  (* loop head: add a0,s2,s4                     *)
Definition ASTRCMP_EXIT         : Z := 0x1a8da0.  (* loop exit: the flag tests                   *)
Definition ASTRCMP_INIT         : Z := 0x1c69a8.  (* the init-once test (jal at 0x1a8d70)        *)
Definition ASTRCMP_HOOK         : Z := 0x1a8d20.  (* the weak hook, a bare `ret` (jal 0x1a8e78)  *)
Definition ASTRCMP_GOT_CFLAGS   : Z := 0x5e7808.  (* GOT cell: &common flags (ld at 0x1a8da4)    *)
Definition ASTRCMP_CFLAGS       : Z := 0x73c428.  (* the common flags struct, in .bss            *)
Definition ASTRCMP_ISTRCMP_CELL : Z := 0x73c522.  (* flags + 0xfa: intercept_strcmp             *)
Definition ASTRCMP_STRICT_CELL  : Z := 0x73c51d.  (* flags + 0xf5: strict_string_checks         *)
Definition ASTRCMP_GOT_SHBASE   : Z := 0x5e7818.  (* GOT cell: &shadow offset (0x1a8dd8, 0x1a8e28) *)
Definition ASTRCMP_SHBASE_CELL  : Z := 0x6aa8f8.  (* the shadow-offset cell                      *)
Definition ASTRCMP_INITED       : Z := 0x6ab5d8.  (* asan_inited (auipc+addi at 0x1c69b4)        *)
Definition ASTRCMP_FRAME        : Z := 2208.      (* 0x7f0 + 0xa0 + 0x10                         *)
(* ------------------------------------------------------------------------------------------ *)

(* The load and store solvers accept a cell only at a small non-negative offset from its base, so
   a far-away literal cell is refused at once instead of being unfolded into a unary offset
   (the same guard N6_tac.v installs). *)
Local Ltac asc_nonneg_lit d := lazymatch (eval vm_compute in (andb (Z.leb 0 d) (Z.leb d 4096))) with true => d end.
Local Ltac addr_diff E A ::=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in let d := eval vm_compute in (c1 - c2)%Z in asc_nonneg_lit d
      | X => let c1 := zlit c1 in asc_nonneg_lit c1
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in asc_nonneg_lit d
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in let d := eval vm_compute in (- c2)%Z in asc_nonneg_lit d
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in let d := eval vm_compute in (e - a)%Z in asc_nonneg_lit d
      end
  end.

Local Notation ZERO8 :=
  [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

(* ---- the loop's mathematics, transcribed from Ref/RStrcmp.v (address-independent) ---- *)

Lemma asc_u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply unsigned_lit.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma asc_u_byte : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. exact asc_u_zxb. Qed.

Lemma asc_list_ext_nth : forall {A} (l l' : list A), (forall n, nth_error l n = nth_error l' n) -> l = l'.
Proof.
  induction l as [|x l IH]; intros [|y l'] H.
  - reflexivity.
  - specialize (H 0%nat). discriminate.
  - specialize (H 0%nat). discriminate.
  - pose proof (H 0%nat) as H0. cbn in H0. inversion H0; subst. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma asc_nth_full : forall (s : list byte) i, (i <= length s)%nat -> exists b, nth_error (s ++ [Z_to_bv 8 0]) i = Some b.
Proof.
  intros s i H. destruct (nth_error (s ++ [Z_to_bv 8 0]) i) as [b|] eqn:E; [eauto|].
  apply nth_error_None in E. rewrite length_app in E. cbn in E. lia.
Qed.

Lemma asc_nth_full_zero : forall (s : list byte) i b, ~ In (Z_to_bv 8 0) s ->
  nth_error (s ++ [Z_to_bv 8 0]) i = Some b -> (i <= length s)%nat ->
  (bv_unsigned b = 0 <-> i = length s).
Proof.
  intros s i b NZ E Hi. destruct (Nat.eq_dec i (length s)) as [->|NE].
  - rewrite nth_error_app2, Nat.sub_diag in E by lia. cbn in E. inversion E; subst. split; reflexivity.
  - rewrite nth_error_app1 in E by lia. split; [|intros; lia]. intros Hb. exfalso. apply NZ.
    replace (Z_to_bv 8 0) with b; [eapply nth_error_In; eauto|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* Where the loop stops, the two bytes agree exactly when the strings do. *)
Lemma asc_prefix : forall (sx sy : list byte), ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  forall k b1 b2, (k <= length sx)%nat -> (k <= length sy)%nat ->
  (forall j, (j < k)%nat -> nth_error (sx ++ [Z_to_bv 8 0]) j = nth_error (sy ++ [Z_to_bv 8 0]) j) ->
  nth_error (sx ++ [Z_to_bv 8 0]) k = Some b1 -> nth_error (sy ++ [Z_to_bv 8 0]) k = Some b2 ->
  (bv_unsigned b1 = 0 \/ bv_unsigned b1 <> bv_unsigned b2) ->
  (bv_unsigned b1 = bv_unsigned b2 <-> sx = sy).
Proof.
  intros sx sy NX NY k b1 b2 Kx Ky P E1 E2 D. split.
  - intros Heq. assert (Z1 : bv_unsigned b1 = 0) by (destruct D; [assumption|contradiction]).
    assert (Z2 : bv_unsigned b2 = 0) by lia.
    apply (asc_nth_full_zero sx k b1 NX E1 Kx) in Z1. apply (asc_nth_full_zero sy k b2 NY E2 Ky) in Z2.
    apply asc_list_ext_nth. intros n. destruct (Nat.lt_ge_cases n k) as [Hn|Hn].
    + specialize (P n Hn). rewrite !nth_error_app1 in P by lia. exact P.
    + rewrite !(proj2 (nth_error_None _ _)) by lia. reflexivity.
  - intros ->. rewrite E1 in E2. inversion E2. reflexivity.
Qed.

(* The interceptor's answer is 0 exactly when the two bytes are equal. *)
Lemma asc_sgn_zero : forall c1 c2 : Z,
  Z_to_bv 64 (Z.b2z (c2 <? c1) - Z.b2z (c1 <? c2)) = Z_to_bv 64 0 <-> c1 = c2.
Proof.
  intros c1 c2.
  destruct (Z.ltb_spec c2 c1) as [H1|H1]; destruct (Z.ltb_spec c1 c2) as [H2|H2]; cbn [Z.b2z];
    split; intros H.
  all: first [ reflexivity | lia | (exfalso; lia)
             | (apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H) ].
Qed.

(* ---- arithmetic of the shadow test ---- *)

Lemma asc_lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x Hx. destruct (Z.eq_dec x 0) as [->|NZ]; [reflexivity|].
  change 18446744073709551615 with (Z.ones 64).
  rewrite <- Z.ldiff_ones_l_low; [| lia | apply Z.log2_lt_pow2; lia].
  rewrite <- Z.sub_nocarry_ldiff.
  - unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity.
  - rewrite Z.ldiff_ones_r_low; [reflexivity | lia | apply Z.log2_lt_pow2; lia].
Qed.

Lemma asc_land_m8 : forall y, 0 <= y < 2^64 -> Z.land y 18446744073709551608 = 8 * (y / 8).
Proof.
  intros y Hy. transitivity (Z.ldiff (Z.land y (Z.ones 64)) (Z.ones 3)).
  - rewrite Z.ldiff_land. rewrite <- Z.land_assoc. f_equal.
  - rewrite Z.land_ones, Z.mod_small by lia. rewrite Z.ldiff_ones_r by lia.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia.
Qed.

(* The quick check's `srli 3; add base` is [sh]. *)
Lemma asc_shr3 : forall c x, c = ASHADOW_BASE -> 0 <= x -> c + Z.shiftr x 3 = sh x.
Proof. intros c x -> Hx. apply sh_shiftr'. exact Hx. Qed.

Lemma asc_shr3' : forall c x, c = ASHADOW_BASE -> 0 <= x -> Z.shiftr x 3 + c = sh x.
Proof. intros c x -> Hx. apply sh_shiftr. exact Hx. Qed.

Lemma asc_sh_range : forall a, 0 <= a < 2^47 -> ASHADOW_BASE <= sh a <= ASHADOW_BASE + 2^44 - 1.
Proof. intros a Ha. unfold sh. Z.div_mod_to_equations. lia. Qed.

(* ---- memory facts in the form the step tactics consume ---- *)

Lemma asc_ro_C1 : forall segs (m : word -> option byte) A b,
  0 <= A < 2^64 -> mrd segs m (wa A) = Some b -> ro_cells segs m A [C1 b].
Proof.
  intros segs m A b HA H. unfold ro_cells, cells_at. split.
  - cbn. split; exact I.
  - unfold bytes_at. split; [lia|]. split; [cbn; lia|].
    intros i Hi. cbn in Hi. destruct i as [|i]; [|lia].
    cbn [nth_error cells_bytes cbytes app]. change (Z.of_nat 0%nat) with 0%Z. rewrite Z.add_0_r. exact H.
Qed.

Lemma asc_read8_zero : forall segs (m : word -> option byte) A, 0 <= A -> A + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> mrd segs m (wa (A + i)) = Some (Z_to_bv 8 0)) ->
  ov_read_bytes segs m (wa A) 8 = Some ZERO8.
Proof.
  intros segs m A H0 H1 H.
  assert (B : bytes_at segs m A ZERO8).
  { unfold bytes_at. split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. rewrite (H (Z.of_nat i)) by lia.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; [reflexivity .. | lia]. }
  pose proof (bytes_at_ov_read segs m A ZERO8 0%nat 8%nat B ltac:(cbn [length]; lia)) as R.
  change (Z.of_nat 0%nat) with 0%Z in R. rewrite Z.add_0_r in R. cbn [firstn skipn] in R. exact R.
Qed.

(* ---- tactics ---- *)

(* A branch whose condition is closed and false. *)
Ltac asc_if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota
  end.
Ltac asc_br_false := first [ if_false | asc_if_lit ].

(* `base + (x >> 3)` to [sh x], and range facts for each [sh x] the goal names. *)
Ltac asc_shr3_all :=
  repeat match goal with
  | |- context [?c + Z.shiftr ?e 3] =>
      rewrite (asc_shr3 c e) by (first [rewrite ASHADOW_BASE_val; reflexivity | reflexivity | lia])
  | |- context [Z.shiftr ?e 3 + ?c] =>
      rewrite (asc_shr3' c e) by (first [rewrite ASHADOW_BASE_val; reflexivity | reflexivity | lia])
  end.
Ltac asc_sh_bounds :=
  repeat match goal with
  | |- context [sh ?e] =>
      lazymatch goal with
      | _ : ASHADOW_BASE <= sh e <= ASHADOW_BASE + 2 ^ 44 - 1 |- _ => fail
      | _ => let R := fresh "RSH" in pose proof (asc_sh_range e ltac:(lia)) as R
      end
  end.
(* `andi -8` of a shadow address. *)
Ltac asc_land8_all :=
  repeat match goal with
  | |- context [Z.land (sh ?e) 18446744073709551608] => rewrite (asc_land_m8 (sh e)) by lia
  end.

Section AsStrcmp.
  Context {HCEIL : HeapCeil}.
  Variable tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Local Notation VS := (asegs ++ tail).

  (* The shadow premise for a string at [x] of [n] non-NUL bytes: every shadow byte from the
     aligned 8-byte word holding [sh x] to the one holding [sh (x + n)] (the NUL's) is in the
     memory or its read-only backing and reads 0.  The quick check reads two such words. *)
  Definition astrcmp_shz (m : mem) (x n : Z) : Prop :=
    0 <= x /\ 0 <= n /\ x + n < AAPP_HI /\
    forall a, 8 * (sh x / 8) <= a < 8 * (sh (x + n) / 8) + 8 -> mrd VS m (wa a) = Some (Z_to_bv 8 0).

  (* The cells the code loads: the two GOT cells, the shadow offset, and the three flag bytes. *)
  Definition astrcmp_cells (m : mem) : Prop :=
    ro_cells VS m ASTRCMP_GOT_CFLAGS [C8 (Z_to_bv 64 ASTRCMP_CFLAGS)]
    /\ ro_cells VS m ASTRCMP_GOT_SHBASE [C8 (Z_to_bv 64 ASTRCMP_SHBASE_CELL)]
    /\ ro_cells VS m ASTRCMP_SHBASE_CELL [C8 (Z_to_bv 64 ASHADOW_BASE)]
    /\ mrd VS m (wa ASTRCMP_INITED) = Some (Z_to_bv 8 1)
    /\ mrd VS m (wa ASTRCMP_ISTRCMP_CELL) = Some (Z_to_bv 8 1)
    /\ mrd VS m (wa ASTRCMP_STRICT_CELL) = Some (Z_to_bv 8 0).

  (* The contract, from a pc that reaches the entry ([astrcmp_contract] is the entry's).
     a1..a4 are written on the path; t0..t6 and a5..a7 are not, so they are stated unchanged. *)
  Definition astrcmp_contract_at (pc : Z) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (sx sy : list byte),
      bytes_at VS m (bv_unsigned a0) (sx ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sx ->
      bytes_at VS m (bv_unsigned a1) (sy ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sy ->
      (length sx < 64 \/ length sy < 64)%nat ->
      astrcmp_shz m (bv_unsigned a0) (Z.of_nat (length sx)) ->
      astrcmp_shz m (bv_unsigned a1) (Z.of_nat (length sy)) ->
      astrcmp_cells m ->
      (bv_unsigned a0 + Z.of_nat (length sx) + 1 <= bv_unsigned sp - ASTRCMP_FRAME \/ bv_unsigned sp <= bv_unsigned a0) ->
      (bv_unsigned a1 + Z.of_nat (length sy) + 1 <= bv_unsigned sp - ASTRCMP_FRAME \/ bv_unsigned sp <= bv_unsigned a1) ->
      stk VS m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASTRCMP_FRAME ->
      mem_inv VS m ->
      evt VS
        (fun ms' => exists (r x11 x12 x13 x14 : word) (m' : mem),
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r x11 x12 x13 x14 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom VS)
           /\ munch [(bv_unsigned sp - ASTRCMP_FRAME, bv_unsigned sp)] m m'
           /\ wmono VS m m' /\ mem_inv VS m' /\ stk VS m' lo (bv_unsigned sp)
           /\ (r = Z_to_bv 64 0 <-> sx = sy))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pc) fc None m (seg_rom VS)).

  Definition astrcmp_contract : Prop := astrcmp_contract_at ASTRCMP.

  (* The shadow premise survives writes above the application's high memory (the frame). *)
  Lemma asc_shz_frame : forall (m m' : mem) x n lo' hi',
    astrcmp_shz m x n -> munch [(lo', hi')] m m' -> AHI_LO <= lo' -> astrcmp_shz m' x n.
  Proof.
    intros m m' x n lo' hi' (H0 & Hn & H1 & H) MU Hlo.
    split; [exact H0|]. split; [exact Hn|]. split; [exact H1|].
    intros a Ha. unfold AHI_LO in Hlo. unfold AAPP_HI in H1. pose proof ASHADOW_BASE_val as HSB.
    pose proof (asc_sh_range x ltac:(lia)) as R0.
    pose proof (asc_sh_range (x + n) ltac:(lia)) as R1.
    assert (D0 : 0 <= sh x / 8) by (apply Z.div_pos; lia).
    pose proof (Z.div_mod (sh (x + n)) 8 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (sh (x + n)) 8 ltac:(lia)) as MB.
    assert (A1 : a < AHI_LO) by (unfold AHI_LO; lia). unfold AHI_LO in A1.
    assert (OUT : outside [(lo', hi')] (bv_unsigned (wa a))).
    { rewrite wa_unsigned by lia. cbn [outside]. split; [lia | exact I]. }
    unfold mrd. rewrite (MU (wa a) OUT). exact (H a Ha).
  Qed.

  (* The aligned shadow word of any byte of the string, its NUL included, reads 0. *)
  Lemma asc_shz_word : forall (m : mem) x n e, astrcmp_shz m x n -> x <= e <= x + n ->
    ov_read_bytes VS m (wa (8 * (sh e / 8))) 8 = Some ZERO8.
  Proof.
    intros m x n e (H0 & Hn & H1 & H) He. unfold AAPP_HI in H1. pose proof ASHADOW_BASE_val as HSB.
    pose proof (sh_mono x e ltac:(lia)) as M1.
    pose proof (sh_mono e (x + n) ltac:(lia)) as M2.
    pose proof (asc_sh_range e ltac:(lia)) as R.
    assert (D1 : sh x / 8 <= sh e / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : sh e / 8 <= sh (x + n) / 8) by (apply Z.div_le_mono; lia).
    assert (D3 : 0 <= sh e / 8) by (apply Z.div_pos; lia).
    assert (D4 : sh e / 8 <= sh e) by (apply Z.div_le_upper_bound; lia).
    apply asc_read8_zero; [lia | lia |].
    intros i Hi. apply H. lia.
  Qed.

  (* The compare loop, from its head with s4 = k to its exit. *)
  Lemma asc_loop : forall (sx sy : list byte) (pa pb : word) (F : bvmap 5 word) (fc : bv 32),
    ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
    forall (n k : nat) (x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19
                        x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (mm : mem),
      (length sx - k = n)%nat -> (k <= length sx)%nat -> (k <= length sy)%nat ->
      (forall j, (j < k)%nat -> nth_error (sx ++ [Z_to_bv 8 0]) j = nth_error (sy ++ [Z_to_bv 8 0]) j) ->
      bytes_at VS mm (bv_unsigned pa) (sx ++ [Z_to_bv 8 0]) ->
      bytes_at VS mm (bv_unsigned pb) (sy ++ [Z_to_bv 8 0]) ->
      evt VS
        (fun ms' => exists (j : nat) (b1 b2 : byte) (x10' : word),
           (j <= length sx)%nat /\ (j <= length sy)%nat /\
           (forall i, (i < j)%nat -> nth_error (sx ++ [Z_to_bv 8 0]) i = nth_error (sy ++ [Z_to_bv 8 0]) i) /\
           nth_error (sx ++ [Z_to_bv 8 0]) j = Some b1 /\ nth_error (sy ++ [Z_to_bv 8 0]) j = Some b2 /\
           (bv_unsigned b1 = 0 \/ bv_unsigned b1 <> bv_unsigned b2) /\
           ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 pb x10' x11 x12 x13 x14 x15 x16 x17 pa x19
                         (Z_to_bv 64 (Z.of_nat j + 1)) x21 x22 x23 x24 (zxb b1) (zxb b2) x27 x28 x29 x30 x31)
                    F (Z_to_bv 64 ASTRCMP_EXIT) fc None mm (seg_rom VS))
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 pb x10 x11 x12 x13 x14 x15 x16 x17 pa x19
                 (Z_to_bv 64 (Z.of_nat k)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 ASTRCMP_LOOP) fc None mm (seg_rom VS)).
  Proof.
    intros sx sy pa pb F fc NX NY n.
    unfold ASTRCMP_LOOP, ASTRCMP_EXIT.
    induction n as [n IH] using lt_wf_ind.
    intros k x1 x2 x3 x4 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19
           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 mm Hn Kx Ky P BX BY.
    destruct (asc_nth_full sx k Kx) as [b1 E1]. destruct (asc_nth_full sy k Ky) as [b2 E2].
    pose proof (u8ro_read VS mm (bv_unsigned pa) (sx ++ [Z_to_bv 8 0]) (Z.of_nat k) b1 _ BX
                  ltac:(rewrite Nat2Z.id; exact E1) ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read VS mm (bv_unsigned pb) (sy ++ [Z_to_bv 8 0]) (Z.of_nat k) b2 _ BY
                  ltac:(rewrite Nat2Z.id; exact E2) ltac:(lia) eq_refl) as RD2.
    pose proof (asc_nth_full_zero sx k b1 NX E1 Kx) as Z1. pose proof (asc_nth_full_zero sy k b2 NY E2 Ky) as Z2.
    (* add a0,s2,s4 ; lbu s9 ; add a0,s1,s4 ; lbu s10 ; addi s4,s4,1 ; beqz s9 *)
    step. step. step. step. step. step.
    if_cases K; zify_cond K; rewrite ?asc_u_zxb, ?asc_u_byte in K.
    - apply evt_done. exists k, b1, b2. eexists.
      split; [exact Kx|]. split; [exact Ky|]. split; [exact P|]. split; [exact E1|]. split; [exact E2|].
      split; [left; lia|]. reflexivity.
    - (* beq s9,s10,loop *)
      step. if_cases K2; zify_cond K2; rewrite ?asc_u_zxb, ?asc_u_byte in K2.
      + assert (Eb : b1 = b2) by (apply bv_eq; lia). subst b2.
        assert (Ix : (k < length sx)%nat) by (destruct (Nat.eq_dec k (length sx)) as [e|e]; [apply Z1 in e; lia | lia]).
        assert (Iy : (k < length sy)%nat) by (destruct (Nat.eq_dec k (length sy)) as [e|e]; [apply Z2 in e; lia | lia]).
        replace (Z.of_nat k + 1) with (Z.of_nat (S k)) by lia.
        apply (IH (length sx - S k)%nat ltac:(lia) (S k)); [lia | lia | lia | | exact BX | exact BY].
        intros j Hj. destruct (Nat.eq_dec j k) as [->|NE]; [rewrite E1, E2; reflexivity | apply P; lia].
      + apply evt_done. exists k, b1, b2. eexists.
        split; [exact Kx|]. split; [exact Ky|]. split; [exact P|]. split; [exact E1|]. split; [exact E2|].
        split; [right; lia|]. reflexivity.
  Qed.

  (* The two shadow words the quick check is about to load. *)
  Ltac asc_hr SZA SZB :=
    repeat match goal with
    | |- context [Z_to_bv 64 (8 * (sh ?e / 8))] =>
        lazymatch goal with
        | _ : ov_read_bytes _ _ (wa (8 * (sh e / 8))) 8%nat = Some _ |- _ => fail
        | _ => let H := fresh "HRZ" in
               first [ pose proof (asc_shz_word _ _ _ e SZA ltac:(lia)) as H
                     | pose proof (asc_shz_word _ _ _ e SZB ltac:(lia)) as H ]
        end
    end.
  Ltac asc_clear_hr := repeat match goal with H : ov_read_bytes _ _ _ 8%nat = Some _ |- _ => clear H end.

  Theorem astrcmp_ok : astrcmp_contract.
  Proof.
    unfold astrcmp_contract, astrcmp_contract_at.
    intros ra sp gp tp t0 t1 t2 s0 s1 pa pb a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo sx sy HX NX HY NY L64 SZX SZY CELLS SEPX SEPY ST CEIL LOB MI.
    acb. pose proof ASHADOW_BASE_val as HSB.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (bv_unsigned_in_range 64 pa) as PAR. unfold bv_modulus in PAR. change (2 ^ Z.of_N 64) with (2^64) in PAR.
    pose proof (bv_unsigned_in_range 64 pb) as PBR. unfold bv_modulus in PBR. change (2 ^ Z.of_N 64) with (2^64) in PBR.
    pose proof SZX as (SX0 & SXn & SX1 & _). pose proof SZY as (SY0 & SYn & SY1 & _).
    unfold AAPP_HI in SX1, SY1.
    destruct CELLS as (CGF & CGS & CSB & FIN & FIC & FST).
    pose proof (asc_ro_C1 _ m ASTRCMP_INITED _ ltac:(unfold ASTRCMP_INITED; lia) FIN) as RIN.
    pose proof (asc_ro_C1 _ m ASTRCMP_ISTRCMP_CELL _ ltac:(unfold ASTRCMP_ISTRCMP_CELL; lia) FIC) as RIC.
    pose proof (asc_ro_C1 _ m ASTRCMP_STRICT_CELL _ ltac:(unfold ASTRCMP_STRICT_CELL; lia) FST) as RSC.
    clear FIN FIC FST.
    unfold ASTRCMP_INITED in RIN. unfold ASTRCMP_ISTRCMP_CELL in RIC. unfold ASTRCMP_STRICT_CELL in RSC.
    unfold ASTRCMP_GOT_CFLAGS, ASTRCMP_CFLAGS in CGF. unfold ASTRCMP_GOT_SHBASE, ASTRCMP_SHBASE_CELL in CGS.
    unfold ASTRCMP_SHBASE_CELL in CSB. rewrite ASHADOW_BASE_val in CSB.
    unfold ASTRCMP_FRAME in *. unfold ASTRCMP.
    pose proof (munch_refl [(bv_unsigned sp - 2208, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl (asegs ++ tail) m) as WM.
    carve_frame 104%nat ST. rename FR into FRS.
    carve_frame 2088%nat ST. rename FR into FRB.
    carve_frame 16%nat ST. rename FR into FRI.
    (* prologue: addi sp ; the 13 saves ; addi s0 ; addi sp ; mv s3,ra ; mv s1,a1 ; mv s2,a0 ; jal init *)
    step. do 13 st1. do 6 step.
    (* the init-once test: addi sp ; sd ra ; sd s0 ; auipc ; addi ; lb ; li a0,1 ; fence ; bne *)
    step. st1. st1. do 5 step.
    step. asc_br_false.
    (* ld ra ; ld s0 ; addi sp ; ret *)
    do 4 step.
    (* beqz a0 on its answer 1 ; mv s4,zero ; addi s11 ; addi s11 *)
    step. asc_br_false.
    do 3 step.
    (* the compare loop *)
    eapply evt_cut.
    { eapply (asc_loop sx sy pa pb F fc NX NY (length sx) 0%nat).
      - lia.
      - lia.
      - lia.
      - intros jj Hj. exfalso. lia.
      - exact HX.
      - exact HY. }
    intros ms' (j & b1 & b2 & x10' & Jx & Jy & P & E1 & E2 & D & ->).
    unfold ASTRCMP_EXIT.
    assert (JL : (j < 64)%nat) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (asc_shz_frame m mm _ _ _ _ SZX MU ltac:(unfold AHI_LO; lia)) as SZXm;
      pose proof (asc_shz_frame m mm _ _ _ _ SZY MU ltac:(unfold AHI_LO; lia)) as SZYm
    end.
    (* auipc ; ld s8 (flags) ; lbu a0,0xfa (intercept_strcmp = 1) ; beqz a0 *)
    zstep. zstep. zstep.
    zstep. asc_br_false.
    (* lbu a1,0xf5 (strict_string_checks = 0) ; addi s5,s4,-1 ; mv s6,s4 ; mv a0,s5 ; bnez a1 *)
    zstep. zstep. zstep. zstep.
    zstep. asc_br_false.
    (* the first string: not a1,s2 ; bltu a1,s6 (overflow) ; li a1,64 ; bgeu a0,a1 (size) *)
    zstep.
    zstep. if_cases K1; zify_cond K1; rewrite ?asc_lxor_ones64 in K1 by lia; [exfalso; lia | clear K1].
    zstep.
    zstep. if_cases K2; zify_cond K2; [exfalso; lia | clear K2].
    (* auipc ; ld ; ld (shadow offset) ; add ; srli ; srli ; add ; add *)
    do 8 zstep. asc_shr3_all. asc_sh_bounds.
    (* andi -8 ; andi -8 ; ld ; ld ; or ; bnez *)
    do 2 zstep. asc_land8_all. asc_hr SZXm SZYm.
    do 3 zstep. asc_clear_hr.
    zstep. asc_br_false.
    (* lbu a0,0xf5 ; bnez a0 ; the second string: not a0,s1 ; bltu a0,s4 ; li a0,64 ; bgeu s5,a0 *)
    zstep.
    zstep. asc_br_false.
    zstep.
    zstep. if_cases K3; zify_cond K3; rewrite ?asc_lxor_ones64 in K3 by lia; [exfalso; lia | clear K3].
    zstep.
    zstep. if_cases K4; zify_cond K4; [exfalso; lia | clear K4].
    do 8 zstep. asc_shr3_all. asc_sh_bounds.
    do 2 zstep. asc_land8_all. asc_hr SZXm SZYm.
    do 3 zstep. asc_clear_hr.
    zstep. asc_br_false.
    (* sltu ; sltu ; sub ; mv a0..a3 ; jal hook ; ret ; mv a0,s4 ; addi sp,0xa0 ; 13 loads ; addi sp ; ret *)
    do 3 zstep.
    do 4 step.
    step. step.
    step. step.
    do 13 step.
    step. step.
    release_frame FRI ST (bv_unsigned sp + -2192).
    release_frame FRB ST (bv_unsigned sp + -104).
    release_frame FRS ST (bv_unsigned sp).
    finish.
    pose proof (asc_prefix sx sy NX NY j b1 b2 Jx Jy P E1 E2 D) as PR.
    pose proof (asc_sgn_zero (bv_unsigned b1) (bv_unsigned b2)) as SG.
    tauto.
  Qed.

  (* The slot __vdsosym's calls reach is one `j` from the entry. *)
  Theorem astrcmp_thunk_ok : astrcmp_contract_at ASTRCMP_THUNK.
  Proof.
    pose proof astrcmp_ok as OK. unfold astrcmp_contract, astrcmp_contract_at, ASTRCMP in OK.
    unfold astrcmp_contract_at, ASTRCMP_THUNK.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo sx sy HX NX HY NY L64 SZX SZY CELLS SEPX SEPY ST CEIL LOB MI.
    step.
    eapply OK; eassumption.
  Qed.

End AsStrcmp.
