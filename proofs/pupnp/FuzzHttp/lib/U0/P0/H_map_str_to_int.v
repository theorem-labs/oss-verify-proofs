(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_strncmp F_strlen F_ctype H_memptr_cmp.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Definition map_str_to_int_entry := 0x173d8%Z.
Ltac sstep := step; fix_lit_store.
Ltac mst_lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Definition mst_al8 (x : Z) : Prop := (x mod 8 = 0)%Z.
Definition mst_pos (x : Z) : Prop := (0 < x)%Z.

Definition table_strings (ws : list word) (ne B : Z) : Prop :=
  forall i, (0 <= i < ne)%Z -> exists S str slack,
    nth_error ws (Z.to_nat (2 * i)) = Some (Z_to_bv 64 S)
    /\ (forall m, mem_inv rsegs m -> bytes_at rsegs m S (str ++ Z_to_bv 8 0 :: slack)) /\ ~ In (Z_to_bv 8 0) str
    /\ ((- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z
    /\ (S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= B)%Z.

Lemma srliw_half : forall x, (0 <= x < 2^31)%Z -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 1) = (x / 2)%Z.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2^32)%Z. change (bv_half_modulus 32) with (2^31)%Z.
  rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma mst_sdiv2_half : forall x, (0 <= x < 2^31)%Z ->
  bv_swrap 32 (Z.shiftr (bv_swrap 32 ((x + bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 31)) mod 18446744073709551616)%Z) 1) = (x / 2)%Z.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2^32)%Z. change (bv_half_modulus 32) with (2^31)%Z.
  rewrite (Z.mod_small x (2^32)) by lia. rewrite (Z.shiftr_div_pow2 x 31) by lia. rewrite (Z.div_small x (2^31)) by lia.
  change ((0 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31)%Z with 0%Z. rewrite Z.add_0_r. rewrite (Z.mod_small x) by lia.
  rewrite (Z.mod_small (x + 2^31)) by lia. replace (x + 2 ^ 31 - 2 ^ 31)%Z with x by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1)%Z with 2%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma mst_slti_neg0 : forall x, (0 <= x < 2^31)%Z ->
  (Z.lxor (bv_swrap 32 (x + 0) mod 18446744073709551616) 9223372036854775808 <? 9223372036854775807)%Z = false.
Proof.
  intros x Hx. rewrite Z.add_0_r, swrap32_id by lia. rewrite Z.mod_small by lia.
  change 9223372036854775808%Z with (2^63)%Z. rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia.
Qed.

Definition map_str_to_int_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ne : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - 144) (bv_unsigned sp)
    /\ (r = -1 \/ 0 <= r < ne)%Z.

Definition map_str_to_int_stmt : Prop :=
  forall (T n TAB ne cs : Z) (tok : list byte) (ws : list word)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bytes_at rsegs m T tok -> (Z.of_nat (length tok) >= n)%Z -> (1 <= n < 2^63)%Z ->
  u64arr rsegs m TAB ws -> Z.of_nat (length ws) = (2 * ne)%Z -> (1 <= ne <= 33)%Z ->
  table_strings ws ne (bv_unsigned sp - 144) ->
  stk rsegs m (bv_unsigned sp - 144) (bv_unsigned sp) -> (256 <= bv_unsigned sp)%Z ->
  (T + Z.of_nat (length tok) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= T)%Z ->
  (TAB + 16 * ne <= bv_unsigned sp - 144 \/ bv_unsigned sp <= TAB)%Z ->
  (0 < TAB)%Z -> (TAB mod 8 = 0)%Z -> (bv_unsigned sp mod 8 = 0)%Z ->
  mem_inv rsegs m -> (0 <= cs < 2^64)%Z ->
  a0 = wz T -> a1 = wz n -> a2 = wz TAB -> a3 = wz ne -> a4 = wz cs ->
  evt rsegs (map_str_to_int_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ne m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz map_str_to_int_entry) fc None m (seg_rom rsegs)).

Section WALK.
Context {HCEIL : HasCeiling}.
  Hypothesis strncasecmp_spec : strncasecmp_stmt.
  Variables (T n TAB ne : Z) (tok : list byte) (ws : list word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis SPR : (256 <= bv_unsigned sp /\ bv_unsigned sp < 2^64)%Z.
  Hypothesis TL : (Z.of_nat (length tok) >= n)%Z.
  Hypothesis N1 : (1 <= n < 2^63)%Z.
  Hypothesis LEN : Z.of_nat (length ws) = (2 * ne)%Z.
  Hypothesis NE : (1 <= ne <= 33)%Z.
  Hypothesis SEPT : (T + Z.of_nat (length tok) <= bv_unsigned sp - 144 \/ bv_unsigned sp <= T)%Z.
  Hypothesis SEPA : (TAB + 16 * ne <= bv_unsigned sp - 144 \/ bv_unsigned sp <= TAB)%Z.
  Hypothesis TS : table_strings ws ne (bv_unsigned sp - 144).
  Hypothesis TAB0 : mst_pos TAB.
  Hypothesis TABAL : mst_al8 TAB.
  Hypothesis SP8 : mst_al8 (bv_unsigned sp).

  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Notation POST := (map_str_to_int_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ne m0).

  Notation LST pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 bot top x20 x28 x29 x30 x31 mm :=
    (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 TAB) (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 bot) (Z_to_bv 64 top) x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Definition linv (m : mem) : Prop :=
    rw_cells rsegs m (bv_unsigned sp + -64) [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 n); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ stk rsegs m (bv_unsigned sp - 144) (bv_unsigned sp + -64)
    /\ bytes_at rsegs m T tok /\ u64arr rsegs m TAB ws
    /\ mem_inv rsegs m /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m0 m /\ wmono rsegs m0 m.

  #[using="Type"] Lemma exit_ok : forall (r : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 m,
    linv m -> (r = -1 \/ 0 <= r < ne)%Z ->
    evt rsegs POST
      (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 TAB) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x17508) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros (FR & ST & TOK & ARR & MI & MU & WM) HR.
    step. step. step. step. step. step. step. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  #[using="SPR TL N1 LEN NE SEPT SEPA TS TAB0 TABAL SP8"] Lemma loopA : forall (k : nat) (top bot : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m,
    (bot - top < Z.of_nat k)%Z -> (0 <= top <= bot)%Z -> (bot < ne)%Z ->
    linv m ->
    evt rsegs POST (LST 0x17428 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 bot top x20 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK TB BN (FR & ST & TOK & ARR & MI & MU & WM); [lia|].
    pose proof (proj1 (bytes_at_bound _ _ _ _ (proj1 ARR))) as TB0. pose proof (bytes_at_bound _ _ _ _ TOK) as TKB.
    pose proof TAB0 as TAB0'. pose proof TABAL as TABAL'. pose proof SP8 as SP8'. unfold mst_pos, mst_al8 in TAB0', TABAL', SP8'.
    zstep. zstep. rewrite swrap32_id by lia. step. ubr.
    zstep. zstep. zstep. rewrite mst_sdiv2_half by lia. set (mid := ((top + bot) / 2)%Z).
    assert (MR : (top <= mid <= bot)%Z) by (subst mid; split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
    clearbody mid.
    zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4)%Z with 16%Z.
    pose proof (bytes_at_bound _ _ _ _ (proj1 ARR)) as TBB. rewrite u64s_length in TBB.
    step. let KU := fresh "KU" in if_cases KU; zify_cond KU; [exfalso; rewrite ?Z.mod_small in KU by lia; lia| try clear KU].
    zstep. zstep. zstep. zstep. zstep.
    rewrite mst_slti_neg0 by lia.
    replace (TAB + mid * 16 <? mid * 16)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1)%Z with 1%Z.
    step. mst_lit_branch.
    zstep. step. ubr_by ltac:(clear - KU TABAL'; Z.div_mod_to_equations; lia).
    destruct (TS mid ltac:(lia)) as (S & str & slack & HN & STRm & NONUL & PAD & SB).
    pose proof (STRm m MI) as STR. pose proof (bytes_at_bound _ _ _ _ STR) as STB. rewrite length_app in STB. cbn [length] in STB.
    pose proof (u64arr_read rsegs m TAB ws (2 * mid) (Z_to_bv 64 S) (Z_to_bv 64 (TAB + mid * 16)) ARR HN ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep.

    destruct (proj1 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 n)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) FR) as [FR1 FR2].
    cbn [cells_size csize Nat.add] in FR2. replace (bv_unsigned sp + -64 + Z.of_nat 16)%Z with (bv_unsigned sp + -48)%Z in FR2 by lia.
    clear FR. destruct (stk_split rsegs _ _ (bv_unsigned sp + -64 - 32)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    call (memptr_cmp_call (bv_unsigned sp + -64)%Z T n S tok str slack (bv_unsigned sp + -64)%Z).
    all: side (rewrite ?unsigned_lit by lia; first [exact FR1 | exact TOK | exact STR | exact NONUL | exact PAD | exact SThi | exact MI | reflexivity | lia]).
    clear RD STR. rename PC into SThi. rename MI0 into MI.
    match goal with |- context [Z_to_bv 64 ?r] => idtac end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (LI : linv mm) end.
    { split; [| split; [| split; [exact TOK| split; [exact ARR| split; [exact MI| split; [exact MU| exact WM]]]]]].
      - apply (proj2 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 n)] _)). split; [exact FR1|].
        cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -64 + Z.of_nat 16)%Z with (bv_unsigned sp + -48)%Z by lia. exact FR2.
      - eapply stk_merge; [exact STlo| exact SThi| lia]. }
    clear FR1 FR2 STlo SThi TOK ARR MU WM.
    zstep. if_cases K1; zify_cond K1.
    -
      zstep. rewrite swrap32_id by lia. zstep. if_cases K3; zify_cond K3; rewrite !signed_lit in K3 by lia.
      +   apply exit_ok; [exact LI| lia].
      + eapply (IH (mid + 1)%Z bot); [lia| lia| lia| exact LI].
    - zstep. if_cases K4; zify_cond K4.
      +
        zstep. apply exit_ok; [exact LI| lia].
      +
        zstep. rewrite swrap32_id by lia. zstep. if_cases K5; zify_cond K5; rewrite !signed_lit in K5 by lia.
        * eapply (IH top (mid - 1)%Z); [lia| lia| lia| exact LI].
        * zstep. apply exit_ok; [exact LI| lia].
  Qed.

  #[using="strncasecmp_spec SPR TL N1 LEN NE SEPT SEPA TS TAB0 TABAL SP8"] Lemma loopB : forall (k : nat) (top bot : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 m,
    (bot - top < Z.of_nat k)%Z -> (0 <= top <= bot)%Z -> (bot < ne)%Z ->
    linv m ->
    evt rsegs POST (LST 0x174a0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 bot top x20 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros until m; intros HK TB BN (FR & ST & TOK & ARR & MI & MU & WM); [lia|].
    pose proof (proj1 (bytes_at_bound _ _ _ _ (proj1 ARR))) as TB0. pose proof (bytes_at_bound _ _ _ _ TOK) as TKB.
    pose proof TAB0 as TAB0'. pose proof TABAL as TABAL'. pose proof SP8 as SP8'. unfold mst_pos, mst_al8 in TAB0', TABAL', SP8'.
    zstep. zstep. rewrite swrap32_id by lia. step. ubr.
    zstep. zstep. zstep. rewrite mst_sdiv2_half by lia. set (mid := ((top + bot) / 2)%Z).
    assert (MR : (top <= mid <= bot)%Z) by (subst mid; split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
    clearbody mid.
    zstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4)%Z with 16%Z.
    pose proof (bytes_at_bound _ _ _ _ (proj1 ARR)) as TBB. rewrite u64s_length in TBB.
    step. let KU := fresh "KU" in if_cases KU; zify_cond KU; [exfalso; rewrite ?Z.mod_small in KU by lia; lia| try clear KU].
    zstep. zstep. zstep. zstep. zstep.
    rewrite mst_slti_neg0 by lia.
    replace (TAB + mid * 16 <? mid * 16)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1)%Z with 1%Z.
    step. mst_lit_branch.
    zstep. step. ubr_by ltac:(clear - KU TABAL'; Z.div_mod_to_equations; lia).
    destruct (TS mid ltac:(lia)) as (S & str & slack & HN & STRm & NONUL & PAD & SB).
    pose proof (STRm m MI) as STR. pose proof (bytes_at_bound _ _ _ _ STR) as STB. rewrite length_app in STB. cbn [length] in STB.
    pose proof (u64arr_read rsegs m TAB ws (2 * mid) (Z_to_bv 64 S) (Z_to_bv 64 (TAB + mid * 16)) ARR HN ltac:(lia)
                  ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. zstep.
    destruct (proj1 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 n)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) FR) as [FR1 FR2].
    cbn [cells_size csize Nat.add] in FR2. replace (bv_unsigned sp + -64 + Z.of_nat 16)%Z with (bv_unsigned sp + -48)%Z in FR2 by lia.
    clear FR. replace (bv_unsigned sp - 144)%Z with (bv_unsigned sp + -64 - 80)%Z in ST by lia.
    call (memptr_cmp_nocase_call strncasecmp_spec (bv_unsigned sp + -64)%Z T n S tok str slack (bv_unsigned sp + -64)%Z).
    all: side (rewrite ?unsigned_lit by lia; first [exact FR1 | exact TOK | exact STR | exact NONUL | exact PAD | exact ST | exact MI | reflexivity | lia]).
    clear RD STR. rename PC into ST. rename MI0 into MI.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (LI : linv mm) end.
    { split; [| split; [| split; [exact TOK| split; [exact ARR| split; [exact MI| split; [exact MU| exact WM]]]]]].
      - apply (proj2 (rw_cells_app rsegs _ _ [C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 n)] _)). split; [exact FR1|].
        cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -64 + Z.of_nat 16)%Z with (bv_unsigned sp + -48)%Z by lia. exact FR2.
      - replace (bv_unsigned sp + -64 - 80)%Z with (bv_unsigned sp - 144)%Z in ST by lia. exact ST. }
    clear FR1 FR2 ST TOK ARR MU WM.
    zstep. if_cases K1; zify_cond K1.
    - zstep. rewrite swrap32_id by lia. zstep. if_cases K3; zify_cond K3; rewrite !signed_lit in K3 by lia.
      + apply exit_ok; [exact LI| lia].
      + eapply (IH (mid + 1)%Z bot); [lia| lia| lia| exact LI].
    - zstep. if_cases K4; zify_cond K4.
      + zstep. apply exit_ok; [exact LI| lia].
      + zstep. rewrite swrap32_id by lia. zstep. if_cases K5; zify_cond K5; rewrite !signed_lit in K5 by lia.
        * eapply (IH top (mid - 1)%Z); [lia| lia| lia| exact LI].
        * zstep. apply exit_ok; [exact LI| lia].
  Qed.

  #[using="strncasecmp_spec SPR TL N1 LEN NE SEPT SEPA TS TAB0 TABAL SP8"] Lemma body : forall (cs : Z) t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    bytes_at rsegs m0 T tok -> u64arr rsegs m0 TAB ws ->
    stk rsegs m0 (bv_unsigned sp - 144) (bv_unsigned sp) -> mem_inv rsegs m0 -> (0 <= cs < 2^64)%Z ->
    evt rsegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 n) (Z_to_bv 64 TAB) (Z_to_bv 64 ne) (Z_to_bv 64 cs) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 map_str_to_int_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until t6. intros TOK ARR ST MI CS. unfold map_str_to_int_entry.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    pose proof (proj1 (bytes_at_bound _ _ _ _ (proj1 ARR))) as TB0. pose proof (bytes_at_bound _ _ _ _ TOK) as TKB.
    pose proof TAB0 as TAB0'. unfold mst_pos in TAB0'.
    destruct (stk_split rsegs _ _ (bv_unsigned sp + -64)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    carve_frame 64%nat SThi.
    sstep. sstep. sstep. sstep. sstep. sstep. sstep.
    zstep. rewrite swrap32_id by lia.
    sstep. sstep.
    step. ubr_by ltac:(rewrite ?signed_lit in KU by lia; lia).
    zstep.
    zstep. if_cases Kb; zify_cond Kb. { exfalso. rewrite ?signed_lit in Kb by lia. lia. }
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (LI : linv mm) end.
    { split; [exact FR| split; [| split; [exact TOK| split; [exact ARR| split; [exact MI| split; [exact MU| exact WM]]]]]].
      eapply stk_merge; [exact STlo| exact SThi| lia]. }
    pose proof (bytes_at_bound _ _ _ _ (proj1 ARR)) as TBB. rewrite u64s_length in TBB.
    zstep. if_cases Kc; zify_cond Kc.
    - step. let KU := fresh "KU" in if_cases KU; zify_cond KU; [exfalso; rewrite ?Z.mod_small in KU by lia; lia| try clear KU].
      zstep. zstep. eapply (loopB (S (Z.to_nat ne)) 0 (ne - 1)); [lia| lia| lia| exact LI].
    - step. let KU := fresh "KU" in if_cases KU; zify_cond KU; [exfalso; rewrite ?Z.mod_small in KU by lia; lia| try clear KU].
      zstep. zstep. eapply (loopA (S (Z.to_nat ne)) 0 (ne - 1)); [lia| lia| lia| exact LI].
  Qed.
End WALK.

Lemma map_str_to_int_spec : strncasecmp_stmt -> map_str_to_int_stmt.
Proof.
  intros SC. unfold map_str_to_int_stmt. intros until m. intros TOK TL N1 ARR LEN NE TS ST SPR SEPT SEPA TAB0 TABAL SP8 MI CS -> -> -> -> ->.
  eapply body; eauto; try (unfold mst_pos, mst_al8; assumption). pose proof (word_lt64 sp). lia.
Qed.

