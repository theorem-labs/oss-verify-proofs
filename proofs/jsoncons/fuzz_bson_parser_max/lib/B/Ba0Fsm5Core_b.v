(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStack1_b Ba0FakeStackGC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_5dc38_5de44_b Ba0_code_r4dae8_4daec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.


Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].


#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try change (2 ^ 11)%Z with 2048%Z; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wv2 | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.

(* [comment removed for export] *)
Lemma zbv_add : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof. intros x c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma zbv_mod : forall x m, (0 < m)%Z -> (m | 2 ^ 64)%Z -> (bv_unsigned (Z_to_bv 64 x) mod m = x mod m)%Z.
Proof. intros x m Hm D. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. symmetry. apply Znumtheory.Zmod_div_mod; [exact Hm | lia | exact D]. Qed.
Lemma div_8192 : (512 | 2 ^ 64)%Z. Proof. exists (2 ^ 55)%Z. reflexivity. Qed.

Lemma land_mask5 : forall a, Z.land a 511 = (a mod 512)%Z.
Proof. intros a. change 511%Z with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity. Qed.

Section CORE5.
  Variable Mx : word -> option byte.
  Variable rom : word -> option byte.
  Variables s fs h j pos ff : Z.
  Variables ra8 r8 r9 r18 : word.
  Hypothesis Hret : ret_ok ra8.
  Hypothesis Hs : (0x1000000 <= s - 32)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 32 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 512)%Z.
  Hypothesis Hpos_def : pos = ((h + j) mod 512)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 5242880 + 2048 * pos)%Z.
  Hypothesis Hhint : rdn ASEGS Mx (Z_to_bv 64 (fs + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
  Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 31744 + (h + i) mod 512)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z.
  Hypothesis Hflag : rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 31744 + pos)) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hwfs : store_ok ASEGS Mx (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HG : rt_layout_globs Mx.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) 256%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 256 <= s - 32 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 256 <= 0x1374c0 \/ 0x140938 <= SB + ff / 8)%Z.
  Hypothesis Hslots : rdn ASEGS Mx (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra8) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 r8)
                      /\ rdn ASEGS Mx (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 r9) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 r18).

  Definition core5_mem : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mx
      (Z_to_bv 64 (fs + 40)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1))))
      (Z_to_bv 64 (fs + 4096 + 31744 + pos)) [Z_to_bv 8 1])
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (ff + 2040)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 31744 + pos))))
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 136)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 144)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 152)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 160)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 168)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 176)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 192)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 200)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 208)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 216)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 224)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 232)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 240)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 248)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition p5_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 12 = Z_to_bv 64 (h + i) /\ getr rg 10 = Z_to_bv 64 (512 - i) /\ getr rg 13 = Z_to_bv 64 (fs + 4096 + 31744) /\ getr rg 14 = Z_to_bv 64 511.
  Definition p5_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 15%bv -> r <> 17%bv -> r <> 5%bv -> getr regs' r = getr regs r.
  #[local] Ltac kp := intros r N10 N12 N15 N17 N5; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  Lemma probe5_loop : forall (q : nat) regs i,
    p5_inv regs i -> (0 <= i)%Z -> (i + Z.of_nat q = j)%Z ->
    exists regs', msteps ASEGS (mkst regs (0x5e170 : word) Mx rom) (mkst regs' (0x5e170 : word) Mx rom) /\ p5_inv regs' j /\ p5_keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs i (H12 & H10 & H13 & H14) Hi Hq.
    - exists regs. replace j with i by lia. split; [apply mst_refl|]. split; [repeat split; assumption | intros r _ _ _ _ _; reflexivity].
    - destruct (Hprobe i ltac:(lia)) as (b & Fi & Bi). destruct Hfs as (Fs1 & Fs2 & Fs3).
      pose proof (Z.mod_pos_bound (h + i) 512 ltac:(lia)) as Pb.
      assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5e170 : word) Mx rom) (mkst r1 (0x5e170 : word) Mx rom) /\ p5_inv r1 (i + 1) /\ p5_keeps regs r1).
      { eexists. split.
        - stepov F_5dd58 D_5dd58 (Z_to_bv 64 ((h + i) mod 512)) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 511) by lia; rewrite land_mask5, (zbv_mod (h + i) 512 ltac:(lia) div_8192); reflexivity).   (* [comment removed for export] *)
          stepiv F_5dd5c D_5dd5c (Z_to_bv 64 (fs + 4096 + 31744 + (h + i) mod 512)) ltac:(wv2).           (* [comment removed for export] *)
          chain_step; [reflexivity | eapply step_lbu; [exact F_5dd60 | reflexivity | exact D_5dd60
              | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 31744 + (h + i) mod 512)) by (symmetry; wv2) end; exact Fi] | step_simpl; vnorm].   (* [comment removed for export] *)
          stepb_ft F_5dd64 D_5dd64 ltac:(rewrite (u_Z2bv8 b) by lia; cond).                                  (* [comment removed for export] *)
          stepiv F_5dd68 D_5dd68 (Z_to_bv 64 (512 - (i + 1))) ltac:(gres; rwH; unfold v_addiw; imm_norm; unorm; rewrite swrap32_small by lia; f_equal; lia).   (* [comment removed for export] *)
          stepiv F_5dd6c D_5dd6c (Z_to_bv 64 (h + (i + 1))) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                      (* [comment removed for export] *)
          stepb_tk F_5dd70 D_5dd70 ltac:(cond).                                                              (* [comment removed for export] *)
          apply mst_refl.
        - split; [unfold p5_inv; post | kp]. }
      destruct STEP as (r1 & RUN1 & INV1 & KP1).
      destruct (IH r1 (i + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & INV2 & KP2).
      exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|].
      intros r N10 N12 N15 N17 N5. rewrite (KP2 r N10 N12 N15 N17 N5). apply KP1; assumption.
  Qed.
  Theorem fsm5_core_run : forall regs,
    getr regs 9 = Z_to_bv 64 fs -> getr regs 18 = Z_to_bv 64 20 -> getr regs 8 = Z_to_bv 64 s -> getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps ASEGS (mkst regs (0x5e120 : word) Mx rom) (mkst regs' ra8 core5_mem rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra8 /\ getr regs' 8 = r8 /\ getr regs' 9 = r9 /\ getr regs' 18 = r18
      /\ keeps_but [1; 2; 8; 9; 18]%bv regs regs'.
  Proof.
    intros regs H9 H18 H8 H2.
    destruct Hfs as (Fs1 & Fs2 & Fs3).
    pose proof (Z.mod_pos_bound (h + j) 512 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Hffb : (fs + 4096 + 32768 + 2 ^ 20 <= ff /\ ff + 2048 <= fs + 4096 + 32768 + 6300864)%Z) by (rewrite Hff_def; lia).
    assert (Hrb : ret_ok (0x5e228 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 256 < 2 ^ 64)%Z).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
    assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x696000)%Z -> M x = Mx x) -> rt_layout_globs M).
    { intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M Mx) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
      repeat split; assumption. }
    set (N1 := wbytes Mx (Z_to_bv 64 (fs + 40)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))).
    set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 31744 + pos)) [Z_to_bv 8 1]).
    set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
    set (N4 := wbytes N3 (Z_to_bv 64 (ff + 2040)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 31744 + pos)))).
    set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N6 := wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N7 := wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N8 := wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N9 := wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N10 := wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N11 := wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N12 := wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N13 := wbytes N12 (Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N14 := wbytes N13 (Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N15 := wbytes N14 (Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N16 := wbytes N15 (Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N17 := wbytes N16 (Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N18 := wbytes N17 (Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N19 := wbytes N18 (Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N20 := wbytes N19 (Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N21 := wbytes N20 (Z_to_bv 64 (SB + ff / 8 + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N22 := wbytes N21 (Z_to_bv 64 (SB + ff / 8 + 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N23 := wbytes N22 (Z_to_bv 64 (SB + ff / 8 + 144)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N24 := wbytes N23 (Z_to_bv 64 (SB + ff / 8 + 152)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N25 := wbytes N24 (Z_to_bv 64 (SB + ff / 8 + 160)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N26 := wbytes N25 (Z_to_bv 64 (SB + ff / 8 + 168)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N27 := wbytes N26 (Z_to_bv 64 (SB + ff / 8 + 176)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N28 := wbytes N27 (Z_to_bv 64 (SB + ff / 8 + 184)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N29 := wbytes N28 (Z_to_bv 64 (SB + ff / 8 + 192)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N30 := wbytes N29 (Z_to_bv 64 (SB + ff / 8 + 200)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N31 := wbytes N30 (Z_to_bv 64 (SB + ff / 8 + 208)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N32 := wbytes N31 (Z_to_bv 64 (SB + ff / 8 + 216)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N33 := wbytes N32 (Z_to_bv 64 (SB + ff / 8 + 224)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N34 := wbytes N33 (Z_to_bv 64 (SB + ff / 8 + 232)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N35 := wbytes N34 (Z_to_bv 64 (SB + ff / 8 + 240)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N36 := wbytes N35 (Z_to_bv 64 (SB + ff / 8 + 248)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (GN4 : mem_grows Mx N4) by (unfold N4, N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (WFS : forall M (a : Z) (k : nat), mem_grows Mx M -> (fs <= a)%Z -> (a + Z.of_nat k <= fs + 4096 + 32768 + 11 * 2 ^ 20)%Z ->
                  store_ok ASEGS M (Z_to_bv 64 a) k = true).
    { intros M a k HM Ha Hk. apply (store_ok_mono _ _ Mx M _ HM).
      apply (store_ok_sub ASEGS Mx (Z_to_bv 64 fs) _ (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)));
        [unorm; rewrite Z2Nat.id by lia; lia | exact Hwfs | unorm; lia | unorm; rewrite Z2Nat.id by lia; lia]. }
    assert (GLN4 : rt_layout_globs N4).
    { apply GL. intros x Hx. pose proof (u64_range x). unfold N4, N3, N2, N1.
      rewrite !wbytes_below; first [reflexivity | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]. }
    (* [comment removed for export] *)
    assert (SA : exists ra_, msteps ASEGS (mkst regs (0x5e120 : word) Mx rom) (mkst ra_ (0x5e170 : word) Mx rom)
              /\ p5_inv ra_ 0 /\ (getr ra_ 11 = Z_to_bv 64 (fs + 4096) /\ getr ra_ 9 = Z_to_bv 64 fs /\ getr ra_ 18 = Z_to_bv 64 20 /\ getr ra_ 8 = Z_to_bv 64 s
                  /\ getr ra_ 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv regs ra_)).
    { eexists. split.
      - 
        stepiv F_5dd08 D_5dd08 (Z_to_bv 64 9) ltac:(wv2).                                                                             (* [comment removed for export] *)
        stepn F_5dd0c D_5dd0c.                                                                             (* [comment removed for export] *)
        stepn F_5dd10 D_5dd10.                                                                             (* [comment removed for export] *)
        stepn F_5dd14 D_5dd14.                                                                             (* [comment removed for export] *)
        stepb F_5dd18 D_5dd18.                                                                             (* [comment removed for export] *)
        stepn F_5dd1c D_5dd1c.                                                                             (* [comment removed for export] *)
        stepiv F_5dd20 D_5dd20 (Z_to_bv 64 5) ltac:(wv2).                                                                             (* [comment removed for export] *)
        stepn F_5dd24 D_5dd24.                                                                             (* [comment removed for export] *)
        stepn F_5dd28 D_5dd28.                                                                             (* [comment removed for export] *)
        stepn F_5dd2c D_5dd2c.                                                                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_5dd30 | reflexivity | exact D_5dd30
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 40)) by (symmetry; wv2) end; exact Hhint | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepn F_5dd34 D_5dd34.                                                                             (* [comment removed for export] *)
        stepn F_5dd38 D_5dd38.                                                                             (* [comment removed for export] *)
        stepiv F_5dd3c D_5dd3c (Z_to_bv 64 (fs + 4096)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepiv F_5dd40 D_5dd40 (Z_to_bv 64 (fs + 4096 + 31744)) ltac:(wv2).                                (* [comment removed for export] *)
        stepn F_5dd44 D_5dd44.                                                                             (* [comment removed for export] *)
        stepn F_5dd48 D_5dd48.                                                                             (* [comment removed for export] *)
        stepn F_5dd4c D_5dd4c.                                                                             (* [comment removed for export] *)
        stepiv F_5dd50 D_5dd50 (Z_to_bv 64 (h + 511)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepiv F_5dd54 D_5dd54 (Z_to_bv 64 (h + 512)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                         (* [comment removed for export] *)
        apply mst_refl.
      - split; [unfold p5_inv; repeat split; gres; rwH; try reflexivity; f_equal; lia|]. repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
    destruct SA as (ra_ & RUNA & INVA & A11 & A9 & A18 & A8 & A2 & KA).
    (* [comment removed for export] *)
    destruct (probe5_loop (Z.to_nat j) ra_ 0%Z INVA ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (rb & RUNB & (B12 & B10 & B13 & B14) & KB).
    assert (B11 : getr rb 11 = Z_to_bv 64 (fs + 4096)) by (rewrite (KB 11%bv) by (intros X; discriminate X); exact A11).
    assert (B9 : getr rb 9 = Z_to_bv 64 fs) by (rewrite (KB 9%bv) by (intros X; discriminate X); exact A9).
    assert (B18 : getr rb 18 = Z_to_bv 64 20) by (rewrite (KB 18%bv) by (intros X; discriminate X); exact A18).
    assert (B8 : getr rb 8 = Z_to_bv 64 s) by (rewrite (KB 8%bv) by (intros X; discriminate X); exact A8).
    assert (B2 : getr rb 2 = Z_to_bv 64 (s - 32)) by (rewrite (KB 2%bv) by (intros X; discriminate X); exact A2).
    (* [comment removed for export] *)
    assert (SC : exists r3, msteps ASEGS (mkst rb (0x5e170 : word) Mx rom) (mkst r3 (0x5e39c : word) N4 rom)
              /\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
                  /\ getr r3 1 = (0x5e228 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv rb r3)).
    { eexists. split.
      - stepov F_5dd58 D_5dd58 (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 511) by lia; rewrite land_mask5, (zbv_mod (h + j) 512 ltac:(lia) div_8192), <- Hpos_def; reflexivity).   (* [comment removed for export] *)
        stepiv F_5dd5c D_5dd5c (Z_to_bv 64 (fs + 4096 + 31744 + pos)) ltac:(wv2).                          (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_5dd60 | reflexivity | exact D_5dd60
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 31744 + pos)) by (symmetry; wv2) end; exact Hflag] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_5dd64 D_5dd64.                                                                             (* [comment removed for export] *)
        stepiv F_5ddd0 D_5ddd0 (Z_to_bv 64 (h + j + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                        (* [comment removed for export] *)
        stepn F_5ddd4 D_5ddd4.                                                                             (* [comment removed for export] *)
        stepiv F_5ddd8 D_5ddd8 (Z_to_bv 64 15) ltac:(wv2).                                                 (* [comment removed for export] *)
        stepsdq F_5dddc D_5dddc (Z_to_bv 64 (fs + 40)) (Z_to_bv 64 (h + j + 1)) ltac:(apply WFS; [apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes Mx (Z_to_bv 64 (fs + 40)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))) with N1.
        chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 31744 + pos)) (b := Z_to_bv 8 1);
            [exact F_5dde0 | reflexivity | exact D_5dde0 | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
            | apply WFS; [unfold N1; eapply mem_grows_trans; [apply mem_grows_refl | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].   (* [comment removed for export] *)
        change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 31744 + pos)) [Z_to_bv 8 1]) with N2.
        stepn F_5dde4 D_5dde4.                                                                             (* [comment removed for export] *)
        stepn F_5dde8 D_5dde8.                                                                             (* [comment removed for export] *)
        stepiv F_5ddec D_5ddec (Z_to_bv 64 (2048 * pos)) ltac:(wv2).                                     (* [comment removed for export] *)
        stepsv F_5ddf0 D_5ddf0 (Z_to_bv 64 (5 * 2 ^ 20)) ltac:(gres; rwH; rewrite v_sll_lit by lia; reflexivity).   (* [comment removed for export] *)
        stepiv F_5ddf4 D_5ddf4 (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).                                (* [comment removed for export] *)
        stepiv F_5ddf8 D_5ddf8 (Z_to_bv 64 (5242880 + 2048 * pos)) ltac:(wv2).                           (* [comment removed for export] *)
        stepiv F_5ddfc D_5ddfc (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepsd F_5de00 D_5de00 (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
          ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
        stepsd F_5de04 D_5de04 (Z_to_bv 64 (ff + 2040)) (Z_to_bv 64 (fs + 4096 + 31744 + pos))
          ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N3 (Z_to_bv 64 (ff + 2040)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 31744 + pos)))) with N4.
        stepiv F_5de08 D_5de08 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepn F_5de0c D_5de0c.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct SC as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
    destruct (memtoshadow47_run r3 N4 rom (0x5e228 : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
    assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
    assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
    destruct Hshadow_dj as [SD1 SD2]. destruct Hslots as (SL8 & SL16 & SL24 & SL32).
    assert (ESB : SB = 2147450880%Z) by reflexivity.
    assert (SL : forall k v, rdn ASEGS Mx (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> (8 <= k <= 32)%Z ->
                 rdn ASEGS N36 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v R Hk. rewrite (rdn_ext ASEGS 8 N36 Mx); [exact R | unorm; cbn; lia |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
      unfold N36, N35, N34, N33, N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1.
      assert (OUT : forall (m : word -> option byte) (a : Z) (l : list byte), (0 <= a)%Z -> (a + Z.of_nat (length l) < 2 ^ 64)%Z ->
                 (a + Z.of_nat (length l) <= s - 32 \/ s <= a)%Z -> wbytes m (Z_to_bv 64 a) l x = m x).
      { intros m a l Ha Hl Hd. destruct Hd as [Hd|Hd].
        - apply wbytes_above. unorm. lia.
        - apply wbytes_below; unorm; lia. }
      rewrite !OUT by (first [rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; lia | lia]). reflexivity. }
    eexists. split.
    - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      stepiv F_5de10 D_5de10 (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_5de14 D_5de14 (Z_to_bv 64 ff) ltac:(wv2).
      stepn F_5de18 D_5de18.
      stepsd F_5de1c D_5de1c (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
      stepsd F_5de20 D_5de20 (Z_to_bv 64 (SB + ff / 8 + 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N5; do 1 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N6.
      stepsd F_5de24 D_5de24 (Z_to_bv 64 (SB + ff / 8 + 16)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N6, N5; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N7.
      stepsd F_5de28 D_5de28 (Z_to_bv 64 (SB + ff / 8 + 24)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N7, N6, N5; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N8.
      stepsd F_5de2c D_5de2c (Z_to_bv 64 (SB + ff / 8 + 32)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N8, N7, N6, N5; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N9.
      stepsd F_5de30 D_5de30 (Z_to_bv 64 (SB + ff / 8 + 40)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N9, N8, N7, N6, N5; do 5 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N10.
      stepsd F_5de34 D_5de34 (Z_to_bv 64 (SB + ff / 8 + 48)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N10, N9, N8, N7, N6, N5; do 6 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N11.
      stepsd F_5de38 D_5de38 (Z_to_bv 64 (SB + ff / 8 + 56)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N11, N10, N9, N8, N7, N6, N5; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N12.
      stepsd F_5de3c D_5de3c (Z_to_bv 64 (SB + ff / 8 + 64)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N12, N11, N10, N9, N8, N7, N6, N5; do 8 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N12 (Z_to_bv 64 (SB + ff / 8 + 64)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N13.
      stepsd F_5de40 D_5de40 (Z_to_bv 64 (SB + ff / 8 + 72)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N13, N12, N11, N10, N9, N8, N7, N6, N5; do 9 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N13 (Z_to_bv 64 (SB + ff / 8 + 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N14.
      stepsd F_5de44 D_5de44 (Z_to_bv 64 (SB + ff / 8 + 80)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 10 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N14 (Z_to_bv 64 (SB + ff / 8 + 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N15.
      stepsd F_5de48 D_5de48 (Z_to_bv 64 (SB + ff / 8 + 88)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 11 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N15 (Z_to_bv 64 (SB + ff / 8 + 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N16.
      stepsd F_5de4c D_5de4c (Z_to_bv 64 (SB + ff / 8 + 96)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 12 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N16 (Z_to_bv 64 (SB + ff / 8 + 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N17.
      stepsd F_5de50 D_5de50 (Z_to_bv 64 (SB + ff / 8 + 104)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 13 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N17 (Z_to_bv 64 (SB + ff / 8 + 104)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N18.
      stepsd F_5de54 D_5de54 (Z_to_bv 64 (SB + ff / 8 + 112)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 14 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N18 (Z_to_bv 64 (SB + ff / 8 + 112)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N19.
      stepsd F_5de58 D_5de58 (Z_to_bv 64 (SB + ff / 8 + 120)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 15 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N19 (Z_to_bv 64 (SB + ff / 8 + 120)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N20.
      stepsd F_5de5c D_5de5c (Z_to_bv 64 (SB + ff / 8 + 128)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 16 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N20 (Z_to_bv 64 (SB + ff / 8 + 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N21.
      stepsd F_5de60 D_5de60 (Z_to_bv 64 (SB + ff / 8 + 136)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 17 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N21 (Z_to_bv 64 (SB + ff / 8 + 136)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N22.
      stepsd F_5de64 D_5de64 (Z_to_bv 64 (SB + ff / 8 + 144)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 18 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N22 (Z_to_bv 64 (SB + ff / 8 + 144)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N23.
      stepsd F_5de68 D_5de68 (Z_to_bv 64 (SB + ff / 8 + 152)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 19 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N23 (Z_to_bv 64 (SB + ff / 8 + 152)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N24.
      stepsd F_5de6c D_5de6c (Z_to_bv 64 (SB + ff / 8 + 160)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 20 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N24 (Z_to_bv 64 (SB + ff / 8 + 160)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N25.
      stepsd F_5de70 D_5de70 (Z_to_bv 64 (SB + ff / 8 + 168)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 21 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N25 (Z_to_bv 64 (SB + ff / 8 + 168)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N26.
      stepsd F_5de74 D_5de74 (Z_to_bv 64 (SB + ff / 8 + 176)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 22 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N26 (Z_to_bv 64 (SB + ff / 8 + 176)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N27.
      stepsd F_5de78 D_5de78 (Z_to_bv 64 (SB + ff / 8 + 184)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 23 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N27 (Z_to_bv 64 (SB + ff / 8 + 184)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N28.
      stepsd F_5de7c D_5de7c (Z_to_bv 64 (SB + ff / 8 + 192)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 24 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N28 (Z_to_bv 64 (SB + ff / 8 + 192)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N29.
      stepsd F_5de80 D_5de80 (Z_to_bv 64 (SB + ff / 8 + 200)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 25 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N29 (Z_to_bv 64 (SB + ff / 8 + 200)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N30.
      stepsd F_5de84 D_5de84 (Z_to_bv 64 (SB + ff / 8 + 208)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 26 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N30 (Z_to_bv 64 (SB + ff / 8 + 208)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N31.
      stepsd F_5de88 D_5de88 (Z_to_bv 64 (SB + ff / 8 + 216)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 27 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N31 (Z_to_bv 64 (SB + ff / 8 + 216)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N32.
      stepsd F_5de8c D_5de8c (Z_to_bv 64 (SB + ff / 8 + 224)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 28 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N32 (Z_to_bv 64 (SB + ff / 8 + 224)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N33.
      stepsd F_5de90 D_5de90 (Z_to_bv 64 (SB + ff / 8 + 232)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N33, N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 29 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N33 (Z_to_bv 64 (SB + ff / 8 + 232)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N34.
      stepsd F_5de94 D_5de94 (Z_to_bv 64 (SB + ff / 8 + 240)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N34, N33, N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 30 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N34 (Z_to_bv 64 (SB + ff / 8 + 240)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N35.
      stepsd F_5de98 D_5de98 (Z_to_bv 64 (SB + ff / 8 + 248)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N35, N34, N33, N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5; do 31 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 256%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N35 (Z_to_bv 64 (SB + ff / 8 + 248)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N36.
      stepld F_5de9c D_5de9c ra8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact SL8 | lia]).
      stepld F_5dea0 D_5dea0 r8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact SL16 | lia]).
      stepld F_5dea4 D_5dea4 r9 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact SL24 | lia]).
      stepld F_5dea8 D_5dea8 r18 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact SL32 | lia]).
      stepiv F_5deac D_5deac (Z_to_bv 64 s) ltac:(wv2).
      stepret F_5deb0 D_5deb0 ra8 ltac:(rwH; reflexivity).
      unfold N36, N35, N34, N33, N32, N31, N30, N29, N28, N27, N26, N25, N24, N23, N22, N21, N20, N19, N18, N17, N16, N15, N14, N13, N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1. fold core5_mem.
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      assert (KBB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
      { eapply keeps_but_trans; [exact KA|]. eapply keeps_but_trans; [|eapply keeps_but_trans; [exact K3 | apply keeps_but_cs; exact K4]].
        intros r Hcs Hn. apply KB; intros ->; cbv in Hcs; clear - Hcs; intuition discriminate. }
      intros r Hcs Hn. repeat (rewrite getr_other; [| intros ->; first [cbv in Hn; clear - Hn; intuition congruence | cbv in Hcs; clear - Hcs; intuition discriminate]]).
      apply KBB; assumption.
  Qed.
End CORE5.
End FPX_1.
