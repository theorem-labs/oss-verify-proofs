(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStack1_b Ba0FakeStackGC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r5d100_5d274_b Ba0_code_r4dae8_4daec_b.
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
  try change (2 ^ 6)%Z with 64%Z; first [reflexivity | f_equal; lia].

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
Lemma div_16384 : (16384 | 2 ^ 64)%Z. Proof. exists (2 ^ 50)%Z. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_mask0 : forall a, Z.land a 16383 = (a mod 16384)%Z.
Proof. intros a. change 16383%Z with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.

Section CORE0.
  Variable Mx : word -> option byte.
  Variable rom : word -> option byte.
  Variables s fs h j pos ff : Z.
  Variables ra8 r8 r9 r18 : word.
  Hypothesis Hret : ret_ok ra8.
  Hypothesis Hs : (0x1000000 <= s - 32)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 32 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 16384)%Z.
  Hypothesis Hpos_def : pos = ((h + j) mod 16384)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 0 + 64 * pos)%Z.
  Hypothesis Hhint : rdn ASEGS Mx (Z_to_bv 64 (fs + 0)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
  Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 0 + (h + i) mod 16384)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z.
  Hypothesis Hflag : rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 0 + pos)) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hwfs : store_ok ASEGS Mx (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HG : rt_layout_globs Mx.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) 8%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 8 <= s - 32 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 8 <= 0x1374c0 \/ 0x140938 <= SB + ff / 8)%Z.
  Hypothesis Hslots : rdn ASEGS Mx (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra8) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 r8)
                      /\ rdn ASEGS Mx (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 r9) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 r18).

  Definition core0_mem : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes Mx
      (Z_to_bv 64 (fs + 0)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1))))
      (Z_to_bv 64 (fs + 4096 + 0 + pos)) [Z_to_bv 8 1])
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (ff + 56)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 0 + pos))))
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition p0_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 12 = Z_to_bv 64 (h + i) /\ getr rg 10 = Z_to_bv 64 (16384 - i) /\ getr rg 11 = Z_to_bv 64 (fs + 4096 + 0) /\ getr rg 13 = Z_to_bv 64 16383.
  Definition p0_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r.
  #[local] Ltac kp := intros r N10 N12 N15 N16 N17; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  Lemma probe0_loop : forall (q : nat) regs i,
    p0_inv regs i -> (0 <= i)%Z -> (i + Z.of_nat q = j)%Z ->
    exists regs', msteps ASEGS (mkst regs (0x5dcb0 : word) Mx rom) (mkst regs' (0x5dcb0 : word) Mx rom) /\ p0_inv regs' j /\ p0_keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs i (H12 & H10 & H11 & H13) Hi Hq.
    - exists regs. replace j with i by lia. split; [apply mst_refl|]. split; [repeat split; assumption | intros r _ _ _ _ _; reflexivity].
    - destruct (Hprobe i ltac:(lia)) as (b & Fi & Bi). destruct Hfs as (Fs1 & Fs2 & Fs3).
      pose proof (Z.mod_pos_bound (h + i) 16384 ltac:(lia)) as Pb.
      assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5dcb0 : word) Mx rom) (mkst r1 (0x5dcb0 : word) Mx rom) /\ p0_inv r1 (i + 1) /\ p0_keeps regs r1).
      { eexists. split.
        - stepov F_5d898 D_5d898 (Z_to_bv 64 ((h + i) mod 16384)) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 16383) by lia; rewrite land_mask0, (zbv_mod (h + i) 16384 ltac:(lia) div_16384); reflexivity).   (* [comment removed for export] *)
          stepiv F_5d89c D_5d89c (Z_to_bv 64 (fs + 4096 + 0 + (h + i) mod 16384)) ltac:(wv2).           (* [comment removed for export] *)
          chain_step; [reflexivity | eapply step_lbu; [exact F_5d8a0 | reflexivity | exact D_5d8a0
              | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 0 + (h + i) mod 16384)) by (symmetry; wv2) end; exact Fi] | step_simpl; vnorm].   (* [comment removed for export] *)
          stepb_ft F_5d8a4 D_5d8a4 ltac:(rewrite (u_Z2bv8 b) by lia; cond).                                  (* [comment removed for export] *)
          stepiv F_5d8a8 D_5d8a8 (Z_to_bv 64 (16384 - (i + 1))) ltac:(gres; rwH; unfold v_addiw; imm_norm; unorm; rewrite swrap32_small by lia; f_equal; lia).   (* [comment removed for export] *)
          stepiv F_5d8ac D_5d8ac (Z_to_bv 64 (h + (i + 1))) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                      (* [comment removed for export] *)
          stepb_tk F_5d8b0 D_5d8b0 ltac:(cond).                                                              (* [comment removed for export] *)
          apply mst_refl.
        - split; [unfold p0_inv; post | kp]. }
      destruct STEP as (r1 & RUN1 & INV1 & KP1).
      destruct (IH r1 (i + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & INV2 & KP2).
      exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|].
      intros r N10 N12 N15 N16 N17. rewrite (KP2 r N10 N12 N15 N16 N17). apply KP1; assumption.
  Qed.
  Theorem fsm0_core_run : forall regs,
    getr regs 9 = Z_to_bv 64 fs -> getr regs 18 = Z_to_bv 64 20 -> getr regs 8 = Z_to_bv 64 s -> getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps ASEGS (mkst regs (0x5dc70 : word) Mx rom) (mkst regs' ra8 core0_mem rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra8 /\ getr regs' 8 = r8 /\ getr regs' 9 = r9 /\ getr regs' 18 = r18
      /\ keeps_but [1; 2; 8; 9; 18]%bv regs regs'.
  Proof.
    intros regs H9 H18 H8 H2.
    destruct Hfs as (Fs1 & Fs2 & Fs3).
    pose proof (Z.mod_pos_bound (h + j) 16384 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Hffb : (fs + 4096 + 32768 <= ff /\ ff + 64 <= fs + 4096 + 32768 + 2 ^ 20)%Z) by (rewrite Hff_def; lia).
    assert (Hrb : ret_ok (0x5dd5c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 8 < 2 ^ 64)%Z).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
    assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x696000)%Z -> M x = Mx x) -> rt_layout_globs M).
    { intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M Mx) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
      repeat split; assumption. }
    set (N1 := wbytes Mx (Z_to_bv 64 (fs + 0)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))).
    set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 0 + pos)) [Z_to_bv 8 1]).
    set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
    set (N4 := wbytes N3 (Z_to_bv 64 (ff + 56)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 0 + pos)))).
    set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
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
    assert (SA : exists ra_, msteps ASEGS (mkst regs (0x5dc70 : word) Mx rom) (mkst ra_ (0x5dcb0 : word) Mx rom)
              /\ p0_inv ra_ 0 /\ (getr ra_ 9 = Z_to_bv 64 fs /\ getr ra_ 18 = Z_to_bv 64 20 /\ getr ra_ 8 = Z_to_bv 64 s
                  /\ getr ra_ 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv regs ra_)).
    { eexists. split.
      - stepiv F_5d858 D_5d858 (Z_to_bv 64 14) ltac:(wv2).                                               (* [comment removed for export] *)
        stepn F_5d85c D_5d85c.                                                                             (* [comment removed for export] *)
        stepn F_5d860 D_5d860.                                                                             (* [comment removed for export] *)
        stepn F_5d864 D_5d864.                                                                             (* [comment removed for export] *)
        stepb F_5d868 D_5d868.                                                                             (* [comment removed for export] *)
        stepn F_5d86c D_5d86c.                                                                             (* [comment removed for export] *)
        stepn F_5d870 D_5d870.                                                                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_5d874 | reflexivity | exact D_5d874
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 0)) by (symmetry; wv2) end; exact Hhint | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepn F_5d878 D_5d878.                                                                             (* [comment removed for export] *)
        stepn F_5d87c D_5d87c.                                                                             (* [comment removed for export] *)
        stepiv F_5d880 D_5d880 (Z_to_bv 64 (fs + 4096)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepn F_5d884 D_5d884.                                                                             (* [comment removed for export] *)
        stepn F_5d888 D_5d888.                                                                             (* [comment removed for export] *)
        stepn F_5d88c D_5d88c.                                                                             (* [comment removed for export] *)
        stepiv F_5d890 D_5d890 (Z_to_bv 64 (h + 16383)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepiv F_5d894 D_5d894 (Z_to_bv 64 (h + 16384)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).   (* [comment removed for export] *)
        apply mst_refl.
      - split; [unfold p0_inv; repeat split; gres; rwH; try reflexivity; f_equal; lia|]. repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
    destruct SA as (ra_ & RUNA & INVA & A9 & A18 & A8 & A2 & KA).
    (* [comment removed for export] *)
    destruct (probe0_loop (Z.to_nat j) ra_ 0%Z INVA ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (rb & RUNB & (B12 & B10 & B11 & B13) & KB).
    assert (B9 : getr rb 9 = Z_to_bv 64 fs) by (rewrite (KB 9%bv) by (intros X; discriminate X); exact A9).
    assert (B18 : getr rb 18 = Z_to_bv 64 20) by (rewrite (KB 18%bv) by (intros X; discriminate X); exact A18).
    assert (B8 : getr rb 8 = Z_to_bv 64 s) by (rewrite (KB 8%bv) by (intros X; discriminate X); exact A8).
    assert (B2 : getr rb 2 = Z_to_bv 64 (s - 32)) by (rewrite (KB 2%bv) by (intros X; discriminate X); exact A2).
    (* [comment removed for export] *)
    assert (SC : exists r3, msteps ASEGS (mkst rb (0x5dcb0 : word) Mx rom) (mkst r3 (0x5e39c : word) N4 rom)
              /\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
                  /\ getr r3 1 = (0x5dd5c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv rb r3)).
    { eexists. split.
      - stepov F_5d898 D_5d898 (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 16383) by lia; rewrite land_mask0, (zbv_mod (h + j) 16384 ltac:(lia) div_16384), <- Hpos_def; reflexivity).   (* [comment removed for export] *)
        stepiv F_5d89c D_5d89c (Z_to_bv 64 (fs + 4096 + 0 + pos)) ltac:(wv2).                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_5d8a0 | reflexivity | exact D_5d8a0
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 0 + pos)) by (symmetry; wv2) end; exact Hflag] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_5d8a4 D_5d8a4.                                                                             (* [comment removed for export] *)
        stepiv F_5d910 D_5d910 (Z_to_bv 64 (h + j + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).   (* [comment removed for export] *)
        stepn F_5d914 D_5d914.                                                                             (* [comment removed for export] *)
        stepiv F_5d918 D_5d918 (Z_to_bv 64 15) ltac:(wv2).                                                 (* [comment removed for export] *)
        stepiv F_5d91c D_5d91c (Z_to_bv 64 (64 * pos)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepsdq F_5d920 D_5d920 (Z_to_bv 64 (fs + 0)) (Z_to_bv 64 (h + j + 1)) ltac:(apply WFS; [apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes Mx (Z_to_bv 64 (fs + 0)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))) with N1.
        chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 0 + pos)) (b := Z_to_bv 8 1);
            [exact F_5d924 | reflexivity | exact D_5d924 | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
            | apply WFS; [unfold N1; eapply mem_grows_trans; [apply mem_grows_refl | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].   (* [comment removed for export] *)
        change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 0 + pos)) [Z_to_bv 8 1]) with N2.
        stepn F_5d928 D_5d928.                                                                             (* [comment removed for export] *)
        stepiv F_5d92c D_5d92c (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).                                (* [comment removed for export] *)
        stepiv F_5d930 D_5d930 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepsd F_5d934 D_5d934 (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
          ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
        stepsd F_5d938 D_5d938 (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (fs + 4096 + 0 + pos))
          ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N3 (Z_to_bv 64 (ff + 56)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 0 + pos)))) with N4.
        stepiv F_5d93c D_5d93c (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepn F_5d940 D_5d940.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct SC as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
    destruct (memtoshadow47_run r3 N4 rom (0x5dd5c : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
    assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
    assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
    destruct Hshadow_dj as [SD1 SD2]. destruct Hslots as (SL8 & SL16 & SL24 & SL32).
    assert (ESB : SB = 2147450880%Z) by reflexivity.
    assert (SL : forall k v, rdn ASEGS Mx (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> (8 <= k <= 32)%Z ->
                 rdn ASEGS N5 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v R Hk. rewrite (rdn_ext ASEGS 8 N5 Mx); [exact R | unorm; cbn; lia |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
      unfold N5, N4, N3, N2, N1.
      assert (OUT : forall (m : word -> option byte) (a : Z) (l : list byte), (0 <= a)%Z -> (a + Z.of_nat (length l) < 2 ^ 64)%Z ->
                 (a + Z.of_nat (length l) <= s - 32 \/ s <= a)%Z -> wbytes m (Z_to_bv 64 a) l x = m x).
      { intros m a l Ha Hl Hd. destruct Hd as [Hd|Hd].
        - apply wbytes_above. unorm. lia.
        - apply wbytes_below; unorm; lia. }
      rewrite !OUT by (first [rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; lia | lia]). reflexivity. }
    eexists. split.
    - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      stepiv F_5d944 D_5d944 (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_5d948 D_5d948 (Z_to_bv 64 ff) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepn F_5d94c D_5d94c.                                                                              (* [comment removed for export] *)
      stepsd F_5d950 D_5d950 (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 8%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
      change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
      stepld F_5d954 D_5d954 ra8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact SL8 | lia]).        (* [comment removed for export] *)
      stepld F_5d958 D_5d958 r8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact SL16 | lia]).
      stepld F_5d95c D_5d95c r9 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact SL24 | lia]).
      stepld F_5d960 D_5d960 r18 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact SL32 | lia]).
      stepiv F_5d964 D_5d964 (Z_to_bv 64 s) ltac:(wv2).                                                 (* [comment removed for export] *)
      stepret F_5d968 D_5d968 ra8 ltac:(rwH; reflexivity).
      unfold N5, N4, N3, N2, N1. fold core0_mem.
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      assert (KBB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
      { eapply keeps_but_trans; [exact KA|]. eapply keeps_but_trans; [|eapply keeps_but_trans; [exact K3 | apply keeps_but_cs; exact K4]].
        intros r Hcs Hn. apply KB; intros ->; cbv in Hcs; clear - Hcs; intuition discriminate. }
      intros r Hcs Hn. repeat (rewrite getr_other; [| intros ->; first [cbv in Hn; clear - Hn; intuition congruence | cbv in Hcs; clear - Hcs; intuition discriminate]]).
      apply KBB; assumption.
  Qed.
End CORE0.
End FPX_1.
