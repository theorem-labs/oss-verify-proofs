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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b Ba0FakeStack1_b Ba0FakeStack3_b Ba0FakeStackGC_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r4dae8_4daec_b.
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
  try change (2 ^ 9)%Z with 512%Z; first [reflexivity | f_equal; lia].

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
Lemma div_8192 : (2048 | 2 ^ 64)%Z. Proof. exists (2 ^ 53)%Z. reflexivity. Qed.

Section CORE3.
  Variable Mx : word -> option byte.
  Variable rom : word -> option byte.
  Variables s fs h j pos ff : Z.
  Variables ra8 r8 r9 r18 : word.
  Hypothesis Hret : ret_ok ra8.
  Hypothesis Hs : (0x1000000 <= s - 32)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 32 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 64)%Z.
  Hypothesis Hj : (0 <= j < 2048)%Z.
  Hypothesis Hpos_def : pos = ((h + j) mod 2048)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 3145728 + 512 * pos)%Z.
  Hypothesis Hhint : rdn ASEGS Mx (Z_to_bv 64 (fs + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)).
  Hypothesis Hprobe : forall i, (0 <= i < j)%Z -> exists b, rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 28672 + (h + i) mod 2048)) 1%nat = Some [Z_to_bv 8 b] /\ (0 < b < 256)%Z.
  Hypothesis Hflag : rdn ASEGS Mx (Z_to_bv 64 (fs + 4096 + 28672 + pos)) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis Hwfs : store_ok ASEGS Mx (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.
  Hypothesis HG : rt_layout_globs Mx.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) 64%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 64 <= s - 32 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 64 <= 0x1374c0 \/ 0x140938 <= SB + ff / 8)%Z.
  Hypothesis Hslots : rdn ASEGS Mx (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra8) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 r8)
                      /\ rdn ASEGS Mx (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 r9) /\ rdn ASEGS Mx (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 r18).

  Definition core3_mem : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mx
      (Z_to_bv 64 (fs + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1))))
      (Z_to_bv 64 (fs + 4096 + 28672 + pos)) [Z_to_bv 8 1])
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))
      (Z_to_bv 64 (ff + 504)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 28672 + pos))))
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Definition p3_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 12 = Z_to_bv 64 (h + i) /\ getr rg 10 = Z_to_bv 64 (2048 - i) /\ getr rg 13 = Z_to_bv 64 (fs + 4096 + 28672) /\ getr rg 14 = Z_to_bv 64 2047.
  Definition p3_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 15%bv -> r <> 17%bv -> r <> 5%bv -> getr regs' r = getr regs r.
  #[local] Ltac kp := intros r N10 N12 N15 N17 N5; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

  Lemma probe3_loop : forall (q : nat) regs i,
    p3_inv regs i -> (0 <= i)%Z -> (i + Z.of_nat q = j)%Z ->
    exists regs', msteps ASEGS (mkst regs (0x5dfc4 : word) Mx rom) (mkst regs' (0x5dfc4 : word) Mx rom) /\ p3_inv regs' j /\ p3_keeps regs regs'.
  Proof.
    induction q as [|q IH]; intros regs i (H12 & H10 & H13 & H14) Hi Hq.
    - exists regs. replace j with i by lia. split; [apply mst_refl|]. split; [repeat split; assumption | intros r _ _ _ _ _; reflexivity].
    - destruct (Hprobe i ltac:(lia)) as (b & Fi & Bi). destruct Hfs as (Fs1 & Fs2 & Fs3).
      pose proof (Z.mod_pos_bound (h + i) 2048 ltac:(lia)) as Pb.
      assert (STEP : exists r1, msteps ASEGS (mkst regs (0x5dfc4 : word) Mx rom) (mkst r1 (0x5dfc4 : word) Mx rom) /\ p3_inv r1 (i + 1) /\ p3_keeps regs r1).
      { eexists. split.
        - stepov F_5dbac D_5dbac (Z_to_bv 64 ((h + i) mod 2048)) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 2047) by lia; rewrite land_mask3, (zbv_mod (h + i) 2048 ltac:(lia) div_8192); reflexivity).   (* [comment removed for export] *)
          stepiv F_5dbb0 D_5dbb0 (Z_to_bv 64 (fs + 4096 + 28672 + (h + i) mod 2048)) ltac:(wv2).           (* [comment removed for export] *)
          chain_step; [reflexivity | eapply step_lbu; [exact F_5dbb4 | reflexivity | exact D_5dbb4
              | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 28672 + (h + i) mod 2048)) by (symmetry; wv2) end; exact Fi] | step_simpl; vnorm].   (* [comment removed for export] *)
          stepb_ft F_5dbb8 D_5dbb8 ltac:(rewrite (u_Z2bv8 b) by lia; cond).                                  (* [comment removed for export] *)
          stepiv F_5dbbc D_5dbbc (Z_to_bv 64 (2048 - (i + 1))) ltac:(gres; rwH; unfold v_addiw; imm_norm; unorm; rewrite swrap32_small by lia; f_equal; lia).   (* [comment removed for export] *)
          stepiv F_5dbc0 D_5dbc0 (Z_to_bv 64 (h + (i + 1))) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                      (* [comment removed for export] *)
          stepb_tk F_5dbc4 D_5dbc4 ltac:(cond).                                                              (* [comment removed for export] *)
          apply mst_refl.
        - split; [unfold p3_inv; post | kp]. }
      destruct STEP as (r1 & RUN1 & INV1 & KP1).
      destruct (IH r1 (i + 1)%Z INV1 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & INV2 & KP2).
      exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact INV2|].
      intros r N10 N12 N15 N17 N5. rewrite (KP2 r N10 N12 N15 N17 N5). apply KP1; assumption.
  Qed.
  Theorem fsm3_core_run : forall regs,
    getr regs 9 = Z_to_bv 64 fs -> getr regs 18 = Z_to_bv 64 20 -> getr regs 8 = Z_to_bv 64 s -> getr regs 2 = Z_to_bv 64 (s - 32) ->
    exists regs',
      msteps ASEGS (mkst regs (0x5df74 : word) Mx rom) (mkst regs' ra8 core3_mem rom)
      /\ getr regs' 10 = Z_to_bv 64 ff /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ra8 /\ getr regs' 8 = r8 /\ getr regs' 9 = r9 /\ getr regs' 18 = r18
      /\ keeps_but [1; 2; 8; 9; 18]%bv regs regs'.
  Proof.
    intros regs H9 H18 H8 H2.
    destruct Hfs as (Fs1 & Fs2 & Fs3).
    pose proof (Z.mod_pos_bound (h + j) 2048 ltac:(lia)) as Hposb. rewrite <- Hpos_def in Hposb.
    assert (Hffb : (fs + 4096 + 32768 + 2 ^ 20 <= ff /\ ff + 512 <= fs + 4096 + 32768 + 4194304)%Z) by (rewrite Hff_def; lia).
    assert (Hrb : ret_ok (0x5e07c : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
    assert (SBb : (0 <= SB + ff / 8 /\ SB + ff / 8 + 64 < 2 ^ 64)%Z).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND, SB in *. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      assert (ff / 8 <= 2 ^ 47 / 8)%Z by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8)%Z with 17592186044416%Z in H. lia. }
    assert (GL : forall M, (forall x : word, (bv_unsigned x < 0x696000)%Z -> M x = Mx x) -> rt_layout_globs M).
    { intros M HM. destruct HG as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8). unfold rt_layout_globs.
      rewrite !(rdn_ext ASEGS _ M Mx) by (first [cbn [Z.of_nat Pos.to_nat]; imm_norm; lia | intros x Hx; apply HM; revert Hx; cbn [Z.of_nat Pos.to_nat]; imm_norm; intros Hx; lia]).
      repeat split; assumption. }
    set (N1 := wbytes Mx (Z_to_bv 64 (fs + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))).
    set (N2 := wbytes N1 (Z_to_bv 64 (fs + 4096 + 28672 + pos)) [Z_to_bv 8 1]).
    set (N3 := wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))).
    set (N4 := wbytes N3 (Z_to_bv 64 (ff + 504)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 28672 + pos)))).
    set (N5 := wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N6 := wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N7 := wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N8 := wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N9 := wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N10 := wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N11 := wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    set (N12 := wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
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
    assert (SA : exists ra_, msteps ASEGS (mkst regs (0x5df74 : word) Mx rom) (mkst ra_ (0x5dfc4 : word) Mx rom)
              /\ p3_inv ra_ 0 /\ (getr ra_ 11 = Z_to_bv 64 (fs + 4096) /\ getr ra_ 9 = Z_to_bv 64 fs /\ getr ra_ 18 = Z_to_bv 64 20 /\ getr ra_ 8 = Z_to_bv 64 s
                  /\ getr ra_ 2 = Z_to_bv 64 (s - 32) /\ keeps_but [1; 2; 8; 9; 18]%bv regs ra_)).
    { eexists. split.
      - 
        stepiv F_5db5c D_5db5c (Z_to_bv 64 11) ltac:(wv2).                                                                             (* [comment removed for export] *)
        stepn F_5db60 D_5db60.                                                                             (* [comment removed for export] *)
        stepn F_5db64 D_5db64.                                                                             (* [comment removed for export] *)
        stepn F_5db68 D_5db68.                                                                             (* [comment removed for export] *)
        stepb F_5db6c D_5db6c.                                                                             (* [comment removed for export] *)
        stepn F_5db70 D_5db70.                                                                             (* [comment removed for export] *)
        stepiv F_5db74 D_5db74 (Z_to_bv 64 5) ltac:(wv2).                                                                             (* [comment removed for export] *)
        stepn F_5db78 D_5db78.                                                                             (* [comment removed for export] *)
        stepn F_5db7c D_5db7c.                                                                             (* [comment removed for export] *)
        stepn F_5db80 D_5db80.                                                                             (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F_5db84 | reflexivity | exact D_5db84
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 24)) by (symmetry; wv2) end; exact Hhint | exact (bytes_le_to_Z_8 _)] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepn F_5db88 D_5db88.                                                                             (* [comment removed for export] *)
        stepn F_5db8c D_5db8c.                                                                             (* [comment removed for export] *)
        stepiv F_5db90 D_5db90 (Z_to_bv 64 (fs + 4096)) ltac:(wv2).                                        (* [comment removed for export] *)
        stepiv F_5db94 D_5db94 (Z_to_bv 64 (fs + 4096 + 28672)) ltac:(wv2).                                (* [comment removed for export] *)
        stepn F_5db98 D_5db98.                                                                             (* [comment removed for export] *)
        stepn F_5db9c D_5db9c.                                                                             (* [comment removed for export] *)
        stepn F_5dba0 D_5dba0.                                                                             (* [comment removed for export] *)
        stepiv F_5dba4 D_5dba4 (Z_to_bv 64 (h + 2047)) ltac:(wv2).                                         (* [comment removed for export] *)
        stepiv F_5dba8 D_5dba8 (Z_to_bv 64 (h + 2048)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                         (* [comment removed for export] *)
        apply mst_refl.
      - split; [unfold p3_inv; repeat split; gres; rwH; try reflexivity; f_equal; lia|]. repeat split; gres; rwH; try reflexivity. solve_keeps_but. }
    destruct SA as (ra_ & RUNA & INVA & A11 & A9 & A18 & A8 & A2 & KA).
    (* [comment removed for export] *)
    destruct (probe3_loop (Z.to_nat j) ra_ 0%Z INVA ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (rb & RUNB & (B12 & B10 & B13 & B14) & KB).
    assert (B11 : getr rb 11 = Z_to_bv 64 (fs + 4096)) by (rewrite (KB 11%bv) by (intros X; discriminate X); exact A11).
    assert (B9 : getr rb 9 = Z_to_bv 64 fs) by (rewrite (KB 9%bv) by (intros X; discriminate X); exact A9).
    assert (B18 : getr rb 18 = Z_to_bv 64 20) by (rewrite (KB 18%bv) by (intros X; discriminate X); exact A18).
    assert (B8 : getr rb 8 = Z_to_bv 64 s) by (rewrite (KB 8%bv) by (intros X; discriminate X); exact A8).
    assert (B2 : getr rb 2 = Z_to_bv 64 (s - 32)) by (rewrite (KB 2%bv) by (intros X; discriminate X); exact A2).
    (* [comment removed for export] *)
    assert (SC : exists r3, msteps ASEGS (mkst rb (0x5dfc4 : word) Mx rom) (mkst r3 (0x5e39c : word) N4 rom)
              /\ (getr r3 10 = Z_to_bv 64 ff /\ getr r3 9 = Z_to_bv 64 ff /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 32)
                  /\ getr r3 1 = (0x5e07c : word) /\ keeps_but [1; 2; 8; 9; 18]%bv rb r3)).
    { eexists. split.
      - stepov F_5dbac D_5dbac (Z_to_bv 64 pos) ltac:(gres; rwH; unfold v_and; imm_norm; rewrite (u_Z2bv 2047) by lia; rewrite land_mask3, (zbv_mod (h + j) 2048 ltac:(lia) div_8192), <- Hpos_def; reflexivity).   (* [comment removed for export] *)
        stepiv F_5dbb0 D_5dbb0 (Z_to_bv 64 (fs + 4096 + 28672 + pos)) ltac:(wv2).                          (* [comment removed for export] *)
        chain_step; [reflexivity | eapply step_lbu; [exact F_5dbb4 | reflexivity | exact D_5dbb4
            | match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (fs + 4096 + 28672 + pos)) by (symmetry; wv2) end; exact Hflag] | step_simpl; vnorm].   (* [comment removed for export] *)
        stepb F_5dbb8 D_5dbb8.                                                                             (* [comment removed for export] *)
        stepiv F_5dc24 D_5dc24 (Z_to_bv 64 (h + j + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; rewrite zbv_add; f_equal; lia).                                        (* [comment removed for export] *)
        stepn F_5dc28 D_5dc28.                                                                             (* [comment removed for export] *)
        stepiv F_5dc2c D_5dc2c (Z_to_bv 64 15) ltac:(wv2).                                                 (* [comment removed for export] *)
        stepsdq F_5dc30 D_5dc30 (Z_to_bv 64 (fs + 24)) (Z_to_bv 64 (h + j + 1)) ltac:(apply WFS; [apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes Mx (Z_to_bv 64 (fs + 24)) (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))) with N1.
        chain_step; [reflexivity | eapply (step_sb_at ASEGS) with (a := Z_to_bv 64 (fs + 4096 + 28672 + pos)) (b := Z_to_bv 8 1);
            [exact F_5dc34 | reflexivity | exact D_5dc34 | wv2 | gres; reflexivity | apply bv_eq; vm_compute; reflexivity
            | apply WFS; [unfold N1; eapply mem_grows_trans; [apply mem_grows_refl | apply wbytes_grows] | lia | cbn [Z.of_nat Pos.to_nat]; lia] ] | step_simpl; vnorm].   (* [comment removed for export] *)
        change (wbytes N1 (Z_to_bv 64 (fs + 4096 + 28672 + pos)) [Z_to_bv 8 1]) with N2.
        stepn F_5dc38 D_5dc38.                                                                             (* [comment removed for export] *)
        stepn F_5dc3c D_5dc3c.                                                                             (* [comment removed for export] *)
        stepiv F_5dc40 D_5dc40 (Z_to_bv 64 (512 * pos)) ltac:(wv2).                                     (* [comment removed for export] *)
        stepsv F_5dc44 D_5dc44 (Z_to_bv 64 (3 * 2 ^ 20)) ltac:(gres; rwH; rewrite v_sll_lit by lia; reflexivity).   (* [comment removed for export] *)
        stepiv F_5dc48 D_5dc48 (Z_to_bv 64 (fs + 4096 + 32768)) ltac:(wv2).                                (* [comment removed for export] *)
        stepiv F_5dc4c D_5dc4c (Z_to_bv 64 (3145728 + 512 * pos)) ltac:(wv2).                           (* [comment removed for export] *)
        stepiv F_5dc50 D_5dc50 (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepsd F_5dc54 D_5dc54 (Z_to_bv 64 (ff + 24)) (Z_to_bv 64 s)
          ltac:(apply WFS; [unfold N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N2 (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with N3.
        stepsd F_5dc58 D_5dc58 (Z_to_bv 64 (ff + 504)) (Z_to_bv 64 (fs + 4096 + 28672 + pos))
          ltac:(apply WFS; [unfold N3, N2, N1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn [Z.of_nat Pos.to_nat]; lia]).   (* [comment removed for export] *)
        change (wbytes N3 (Z_to_bv 64 (ff + 504)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 28672 + pos)))) with N4.
        stepiv F_5dc5c D_5dc5c (Z_to_bv 64 ff) ltac:(wv2).                                                (* [comment removed for export] *)
        stepn F_5dc60 D_5dc60.                                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct SC as (r3 & RUN3 & U10 & U9 & U8 & U2 & U1 & K3).
    destruct (memtoshadow47_run r3 N4 rom (0x5e07c : word) ff GLN4 Happ U10 U1 Hrb) as (r4 & RUN4 & V10 & K4).
    assert (V9 : getr r4 9 = Z_to_bv 64 ff) by (rewrite (K4 9%bv) by (cbv; tauto); exact U9).
    assert (V8 : getr r4 8 = Z_to_bv 64 s) by (rewrite (K4 8%bv) by (cbv; tauto); exact U8).
    assert (V2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (cbv; tauto); exact U2).
    destruct Hshadow_dj as [SD1 SD2]. destruct Hslots as (SL8 & SL16 & SL24 & SL32).
    assert (ESB : SB = 2147450880%Z) by reflexivity.
    assert (SL : forall k v, rdn ASEGS Mx (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> (8 <= k <= 32)%Z ->
                 rdn ASEGS N12 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v R Hk. rewrite (rdn_ext ASEGS 8 N12 Mx); [exact R | unorm; cbn; lia |].
      intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. pose proof (u64_range x).
      unfold N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1.
      assert (OUT : forall (m : word -> option byte) (a : Z) (l : list byte), (0 <= a)%Z -> (a + Z.of_nat (length l) < 2 ^ 64)%Z ->
                 (a + Z.of_nat (length l) <= s - 32 \/ s <= a)%Z -> wbytes m (Z_to_bv 64 a) l x = m x).
      { intros m a l Ha Hl Hd. destruct Hd as [Hd|Hd].
        - apply wbytes_above. unorm. lia.
        - apply wbytes_below; unorm; lia. }
      rewrite !OUT by (first [rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; lia | lia]). reflexivity. }
    eexists. split.
    - eapply msteps_trans; [exact RUNA|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      stepiv F_5dc64 D_5dc64 (Z_to_bv 64 (SB + ff / 8)) ltac:(gres; rwH; unfold v_addi; imm_norm; unorm; f_equal; lia).   (* [comment removed for export] *)
      stepiv F_5dc68 D_5dc68 (Z_to_bv 64 ff) ltac:(wv2).
      stepn F_5dc6c D_5dc6c.
      stepsd F_5dc70 D_5dc70 (Z_to_bv 64 (SB + ff / 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N4 (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N5.
      stepsd F_5dc74 D_5dc74 (Z_to_bv 64 (SB + ff / 8 + 8)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N5; do 1 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N5 (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N6.
      stepsd F_5dc78 D_5dc78 (Z_to_bv 64 (SB + ff / 8 + 16)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N6, N5; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N6 (Z_to_bv 64 (SB + ff / 8 + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N7.
      stepsd F_5dc7c D_5dc7c (Z_to_bv 64 (SB + ff / 8 + 24)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N7, N6, N5; do 3 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N7 (Z_to_bv 64 (SB + ff / 8 + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N8.
      stepsd F_5dc80 D_5dc80 (Z_to_bv 64 (SB + ff / 8 + 32)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N8, N7, N6, N5; do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N8 (Z_to_bv 64 (SB + ff / 8 + 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N9.
      stepsd F_5dc84 D_5dc84 (Z_to_bv 64 (SB + ff / 8 + 40)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N9, N8, N7, N6, N5; do 5 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N9 (Z_to_bv 64 (SB + ff / 8 + 40)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N10.
      stepsd F_5dc88 D_5dc88 (Z_to_bv 64 (SB + ff / 8 + 48)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N10, N9, N8, N7, N6, N5; do 6 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N10 (Z_to_bv 64 (SB + ff / 8 + 48)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N11.
      stepsd F_5dc8c D_5dc8c (Z_to_bv 64 (SB + ff / 8 + 56)) (Z_to_bv 64 0)
        ltac:(apply (store_ok_mono _ _ Mx); [unfold N11, N10, N9, N8, N7, N6, N5; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GN4|]; apply (store_ok_sub ASEGS Mx (Z_to_bv 64 (SB + ff / 8)) _ 64%nat); [unorm; cbn; lia | exact Hshadow_ok | unorm; lia | unorm; cbn; lia]).
      change (wbytes N11 (Z_to_bv 64 (SB + ff / 8 + 56)) (word_to_le_bytes 8 (Z_to_bv 64 0))) with N12.
      stepld F_5dc90 D_5dc90 ra8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact SL8 | lia]).
      stepld F_5dc94 D_5dc94 r8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact SL16 | lia]).
      stepld F_5dc98 D_5dc98 r9 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact SL24 | lia]).
      stepld F_5dc9c D_5dc9c r18 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact SL32 | lia]).
      stepiv F_5dca0 D_5dca0 (Z_to_bv 64 s) ltac:(wv2).
      stepret F_5dca4 D_5dca4 ra8 ltac:(rwH; reflexivity).
      unfold N12, N11, N10, N9, N8, N7, N6, N5, N4, N3, N2, N1. fold core3_mem.
      apply mst_refl.
    - split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
      assert (KBB : keeps_but [1; 2; 8; 9; 18]%bv regs r4).
      { eapply keeps_but_trans; [exact KA|]. eapply keeps_but_trans; [|eapply keeps_but_trans; [exact K3 | apply keeps_but_cs; exact K4]].
        intros r Hcs Hn. apply KB; intros ->; cbv in Hcs; clear - Hcs; intuition discriminate. }
      intros r Hcs Hn. repeat (rewrite getr_other; [| intros ->; first [cbv in Hn; clear - Hn; intuition congruence | cbv in Hcs; clear - Hcs; intuition discriminate]]).
      apply KBB; assumption.
  Qed.
End CORE3.
End FPX_1.
