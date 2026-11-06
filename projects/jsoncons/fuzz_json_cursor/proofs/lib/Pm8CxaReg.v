(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib ArtMem Pm8RegionPoisoned Pm8AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_133000_134000 Pm8_code_145000_146000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Definition CXA_AX : Z := 0x6b0aa0%Z.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  first [reflexivity | f_equal; lia].
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wv2 | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].

Section REG.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s f arg n : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 48)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M0 (Z_to_bv 64 (s - 48)) 48%nat = true.
  Hypothesis Hn : (0 < n < 32)%Z.
  Hypothesis Hf : (0 <= f < 2 ^ 64)%Z.
  Hypothesis Harg : (0 <= arg < 2 ^ 64)%Z.

  Hypothesis HNL : rdn ASEGS M0 (0x6b0ce3 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HFIN : rdn ASEGS M0 (0x6b0aa0 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HHEAD : rdn ASEGS M0 (0x6b0ab0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x6b0aa0 + 24))).
  Hypothesis HSLOT : rdn ASEGS M0 (0x6b0aa8 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis HLOCKW : rdn ASEGS M0 (0x6b0aa4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis HWTAB : forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M0 (Z_to_bv 64 (0x6b0aa0 + d)) m = true.

  Definition cxr_F (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)).
  Definition cxr_mem (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (cxr_F rg) (Z_to_bv 64 (0x6b0aa0 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f)))
      (Z_to_bv 64 (0x6b0aa0 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg)))
      (Z_to_bv 64 (0x6b0aa0 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1))).

  Lemma sp_cxr : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem cxa_reg_run : forall regs,
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 arg -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x133c98 : word) M0 rom) (mkst regs' ra (cxr_mem regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20
      /\ keeps_but [1; 2; 8; 9; 18; 19; 20]%bv regs regs'.
  Proof.
    intros regs H10 H11 H2 H1. rewrite sp_cxr in H2. rewrite sp_cxr.
    set (F1 := wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)).
    set (F2 := wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))).
    set (F3 := wbytes F2 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))).
    set (F4 := wbytes F3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
    set (F5 := wbytes F4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))).
    set (F6 := wbytes F5 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20))).
    assert (GF : forall k : Z, mem_grows M0 F6) by (intros _; unfold F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (FOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 48)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - 48 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply (store_ok_sub ASEGS M0 (Z_to_bv 64 (s - 48)) _ 48%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }

    assert (RDF : forall (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 0x6b3000)%Z -> rdn ASEGS M0 a k = Some bs -> rdn ASEGS F6 a k = Some bs).
    { intros a k bs Ha R. rewrite <- R. apply rdn_ext; [pose proof (u64_range a); lia|]. intros x Hx. pose proof (u64_range x). unfold F6, F5, F4, F3, F2, F1.
      rewrite !wbytes_below; first [reflexivity | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]. }
    set (T1 := wbytes F6 (Z_to_bv 64 (0x6b0aa0 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f))).
    set (T2 := wbytes T1 (Z_to_bv 64 (0x6b0aa0 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg))).
    set (T3 := wbytes T2 (Z_to_bv 64 (0x6b0aa0 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))).
    assert (GF6 : mem_grows M0 F6) by exact (GF 0%Z).
    assert (TOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M (Z_to_bv 64 (0x6b0aa0 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply HWTAB; assumption. }
    assert (RLOCK : rdn ASEGS T3 (Z_to_bv 64 0x6b0aa4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { unfold T3, T2, T1. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia).
      apply RDF; [unorm; cbn; lia |]. replace (Z_to_bv 64 0x6b0aa4 : word) with (0x6b0aa4 : word) by (apply bv_eq; reflexivity). exact HLOCKW. }
    assert (SL : forall k v, rdn ASEGS F6 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> (8 <= k <= 48)%Z ->
                 rdn ASEGS T3 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v R Hk. unfold T3, T2, T1. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). exact R. }
    assert (S8 : rdn ASEGS F6 (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra)).
    { unfold F6, F5, F4, F3, F2, F1. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). apply rdn_wbytes_hit8. unorm. lia. }
    assert (S16 : rdn ASEGS F6 (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))).
    { unfold F6, F5, F4, F3, F2. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). apply rdn_wbytes_hit8. unorm. lia. }
    assert (S24 : rdn ASEGS F6 (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))).
    { unfold F6, F5, F4, F3. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). apply rdn_wbytes_hit8. unorm. lia. }
    assert (S32 : rdn ASEGS F6 (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))).
    { unfold F6, F5, F4. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). apply rdn_wbytes_hit8. unorm. lia. }
    assert (S40 : rdn ASEGS F6 (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))).
    { unfold F6, F5. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia). apply rdn_wbytes_hit8. unorm. lia. }
    assert (S48 : rdn ASEGS F6 (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))).
    { unfold F6. apply rdn_wbytes_hit8. unorm. lia. }
    eexists. split.
    - stepiv F_133c54 D_133c54 (Z_to_bv 64 (s - 48)) ltac:(wv2).
      stepsdq F_133c58 D_133c58 (Z_to_bv 64 (s - 8)) ra ltac:(replace (s - 8)%Z with (s - 48 + 40)%Z by ring; apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) with F1.
      stepsdq F_133c5c D_133c5c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(replace (s - 16)%Z with (s - 48 + 32)%Z by ring; apply FOK; [unfold F1; apply wbytes_grows | lia | cbn; lia]).
      change (wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) with F2.
      stepsdq F_133c60 D_133c60 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(replace (s - 24)%Z with (s - 48 + 24)%Z by ring; apply FOK; [unfold F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F2 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) with F3.
      stepsdq F_133c64 D_133c64 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(replace (s - 32)%Z with (s - 48 + 16)%Z by ring; apply FOK; [unfold F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) with F4.
      stepsdq F_133c68 D_133c68 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(replace (s - 40)%Z with (s - 48 + 8)%Z by ring; apply FOK; [unfold F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))) with F5.
      stepsdq F_133c6c D_133c6c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(replace (s - 48)%Z with (s - 48 + 0)%Z by ring; apply FOK; [unfold F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F5 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20))) with F6.
      stepiv F_133c70 D_133c70 (Z_to_bv 64 arg) ltac:(wv2).
      stepiv F_133c74 D_133c74 (Z_to_bv 64 f) ltac:(wv2).
      stepn F_133c78 D_133c78. stepn F_133c7c D_133c7c. stepn F_133c80 D_133c80. stepn F_133c84 D_133c84.
      stepn F_133c88 D_133c88.
      stepn F_145b80 D_145b80.
      mlb F_145b84 D_145b84 (0x6b0ce3 : word) (RDF (0x6b0ce3 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HNL).
      stepb F_145b88 D_145b88.
      stepret F_145d78 D_145d78 (0x133cd0 : word) ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mlbu F_133c8c D_133c8c (0x6b0aa0 : word) (RDF (0x6b0aa0 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HFIN).
      stepn F_133c90 D_133c90.
      stepb F_133c94 D_133c94.
      mld F_133c98 D_133c98 (0x6b0ab0 : word) (RDF (0x6b0ab0 : word) 8%nat _ ltac:(vm_compute; intuition discriminate) HHEAD).
      stepb F_133c9c D_133c9c.
      mlw F_133ca8 D_133ca8 (0x6b0aa8 : word) (RDF (0x6b0aa8 : word) 4%nat _ ltac:(vm_compute; intuition discriminate) HSLOT).
      rewrite (art_v_lw_small n) by lia.
      stepn F_133cac D_133cac.
      stepb_tk F_133cb0 D_133cb0 ltac:(cond).
      stepn F_133cd4 D_133cd4.
      stepiv F_133cd8 D_133cd8 (Z_to_bv 64 (8 * n)) ltac:(wv2).
      stepiv F_133cdc D_133cdc (Z_to_bv 64 (0x6b0aa0 + 24 + 8 * n)) ltac:(wv2).
      stepiv F_133ce0 D_133ce0 (Z_to_bv 64 (n + 1)) ltac:(wv2).
      stepsdq F_133ce4 D_133ce4 (Z_to_bv 64 (0x6b0aa0 + 32 + 8 * n)) (Z_to_bv 64 f)
        ltac:(replace (0x6b0aa0 + 32 + 8 * n)%Z with (0x6b0aa0 + (32 + 8 * n))%Z by ring; apply TOK; [exact GF6 | lia | cbn; lia]).
      change (wbytes F6 (Z_to_bv 64 (0x6b0aa0 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f))) with T1.
      stepsdq F_133ce8 D_133ce8 (Z_to_bv 64 (0x6b0aa0 + 288 + 8 * n)) (Z_to_bv 64 arg)
        ltac:(replace (0x6b0aa0 + 288 + 8 * n)%Z with (0x6b0aa0 + (288 + 8 * n))%Z by ring; apply TOK; [unfold T1; eapply mem_grows_trans; [exact GF6 | apply wbytes_grows] | lia | cbn; lia]).
      change (wbytes T1 (Z_to_bv 64 (0x6b0aa0 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg))) with T2.
      chain_step; [reflexivity | eapply (step_sw_at ASEGS) with (a := Z_to_bv 64 (0x6b0aa0 + 8)) (v := Z_to_bv 64 (n + 1));
          [exact F_133cec | reflexivity | exact D_133cec | wv2 | gres; rwH; reflexivity
          | apply TOK; [unfold T2, T1; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GF6 | lia | cbn; lia] ] | step_simpl].
      change (wbytes T2 (Z_to_bv 64 (0x6b0aa0 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) with T3.
      stepn F_133cf0 D_133cf0.
      stepn F_133cf4 D_133cf4.
      mlw F_145e08 D_145e08 (Z_to_bv 64 0x6b0aa4 : word) RLOCK.
      stepb F_145e0c D_145e0c.
      stepret F_145e10 D_145e10 (0x133d3c : word) ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      stepn F_133cf8 D_133cf8.
      stepld F_133cfc D_133cfc ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact S8 | lia]).
      stepld F_133d00 D_133d00 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact S16 | lia]).
      stepld F_133d04 D_133d04 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact S24 | lia]).
      stepld F_133d08 D_133d08 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact S32 | lia]).
      stepld F_133d0c D_133d0c (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 40)) by (symmetry; wv2) end; apply SL; [exact S40 | lia]).
      stepld F_133d10 D_133d10 (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 48)) by (symmetry; wv2) end; apply SL; [exact S48 | lia]).
      stepiv F_133d14 D_133d14 (Z_to_bv 64 s) ltac:(wv2).
      stepret F_133d18 D_133d18 ra ltac:(rwH; reflexivity).
      unfold T3, T2, T1, F6, F5, F4, F3, F2, F1. fold (cxr_F regs). fold (cxr_mem regs).
      apply mst_refl.
    - repeat (split; [gres; reflexivity|]). solve_keeps_but.
  Qed.
End REG.
End FPX_1.
