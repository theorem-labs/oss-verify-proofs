(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib ArtMem Pm4RegionPoisoned Pm4AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm4_code_141000_142000 Pm4_code_153000_154000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
Definition CXA_AX : Z := 0x6be020%Z.

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
  (* [comment removed for export] *)
  Hypothesis HNL : rdn ASEGS M0 (0x6be263 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HFIN : rdn ASEGS M0 (0x6be020 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HHEAD : rdn ASEGS M0 (0x6be030 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x6be020 + 24))).
  Hypothesis HSLOT : rdn ASEGS M0 (0x6be028 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis HLOCKW : rdn ASEGS M0 (0x6be024 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis HWTAB : forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M0 (Z_to_bv 64 (0x6be020 + d)) m = true.

  Definition cxr_F (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19))) (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)).
  Definition cxr_mem (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (cxr_F rg) (Z_to_bv 64 (0x6be020 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f)))
      (Z_to_bv 64 (0x6be020 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg)))
      (Z_to_bv 64 (0x6be020 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1))).

  Lemma sp_cxr : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem cxa_reg_run : forall regs,
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 arg -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x141834 : word) M0 rom) (mkst regs' ra (cxr_mem regs) rom)
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
    (* [comment removed for export] *)
    assert (RDF : forall (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 0x6c0000)%Z -> rdn ASEGS M0 a k = Some bs -> rdn ASEGS F6 a k = Some bs).
    { intros a k bs Ha R. rewrite <- R. apply rdn_ext; [pose proof (u64_range a); lia|]. intros x Hx. pose proof (u64_range x). unfold F6, F5, F4, F3, F2, F1.
      rewrite !wbytes_below; first [reflexivity | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]. }
    set (T1 := wbytes F6 (Z_to_bv 64 (0x6be020 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f))).
    set (T2 := wbytes T1 (Z_to_bv 64 (0x6be020 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg))).
    set (T3 := wbytes T2 (Z_to_bv 64 (0x6be020 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))).
    assert (GF6 : mem_grows M0 F6) by exact (GF 0%Z).
    assert (TOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M (Z_to_bv 64 (0x6be020 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply HWTAB; assumption. }
    assert (RLOCK : rdn ASEGS T3 (Z_to_bv 64 0x6be024) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { unfold T3, T2, T1. rewrite !rdn_wbytes_out by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; unorm; lia).
      apply RDF; [unorm; cbn; lia |]. replace (Z_to_bv 64 0x6be024 : word) with (0x6be024 : word) by (apply bv_eq; reflexivity). exact HLOCKW. }
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
    - stepiv F_1417f0 D_1417f0 (Z_to_bv 64 (s - 48)) ltac:(wv2).
      stepsdq F_1417f4 D_1417f4 (Z_to_bv 64 (s - 8)) ra ltac:(replace (s - 8)%Z with (s - 48 + 40)%Z by ring; apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) with F1.
      stepsdq F_1417f8 D_1417f8 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(replace (s - 16)%Z with (s - 48 + 32)%Z by ring; apply FOK; [unfold F1; apply wbytes_grows | lia | cbn; lia]).
      change (wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) with F2.
      stepsdq F_1417fc D_1417fc (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(replace (s - 24)%Z with (s - 48 + 24)%Z by ring; apply FOK; [unfold F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F2 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) with F3.
      stepsdq F_141800 D_141800 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(replace (s - 32)%Z with (s - 48 + 16)%Z by ring; apply FOK; [unfold F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) with F4.
      stepsdq F_141804 D_141804 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(replace (s - 40)%Z with (s - 48 + 8)%Z by ring; apply FOK; [unfold F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))) with F5.
      stepsdq F_141808 D_141808 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(replace (s - 48)%Z with (s - 48 + 0)%Z by ring; apply FOK; [unfold F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F5 (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20))) with F6.
      stepiv F_14180c D_14180c (Z_to_bv 64 arg) ltac:(wv2).                                              (* [comment removed for export] *)
      stepiv F_141810 D_141810 (Z_to_bv 64 f) ltac:(wv2).                                                (* [comment removed for export] *)
      stepn F_141814 D_141814. stepn F_141818 D_141818. stepn F_14181c D_14181c. stepn F_141820 D_141820.
      stepn F_141824 D_141824.                                                                       (* [comment removed for export] *)
      stepn F_15371c D_15371c.
      mlb F_153720 D_153720 (0x6be263 : word) (RDF (0x6be263 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HNL).     (* [comment removed for export] *)
      stepb F_153724 D_153724.                                                                         (* [comment removed for export] *)
      stepret F_153914 D_153914 (0x14186c : word) ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mlbu F_141828 D_141828 (0x6be020 : word) (RDF (0x6be020 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HFIN).  (* [comment removed for export] *)
      stepn F_14182c D_14182c.
      stepb F_141830 D_141830.
      mld F_141834 D_141834 (0x6be030 : word) (RDF (0x6be030 : word) 8%nat _ ltac:(vm_compute; intuition discriminate) HHEAD).   (* [comment removed for export] *)
      stepb F_141838 D_141838.
      mlw F_141844 D_141844 (0x6be028 : word) (RDF (0x6be028 : word) 4%nat _ ltac:(vm_compute; intuition discriminate) HSLOT).    (* [comment removed for export] *)
      rewrite (art_v_lw_small n) by lia.
      stepn F_141848 D_141848.
      stepb_tk F_14184c D_14184c ltac:(cond).                                                         (* [comment removed for export] *)
      stepn F_141870 D_141870.
      stepiv F_141874 D_141874 (Z_to_bv 64 (8 * n)) ltac:(wv2).                                        (* [comment removed for export] *)
      stepiv F_141878 D_141878 (Z_to_bv 64 (0x6be020 + 24 + 8 * n)) ltac:(wv2).                             (* [comment removed for export] *)
      stepiv F_14187c D_14187c (Z_to_bv 64 (n + 1)) ltac:(wv2).                                        (* [comment removed for export] *)
      stepsdq F_141880 D_141880 (Z_to_bv 64 (0x6be020 + 32 + 8 * n)) (Z_to_bv 64 f)
        ltac:(replace (0x6be020 + 32 + 8 * n)%Z with (0x6be020 + (32 + 8 * n))%Z by ring; apply TOK; [exact GF6 | lia | cbn; lia]).
      change (wbytes F6 (Z_to_bv 64 (0x6be020 + 32 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 f))) with T1.
      stepsdq F_141884 D_141884 (Z_to_bv 64 (0x6be020 + 288 + 8 * n)) (Z_to_bv 64 arg)
        ltac:(replace (0x6be020 + 288 + 8 * n)%Z with (0x6be020 + (288 + 8 * n))%Z by ring; apply TOK; [unfold T1; eapply mem_grows_trans; [exact GF6 | apply wbytes_grows] | lia | cbn; lia]).
      change (wbytes T1 (Z_to_bv 64 (0x6be020 + 288 + 8 * n)) (word_to_le_bytes 8 (Z_to_bv 64 arg))) with T2.
      chain_step; [reflexivity | eapply (step_sw_at ASEGS) with (a := Z_to_bv 64 (0x6be020 + 8)) (v := Z_to_bv 64 (n + 1));
          [exact F_141888 | reflexivity | exact D_141888 | wv2 | gres; rwH; reflexivity
          | apply TOK; [unfold T2, T1; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); exact GF6 | lia | cbn; lia] ] | step_simpl].   (* [comment removed for export] *)
      change (wbytes T2 (Z_to_bv 64 (0x6be020 + 8)) (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))) with T3.
      stepn F_14188c D_14188c.
      stepn F_141890 D_141890.                                                                       (* [comment removed for export] *)
      mlw F_1539a4 D_1539a4 (Z_to_bv 64 0x6be024 : word) RLOCK.                                                       (* [comment removed for export] *)
      stepb F_1539a8 D_1539a8.
      stepret F_1539ac D_1539ac (0x1418d8 : word) ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      stepn F_141894 D_141894.                                                                       (* [comment removed for export] *)
      stepld F_141898 D_141898 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [exact S8 | lia]).
      stepld F_14189c D_14189c (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [exact S16 | lia]).
      stepld F_1418a0 D_1418a0 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [exact S24 | lia]).
      stepld F_1418a4 D_1418a4 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [exact S32 | lia]).
      stepld F_1418a8 D_1418a8 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 40)) by (symmetry; wv2) end; apply SL; [exact S40 | lia]).
      stepld F_1418ac D_1418ac (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 48)) by (symmetry; wv2) end; apply SL; [exact S48 | lia]).
      stepiv F_1418b0 D_1418b0 (Z_to_bv 64 s) ltac:(wv2).
      stepret F_1418b4 D_1418b4 ra ltac:(rwH; reflexivity).
      unfold T3, T2, T1, F6, F5, F4, F3, F2, F1. fold (cxr_F regs). fold (cxr_mem regs).
      apply mst_refl.
    - repeat (split; [gres; reflexivity|]). solve_keeps_but.
  Qed.
End REG.
End FPX_1.
