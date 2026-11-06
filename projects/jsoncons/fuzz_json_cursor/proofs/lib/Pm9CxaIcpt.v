(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib ArtMem Pm9RegionPoisoned Pm9AsanMemset Pm9CxaReg.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9CxaTab.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac wv2 := gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  first [reflexivity | f_equal; lia].
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wv2 | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].
#[local] Ltac ulit := repeat match goal with |- context [bv_unsigned ?l] => lazymatch l with @BV _ ?z _ => change (bv_unsigned l) with z end end.
#[local] Ltac wlen := rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat]; ulit; unorm; lia.

Section ENS.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra v8 : word.
  Variable s : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 16)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M0 (Z_to_bv 64 (s - 16)) 16%nat = true.
  Hypothesis HINIT : rdn ASEGS M0 (0x15e9d8 : word) 1%nat = Some [Z_to_bv 8 1].

  Definition ens_mem : word -> option byte :=
    wbytes (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8).

  Lemma sp_ens : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem ens_run : forall regs, getr regs 2 = sp -> getr regs 1 = ra -> getr regs 8 = v8 ->
    exists regs',
      msteps ASEGS (mkst regs (0x88340 : word) M0 rom) (mkst regs' ra ens_mem rom)
      /\ getr regs' 1 = ra /\ getr regs' 2 = sp /\ getr regs' 8 = v8 /\ keeps_but [1; 2; 8]%bv regs regs'.
  Proof.
    intros regs H2 H1 H8. rewrite sp_ens in H2. rewrite sp_ens.
    set (F1 := wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)).
    set (F2 := wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8)).
    assert (FOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 16)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - 16 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply (store_ok_sub ASEGS M0 (Z_to_bv 64 (s - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }
    assert (RDF : forall (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 0x6b4000)%Z -> rdn ASEGS M0 a k = Some bs -> rdn ASEGS F2 a k = Some bs).
    { intros a k bs Ha R. rewrite <- R. apply rdn_ext; [pose proof (u64_range a); lia|]. intros x Hx. pose proof (u64_range x). unfold F2, F1.
      rewrite !wbytes_below; first [reflexivity | wlen | unorm; lia]. }
    assert (S8 : rdn ASEGS F2 (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra)).
    { unfold F2. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S16 : rdn ASEGS F2 (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 v8)).
    { unfold F2. apply rdn_wbytes_hit8. unorm. lia. }
    eexists. split.
    - stepiv Fx_882f8 Dx_882f8 (Z_to_bv 64 (s - 16)) ltac:(wv2).
      stepsdq Fx_882fc Dx_882fc (Z_to_bv 64 (s - 8)) ra ltac:(replace (s - 8)%Z with (s - 16 + 8)%Z by ring; apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) with F1.
      stepsdq Fx_88300 Dx_88300 (Z_to_bv 64 (s - 16)) v8 ltac:(replace (s - 16)%Z with (s - 16 + 0)%Z by ring; apply FOK; [unfold F1; apply wbytes_grows | lia | cbn; lia]).
      change (wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8)) with F2.
      stepn Fx_88304 Dx_88304. stepn Fx_88308 Dx_88308.
      mlb Fx_8830c Dx_8830c (0x15e9d8 : word) (RDF (0x15e9d8 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HINIT).
      stepn Fx_88310 Dx_88310.
      stepfence Fx_88314 Dx_88314.
      stepb Fx_88318 Dx_88318.
      stepld Fx_8831c Dx_8831c ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; exact S8).
      stepld Fx_88320 Dx_88320 v8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; exact S16).
      stepiv Fx_88324 Dx_88324 (Z_to_bv 64 s) ltac:(wv2).
      stepret Fx_88328 Dx_88328 ra ltac:(rwH; reflexivity).
      unfold F2, F1. fold ens_mem. apply mst_refl.
    - repeat (split; [gres; rwH; reflexivity|]). solve_keeps_but.
  Qed.
End ENS.

Section LSD.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HLOFF : rdn ASEGS M0 (0x155160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10)).
  Hypothesis HCNT : rdn ASEGS M0 (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis Hcw : store_ok ASEGS M0 (0x691da0 : word) 4%nat = true.

  Definition lsd_mem : word -> option byte := wbytes M0 (0x691da0 : word) (word_to_le_bytes 4 (Z_to_bv 64 1)).

  Theorem lsd_run : forall regs, getr regs 4 = (0x691d90 : word) -> getr regs 1 = ra ->
    exists regs', msteps ASEGS (mkst regs (0xaea7c : word) M0 rom) (mkst regs' ra lsd_mem rom) /\ keeps_cs regs regs'.
  Proof.
    intros regs H4 H1.
    eexists. split.
    - stepn Fx_aea34 Dx_aea34.
      mld Fx_aea38 Dx_aea38 (0x155160 : word) HLOFF.
      stepiv Fx_aea3c Dx_aea3c (0x691da0 : word) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
      mlw Fx_aea40 Dx_aea40 (0x691da0 : word) HCNT.
      stepiv Fx_aea44 Dx_aea44 (Z_to_bv 64 1) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
      chain_step; [reflexivity | eapply (step_sw_at ASEGS) with (a := (0x691da0 : word)) (v := Z_to_bv 64 1);
          [exact Fx_aea48 | reflexivity | exact Dx_aea48 | gres; apply bv_eq; vm_compute; reflexivity | gres; reflexivity | exact Hcw ] | step_simpl].
      stepret Fx_aea4c Dx_aea4c ra ltac:(rwH; reflexivity).
      fold lsd_mem. apply mst_refl.
    - intros r Hr. repeat (rewrite getr_other; [|intros ->; revert Hr; not_kept]). reflexivity.
  Qed.
End LSD.

Section LSE.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra v8 : word.
  Variable s : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 16)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M0 (Z_to_bv 64 (s - 16)) 16%nat = true.
  Hypothesis HLOFF : rdn ASEGS M0 (0x155160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10)).
  Hypothesis HCNT : rdn ASEGS M0 (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Hypothesis Hcw : store_ok ASEGS M0 (0x691da0 : word) 4%nat = true.

  Definition lse_mem : word -> option byte :=
    wbytes (wbytes (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8)) (0x691da0 : word) (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma sp_lse : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem lse_run : forall regs, getr regs 2 = sp -> getr regs 1 = ra -> getr regs 8 = v8 -> getr regs 4 = (0x691d90 : word) ->
    exists regs', msteps ASEGS (mkst regs (0xaea98 : word) M0 rom) (mkst regs' ra lse_mem rom)
      /\ getr regs' 1 = ra /\ getr regs' 2 = sp /\ getr regs' 8 = v8 /\ keeps_but [1; 2; 8]%bv regs regs'.
  Proof.
    intros regs H2 H1 H8 H4. rewrite sp_lse in H2. rewrite sp_lse.
    set (F1 := wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)).
    set (F2 := wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8)).
    set (F3 := wbytes F2 (0x691da0 : word) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    assert (GF2 : mem_grows M0 F2) by (unfold F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (FOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 16)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - 16 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply (store_ok_sub ASEGS M0 (Z_to_bv 64 (s - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }
    assert (RDF : forall (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 0x6b4000)%Z -> rdn ASEGS M0 a k = Some bs -> rdn ASEGS F2 a k = Some bs).
    { intros a k bs Ha R. rewrite <- R. apply rdn_ext; [pose proof (u64_range a); lia|]. intros x Hx. pose proof (u64_range x). unfold F2, F1.
      rewrite !wbytes_below; first [reflexivity | wlen | unorm; lia]. }
    assert (S8 : rdn ASEGS F3 (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra)).
    { unfold F3, F2. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S16 : rdn ASEGS F3 (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 v8)).
    { unfold F3. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    eexists. split.
    - stepiv Fx_aea50 Dx_aea50 (Z_to_bv 64 (s - 16)) ltac:(wv2).
      stepsdq Fx_aea54 Dx_aea54 (Z_to_bv 64 (s - 8)) ra ltac:(replace (s - 8)%Z with (s - 16 + 8)%Z by ring; apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) with F1.
      stepsdq Fx_aea58 Dx_aea58 (Z_to_bv 64 (s - 16)) v8 ltac:(replace (s - 16)%Z with (s - 16 + 0)%Z by ring; apply FOK; [unfold F1; apply wbytes_grows | lia | cbn; lia]).
      change (wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 v8)) with F2.
      stepn Fx_aea5c Dx_aea5c.
      mld Fx_aea60 Dx_aea60 (0x155160 : word) (RDF (0x155160 : word) 8%nat _ ltac:(vm_compute; intuition discriminate) HLOFF).
      stepiv Fx_aea64 Dx_aea64 (0x691da0 : word) ltac:(gres; rwH; apply bv_eq; vm_compute; reflexivity).
      mlw Fx_aea68 Dx_aea68 (0x691da0 : word) (RDF (0x691da0 : word) 4%nat _ ltac:(vm_compute; intuition discriminate) HCNT).
      stepb Fx_aea6c Dx_aea6c.
      stepiv Fx_aea70 Dx_aea70 (Z_to_bv 64 0) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
      chain_step; [reflexivity | eapply (step_sw_at ASEGS) with (a := (0x691da0 : word)) (v := Z_to_bv 64 0);
          [exact Fx_aea74 | reflexivity | exact Dx_aea74 | gres; apply bv_eq; vm_compute; reflexivity | gres; reflexivity | exact (store_ok_mono _ _ M0 F2 _ GF2 Hcw) ] | step_simpl].
      change (wbytes F2 (0x691da0 : word) (word_to_le_bytes 4 (Z_to_bv 64 0))) with F3.
      stepld Fx_aea78 Dx_aea78 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; exact S8).
      stepld Fx_aea7c Dx_aea7c v8 ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; exact S16).
      stepiv Fx_aea80 Dx_aea80 (Z_to_bv 64 s) ltac:(wv2).
      stepret Fx_aea84 Dx_aea84 ra ltac:(rwH; reflexivity).
      unfold F3, F2, F1. fold lse_mem. apply mst_refl.
    - repeat (split; [gres; rwH; reflexivity|]). solve_keeps_but.
  Qed.
End LSE.

Section HND.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variable s : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 96)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M0 (Z_to_bv 64 (s - 96)) 96%nat = true.
  Hypothesis HFLG : rdn ASEGS M0 (0x1544f8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15b4f8)).
  Hypothesis HCIO : rdn ASEGS M0 (0x15b514 : word) 1%nat = Some [Z_to_bv 8 0].

  Definition hnd_mem (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (M0) (Z_to_bv 64 (s - 96 + 88)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 96 + 80)) (word_to_le_bytes 8 (getr regs 8))) (Z_to_bv 64 (s - 96 + 72)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 96 + 64)) (word_to_le_bytes 8 (getr regs 18))) (Z_to_bv 64 (s - 96 + 56)) (word_to_le_bytes 8 (getr regs 19))) (Z_to_bv 64 (s - 96 + 48)) (word_to_le_bytes 8 (getr regs 20))) (Z_to_bv 64 (s - 96 + 40)) (word_to_le_bytes 8 (getr regs 21))) (Z_to_bv 64 (s - 96 + 32)) (word_to_le_bytes 8 (getr regs 22))) (Z_to_bv 64 (s - 96 + 24)) (word_to_le_bytes 8 (getr regs 23))) (Z_to_bv 64 (s - 96 + 16)) (word_to_le_bytes 8 (getr regs 24))) (Z_to_bv 64 (s - 96 + 8)) (word_to_le_bytes 8 (getr regs 25)).

  Lemma sp_hnd : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Theorem hnd_run : forall regs, getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs', msteps ASEGS (mkst regs (0x7503c : word) M0 rom) (mkst regs' ra (hnd_mem regs) rom) /\ keeps_cs regs regs'.
  Proof.
    intros regs H2 H1. rewrite sp_hnd in H2.
    set (F1 := wbytes M0 (Z_to_bv 64 (s - 96 + 88)) (word_to_le_bytes 8 ra)).
    set (F2 := wbytes F1 (Z_to_bv 64 (s - 96 + 80)) (word_to_le_bytes 8 (getr regs 8))).
    set (F3 := wbytes F2 (Z_to_bv 64 (s - 96 + 72)) (word_to_le_bytes 8 (getr regs 9))).
    set (F4 := wbytes F3 (Z_to_bv 64 (s - 96 + 64)) (word_to_le_bytes 8 (getr regs 18))).
    set (F5 := wbytes F4 (Z_to_bv 64 (s - 96 + 56)) (word_to_le_bytes 8 (getr regs 19))).
    set (F6 := wbytes F5 (Z_to_bv 64 (s - 96 + 48)) (word_to_le_bytes 8 (getr regs 20))).
    set (F7 := wbytes F6 (Z_to_bv 64 (s - 96 + 40)) (word_to_le_bytes 8 (getr regs 21))).
    set (F8 := wbytes F7 (Z_to_bv 64 (s - 96 + 32)) (word_to_le_bytes 8 (getr regs 22))).
    set (F9 := wbytes F8 (Z_to_bv 64 (s - 96 + 24)) (word_to_le_bytes 8 (getr regs 23))).
    set (F10 := wbytes F9 (Z_to_bv 64 (s - 96 + 16)) (word_to_le_bytes 8 (getr regs 24))).
    set (F11 := wbytes F10 (Z_to_bv 64 (s - 96 + 8)) (word_to_le_bytes 8 (getr regs 25))).
    assert (FOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 96)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - 96 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply (store_ok_sub ASEGS M0 (Z_to_bv 64 (s - 96)) _ 96%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }
    assert (RDF : forall (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 0x6b4000)%Z -> rdn ASEGS M0 a k = Some bs -> rdn ASEGS F11 a k = Some bs).
    { intros a k bs Ha R. rewrite <- R. apply rdn_ext; [pose proof (u64_range a); lia|]. intros x Hx. pose proof (u64_range x). unfold F11, F10, F9, F8, F7, F6, F5, F4, F3, F2, F1.
      rewrite !wbytes_below; first [reflexivity | wlen | unorm; lia]. }
    assert (S88 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 88)) 8%nat = Some (word_to_le_bytes 8 ra)).
    { unfold F11, F10, F9, F8, F7, F6, F5, F4, F3, F2. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S80 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 80)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))).
    { unfold F11, F10, F9, F8, F7, F6, F5, F4, F3. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S72 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 72)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))).
    { unfold F11, F10, F9, F8, F7, F6, F5, F4. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S64 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))).
    { unfold F11, F10, F9, F8, F7, F6, F5. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S56 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))).
    { unfold F11, F10, F9, F8, F7, F6. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S48 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))).
    { unfold F11, F10, F9, F8, F7. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S40 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))).
    { unfold F11, F10, F9, F8. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S32 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))).
    { unfold F11, F10, F9. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S24 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 23))).
    { unfold F11, F10. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S16 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 24))).
    { unfold F11. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S8 : rdn ASEGS F11 (Z_to_bv 64 (s - 96 + 8)) 8%nat = Some (word_to_le_bytes 8 (getr regs 25))).
    { unfold F11. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    eexists. split.
    - stepn Fx_74ff4 Dx_74ff4.
      stepiv Fx_66f38 Dx_66f38 (Z_to_bv 64 (s - 96)) ltac:(wv2).
      stepsdq Fx_66f3c Dx_66f3c (Z_to_bv 64 (s - 96 + 88)) ra ltac:(apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes M0 (Z_to_bv 64 (s - 96 + 88)) (word_to_le_bytes 8 ra)) with F1.
      stepsdq Fx_66f40 Dx_66f40 (Z_to_bv 64 (s - 96 + 80)) (getr regs 8) ltac:(apply FOK; [unfold F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F1 (Z_to_bv 64 (s - 96 + 80)) (word_to_le_bytes 8 (getr regs 8))) with F2.
      stepsdq Fx_66f44 Dx_66f44 (Z_to_bv 64 (s - 96 + 72)) (getr regs 9) ltac:(apply FOK; [unfold F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F2 (Z_to_bv 64 (s - 96 + 72)) (word_to_le_bytes 8 (getr regs 9))) with F3.
      stepsdq Fx_66f48 Dx_66f48 (Z_to_bv 64 (s - 96 + 64)) (getr regs 18) ltac:(apply FOK; [unfold F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F3 (Z_to_bv 64 (s - 96 + 64)) (word_to_le_bytes 8 (getr regs 18))) with F4.
      stepsdq Fx_66f4c Dx_66f4c (Z_to_bv 64 (s - 96 + 56)) (getr regs 19) ltac:(apply FOK; [unfold F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F4 (Z_to_bv 64 (s - 96 + 56)) (word_to_le_bytes 8 (getr regs 19))) with F5.
      stepsdq Fx_66f50 Dx_66f50 (Z_to_bv 64 (s - 96 + 48)) (getr regs 20) ltac:(apply FOK; [unfold F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F5 (Z_to_bv 64 (s - 96 + 48)) (word_to_le_bytes 8 (getr regs 20))) with F6.
      stepsdq Fx_66f54 Dx_66f54 (Z_to_bv 64 (s - 96 + 40)) (getr regs 21) ltac:(apply FOK; [unfold F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F6 (Z_to_bv 64 (s - 96 + 40)) (word_to_le_bytes 8 (getr regs 21))) with F7.
      stepsdq Fx_66f58 Dx_66f58 (Z_to_bv 64 (s - 96 + 32)) (getr regs 22) ltac:(apply FOK; [unfold F7, F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F7 (Z_to_bv 64 (s - 96 + 32)) (word_to_le_bytes 8 (getr regs 22))) with F8.
      stepsdq Fx_66f5c Dx_66f5c (Z_to_bv 64 (s - 96 + 24)) (getr regs 23) ltac:(apply FOK; [unfold F8, F7, F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F8 (Z_to_bv 64 (s - 96 + 24)) (word_to_le_bytes 8 (getr regs 23))) with F9.
      stepsdq Fx_66f60 Dx_66f60 (Z_to_bv 64 (s - 96 + 16)) (getr regs 24) ltac:(apply FOK; [unfold F9, F8, F7, F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F9 (Z_to_bv 64 (s - 96 + 16)) (word_to_le_bytes 8 (getr regs 24))) with F10.
      stepsdq Fx_66f64 Dx_66f64 (Z_to_bv 64 (s - 96 + 8)) (getr regs 25) ltac:(apply FOK; [unfold F10, F9, F8, F7, F6, F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
      change (wbytes F10 (Z_to_bv 64 (s - 96 + 8)) (word_to_le_bytes 8 (getr regs 25))) with F11.
      stepn Fx_66f68 Dx_66f68.
      mld Fx_66f6c Dx_66f6c (0x1544f8 : word) (RDF (0x1544f8 : word) 8%nat _ ltac:(vm_compute; intuition discriminate) HFLG).
      mlbu Fx_66f70 Dx_66f70 (0x15b514 : word) (RDF (0x15b514 : word) 1%nat _ ltac:(vm_compute; intuition discriminate) HCIO).
      stepb Fx_66f74 Dx_66f74.
      stepld Fx_67170 Dx_67170 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 88)) by (symmetry; wv2) end; exact S88).
      stepld Fx_67174 Dx_67174 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 80)) by (symmetry; wv2) end; exact S80).
      stepld Fx_67178 Dx_67178 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 72)) by (symmetry; wv2) end; exact S72).
      stepld Fx_6717c Dx_6717c (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 64)) by (symmetry; wv2) end; exact S64).
      stepld Fx_67180 Dx_67180 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 56)) by (symmetry; wv2) end; exact S56).
      stepld Fx_67184 Dx_67184 (getr regs 20) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 48)) by (symmetry; wv2) end; exact S48).
      stepld Fx_67188 Dx_67188 (getr regs 21) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 40)) by (symmetry; wv2) end; exact S40).
      stepld Fx_6718c Dx_6718c (getr regs 22) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 32)) by (symmetry; wv2) end; exact S32).
      stepld Fx_67190 Dx_67190 (getr regs 23) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 24)) by (symmetry; wv2) end; exact S24).
      stepld Fx_67194 Dx_67194 (getr regs 24) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 16)) by (symmetry; wv2) end; exact S16).
      stepld Fx_67198 Dx_67198 (getr regs 25) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 96 + 8)) by (symmetry; wv2) end; exact S8).
      stepiv Fx_6719c Dx_6719c (Z_to_bv 64 s) ltac:(wv2).
      stepret Fx_671a0 Dx_671a0 ra ltac:(rwH; reflexivity).
      unfold F11, F10, F9, F8, F7, F6, F5, F4, F3, F2, F1. fold (hnd_mem regs). apply mst_refl.
    - intros r Hr. unfold callee_saved in Hr. cbn [In] in Hr.
      repeat (destruct Hr as [<- | Hr]; [gres; rwH; reflexivity|]). destruct Hr.
  Qed.
End HND.

Section CXRP.
  Variable M0 : word -> option byte.
  Variable ra : word.
  Variables s f arg n : Z.
  Variable rg : bvmap 5 word.
  Hypothesis Hs : (0x1000000 <= s - 48)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hn : (0 < n < 32)%Z.
  Lemma cxr_grows : mem_grows M0 (cxr_mem M0 ra s f arg n rg).
  Proof. unfold cxr_mem, cxr_F. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma cxr_frame : forall x : word,
    ~ (s - 48 <= bv_unsigned x < s)%Z -> ~ (0x6b1de0 + 8 <= bv_unsigned x < 0x6b1de0 + 12)%Z ->
    ~ (0x6b1de0 + 32 + 8 * n <= bv_unsigned x < 0x6b1de0 + 40 + 8 * n)%Z -> ~ (0x6b1de0 + 288 + 8 * n <= bv_unsigned x < 0x6b1de0 + 296 + 8 * n)%Z ->
    cxr_mem M0 ra s f arg n rg x = M0 x.
  Proof.
    intros x X1 X2 X3 X4. pose proof (u64_range x). unfold cxr_mem, cxr_F. rewrite !wbytes_outside by wlen. reflexivity.
  Qed.
  Lemma cxr_rd_slot : rdn ASEGS (cxr_mem M0 ra s f arg n rg) (Z_to_bv 64 (0x6b1de0 + 8)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (n + 1))).
  Proof. unfold cxr_mem. apply (rdn_wbytes_hit ASEGS (word_to_le_bytes 4 (Z_to_bv 64 (n + 1)))). wlen. Qed.
  Lemma cxr_rd_a : rdn ASEGS (cxr_mem M0 ra s f arg n rg) (Z_to_bv 64 (0x6b1de0 + 288 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 arg)).
  Proof. unfold cxr_mem. rewrite rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. wlen. Qed.
  Lemma cxr_rd_f : rdn ASEGS (cxr_mem M0 ra s f arg n rg) (Z_to_bv 64 (0x6b1de0 + 32 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f)).
  Proof. unfold cxr_mem. rewrite !rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. wlen. Qed.
End CXRP.

Section PROPS.
  Variable M0 : word -> option byte.
  Variables ra v8 : word.
  Variable s : Z.
  Hypothesis Hs : (0x1000000 <= s - 16)%Z /\ (s < 2 ^ 64)%Z.
  Lemma ens_grows : mem_grows M0 (ens_mem M0 ra v8 s).
  Proof. unfold ens_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma ens_frame : forall x : word, ~ (s - 16 <= bv_unsigned x < s)%Z -> ens_mem M0 ra v8 s x = M0 x.
  Proof. intros x X1. pose proof (u64_range x). unfold ens_mem. rewrite !wbytes_outside by wlen. reflexivity. Qed.
  Lemma lsd_grows : mem_grows M0 (lsd_mem M0).
  Proof. unfold lsd_mem. apply wbytes_grows. Qed.
  Lemma lsd_frame : forall x : word, ~ (0x691da0 <= bv_unsigned x < 0x691da4)%Z -> lsd_mem M0 x = M0 x.
  Proof. intros x X1. pose proof (u64_range x). unfold lsd_mem. rewrite !wbytes_outside by wlen. reflexivity. Qed.
  Lemma lsd_rd : rdn ASEGS (lsd_mem M0) (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Proof. unfold lsd_mem. apply (rdn_wbytes_hit ASEGS (word_to_le_bytes 4 (Z_to_bv 64 1))). wlen. Qed.
  Lemma lse_grows : mem_grows M0 (lse_mem M0 ra v8 s).
  Proof. unfold lse_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma lse_frame : forall x : word, ~ (s - 16 <= bv_unsigned x < s)%Z -> ~ (0x691da0 <= bv_unsigned x < 0x691da4)%Z -> lse_mem M0 ra v8 s x = M0 x.
  Proof. intros x X1 X2. pose proof (u64_range x). unfold lse_mem. rewrite !wbytes_outside by wlen. reflexivity. Qed.
  Lemma lse_rd : rdn ASEGS (lse_mem M0 ra v8 s) (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Proof. unfold lse_mem. apply (rdn_wbytes_hit ASEGS (word_to_le_bytes 4 (Z_to_bv 64 0))). wlen. Qed.
End PROPS.

Section HPROPS.
  Variable M0 : word -> option byte.
  Variable ra : word.
  Variable s : Z.
  Variable rg : bvmap 5 word.
  Hypothesis Hs : (0x1000000 <= s - 96)%Z /\ (s < 2 ^ 64)%Z.
  Lemma hnd_grows : mem_grows M0 (hnd_mem M0 ra s rg).
  Proof. unfold hnd_mem. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
  Lemma hnd_frame : forall x : word, ~ (s - 96 <= bv_unsigned x < s)%Z -> hnd_mem M0 ra s rg x = M0 x.
  Proof. intros x X1. pose proof (u64_range x). unfold hnd_mem. rewrite !wbytes_outside by wlen. reflexivity. Qed.
End HPROPS.

Lemma rd_keep : forall (M M' : word -> option byte) (a : word) (k : nat) bs, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
  (forall x : word, (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k)%Z -> M' x = M x) -> rdn ASEGS M a k = Some bs -> rdn ASEGS M' a k = Some bs.
Proof. intros M M' a k bs Hw E R. rewrite <- R. apply rdn_ext; assumption. Qed.

Section ICPT.
  Variable M0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s f arg n : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 96)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M0 (Z_to_bv 64 (s - 96)) 96%nat = true.
  Hypothesis Hn : (0 < n)%Z /\ (n + 1 < 32)%Z.
  Hypothesis Hf : (0 <= f < 2 ^ 64)%Z.
  Hypothesis Harg : (0 <= arg < 2 ^ 64)%Z.
  Hypothesis HINIT : rdn ASEGS M0 (0x15e9d8 : word) 1%nat = Some [Z_to_bv 8 1].
  Hypothesis HLOFF : rdn ASEGS M0 (0x155160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10)).
  Hypothesis HCNT : rdn ASEGS M0 (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis Hcw : store_ok ASEGS M0 (0x691da0 : word) 4%nat = true.
  Hypothesis HREAL : rdn ASEGS M0 (0x1564c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1351b4)).
  Hypothesis HNL : rdn ASEGS M0 (0x6b2023 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HFIN : rdn ASEGS M0 (0x6b1de0 : word) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis HHEAD : rdn ASEGS M0 (0x6b1df0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (0x6b1de0 + 24))).
  Hypothesis HSLOT : rdn ASEGS M0 (0x6b1de8 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 n)).
  Hypothesis HLOCKW : rdn ASEGS M0 (0x6b1de4 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis HWTAB : forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M0 (Z_to_bv 64 (0x6b1de0 + d)) m = true.

  Definition cxi_fp (z : Z) : Prop :=
    (s - 96 <= z < s)%Z \/ (0x691da0 <= z < 0x691da4)%Z \/ (0x6b1de0 + 8 <= z < 0x6b1de0 + 12)%Z
    \/ (0x6b1de0 + 32 + 8 * n <= z < 0x6b1de0 + 48 + 8 * n)%Z \/ (0x6b1de0 + 288 + 8 * n <= z < 0x6b1de0 + 304 + 8 * n)%Z.

  Lemma sp_cxi : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

  #[local] Ltac rfact := gres; rwH; first [reflexivity | apply bv_eq; reflexivity].
  #[local] Ltac rdk FR H := refine (rd_keep _ _ _ _ _ _ _ H); [wlen | let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply FR; try unfold cxi_fp; revert Hx; cbn [Z.of_nat Pos.to_nat]; ulit; unorm; lia].
  #[local] Ltac oth_seg OTHp := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [gres; apply OTHp; cbn [In]; tauto|]); destruct Hr.
  #[local] Ltac oth_kb OTHp K := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite <- (OTHp r Hr); cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [first [assumption | apply K; [cbv; tauto | cbv; intuition discriminate]]|]); destruct Hr.
  #[local] Ltac kbg K := apply K; [cbv; tauto | cbv; intuition discriminate].

  Theorem cxi_run : forall regs,
    getr regs 10 = Z_to_bv 64 f -> getr regs 11 = Z_to_bv 64 arg -> getr regs 2 = sp -> getr regs 1 = ra -> getr regs 4 = (0x691d90 : word) ->
    exists regs' M1,
      msteps ASEGS (mkst regs (0x6a9ec : word) M0 rom) (mkst regs' ra M1 rom)
      /\ mem_grows M0 M1 /\ (forall x : word, ~ cxi_fp (bv_unsigned x) -> M1 x = M0 x)
      /\ rdn ASEGS M1 (Z_to_bv 64 (0x6b1de0 + 32 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 f))
      /\ rdn ASEGS M1 (Z_to_bv 64 (0x6b1de0 + 288 + 8 * n)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 arg))
      /\ rdn ASEGS M1 (Z_to_bv 64 (0x6b1de0 + 32 + 8 * (n + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7503c))
      /\ rdn ASEGS M1 (Z_to_bv 64 (0x6b1de0 + 288 + 8 * (n + 1))) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
      /\ rdn ASEGS M1 (Z_to_bv 64 (0x6b1de0 + 8)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 (n + 2)))
      /\ rdn ASEGS M1 (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))
      /\ getr regs' 10 = Z_to_bv 64 0 /\ keeps_cs regs regs'.
  Proof.
    intros regs H10 H11 H2 H1 H4. rewrite sp_cxi in H2.
    set (OTH := fun rg : bvmap 5 word => forall r : reg, In r [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rg r = getr regs r).
    assert (OTH0 : OTH regs) by (intros r _; reflexivity).

    set (F1 := wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)).
    set (F2 := wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))).
    set (F3 := wbytes F2 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))).
    set (F4 := wbytes F3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
    set (F5 := wbytes F4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))).
    assert (GR1 : mem_grows M0 F5) by (unfold F5, F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (FR1 : forall x : word, ~ (s - 96 <= bv_unsigned x < s)%Z -> F5 x = M0 x).
    { intros x X1. pose proof (u64_range x). unfold F5, F4, F3, F2, F1. rewrite !wbytes_outside by wlen. reflexivity. }
    assert (FOK : forall (M : word -> option byte) d (m : nat), mem_grows M0 M -> (0 <= d)%Z -> (d + Z.of_nat m <= 96)%Z -> store_ok ASEGS M (Z_to_bv 64 (s - 96 + d)) m = true).
    { intros M d m G Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply (store_ok_sub ASEGS M0 (Z_to_bv 64 (s - 96)) _ 96%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]. }
    assert (S8 : rdn ASEGS F5 (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra)).
    { unfold F5, F4, F3, F2, F1. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S16 : rdn ASEGS F5 (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))).
    { unfold F5, F4, F3, F2. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S24 : rdn ASEGS F5 (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))).
    { unfold F5, F4, F3. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S32 : rdn ASEGS F5 (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))).
    { unfold F5, F4. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }
    assert (S40 : rdn ASEGS F5 (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))).
    { unfold F5. rewrite ?rdn_wbytes_out by wlen. apply rdn_wbytes_hit8. unorm. lia. }

    assert (SEG0 : exists rg, msteps ASEGS (mkst regs (0x6a9ec : word) M0 rom) (mkst rg (0x88340 : word) F5 rom)
                   /\ getr rg 1 = (0x74fe0 : word) /\ getr rg 2 = Z_to_bv 64 (s - 48) /\ getr rg 8 = getr regs 12 /\ getr rg 9 = Z_to_bv 64 arg /\ getr rg 18 = Z_to_bv 64 f /\ OTH rg).
    { eexists. split.
      - stepn Fx_6a9a4 Dx_6a9a4.
        stepiv Fx_74f70 Dx_74f70 (Z_to_bv 64 (s - 48)) ltac:(wv2).
        stepsdq Fx_74f74 Dx_74f74 (Z_to_bv 64 (s - 8)) ra ltac:(replace (s - 8)%Z with (s - 96 + 88)%Z by ring; apply FOK; [apply mem_grows_refl | lia | cbn; lia]).
        change (wbytes M0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) with F1.
        stepsdq Fx_74f78 Dx_74f78 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(replace (s - 16)%Z with (s - 96 + 80)%Z by ring; apply FOK; [unfold F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
        change (wbytes F1 (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) with F2.
        stepsdq Fx_74f7c Dx_74f7c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(replace (s - 24)%Z with (s - 96 + 72)%Z by ring; apply FOK; [unfold F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
        change (wbytes F2 (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) with F3.
        stepsdq Fx_74f80 Dx_74f80 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(replace (s - 32)%Z with (s - 96 + 64)%Z by ring; apply FOK; [unfold F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
        change (wbytes F3 (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))) with F4.
        stepsdq Fx_74f84 Dx_74f84 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(replace (s - 40)%Z with (s - 96 + 56)%Z by ring; apply FOK; [unfold F4, F3, F2, F1; repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl | lia | cbn; lia]).
        change (wbytes F4 (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19))) with F5.
        stepn Fx_74f88 Dx_74f88. stepn Fx_74f8c Dx_74f8c. stepn Fx_74f90 Dx_74f90.
        stepn Fx_74f94 Dx_74f94.
        apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. oth_seg OTH0. }
    destruct SEG0 as (rgA & RUN0 & A1 & A2 & A8 & A9 & A18 & OTHA).

    assert (Hs16 : (0x1000000 <= s - 48 - 16)%Z /\ (s - 48 < 2 ^ 64)%Z) by lia.
    assert (UA : bv_unsigned (Z_to_bv 64 (s - 48)) = (s - 48)%Z) by (unorm; reflexivity).
    assert (RETA : forall k : word, ret_ok k -> ret_ok k) by (intros k X; exact X).
    destruct (ens_run F5 rom (Z_to_bv 64 (s - 48)) (0x74fe0 : word) (getr regs 12) (s - 48) UA ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Hs16
                ltac:(replace (s - 48 - 16)%Z with (s - 96 + 32)%Z by ring; apply FOK; [exact GR1 | lia | cbn; lia])
                ltac:(rdk FR1 HINIT) rgA A2 A1 A8) as (rgB & RUNB & B1 & B2 & B8 & KB).
    set (M2 := ens_mem F5 (0x74fe0 : word) (getr regs 12) (s - 48)) in *.
    assert (GR2 : mem_grows M0 M2) by (eapply mem_grows_trans; [exact GR1 | apply ens_grows]).
    assert (FR2 : forall x : word, ~ (s - 96 <= bv_unsigned x < s)%Z -> M2 x = M0 x).
    { intros x X1. unfold M2. rewrite ens_frame by lia. apply FR1. exact X1. }
    assert (B9 : getr rgB 9 = Z_to_bv 64 arg) by (rewrite <- A9; kbg KB).
    assert (B18 : getr rgB 18 = Z_to_bv 64 f) by (rewrite <- A18; kbg KB).
    assert (OTHB : OTH rgB) by (oth_kb OTHA KB).

    assert (SEG1 : exists rg, msteps ASEGS (mkst rgB (0x74fe0 : word) M2 rom) (mkst rg (0xaea7c : word) M2 rom)
                   /\ getr rg 1 = (0x74fe4 : word) /\ getr rg 2 = Z_to_bv 64 (s - 48) /\ getr rg 8 = getr regs 12 /\ getr rg 9 = Z_to_bv 64 arg /\ getr rg 18 = Z_to_bv 64 f /\ OTH rg).
    { eexists. split.
      - stepn Fx_74f98 Dx_74f98. apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. oth_seg OTHB. }
    destruct SEG1 as (rgC & RUN1 & C1 & C2 & C8 & C9 & C18 & OTHC).
    destruct (lsd_run M2 rom (0x74fe4 : word) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) ltac:(rdk FR2 HLOFF) ltac:(rdk FR2 HCNT) (store_ok_mono _ _ M0 M2 _ GR2 Hcw)
                rgC ltac:(rewrite (OTHC 4%bv) by (cbn [In]; tauto); exact H4) C1) as (rgD & RUND & KD).
    set (M3 := lsd_mem M2) in *.
    assert (GR3 : mem_grows M0 M3) by (eapply mem_grows_trans; [exact GR2 | apply lsd_grows]).
    assert (FR3 : forall x : word, ~ (s - 96 <= bv_unsigned x < s)%Z -> ~ (0x691da0 <= bv_unsigned x < 0x691da4)%Z -> M3 x = M0 x).
    { intros x X1 X2. unfold M3. rewrite lsd_frame by lia. apply FR2. exact X1. }
    assert (D2 : getr rgD 2 = Z_to_bv 64 (s - 48)) by (rewrite <- C2; apply KD; cbv; tauto).
    assert (D8 : getr rgD 8 = getr regs 12) by (rewrite <- C8; apply KD; cbv; tauto).
    assert (D9 : getr rgD 9 = Z_to_bv 64 arg) by (rewrite <- C9; apply KD; cbv; tauto).
    assert (D18 : getr rgD 18 = Z_to_bv 64 f) by (rewrite <- C18; apply KD; cbv; tauto).
    assert (OTHD : OTH rgD). { intros r Hr. rewrite <- (OTHC r Hr). apply KD. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [cbv; tauto|]). destruct Hr. }

    assert (REAL3 : rdn ASEGS M3 (0x1564c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1351b4))) by (rdk FR3 HREAL).
    assert (SEG2 : exists rg, msteps ASEGS (mkst rgD (0x74fe4 : word) M3 rom) (mkst rg (0x1351b4 : word) M3 rom)
                   /\ getr rg 1 = (0x74ffc : word) /\ getr rg 2 = Z_to_bv 64 (s - 48) /\ getr rg 10 = Z_to_bv 64 f /\ getr rg 11 = Z_to_bv 64 arg /\ getr rg 19 = (0x155fe4 : word) /\ OTH rg).
    { eexists. split.
      - stepn Fx_74f9c Dx_74f9c.
        mld Fx_74fa0 Dx_74fa0 (0x1564c8 : word) REAL3.
        stepn Fx_74fa4 Dx_74fa4. stepn Fx_74fa8 Dx_74fa8. stepn Fx_74fac Dx_74fac.
        stepret Fx_74fb0 Dx_74fb0 (0x1351b4 : word) ltac:(apply bv_eq; vm_compute; reflexivity). vnorm.
        apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. oth_seg OTHD. }
    destruct SEG2 as (rgE & RUN2 & E1 & E2 & E10 & E11 & E19 & OTHE).
    assert (Hs48 : (0x1000000 <= s - 48 - 48)%Z /\ (s - 48 < 2 ^ 64)%Z) by lia.
    assert (Hn1 : (0 < n < 32)%Z) by lia.
    assert (TOK : forall (M : word -> option byte), mem_grows M0 M -> forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 544)%Z -> store_ok ASEGS M (Z_to_bv 64 (0x6b1de0 + d)) m = true).
    { intros M G d m Hd Hm. apply (store_ok_mono _ _ M0 M _ G). apply HWTAB; assumption. }
    destruct (cxa_reg_run M3 rom (Z_to_bv 64 (s - 48)) (0x74ffc : word) (s - 48) f arg n UA ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Hs48
                ltac:(replace (s - 48 - 48)%Z with (s - 96 + 0)%Z by ring; apply FOK; [exact GR3 | lia | cbn; lia]) Hn1 Hf Harg
                ltac:(rdk FR3 HNL) ltac:(rdk FR3 HFIN) ltac:(rdk FR3 HHEAD) ltac:(rdk FR3 HSLOT) ltac:(rdk FR3 HLOCKW) (TOK M3 GR3)
                rgE E10 E11 E2 E1) as (rgF & RUNF & F10 & F2' & F1' & F8 & F9 & F18 & F19 & F20 & KF).
    set (M4 := cxr_mem M3 (0x74ffc : word) (s - 48) f arg n rgE) in *.
    assert (GR4 : mem_grows M0 M4) by (eapply mem_grows_trans; [exact GR3 | apply cxr_grows]).
    assert (FR4 : forall x : word, ~ cxi_fp (bv_unsigned x) -> M4 x = M0 x).
    { intros x X. unfold cxi_fp in X. unfold M4. rewrite cxr_frame by lia. apply FR3; lia. }
    assert (OTHF : OTH rgF) by (oth_kb OTHE KF).

    assert (REAL4 : rdn ASEGS M4 (0x1564c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1351b4))) by (rdk FR4 HREAL).
    assert (SEG3 : exists rg, msteps ASEGS (mkst rgF (0x74ffc : word) M4 rom) (mkst rg (0x1351b4 : word) M4 rom)
                   /\ getr rg 1 = (0x75018 : word) /\ getr rg 2 = Z_to_bv 64 (s - 48) /\ getr rg 8 = Z_to_bv 64 0 /\ getr rg 10 = Z_to_bv 64 0x7503c /\ getr rg 11 = Z_to_bv 64 0 /\ OTH rg).
    { eexists. split.
      - mld Fx_74fb4 Dx_74fb4 (0x1564c8 : word) REAL4.
        stepn Fx_74fb8 Dx_74fb8. stepn Fx_74fbc Dx_74fbc. stepn Fx_74fc0 Dx_74fc0. stepn Fx_74fc4 Dx_74fc4. stepn Fx_74fc8 Dx_74fc8.
        stepret Fx_74fcc Dx_74fcc (0x1351b4 : word) ltac:(apply bv_eq; vm_compute; reflexivity). vnorm.
        apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. oth_seg OTHF. }
    destruct SEG3 as (rgG & RUN3 & G1 & G2 & G8 & G10 & G11 & OTHG).
    assert (Hn2 : (0 < n + 1 < 32)%Z) by lia.
    destruct (cxa_reg_run M4 rom (Z_to_bv 64 (s - 48)) (0x75018 : word) (s - 48) 0x7503c 0 (n + 1) UA ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Hs48
                ltac:(replace (s - 48 - 48)%Z with (s - 96 + 0)%Z by ring; apply FOK; [exact GR4 | lia | cbn; lia]) Hn2 ltac:(lia) ltac:(lia)
                ltac:(rdk FR4 HNL) ltac:(rdk FR4 HFIN) ltac:(rdk FR4 HHEAD)
                ltac:(replace (0x6b1de8 : word) with (Z_to_bv 64 (0x6b1de0 + 8)) by (apply bv_eq; reflexivity); apply cxr_rd_slot; lia)
                ltac:(rdk FR4 HLOCKW) (TOK M4 GR4)
                rgG G10 G11 G2 G1) as (rgH & RUNH & H10' & H2' & H1' & H8 & H9 & H18 & H19 & H20 & KH).
    set (M5 := cxr_mem M4 (0x75018 : word) (s - 48) 0x7503c 0 (n + 1) rgG) in *.
    assert (GR5 : mem_grows M0 M5) by (eapply mem_grows_trans; [exact GR4 | apply cxr_grows]).
    assert (FR5 : forall x : word, ~ cxi_fp (bv_unsigned x) -> M5 x = M0 x).
    { intros x X. unfold M5. rewrite cxr_frame by (unfold cxi_fp in X; lia). apply FR4. exact X. }
    assert (OTHH : OTH rgH) by (oth_kb OTHG KH).

    assert (SEG4 : exists rg, msteps ASEGS (mkst rgH (0x75018 : word) M5 rom) (mkst rg (0xaea98 : word) M5 rom)
                   /\ getr rg 1 = (0x7501c : word) /\ getr rg 2 = Z_to_bv 64 (s - 48) /\ getr rg 8 = Z_to_bv 64 0 /\ OTH rg).
    { eexists. split.
      - stepn Fx_74fd0 Dx_74fd0. apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [gres; rewrite H8; exact G8|]. oth_seg OTHH. }
    destruct SEG4 as (rgI & RUN4 & I1 & I2 & I8 & OTHI).
    assert (CNT5 : rdn ASEGS M5 (0x691da0 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
    { apply (rd_keep M3 M5); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; ulit; intros Hx; unfold M5; rewrite cxr_frame by lia; unfold M4; rewrite cxr_frame by lia; reflexivity | apply lsd_rd]. }
    destruct (lse_run M5 rom (Z_to_bv 64 (s - 48)) (0x7501c : word) (Z_to_bv 64 0) (s - 48) UA ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity) Hs16
                ltac:(replace (s - 48 - 16)%Z with (s - 96 + 32)%Z by ring; apply FOK; [exact GR5 | lia | cbn; lia])
                ltac:(rdk FR5 HLOFF) CNT5 (store_ok_mono _ _ M0 M5 _ GR5 Hcw)
                rgI I2 I1 I8 ltac:(rewrite (OTHI 4%bv) by (cbn [In]; tauto); exact H4)) as (rgJ & RUNJ & J1 & J2 & J8 & KJ).
    set (M6 := lse_mem M5 (0x7501c : word) (Z_to_bv 64 0) (s - 48)) in *.
    assert (GR6 : mem_grows M0 M6) by (eapply mem_grows_trans; [exact GR5 | apply lse_grows]).
    assert (FR6 : forall x : word, ~ cxi_fp (bv_unsigned x) -> M6 x = M0 x).
    { intros x X. unfold M6. rewrite lse_frame by (unfold cxi_fp in X; lia). apply FR5. exact X. }
    assert (OTHJ : OTH rgJ) by (oth_kb OTHI KJ).

    assert (KEEP : forall x : word, (s - 48 <= bv_unsigned x < s)%Z -> M6 x = F5 x).
    { intros x Hx. unfold M6. rewrite lse_frame by lia. unfold M5. rewrite cxr_frame by lia. unfold M4. rewrite cxr_frame by lia.
      unfold M3. rewrite lsd_frame by lia. unfold M2. rewrite ens_frame by lia. reflexivity. }
    assert (SL : forall k v, (8 <= k <= 40)%Z -> rdn ASEGS F5 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v) -> rdn ASEGS M6 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros k v Hk R. refine (rd_keep F5 M6 _ _ _ _ _ R); [wlen|]. intros x Hx. apply KEEP. revert Hx. cbn [Z.of_nat Pos.to_nat]. unorm. lia. }

    assert (SEG5 : exists rg, msteps ASEGS (mkst rgJ (0x7501c : word) M6 rom) (mkst rg ra M6 rom)
                   /\ getr rg 10 = Z_to_bv 64 0 /\ getr rg 1 = ra /\ getr rg 2 = Z_to_bv 64 s /\ getr rg 8 = getr regs 8 /\ getr rg 9 = getr regs 9 /\ getr rg 18 = getr regs 18
                   /\ getr rg 19 = getr regs 19 /\ OTH rg).
    { eexists. split.
      - stepn Fx_74fd4 Dx_74fd4.
        stepld Fx_74fd8 Dx_74fd8 ra ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 8)) by (symmetry; wv2) end; apply SL; [lia | exact S8]).
        stepld Fx_74fdc Dx_74fdc (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 16)) by (symmetry; wv2) end; apply SL; [lia | exact S16]).
        stepld Fx_74fe0 Dx_74fe0 (getr regs 9) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 24)) by (symmetry; wv2) end; apply SL; [lia | exact S24]).
        stepld Fx_74fe4 Dx_74fe4 (getr regs 18) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 32)) by (symmetry; wv2) end; apply SL; [lia | exact S32]).
        stepld Fx_74fe8 Dx_74fe8 (getr regs 19) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (s - 40)) by (symmetry; wv2) end; apply SL; [lia | exact S40]).
        stepiv Fx_74fec Dx_74fec (Z_to_bv 64 s) ltac:(wv2).
        stepret Fx_74ff0 Dx_74ff0 ra ltac:(rwH; reflexivity).
        apply mst_refl.
      - split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. split; [rfact|]. oth_seg OTHJ. }
    destruct SEG5 as (rgK & RUN5 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & OTHK).
    exists rgK, M6.
    split. { eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUNB|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUND|].
             eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUNF|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUNH|].
             eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUNJ|]. exact RUN5. }
    split; [exact GR6|]. split; [exact FR6|].
    split. { apply (rd_keep M4 M6); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; unorm; intros Hx; unfold M6; rewrite lse_frame by lia; unfold M5; rewrite cxr_frame by lia; reflexivity | apply cxr_rd_f; lia]. }
    split. { apply (rd_keep M4 M6); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; unorm; intros Hx; unfold M6; rewrite lse_frame by lia; unfold M5; rewrite cxr_frame by lia; reflexivity | apply cxr_rd_a; lia]. }
    split. { apply (rd_keep M5 M6); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; unorm; intros Hx; unfold M6; rewrite lse_frame by lia; reflexivity | apply cxr_rd_f; lia]. }
    split. { apply (rd_keep M5 M6); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; unorm; intros Hx; unfold M6; rewrite lse_frame by lia; reflexivity | apply cxr_rd_a; lia]. }
    split. { replace (n + 2)%Z with (n + 1 + 1)%Z by ring. apply (rd_keep M5 M6); [wlen | intros x Hx; revert Hx; cbn [Z.of_nat Pos.to_nat]; unorm; intros Hx; unfold M6; rewrite lse_frame by lia; reflexivity | apply cxr_rd_slot; lia]. }
    split; [apply lse_rd; lia|]. split; [exact K10|].
    intros r Hr. unfold callee_saved in Hr. cbn [In] in Hr.
    destruct Hr as [<- | Hr]; [rewrite K1; symmetry; exact H1|]. destruct Hr as [<- | Hr]; [rewrite K2, H2; reflexivity|].
    destruct Hr as [<- | Hr]; [apply OTHK; cbn [In]; tauto|]. destruct Hr as [<- | Hr]; [apply OTHK; cbn [In]; tauto|].
    destruct Hr as [<- | Hr]; [exact K8|]. destruct Hr as [<- | Hr]; [exact K9|]. destruct Hr as [<- | Hr]; [exact K18|]. destruct Hr as [<- | Hr]; [exact K19|].
    repeat (destruct Hr as [<- | Hr]; [apply OTHK; cbn [In]; tauto|]). destruct Hr.
  Qed.
End ICPT.
End FPX_1.
