(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX BellsX HWord.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BXXRep RtB_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_ContStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition TF_HEAD : Z := 0xffed4.
Definition TF_ANN_RET : Z := 0xfff44.
Definition TF_XP_RET : Z := 0xfff50.
Definition TF_RET : Z := 0xfff9c.

Definition KTB1 : list reg := [3; 4; 19; 25; 26; 27]%bv.
Definition KTPOP : list reg := [2; 3; 4; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTCALL : list reg := [2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTBACK : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition KTEXIT : list reg := [3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma ext4_small : forall x, 0 <= x < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. f_equal.
  change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). rewrite Z.mod_small by lia.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31). change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Section TF1.
  Context {HCEIL : HeapCeil}.

  Lemma tf_b1 : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (SP v lo : Z),
    getr R 1 = ra -> getr R 2 = Z_to_bv 64 SP -> getr R 8 = s0 -> getr R 9 = s1 -> getr R 18 = s2 -> getr R 19 = s3 ->
    getr R 20 = s4 -> getr R 21 = s5 -> getr R 22 = s6 -> getr R 23 = s7 -> getr R 24 = s8 -> getr R 10 = Z_to_bv 64 v -> rfull R ->
    SP mod 16 = 0 -> 2 ^ 45 <= SP <= 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 47 -> v <> 0 -> v mod 8 = 0 ->
    stk asegs m lo SP -> lo <= SP - 80 -> mem_inv asegs m -> ACONST m ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 AT_TAKE_FIRST) fc None m ro) (MS R' F (Z_to_bv 64 TF_HEAD) fc None M' ro)
      /\ rfull R' /\ kept_in KTB1 R R'
      /\ getr R' 2 = Z_to_bv 64 (SP - 80) /\ getr R' 8 = Z_to_bv 64 v /\ getr R' 9 = Z_to_bv 64 (v + 8) /\ getr R' 18 = Z_to_bv 64 (v + 16)
      /\ getr R' 20 = Z_to_bv 64 5 /\ getr R' 21 = Z_to_bv 64 0x7fff8000 /\ getr R' 22 = Z_to_bv 64 (sh (v + 8))
      /\ getr R' 23 = Z_to_bv 64 (sh v) /\ getr R' 24 = Z_to_bv 64 (sh (v + 16))
      /\ munch [(SP - 80, SP)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo' hi', stk asegs m lo' hi' -> stk asegs M' lo' hi')
      /\ rw_cells asegs M' (SP - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Proof.
    intros R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 SP v lo ra_at sp_at s0_at s1_at s2_at s3_at s4_at s5_at s6_at
      s7_at s8_at a0_at full_R sp_align sp_range v_nonneg v_top v_nz v_align stack_m lo_room inv_m const_m.
    subst ra s0 s1 s2 s3 s4 s5 s6 s7 s8.
    pose (env0 := Eseed R []).
    assert (sp_ev : ev env0 2 = Z_to_bv 64 SP) by (subst env0; rewrite (Eseed_regZ R [] 2%bv); exact sp_at).
    assert (a0_ev : ev env0 10 = Z_to_bv 64 v) by (subst env0; rewrite (Eseed_regZ R [] 10%bv); exact a0_at).
    assert (shadow_sum : forall x, 0 <= x < 2 ^ 47 ->
      alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (sh x)).
    { intros x x_rng. pose proof (div8_bound x x_rng) as quot.
      rewrite w_srl by lia. change (2 ^ 3) with 8. rewrite w_add by lia.
      unfold sh, ASHADOW_BASE. f_equal. lia. }
    assert (frame_wr : wr_at asegs m (SP - 80) 80).
    { eapply wr_at_sub; [exact (wr_at_of_stk asegs m lo SP stack_m) | lia | lia | lia]. }
    destruct (ACONST_shbase m const_m) as [got_cell base_cell].
    assert (regs0 : regs_ok env0 sr_id R) by apply regs_ok_seed.
    assert (know0 : know_ok asegs env0 m
      [KWr (SA (EVar 2) (-80)) (ELit 80);
       KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
       KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit ASHADOW_BASE)]).
    { unfold know_ok. repeat apply Forall_cons; try apply Forall_nil.
      - apply (kwr_of_stk asegs env0 m lo SP _ _ stack_m); unfold estart, elenZ; cbn [a_base a_off edenot];
          rewrite ?sp_ev, ?u64_of_Z by lia; lia.
      - eapply (kword_of_rw_cells asegs env0 m AGOT_SHBASE _ 0 _ _ _ 8 got_cell);
          [reflexivity | reflexivity | lia | reflexivity | unfold AGOT_SHBASE; lia | unfold AGOT_SHBASE; lia | reflexivity].
      - eapply (kword_of_rw_cells asegs env0 m ASHBASE_CELL _ 0 _ _ _ 8 base_cell);
          [reflexivity | reflexivity | lia | reflexivity | unfold ASHBASE_CELL; lia | unfold ASHBASE_CELL; lia | reflexivity]. }
    xrun_at (PropExec.mkFP F fc) asegs R AT_TAKE_FIRST m ro regs0 know0 40%nat [TF_HEAD] (SCR [false; false] [] []) 32%N.
    { unfold scs_denot; repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot];
        lazymatch goal with
        | |- branch_taken BC_EQ _ _ = _ => cbn [edenot]; rewrite a0_ev, br_eq by lia; apply Z.eqb_neq; exact v_nz
        | |- branch_taken BC_NE _ _ = _ => cbn [edenot]; rewrite a0_ev, land7_val, v_align by lia; reflexivity
        | |- _ => unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?sp_ev; rewrite ?u64_of_Z by lia; lia
        end. }
    rename R' into R1, HR' into regs1, Hlf into flat1, Hms into run1.
    lazymatch type of flat1 with log_flat _ ?lg => exists R1, (mem_denot env0 m lg) end.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
      | |- CatSim.msteps _ _ _ => exact run1
      | |- rfull _ => exact (msteps_full asegs _ _ run1 full_R)
      | |- kept_in _ _ _ =>
          intros r r_in; apply (syms_id_sound R _ _ R1 KTB1 regs1); [vm_compute; reflexivity | exact r_in]
      | |- getr _ _ = _ =>
          rewrite regs1;
          lazymatch goal with |- edenot _ (sr_get ?sr ?r) = _ =>
            let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end;
          cbn [edenot]; rewrite ?a0_ev, ?sp_ev;
          first [ reflexivity
                | rewrite w_addm by lia; f_equal; lia
                | apply shadow_sum; lia
                | rewrite w_add by lia; first [reflexivity | apply shadow_sum; lia] ]
      | |- munch _ _ _ =>
          eapply munch_eqW; [eapply (munch_mem_denot_sb [(-80, 0)] (EVar 2)); [exact flat1 | vm_compute; reflexivity] |];
          cbn [map fst snd edenot]; rewrite sp_ev, u64_of_Z by lia; f_equal; f_equal; lia
      | |- wmono _ _ _ => apply wmono_mem_denot
      | |- mem_inv _ _ => exact (msteps_mem_inv asegs _ _ run1 inv_m)
      | |- forall _ _, stk _ _ _ _ -> _ => intros lo1 hi1 frame_stk; apply stk_mem_denot; exact frame_stk
      | |- rw_cells _ _ _ _ =>
          let slot k :=
            eapply (rw_cells_log_nth_sb env0 m _ k (EVar 2));
            [ exact flat1 | reflexivity | vm_compute; reflexivity
            | cbn [edenot]; rewrite sp_ev, u64_of_Z by lia; lia
            | eapply wr_at_sub; [exact frame_wr | lia | lia | lia]
            | reflexivity | exact I | reflexivity ] in
          let rec walk k :=
            lazymatch goal with
            | |- rw_cells _ _ _ [_] => slot k
            | |- rw_cells _ _ _ (_ :: _) => apply rw_cells_cons8_c; [slot k | walk (S k)]
            end in
          walk 0%nat
      end.
  Qed.

  Lemma tf_pop : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (v b d c t j : Z),
    getr R 8 = Z_to_bv 64 v -> getr R 9 = Z_to_bv 64 (v + 8) -> getr R 18 = Z_to_bv 64 (v + 16) -> getr R 20 = Z_to_bv 64 5 ->
    getr R 21 = Z_to_bv 64 0x7fff8000 -> getr R 22 = Z_to_bv 64 (sh (v + 8)) -> getr R 23 = Z_to_bv 64 (sh v) -> getr R 24 = Z_to_bv 64 (sh (v + 16)) -> rfull R ->
    v mod 8 = 0 -> 0x6e8000 <= v -> (v + 24 <= 0x7fff7000 \/ 0x10007fff8000 <= v) -> v + 24 <= 2 ^ 47 ->
    16 <= b -> b mod 8 = 0 -> b <= d -> d + 4 <= c -> c <= 2 ^ 47 -> d mod 4 = 0 -> (c <= 0x7fff7000 \/ 0x10007fff8000 <= b) ->
    (v + 24 <= b \/ c <= v) ->
    fldA m v 8 b -> fldA m (v + 8) 8 (d + 4) -> fldA m (v + 16) 8 c -> gz m v 24 ->
    fldA m d 4 t -> 0 <= t < 2 ^ 31 ->
    LbB_Kit.shk m d j -> (j = 0 \/ (d mod 8 = 0 /\ 4 <= j < 8)) ->
    wr_at asegs m (v + 8) 8 ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_HEAD) fc None m ro) (MS R' F (Z_to_bv 64 AANNOTATE_CC) fc None M' ro)
      /\ rfull R' /\ kept_in KTPOP R R'
      /\ getr R' 1 = Z_to_bv 64 TF_ANN_RET /\ getr R' 10 = Z_to_bv 64 b /\ getr R' 11 = Z_to_bv 64 c
      /\ getr R' 12 = Z_to_bv 64 (d + 4) /\ getr R' 13 = Z_to_bv 64 d /\ getr R' 19 = Z_to_bv 64 t
      /\ getr R' 8 = Z_to_bv 64 v /\ getr R' 9 = Z_to_bv 64 (v + 8) /\ getr R' 18 = Z_to_bv 64 (v + 16) /\ getr R' 20 = Z_to_bv 64 5
      /\ getr R' 21 = Z_to_bv 64 0x7fff8000 /\ getr R' 22 = Z_to_bv 64 (sh (v + 8)) /\ getr R' 23 = Z_to_bv 64 (sh v) /\ getr R' 24 = Z_to_bv 64 (sh (v + 16))
      /\ munch [(v + 8, v + 16)] m M' /\ wmono asegs m M' /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ (mem_inv asegs m -> mem_inv asegs M')
      /\ rw_cells asegs M' (v + 8) [C8 (Z_to_bv 64 d)].
  Proof.
    intros R F fc m ro v b d c t j s0_at s1_at s2_at s4_at s5_at s6_at s7_at s8_at full_R
      v_align v_low v_window v_top b_low b_align b_le_d d_room c_top d_align c_window apart
      cell_b cell_d4 cell_c shadow_v cell_t t_range shadow_d j_cases slot_wr.
    assert (j_byte : 0 <= j < 8) by lia.
    pose proof (div8_bound v ltac:(lia)) as q_v.
    pose proof (div8_bound (v + 8) ltac:(lia)) as q_v8.
    pose proof (div8_bound (v + 16) ltac:(lia)) as q_v16.
    pose proof (div8_bound d ltac:(lia)) as q_d.
    assert (d_low2 : Z.land d 3 = 0).
    { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact d_align. }
    pose (env0 := Eseed R [Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d; Z_to_bv 64 j; Z_to_bv 64 t]).
    assert (ev8 : ev env0 8 = Z_to_bv 64 v) by (subst env0; rewrite (Eseed_regZ R _ 8%bv); exact s0_at).
    assert (ev9 : ev env0 9 = Z_to_bv 64 (v + 8)) by (subst env0; rewrite (Eseed_regZ R _ 9%bv); exact s1_at).
    assert (ev18 : ev env0 18 = Z_to_bv 64 (v + 16)) by (subst env0; rewrite (Eseed_regZ R _ 18%bv); exact s2_at).
    assert (ev_b : ev env0 32 = Z_to_bv 64 b) by reflexivity.
    assert (ev_c : ev env0 33 = Z_to_bv 64 c) by reflexivity.
    assert (ev_d : ev env0 34 = Z_to_bv 64 d) by reflexivity.
    assert (ev_j : ev env0 35 = Z_to_bv 64 j) by reflexivity.
    assert (ev_t : ev env0 36 = Z_to_bv 64 t) by reflexivity.
    assert (plain_at : forall (n : N) x o, ev env0 n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
      estart env0 (SA (EVar n) o) = x + o).
    { intros n x o ev_x x_rng. unfold estart. cbn [a_base a_off edenot]. rewrite ev_x, u64_of_Z by lia. reflexivity. }
    assert (sh_at : forall (n : N) x, ev env0 n = Z_to_bv 64 x -> 0 <= x < 2 ^ 47 ->
      estart env0 (SA (EAlu ALU_SRL (EVar n) (ELit 3)) 2147450880) = sh x).
    { intros n x ev_x x_rng. unfold estart. cbn [a_base a_off].
      rewrite (srl3_val env0 (EVar n) x ev_x) by lia. unfold sh, ASHADOW_BASE. lia. }
    assert (shadow_sum : forall x, 0 <= x < 2 ^ 47 ->
      alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (sh x)).
    { intros x x_rng. pose proof (div8_bound x x_rng) as quot.
      rewrite w_srl by lia. change (2 ^ 3) with 8. rewrite w_add by lia.
      unfold sh, ASHADOW_BASE. f_equal. lia. }
    assert (regs0 : regs_ok env0 (srs sr_id
      [(20%bv, ELit 5); (21%bv, ELit 2147450880);
       (22%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 9) (ELit 3)) (ELit 2147450880));
       (23%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 8) (ELit 3)) (ELit 2147450880));
       (24%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 18) (ELit 3)) (ELit 2147450880))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [discriminate|]); cbn [edenot]; rewrite ?ev8, ?ev9, ?ev18.
      - exact s4_at.
      - exact s5_at.
      - rewrite s6_at. symmetry. apply shadow_sum. lia.
      - rewrite s7_at. symmetry. apply shadow_sum. lia.
      - rewrite s8_at. symmetry. apply shadow_sum. lia. }
    assert (know_fld : forall (sa : saddr) (k : nat) (p x : Z) (ex : expr),
      fldA m p k x -> (k <= 8)%nat -> estart env0 sa = p -> 0 <= p < 2 ^ 64 -> p + Z.of_nat k <= 2 ^ 64 ->
      edenot env0 ex = Z_to_bv 64 x -> kentry_ok asegs env0 m (KWord sa k ex)).
    { intros sa k p x ex fld_px k_le at_p p_rng p_hi val_x. cbn [kentry_ok].
      pose proof (Nat2Z.is_nonneg k) as k_pos.
      split; [exact k_le|]. split; [unfold flat; rewrite at_p; lia|].
      rewrite (adenot_of_estart env0 sa p at_p p_rng), val_x. exact fld_px. }
    assert (know0 : know_ok asegs env0 m
      [KWord (SA (EAlu ALU_SRL (EVar 9) (ELit 3)) 2147450880) 1 (ELit 0);
       KWord (SA (EAlu ALU_SRL (EVar 8) (ELit 3)) 2147450880) 1 (ELit 0);
       KWord (SA (EAlu ALU_SRL (EVar 18) (ELit 3)) 2147450880) 1 (ELit 0);
       KWord (SA (EVar 9) 0) 8 (EAlu ALU_ADD (EVar 34) (ELit 4));
       KWord (SA (EVar 8) 0) 8 (EVar 32);
       KWord (SA (EVar 18) 0) 8 (EVar 33);
       KWord (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) 2147450880) 1 (EVar 35);
       KWord (SA (EVar 34) 0) 4 (EVar 36);
       KWr (SA (EVar 9) 0) (ELit 8)]).
    { unfold know_ok. repeat apply Forall_cons; try apply Forall_nil.
      - apply (kshadow0 env0 m (EVar 9) (v + 8) ev9); [lia | exact (gz_at m v 24 8 shadow_v ltac:(lia))].
      - pose proof (gz_at m v 24 0 shadow_v ltac:(lia)) as sv. rewrite Z.add_0_r in sv.
        apply (kshadow0 env0 m (EVar 8) v ev8); [lia | exact sv].
      - apply (kshadow0 env0 m (EVar 18) (v + 16) ev18); [lia | exact (gz_at m v 24 16 shadow_v ltac:(lia))].
      - apply (know_fld _ 8%nat (v + 8) (d + 4)); [exact cell_d4 | lia | rewrite (plain_at 9%N (v + 8)) by (exact ev9 || lia); lia | lia | lia |].
        cbn [edenot]. rewrite ev_d, w_add by lia. reflexivity.
      - apply (know_fld _ 8%nat v b); [exact cell_b | lia | rewrite (plain_at 8%N v) by (exact ev8 || lia); lia | lia | lia | exact ev_b].
      - apply (know_fld _ 8%nat (v + 16) c); [exact cell_c | lia | rewrite (plain_at 18%N (v + 16)) by (exact ev18 || lia); lia | lia | lia | exact ev_c].
      - apply (kshadow env0 m (EVar 34) d j (EVar 35) ev_d); [lia | lia | exact ev_j | exact shadow_d].
      - apply (know_fld _ 4%nat d t); [exact cell_t | lia | rewrite (plain_at 34%N d) by (exact ev_d || lia); lia | lia | lia | exact ev_t].
      - apply (kwr_of_wr_at asegs env0 m (v + 8) 8 _ _ slot_wr); rewrite ?(plain_at 9%N (v + 8)) by (exact ev9 || lia);
          unfold elenZ; cbn [edenot]; rewrite ?u64_of_Z by lia; lia. }
    destruct j_cases as [j_zero | [d_al8 j_big]];
      [ xrun_at (PropExec.mkFP F fc) asegs R TF_HEAD m ro regs0 know0 60%nat [AANNOTATE_CC]
          (SCR [false; false; false; false; false; false; false; false; false] [] []) 37%N
      | xrun_at (PropExec.mkFP F fc) asegs R TF_HEAD m ro regs0 know0 60%nat [AANNOTATE_CC]
          (SCR [false; false; true; true; false; false; false; false; false; false] [] []) 37%N ].
    1, 3: unfold scs_denot; repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot];
      lazymatch goal with
      | |- branch_taken _ _ _ = _ =>
          cbn [edenot]; rewrite ?ev_b, ?ev_c, ?ev_d, ?ev_j, ?ev_t;
          rewrite ?ext4_small, ?ext_shadow_small, ?land7_val, ?w_and by lia;
          rewrite ?d_low2;
          repeat match goal with al : ?x mod 8 = 0 |- context [?x mod 8] => rewrite al end;
          rewrite ?w_add by lia;
          rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_lts_small by lia; bool_lia
      | |- _ =>
          unfold flat, elenZ;
          rewrite ?(sh_at 9%N (v + 8)), ?(sh_at 8%N v), ?(sh_at 18%N (v + 16)), ?(sh_at 34%N d),
                  ?(plain_at 9%N (v + 8)), ?(plain_at 8%N v), ?(plain_at 18%N (v + 16)), ?(plain_at 34%N d)
            by first [assumption | lia];
          cbn [edenot]; rewrite ?u64_of_Z by lia; unfold sh, ASHADOW_BASE; lia
      end.
    all: rename R' into R1, HR' into regs1, Hlf into flat1, Hms into run1.
    all: lazymatch type of flat1 with log_flat _ ?lg => exists R1, (mem_denot env0 m lg) end.
    all: repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
      | |- CatSim.msteps _ _ _ => exact run1
      | |- rfull _ => exact (msteps_full asegs _ _ run1 full_R)
      | |- kept_in _ _ _ =>
          intros r r_in; apply (syms_id_sound R _ _ R1 KTPOP regs1); [vm_compute; reflexivity | exact r_in]
      | |- getr _ _ = _ =>
          rewrite regs1;
          lazymatch goal with |- edenot _ (sr_get ?sr ?r) = _ =>
            let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end;
          cbn [edenot]; rewrite ?ev8, ?ev9, ?ev18, ?ev_b, ?ev_c, ?ev_d, ?ev_t;
          first [ reflexivity
                | apply shadow_sum; lia
                | rewrite w_add by lia; reflexivity
                | rewrite ext4_small by lia; reflexivity ]
      | |- munch _ _ _ =>
          eapply munch_eqW; [eapply (munch_mem_denot_sb [(0, 8)] (EVar 9)); [exact flat1 | vm_compute; reflexivity] |];
          cbn [map fst snd edenot]; rewrite ev9, u64_of_Z by lia; f_equal; f_equal; lia
      | |- wmono _ _ _ => apply wmono_mem_denot
      | |- forall _ _, stk _ _ _ _ -> _ => intros lo1 hi1 frame_stk; apply stk_mem_denot; exact frame_stk
      | |- mem_inv _ _ -> mem_inv _ _ => intros inv_m; exact (msteps_mem_inv asegs _ _ run1 inv_m)
      | |- rw_cells _ _ _ _ =>
          eapply (rw_cells_log_nth_sb env0 m _ 0 (EVar 9));
          [ exact flat1 | reflexivity | reflexivity | cbn [edenot]; rewrite ev9, u64_of_Z by lia; lia
          | exact slot_wr | reflexivity | exact I | reflexivity ]
      end.
  Qed.

  Lemma tf_call : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte),
    rfull R ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_ANN_RET) fc None m ro) (MS R' F (Z_to_bv 64 AT_EXPAND) fc None m ro)
      /\ rfull R' /\ kept_in KTCALL R R'
      /\ getr R' 1 = Z_to_bv 64 TF_XP_RET /\ getr R' 10 = getr R 19 /\ getr R' 11 = getr R 8.
  Proof.
    intros R F fc m ro HF.
    pose (E := Eseed R []).
    assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R TF_ANN_RET m ro HR HK 10%nat [AT_EXPAND] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R1 _ ?mm _) |- _ =>
      change mm with m in Hms; exists R1; split; [exact Hms|]; split; [exact (msteps_full asegs _ _ Hms HF)|] end.
    split; [intros rr Hrr; eapply (syms_id_sound R _ _ R' KTCALL HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]|].
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    split; [exact L1|]. split; [rewrite L10; try subst E; evs; reflexivity | rewrite L11; try subst E; evs; reflexivity].
  Qed.

  Lemma tf_back : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte),
    getr R 10 = Z_to_bv 64 1 -> rfull R ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_XP_RET) fc None m ro) (MS R' F (Z_to_bv 64 TF_HEAD) fc None m ro)
      /\ rfull R' /\ kept_in KTBACK R R'.
  Proof.
    intros R F fc m ro P10 HF.
    pose (E := Eseed R []).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 1)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); try subst E; evs; exact P10).
    assert (HK : know_ok asegs E m []) by constructor.
    xrun_at (PropExec.mkFP F fc) asegs R TF_XP_RET m ro HR HK 4%nat [TF_HEAD; 0xfff6c] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch goal with Hms : CatSim.msteps _ _ (@PropExec.mkst _ ?R1 _ ?mm _) |- _ =>
      change mm with m in Hms; exists R1; split; [exact Hms|]; split; [exact (msteps_full asegs _ _ Hms HF)|] end.
    intros rr Hrr; eapply (syms_id_sound R _ _ R' KTBACK HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr].
  Qed.

  Lemma tf_exit : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 : word) (SP : Z),
    getr R 10 = Z_to_bv 64 0 -> getr R 2 = Z_to_bv 64 (SP - 80) -> rfull R ->
    2 ^ 45 <= SP <= 2 ^ 47 ->
    rw_cells asegs m (SP - 80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> mem_inv asegs m ->
    exists R',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 TF_XP_RET) fc None m ro) (MS R' F (Z_to_bv 64 TF_RET) fc None m ro)
      /\ rfull R' /\ kept_in KTEXIT R R'
      /\ getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 SP /\ getr R' 8 = s0 /\ getr R' 9 = s1 /\ getr R' 18 = s2 /\ getr R' 19 = s3
      /\ getr R' 20 = s4 /\ getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7 /\ getr R' 24 = s8 /\ getr R' 10 = getr R 19.
  Proof.
    intros R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 SP a0_at sp_at full_R sp_range frame_cells _.
    pose (env0 := Eseed R [s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]).
    assert (sp_ev : ev env0 2 = Z_to_bv 64 (SP - 80)) by (subst env0; rewrite (Eseed_regZ R _ 2%bv); exact sp_at).
    assert (a0_ev : ev env0 10 = Z_to_bv 64 0) by (subst env0; rewrite (Eseed_regZ R _ 10%bv); exact a0_at).
    assert (regs0 : regs_ok env0 sr_id R) by apply regs_ok_seed.
    assert (know0 : know_ok asegs env0 m
      ltac:(let l := eval vm_compute in
              (map (fun k => KWord (SA (EVar 2) (8 * Z.of_nat k)) 8 (EVar (32 + N.of_nat k))) (seq 0 10)) in exact l)).
    { unfold know_ok; repeat apply Forall_cons; try apply Forall_nil;
        lazymatch goal with |- kentry_ok _ _ _ (KWord (SA _ ?o) _ _) =>
          let k := eval vm_compute in (Z.to_nat o) in
          eapply (kword_of_rw_cells asegs env0 m (SP - 80) _ k _ _ _ 8 frame_cells);
          [ reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off edenot]; rewrite sp_ev, u64_of_Z by lia; reflexivity
          | lia | lia | reflexivity ]
        end. }
    xrun_at (PropExec.mkFP F fc) asegs R TF_XP_RET m ro regs0 know0 30%nat [TF_RET] (SCR [false] [] []) 42%N.
    { unfold scs_denot; repeat apply Forall_cons; try apply Forall_nil; cbn [sc_denot];
        lazymatch goal with
        | |- branch_taken _ _ _ = _ => cbn [edenot]; rewrite a0_ev; reflexivity
        | |- _ => unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite sp_ev, ?u64_of_Z by lia; lia
        end. }
    rename R' into R1, HR' into regs1, Hms into run1. clear Hlf.
    exists R1.
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
      | |- CatSim.msteps _ _ _ => exact run1
      | |- rfull _ => exact (msteps_full asegs _ _ run1 full_R)
      | |- kept_in _ _ _ =>
          intros r r_in; apply (syms_id_sound R _ _ R1 KTEXIT regs1); [vm_compute; reflexivity | exact r_in]
      | |- getr _ _ = _ =>
          rewrite regs1;
          lazymatch goal with |- edenot _ (sr_get ?sr ?r) = _ =>
            let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e end;
          cbn [edenot]; rewrite ?sp_ev;
          first [ reflexivity | rewrite w_add by lia; f_equal; lia ]
      end.
  Qed.
End TF1.
