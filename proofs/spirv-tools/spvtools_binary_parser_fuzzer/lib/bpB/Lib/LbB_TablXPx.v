(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_DStat LbB_RGb2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGl LbB_TablStmt LbB_TablOS1 LbB_TablPT1 LbB_TablPT3 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition KTX : list reg := [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Ltac xp_fin EF ESH EQ WP MI :=
  lazymatch goal with
  | Hlf : log_flat ?E ?lg, Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok _ _ ?R' |- _ =>
    lazymatch type of WP with
    | wr_at _ ?m ?fp _ =>
      change mm with (mem_denot E m lg) in Hms;
      let M1 := fresh "M1" in set (M1 := mem_denot E m lg) in Hms;
      exists R', M1; split; [exact Hms|];
      repeat lazymatch goal with
        | |- getr R' ?r = _ /\ _ => split; [let L := fresh "L" in rreg_ HR' r L; rewrite L; reflexivity|]
        end;
      split; [intros r Hr; eapply (syms_id_sound _ _ _ R' KTX HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]|];
      split;
      [ cbv iota;
        first [ let L := fresh "L" in rreg HR' 10%bv L; rewrite L; reflexivity
              | eapply (syms_id_sound _ _ _ R' [10%bv] HR'); [vm_cast_no_check (@eq_refl bool true) | left; reflexivity] ] |];
      split;
      [ subst M1; apply munch_mem_denot; [exact Hlf|];
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                    first [rewrite ESH | rewrite EF | rewrite EQ];
                                    cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]);
        apply Forall_nil |];
      split; [subst M1; apply wmono_mem_denot|];
      split; [exact (msteps_mem_inv asegs _ _ Hms MI)|];
      split; [intros lo' hi' SK; subst M1; apply stk_mem_denot; exact SK|];
      let FL := fresh "FL" in
      assert (FL : rw_cells asegs M1 fp [C1 (b8 0)])
        by (subst M1; eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
              | unfold estart; cbn [a_base a_off]; rewrite EQ; lia | exact WP | reflexivity | exact I | reflexivity]);
      let B := fresh "B" in
      destruct FL as [[_ (_ & _ & B)] _]; specialize (B 0%nat ltac:(cbn; lia)); rewrite Z.add_0_r in B; exact B
    end
  end.

Section XPx.
  Context {HCEIL : HeapCeil}.

  Lemma xp_tail : forall (one : bool) (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (ff fp SP S1 : Z),
    getr R 8 = Z_to_bv 64 SP -> getr R 9 = Z_to_bv 64 S1 -> getr R 18 = Z_to_bv 64 ff -> getr R 25 = Z_to_bv 64 (sh ff) ->
    getr R 26 = Z_to_bv 64 ff ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 256 <= 2 ^ 47 -> (ff + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0x6e8000 <= fp -> fp + 1 <= ff -> (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp) ->
    2 ^ 45 <= S1 -> S1 + 160 <= SP -> SP <= 2 ^ 47 -> ff + 256 <= S1 ->
    rw_cells asegs m (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m (ff + 248) [C8 (Z_to_bv 64 fp)] ->
    wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 32 -> wr_at asegs m fp 1 -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 (if one then XP_ONE else XP_EXIT)) fc None m ro) (MS R' F (Z_to_bv 64 XP_RET) fc None M' ro)
      /\ getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 SP /\ getr R' 8 = s0 /\ getr R' 9 = s1
      /\ getr R' 18 = s2 /\ getr R' 19 = s3 /\ getr R' 20 = s4 /\ getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7
      /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\ getr R' 27 = s11
      /\ kept_in KTX R R' /\ getr R' 10 = (if one then Z_to_bv 64 1 else getr R 10)
      /\ munch [(sh ff, sh ff + 32); (ff, ff + 8); (fp, fp + 1)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ mrd asegs M' (wa fp) = Some (b8 0).
Proof.
    intros one R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ff fp SP S1 H8 H9 H18 H25 H26 F64 FLO FHI FB PLO PFF PB
      SLO SSP SHI SFF CSF CFP WF WS WP MI.
    pose (E := Eseed R [Z_to_bv 64 SP; Z_to_bv 64 S1; Z_to_bv 64 ff; Z_to_bv 64 fp;
                        s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (9%bv, EVar 33); (18%bv, EVar 34);
                                       (25%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 34) (ELit 3)) (ELit SHBASE));
                                       (26%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
        first [exact H8 | exact H9 | exact H18 | exact H26 | rewrite H25; unfold SHBASE; symmetry; apply sh_word; lia]. }
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (ES1 : bv_unsigned (edenot E (EVar 33)) = S1) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EF : bv_unsigned (edenot E (EVar 34)) = ff) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EQ : bv_unsigned (edenot E (EVar 35)) = fp) by (evs; rewrite u64_of_Z by lia; reflexivity).
    assert (ESH : bv_unsigned (edenot E (EAlu ALU_SRL (EVar 34) (ELit 3))) = ff / 8)
      by (evs; rewrite TablLib.w_srl by lia; change (2 ^ 3) with 8;
          rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (SHK : ff / 8 + SHBASE = sh ff) by (apply sh_kit; lia).
    assert (D3 : ff / 8 + SHBASE + 32 <= SP - 104) by (unfold SHBASE; Z.div_mod_to_equations; lia).
    assert (D4 : ff + 256 <= ff / 8 + SHBASE \/ ff / 8 + SHBASE + 32 <= ff + 248)
      by (unfold SHBASE; Z.div_mod_to_equations; lia).
    assert (HK : know_ok asegs E m
      [ KWord (SA (EVar 32) (-104)) 8 (EVar 36); KWord (SA (EVar 32) (-96)) 8 (EVar 37); KWord (SA (EVar 32) (-88)) 8 (EVar 38);
        KWord (SA (EVar 32) (-80)) 8 (EVar 39); KWord (SA (EVar 32) (-72)) 8 (EVar 40); KWord (SA (EVar 32) (-64)) 8 (EVar 41);
        KWord (SA (EVar 32) (-56)) 8 (EVar 42); KWord (SA (EVar 32) (-48)) 8 (EVar 43); KWord (SA (EVar 32) (-40)) 8 (EVar 44);
        KWord (SA (EVar 32) (-32)) 8 (EVar 45); KWord (SA (EVar 32) (-24)) 8 (EVar 46); KWord (SA (EVar 32) (-16)) 8 (EVar 47);
        KWord (SA (EVar 32) (-8)) 8 (EVar 48);
        KWord (SA (EVar 34) 248) 8 (EVar 35);
        KWr (SA (EVar 34) 0) (ELit 8);
        KWr (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) SHBASE) (ELit 32);
        KWr (SA (EVar 35) 0) (ELit 1);
        KRange (EVar 34) AIMG_TOP (2 ^ 47 - 256); KAlign (EVar 34) 64; KRange (EVar 35) AIMG_TOP (2 ^ 47);
        KRange (EVar 32) (2 ^ 45) (2 ^ 47); KRange (EVar 33) (2 ^ 45) (2 ^ 47);
        KDisj (SA (EVar 32) (-104)) (ELit 104) (SA (EVar 34) 0) (ELit 8);
        KDisj (SA (EVar 32) (-104)) (ELit 104) (SA (EVar 35) 0) (ELit 1);
        KDisj (SA (EVar 32) (-104)) (ELit 104) (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) SHBASE) (ELit 32);
        KDisj (SA (EVar 34) 248) (ELit 8) (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) SHBASE) (ELit 32) ]).
    { unfold know_ok.
      apply Forall_cons. { kword_cell CSF 0%nat (C8 s11). }
      apply Forall_cons. { kword_cell CSF 8%nat (C8 s10). }
      apply Forall_cons. { kword_cell CSF 16%nat (C8 s9). }
      apply Forall_cons. { kword_cell CSF 24%nat (C8 s8). }
      apply Forall_cons. { kword_cell CSF 32%nat (C8 s7). }
      apply Forall_cons. { kword_cell CSF 40%nat (C8 s6). }
      apply Forall_cons. { kword_cell CSF 48%nat (C8 s5). }
      apply Forall_cons. { kword_cell CSF 56%nat (C8 s4). }
      apply Forall_cons. { kword_cell CSF 64%nat (C8 s3). }
      apply Forall_cons. { kword_cell CSF 72%nat (C8 s2). }
      apply Forall_cons. { kword_cell CSF 80%nat (C8 s1). }
      apply Forall_cons. { kword_cell CSF 88%nat (C8 s0). }
      apply Forall_cons. { kword_cell CSF 96%nat (C8 ra). }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 248) _ 0%nat (C8 (Z_to_bv 64 fp))); [exact CFP | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; lia | lia | lia | evs; reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; evs; rewrite ?u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ESH; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ESH; evs; rewrite ?u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [a_base a_off]; rewrite EQ; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EQ; evs; rewrite ?u64_of_Z by lia; lia
                                  | unfold elenZ; evs; rewrite ?u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EF. unfold AIMG_TOP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EF. split; [lia | exact F64]. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EQ. unfold AIMG_TOP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite ES1. lia. }
      do 4 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?ESH, ?EF, ?EP, ?EQ; evs;
                                rewrite ?u64_of_Z by lia; lia|]).
      apply Forall_nil. }
    destruct one.
    - xrun_at (PropExec.mkFP F fc) asegs R XP_ONE m ro HR HK 100%nat [XP_RET] (SCR [] [] []) 49%N.
      { split_scs. }
      xp_fin EF ESH EQ WP MI.
    - xrun_at (PropExec.mkFP F fc) asegs R XP_EXIT m ro HR HK 100%nat [XP_RET] (SCR [] [] []) 49%N.
      { split_scs. }
      xp_fin EF ESH EQ WP MI.
  Qed.
End XPx.
