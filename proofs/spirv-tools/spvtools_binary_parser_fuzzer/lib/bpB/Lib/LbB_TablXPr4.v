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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX BellsX HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_RGl LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablLO LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition KRKa : list reg := [2; 3; 4; 8; 18; 20; 25; 26; 28; 29; 30; 31]%bv.
Definition KRKb : list reg := [2; 3; 4; 8; 18; 19; 21; 23; 25; 28; 29; 30; 31]%bv.
Definition KRKc : list reg := [2; 3; 4; 8; 18; 19; 21; 23; 25; 28; 29; 30; 31]%bv.
Definition KRKbB : list reg := [2; 3; 4; 8; 18; 19; 21; 22; 25; 28; 29; 30; 31]%bv.
Definition KRKcB : list reg := [2; 3; 4; 8; 18; 19; 21; 22; 25; 28; 29; 30; 31]%bv.
Definition KRLa : list reg := [2; 3; 4; 8; 18; 24; 26; 28; 29; 30; 31]%bv.
Definition KRLb : list reg := [2; 3; 4; 8; 18; 21; 23; 26; 28; 29; 30; 31]%bv.
Definition KRLc : list reg := [2; 3; 4; 8; 18; 19; 20; 21; 22; 23; 26; 28; 29; 30; 31]%bv.
Definition KRLba : list reg := [2; 3; 4; 8; 18; 26; 28; 29; 30; 31]%bv.
Definition KRLbb : list reg := [2; 3; 4; 8; 18; 19; 21; 22; 25; 28; 29; 30; 31]%bv.
Definition KRLcb : list reg := [2; 3; 4; 8; 18; 21; 22; 24; 26; 28; 29; 30; 31]%bv.
Definition KRLcc : list reg := [2; 3; 4; 8; 18; 20; 21; 22; 23; 24; 26; 28; 29; 30; 31]%bv.

Section XPr4.
  Context {HCEIL : HeapCeil}.

#[local] Definition HTTablXPr4_0 : list (reg * expr) := [(19%bv, EVar 32); (9%bv, EVar 33); (23%bv, EVar 34); (24%bv, EVar 35); (25%bv, EVar 36); (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) (ELit 2147450880)); (22%bv, EAlu ALU_ADD (EVar 32) (ELit 16)); (27%bv, ELit 2147450880)].
  Lemma L4_a : xrun_a L4.
  Proof.
    unfold xrun_a. intros R F fc m ro g RP GOK F0 F8 F16 GZ WS SLi WSH WFR.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L4
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 RP].
    apply RPl_cons in RP as [P23 RP]. apply RPl_cons in RP as [P24 _].
    specialize (SLi eq_refl).
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHV0 : 0x7fff8000 <= sh v /\ sh (v + 16) + 1 <= 0x10007fff8000 /\ sh v + 2 = sh (v + 16))
      by (clear - VLO VHI VB V8; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHD : sh (v + 16) + 1 <= sh ff \/ sh ff + 32 <= sh v) by (clear - VF V8 F64; unfold sh; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 e; Z_to_bv 64 (ff + 80); Z_to_bv 64 (sh ff); Z_to_bv 64 c; Z_to_bv 64 b]).
    set (SR0 := srs sr_id HTTablXPr4_0).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P19 | exact P9 | exact P23 | exact P24 | exact P25 | rewrite P21, TablLib.zbv_add, sh_word by lia; reflexivity
        | rewrite P22, TablLib.zbv_add; reflexivity | exact P27]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ET : forall o, estart E (SA (EVar 35) o) = ff + 80 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EH : forall o, estart E (SA (EVar 36) o) = sh ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 0) 8 (EVar 38); KWord (SA (EVar 32) 16) 8 (EVar 37);
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 35) 0) (ELit 4); KWr (SA (EVar 36) 0) (ELit 32);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160);
         KRange (EVar 34) 0 (2 ^ 47); KRange (EVar 35) 0x6e8000 (2 ^ 47); KRange (EVar 36) 0x7fff8000 (0x10007fff8000 - 32);
         KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 47);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EVar 32) 0) (ELit 24);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 32) 0) (ELit 24);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 1) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 0) (EVar 38) 8%nat v b F0); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 16) (EVar 37) 8%nat (v + 16) c F16); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 16)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact (gz_at m v 24 16 GZ ltac:(lia))]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ v); [subst E; evs; reflexivity | lia | pose proof (gz_at m v 24 0 GZ ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WFR | rewrite ET; lia | unfold elenZ; rewrite ET; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WSH | rewrite EH; lia | unfold elenZ; rewrite EH; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 7 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite ET, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - VF; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite EH, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - SHF VB; lia|].
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI SHF; Z.div_mod_to_equations; lia). clear - SHD SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI SHF; Z.div_mod_to_equations; lia). clear - SHD SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI FLO FHI S45 SS SPH; Z.div_mod_to_equations; lia). clear - FB SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons; [|apply Forall_nil].
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI FLO FHI S45 SS SPH; Z.div_mod_to_equations; lia). clear - FB SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. } }
    assert (DSL : disjoint_from [(ff + 80, ff + 80 + 4); (sh ff + 10, sh ff + 10 + 1)] (S1 + 16) 16)
      by (cbn; clear - FHI SHF S45; lia).
    destruct (Z.ltb_spec e c) as [LT|GE].
    - xrun_at (PropExec.mkFP F fc) asegs R 0xff4a0 m ro HR HK 30%nat [AANNOTATE_CC; 0xfb3d4] (SCR [false; false; false; false] [] []) 39%N.
      { assert (B16 : 16 <= b) by (destruct (Z.eq_dec b 0) as [Z0|NZ]; [specialize (BC Z0); lia | exact (proj1 (BNZ NZ))]).
        split_scs; cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_add;
        first [rewrite br_eq by lia; bool_lia | rewrite br_ltu by lia; bool_lia | rewrite br_geu by lia; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1, AANNOTATE_CC. split; [exact Hms|].
      assert (KK : kept_in KRLba R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLba HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 80, ff + 80 + 4); (sh ff + 10, sh ff + 10 + 1)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?ET, ?EH; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split; [exact MU1|]. split; [exact WM1|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [eapply rw_cells_transport; [exact SLi | exact MU1 | exact WM1 | exact DSL]|].
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat); [exact Hlf | reflexivity | reflexivity
          | subst E; evs; rewrite u64_of_Z by lia; lia
          | eapply os_wr_at_sub; [exact WFR | lia | lia | lia]
          | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite ET, EH; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FB SHF; lia | apply Forall_nil]
          | rewrite EH; lia | eapply os_wr_at_sub; [exact WSH | lia | lia | lia] | reflexivity | exact I
          | subst E; evs; first [reflexivity | cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      split; [reflexivity|].
      rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13.
      rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
      rreg HR' 25%bv L25. rreg HR' 27%bv L27.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|]. split; [exact L12|].
      split; [rewrite L13, TablLib.zbv_add; reflexivity|].
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + exact L25.
      + rewrite (KK 26%bv ltac:(inb)); exact P26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + exact L19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite L21, TablLib.zbv_add, sh_word by lia; reflexivity.
      + rewrite L22, TablLib.zbv_add; reflexivity.
      + exact L23.
      + exact L24.
    - xrun_at (PropExec.mkFP F fc) asegs R 0xff4a0 m ro HR HK 30%nat [AANNOTATE_CC; 0xfb3d4] (SCR [true] [] []) 39%N.
      { split_scs; cbn [sc_denot]; subst E; evs; rewrite br_geu by lia; bool_lia. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1, 0xfb3d4. split; [exact Hms|].
      assert (KK : kept_in KRLba R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLba HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 80, ff + 80 + 4); (sh ff + 10, sh ff + 10 + 1)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?ET, ?EH; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split; [exact MU1|]. split; [exact WM1|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [eapply rw_cells_transport; [exact SLi | exact MU1 | exact WM1 | exact DSL]|].
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat); [exact Hlf | reflexivity | reflexivity
          | subst E; evs; rewrite u64_of_Z by lia; lia
          | eapply os_wr_at_sub; [exact WFR | lia | lia | lia]
          | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite ET, EH; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FB SHF; lia | apply Forall_nil]
          | rewrite EH; lia | eapply os_wr_at_sub; [exact WSH | lia | lia | lia] | reflexivity | exact I
          | subst E; evs; first [reflexivity | cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      split; [reflexivity|].
      rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 19%bv L19. rreg HR' 21%bv L21. rreg HR' 22%bv L22.
      rreg HR' 25%bv L25. rreg HR' 27%bv L27.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|].
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + exact L25.
      + rewrite (KK 26%bv ltac:(inb)); exact P26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + exact L19.
      + rewrite L21, TablLib.zbv_add, sh_word by lia; reflexivity.
      + rewrite L22, TablLib.zbv_add; reflexivity.
  Qed.

#[local] Definition HTTablXPr4_1 : list (reg * expr) := [(23%bv, EVar 34); (9%bv, EVar 33); (24%bv, EVar 35); (27%bv, ELit 2147450880); (20%bv, EAlu ALU_ADD (EVar 34) (ELit 4)); (26%bv, EVar 37)].
  Lemma L4_b : xrun_b L4.
  Proof.
    unfold xrun_b. intros R F fc m ro g j RP GOK LT CL SJ JC SL S8 WE WV WSH.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L4
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb XP_ONE] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P20 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 RP].
    apply RPl_cons in RP as [P23 RP]. apply RPl_cons in RP as [P24 _].
    assert (BN : b <> 0) by lia. destruct (BNZ BN) as (B16 & B8 & BB & DJV & DJF).
    apply (rw_cells_app asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh (v + 8)))] [C8 (Z_to_bv 64 (v + 8))]) in SL as [C16 C24].
    cbn [cells_size csize] in C24. replace (S1 + 16 + Z.of_nat (8 + 0)) with (S1 + 24) in C24 by lia.
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 e; Z_to_bv 64 (ff + 80); Z_to_bv 64 j; Z_to_bv 64 ff]).
    set (SR0 := srs sr_id HTTablXPr4_1).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P23 | exact P9 | exact P24 | exact P27 | rewrite P20, TablLib.zbv_add; reflexivity | exact P26]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EE : forall o, estart E (SA (EVar 34) o) = e + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ET : forall o, estart E (SA (EVar 35) o) = ff + 80 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EF : forall o, estart E (SA (EVar 37) o) = ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) 2147450880) 1 (EVar 36);
         KWord (SA (EVar 35) 0) 4 (ELit 1);
         KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880));
         KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 32) (ELit 8));
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 34) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160);
         KRange (EVar 34) 16 (2 ^ 47 - 4); KAlign (EVar 34) 4; KRange (EVar 35) 0x6e8000 (2 ^ 47); KRange (EVar 36) 0 7;
         KRange (EVar 37) 0x6f1000 (2 ^ 47 - 256);
         KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 32) 8) (ELit 8);
         KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 33) 16) (ELit 16) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kshadow _ _ _ e j); [subst E; evs; reflexivity | lia | destruct JC; lia | subst E; evs; reflexivity | exact SJ]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 80) _ 0%nat (C4 (Z_to_bv 64 1))); [exact CL | reflexivity | reflexivity | lia
          | rewrite ET; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (sh (v + 8))))); [exact C16 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add, sh_word by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 (v + 8)))); [exact C24 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WE | rewrite EE; lia | unfold elenZ; rewrite EE; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; lia | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact E4]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by (destruct JC; lia); destruct JC; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite EE, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - DJV BE LT; lia|].
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. unfold elenZ. rewrite EE, ES1. subst E; evs. rewrite !u64_of_Z by lia. clear - EC CS1; lia. }
    assert (SHV : estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) = sh (v + 8)).
    { unfold estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
      rewrite u64_of_Z by (clear - VLO VHI; Z.div_mod_to_equations; lia). unfold sh. rewrite ASHADOW_BASE_val. change (2 ^ 3) with 8. lia. }
    assert (SHB : 0x7fff8000 <= sh (v + 8) /\ sh (v + 8) + 1 <= 0x10007fff8000) by (clear - VLO VHI; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SD : sc_denot asegs m E (SCDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 34) 0) (ELit 4))).
    { cbn [sc_denot]. unfold flat, elenZ. rewrite SHV, EE. cbn [edenot]. rewrite !u64_of_Z by lia. clear - SHB BB B0 BE LT EC CS1 SS SPH. lia. }
    destruct JC as [J0|(JA & J1)].
    - subst j. xrun_at (PropExec.mkFP F fc) asegs R 0xff4fc m ro HR HK 30%nat [0xff860] (SCR [false] [] []) 38%N.
      { split_scs; first [exact SD | cbn [sc_denot]; subst E; evs; rewrite br_ne by lia; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV, ?EE; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite EV, EE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DJV BE LT; lia | apply Forall_nil]
          | rewrite EE; lia | exact WE | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + rewrite (KK 25%bv ltac:(inb)); exact P25.
      + exact L26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + rewrite (KK 19%bv ltac:(inb)); exact P19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite (KK 21%bv ltac:(inb)); exact P21.
      + rewrite (KK 22%bv ltac:(inb)); exact P22.
      + rewrite L23, TablLib.zbv_add; reflexivity.
    - assert (SL : sc_denot asegs m E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND (EVar 34) (ELit 7)) (ELit 3)) (EVar 36))).
      { cbn [sc_denot]. subst E; evs. rewrite land7_val by lia. rewrite JA, TablLib.zbv_add. rewrite br_lts_small by lia. apply Z.ltb_lt. lia. }
      assert (SN : sc_denot asegs m E (SCBr true BC_NE (EVar 36) (ELit 0))).
      { cbn [sc_denot]. subst E; evs. rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R 0xff4fc m ro HR HK 30%nat [0xff860] (SCR [true; true] [] []) 38%N.
      { split_scs; first [exact SD | exact SL | exact SN]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV, ?EE; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite EV, EE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DJV BE LT; lia | apply Forall_nil]
          | rewrite EE; lia | exact WE | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + rewrite (KK 25%bv ltac:(inb)); exact P25.
      + exact L26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + rewrite (KK 19%bv ltac:(inb)); exact P19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite (KK 21%bv ltac:(inb)); exact P21.
      + rewrite (KK 22%bv ltac:(inb)); exact P22.
      + rewrite L23, TablLib.zbv_add; reflexivity.
  Qed.

#[local] Definition HTTablXPr4_2 : list (reg * expr) := [(10%bv, EVar 34); (9%bv, EVar 33); (27%bv, ELit 2147450880); (26%bv, EVar 35)].
  Lemma L4_c : xrun_c L4.
  Proof.
    unfold xrun_c. intros R F fc m ro g E' RP P10 GOK EB E5 EA SL S8 WV WSH.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L4
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb XP_ONE] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 _].
    apply (rw_cells_app asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh (v + 8)))] [C8 (Z_to_bv 64 (v + 8))]) in SL as [C16 C24].
    cbn [cells_size csize] in C24. replace (S1 + 16 + Z.of_nat (8 + 0)) with (S1 + 24) in C24 by lia.
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 E'; Z_to_bv 64 ff]).
    set (SR0 := srs sr_id HTTablXPr4_2).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P10 | exact P9 | exact P27 | exact P26]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EF : forall o, estart E (SA (EVar 35) o) = ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880));
         KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 32) (ELit 8));
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 32) 8) (ELit 8);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160); KRange (EVar 34) 5 (2 ^ 47); KAlign (EVar 34) 4;
         KRange (EVar 35) 0x6f1000 (2 ^ 47 - 256) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (sh (v + 8))))); [exact C16 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add, sh_word by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 (v + 8)))); [exact C24 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; lia | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact EA]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xff830 m ro HR HK 20%nat [0xff860] (SCR [] [] []) 36%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
    split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split.
    { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; reflexivity]. }
    split; [intros X; exfalso; apply X; reflexivity|].
    rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (KK 2%bv ltac:(inb)); exact P2.
    + rewrite (KK 8%bv ltac:(inb)); exact P8.
    + exact L9.
    + rewrite (KK 25%bv ltac:(inb)); exact P25.
    + exact L26.
    + exact L27.
    + rewrite (KK 18%bv ltac:(inb)); exact P18.
    + rewrite (KK 19%bv ltac:(inb)); exact P19.
    + exact L20.
    + rewrite (KK 21%bv ltac:(inb)); exact P21.
    + rewrite (KK 22%bv ltac:(inb)); exact P22.
    + rewrite L23, TablLib.zbv_add; reflexivity.
  Qed.

  Lemma L4_runs : site_runs L4.
  Proof. exact (conj L4_a (conj L4_b L4_c)). Qed.

  Lemma L6_a : xrun_a L6.
  Proof.
    unfold xrun_a. intros R F fc m ro g RP GOK F0 F8 F16 GZ WS SLi WSH WFR.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L6
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 RP].
    apply RPl_cons in RP as [P23 RP]. apply RPl_cons in RP as [P24 _].
    specialize (SLi eq_refl).
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHV0 : 0x7fff8000 <= sh v /\ sh (v + 16) + 1 <= 0x10007fff8000 /\ sh v + 2 = sh (v + 16))
      by (clear - VLO VHI VB V8; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHD : sh (v + 16) + 1 <= sh ff \/ sh ff + 32 <= sh v) by (clear - VF V8 F64; unfold sh; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 e; Z_to_bv 64 (ff + 112); Z_to_bv 64 (sh ff); Z_to_bv 64 c; Z_to_bv 64 b]).
    set (SR0 := srs sr_id HTTablXPr4_0).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P19 | exact P9 | exact P23 | exact P24 | exact P25 | rewrite P21, TablLib.zbv_add, sh_word by lia; reflexivity
        | rewrite P22, TablLib.zbv_add; reflexivity | exact P27]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ET : forall o, estart E (SA (EVar 35) o) = ff + 112 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EH : forall o, estart E (SA (EVar 36) o) = sh ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 32) 0) 8 (EVar 38); KWord (SA (EVar 32) 16) 8 (EVar 37);
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 35) 0) (ELit 4); KWr (SA (EVar 36) 0) (ELit 32);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160);
         KRange (EVar 34) 0 (2 ^ 47); KRange (EVar 35) 0x6e8000 (2 ^ 47); KRange (EVar 36) 0x7fff8000 (0x10007fff8000 - 32);
         KRange (EVar 37) 0 (2 ^ 47); KRange (EVar 38) 0 (2 ^ 47);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EVar 32) 0) (ELit 24);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EVar 32) 0) (ELit 24);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 36) 0) (ELit 32) (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 16)) (ELit 3)) 2147450880) (ELit 1);
         KDisj (SA (EVar 35) 0) (ELit 4) (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) 2147450880) (ELit 1) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 0) (EVar 38) 8%nat v b F0); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (pt_kword_of_fld E m (SA (EVar 32) 16) (EVar 37) 8%nat (v + 16) c F16); [lia | rewrite EV; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 16)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact (gz_at m v 24 16 GZ ltac:(lia))]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ v); [subst E; evs; reflexivity | lia | pose proof (gz_at m v 24 0 GZ ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WFR | rewrite ET; lia | unfold elenZ; rewrite ET; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WSH | rewrite EH; lia | unfold elenZ; rewrite EH; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 7 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite ET, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - VF; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite EH, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - SHF VB; lia|].
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI SHF; Z.div_mod_to_equations; lia). clear - SHD SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI SHF; Z.div_mod_to_equations; lia). clear - SHD SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI FLO FHI S45 SS SPH; Z.div_mod_to_equations; lia). clear - FB SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. }
      apply Forall_cons; [|apply Forall_nil].
      { cbn [kentry_ok]. unfold elenZ, estart. cbn [a_base a_off]. subst E; evs. rewrite HWord.w_srl by lia.
        rewrite !u64_of_Z by (clear - VLO VHI FLO FHI S45 SS SPH; Z.div_mod_to_equations; lia). clear - FB SHV0.
        unfold sh in *. rewrite ASHADOW_BASE_val in *. change (2 ^ 3) with 8. lia. } }
    assert (DSL : disjoint_from [(ff + 112, ff + 112 + 4); (sh ff + 14, sh ff + 14 + 1)] (S1 + 16) 16)
      by (cbn; clear - FHI SHF S45; lia).
    destruct (Z.ltb_spec e c) as [LT|GE].
    - xrun_at (PropExec.mkFP F fc) asegs R 0xff560 m ro HR HK 30%nat [AANNOTATE_CC; 0xfb3d4] (SCR [false; false; false; false] [] []) 39%N.
      { assert (B16 : 16 <= b) by (destruct (Z.eq_dec b 0) as [Z0|NZ]; [specialize (BC Z0); lia | exact (proj1 (BNZ NZ))]).
        split_scs; cbn [sc_denot]; subst E; evs; rewrite ?TablLib.zbv_add;
        first [rewrite br_eq by lia; bool_lia | rewrite br_ltu by lia; bool_lia | rewrite br_geu by lia; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1, AANNOTATE_CC. split; [exact Hms|].
      assert (KK : kept_in KRLba R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLba HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 112, ff + 112 + 4); (sh ff + 14, sh ff + 14 + 1)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?ET, ?EH; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split; [exact MU1|]. split; [exact WM1|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [eapply rw_cells_transport; [exact SLi | exact MU1 | exact WM1 | exact DSL]|].
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat); [exact Hlf | reflexivity | reflexivity
          | subst E; evs; rewrite u64_of_Z by lia; lia
          | eapply os_wr_at_sub; [exact WFR | lia | lia | lia]
          | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite ET, EH; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FB SHF; lia | apply Forall_nil]
          | rewrite EH; lia | eapply os_wr_at_sub; [exact WSH | lia | lia | lia] | reflexivity | exact I
          | subst E; evs; first [reflexivity | cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      split; [reflexivity|].
      rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12. rreg HR' 13%bv L13.
      rreg HR' 19%bv L19. rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24.
      rreg HR' 25%bv L25. rreg HR' 27%bv L27.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|]. split; [exact L12|].
      split; [rewrite L13, TablLib.zbv_add; reflexivity|].
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + exact L25.
      + rewrite (KK 26%bv ltac:(inb)); exact P26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + exact L19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite L21, TablLib.zbv_add, sh_word by lia; reflexivity.
      + rewrite L22, TablLib.zbv_add; reflexivity.
      + exact L23.
      + exact L24.
    - xrun_at (PropExec.mkFP F fc) asegs R 0xff560 m ro HR HK 30%nat [AANNOTATE_CC; 0xfb3d4] (SCR [true] [] []) 39%N.
      { split_scs; cbn [sc_denot]; subst E; evs; rewrite br_geu by lia; bool_lia. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1, 0xfb3d4. split; [exact Hms|].
      assert (KK : kept_in KRLba R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLba HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      assert (MU1 : munch [(ff + 112, ff + 112 + 4); (sh ff + 14, sh ff + 14 + 1)] m M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?ET, ?EH; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split; [exact MU1|]. split; [exact WM1|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split; [eapply rw_cells_transport; [exact SLi | exact MU1 | exact WM1 | exact DSL]|].
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat); [exact Hlf | reflexivity | reflexivity
          | subst E; evs; rewrite u64_of_Z by lia; lia
          | eapply os_wr_at_sub; [exact WFR | lia | lia | lia]
          | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { intros _. subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite ET, EH; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - FB SHF; lia | apply Forall_nil]
          | rewrite EH; lia | eapply os_wr_at_sub; [exact WSH | lia | lia | lia] | reflexivity | exact I
          | subst E; evs; first [reflexivity | cbn [cbytes]; unfold word_to_le_bytes; cbn; f_equal; apply bv_eq; vm_compute; reflexivity]]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      split; [reflexivity|].
      rreg HR' 1%bv L1. rreg HR' 9%bv L9. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 19%bv L19. rreg HR' 21%bv L21. rreg HR' 22%bv L22.
      rreg HR' 25%bv L25. rreg HR' 27%bv L27.
      split; [exact L1|]. split; [exact L10|]. split; [exact L11|].
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + exact L25.
      + rewrite (KK 26%bv ltac:(inb)); exact P26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + exact L19.
      + rewrite L21, TablLib.zbv_add, sh_word by lia; reflexivity.
      + rewrite L22, TablLib.zbv_add; reflexivity.
  Qed.

  Lemma L6_b : xrun_b L6.
  Proof.
    unfold xrun_b. intros R F fc m ro g j RP GOK LT CL SJ JC SL S8 WE WV WSH.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L6
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb XP_ONE] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P20 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 RP].
    apply RPl_cons in RP as [P23 RP]. apply RPl_cons in RP as [P24 _].
    assert (BN : b <> 0) by lia. destruct (BNZ BN) as (B16 & B8 & BB & DJV & DJF).
    apply (rw_cells_app asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh (v + 8)))] [C8 (Z_to_bv 64 (v + 8))]) in SL as [C16 C24].
    cbn [cells_size csize] in C24. replace (S1 + 16 + Z.of_nat (8 + 0)) with (S1 + 24) in C24 by lia.
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 e; Z_to_bv 64 (ff + 112); Z_to_bv 64 j; Z_to_bv 64 ff]).
    set (SR0 := srs sr_id HTTablXPr4_1).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P23 | exact P9 | exact P24 | exact P27 | rewrite P20, TablLib.zbv_add; reflexivity | exact P26]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EE : forall o, estart E (SA (EVar 34) o) = e + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ET : forall o, estart E (SA (EVar 35) o) = ff + 112 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EF : forall o, estart E (SA (EVar 37) o) = ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EAlu ALU_SRL (EVar 34) (ELit 3)) 2147450880) 1 (EVar 36);
         KWord (SA (EVar 35) 0) 4 (ELit 6);
         KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880));
         KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 32) (ELit 8));
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 34) 0) (ELit 4); KWr (SA (EVar 32) 8) (ELit 8);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160);
         KRange (EVar 34) 16 (2 ^ 47 - 4); KAlign (EVar 34) 4; KRange (EVar 35) 0x6e8000 (2 ^ 47); KRange (EVar 36) 0 7;
         KRange (EVar 37) 0x6f1000 (2 ^ 47 - 256);
         KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 32) 8) (ELit 8);
         KDisj (SA (EVar 34) 0) (ELit 4) (SA (EVar 33) 16) (ELit 16) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kshadow _ _ _ e j); [subst E; evs; reflexivity | lia | destruct JC; lia | subst E; evs; reflexivity | exact SJ]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (ff + 112) _ 0%nat (C4 (Z_to_bv 64 6))); [exact CL | reflexivity | reflexivity | lia
          | rewrite ET; lia | lia | lia | subst E; evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (sh (v + 8))))); [exact C16 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add, sh_word by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 (v + 8)))); [exact C24 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WE | rewrite EE; lia | unfold elenZ; rewrite EE; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; lia | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact E4]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by (destruct JC; lia); destruct JC; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|].
      apply Forall_cons; [cbn [kentry_ok]; unfold elenZ; rewrite EE, EV; subst E; evs; rewrite !u64_of_Z by lia; clear - DJV BE LT; lia|].
      apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. unfold elenZ. rewrite EE, ES1. subst E; evs. rewrite !u64_of_Z by lia. clear - EC CS1; lia. }
    assert (SHV : estart E (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) = sh (v + 8)).
    { unfold estart. cbn [a_base a_off]. subst E; evs. rewrite TablLib.zbv_add, HWord.w_srl by lia.
      rewrite u64_of_Z by (clear - VLO VHI; Z.div_mod_to_equations; lia). unfold sh. rewrite ASHADOW_BASE_val. change (2 ^ 3) with 8. lia. }
    assert (SHB : 0x7fff8000 <= sh (v + 8) /\ sh (v + 8) + 1 <= 0x10007fff8000) by (clear - VLO VHI; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SD : sc_denot asegs m E (SCDisj (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) (ELit 1) (SA (EVar 34) 0) (ELit 4))).
    { cbn [sc_denot]. unfold flat, elenZ. rewrite SHV, EE. cbn [edenot]. rewrite !u64_of_Z by lia. clear - SHB BB B0 BE LT EC CS1 SS SPH. lia. }
    destruct JC as [J0|(JA & J1)].
    - subst j. xrun_at (PropExec.mkFP F fc) asegs R 0xff5bc m ro HR HK 30%nat [0xff928] (SCR [false] [] []) 38%N.
      { split_scs; first [exact SD | cbn [sc_denot]; subst E; evs; rewrite br_ne by lia; bool_lia]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV, ?EE; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite EV, EE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DJV BE LT; lia | apply Forall_nil]
          | rewrite EE; lia | exact WE | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + rewrite (KK 25%bv ltac:(inb)); exact P25.
      + exact L26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + rewrite (KK 19%bv ltac:(inb)); exact P19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite (KK 21%bv ltac:(inb)); exact P21.
      + rewrite (KK 22%bv ltac:(inb)); exact P22.
      + rewrite L23, TablLib.zbv_add; reflexivity.
    - assert (SL : sc_denot asegs m E (SCBr true BC_LT (EAlu ALU_ADD (EAlu ALU_AND (EVar 34) (ELit 7)) (ELit 3)) (EVar 36))).
      { cbn [sc_denot]. subst E; evs. rewrite land7_val by lia. rewrite JA, TablLib.zbv_add. rewrite br_lts_small by lia. apply Z.ltb_lt. lia. }
      assert (SN : sc_denot asegs m E (SCBr true BC_NE (EVar 36) (ELit 0))).
      { cbn [sc_denot]. subst E; evs. rewrite br_ne by lia. apply negb_true_iff, Z.eqb_neq. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R 0xff5bc m ro HR HK 30%nat [0xff928] (SCR [true; true] [] []) 38%N.
      { split_scs; first [exact SD | exact SL | exact SN]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      exists R', M1. split; [exact Hms|].
      assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
      split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV, ?EE; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
      split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
      split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 1%nat); [exact Hlf | reflexivity
          | apply Forall_cons; [cbn [e_addr e_width]; rewrite EV, EE; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; clear - DJV BE LT; lia | apply Forall_nil]
          | rewrite EE; lia | exact WE | reflexivity | exact I | subst E; evs; reflexivity]. }
      split.
      { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
          | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      split; [intros X; exfalso; apply X; reflexivity|].
      rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
      unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + rewrite (KK 2%bv ltac:(inb)); exact P2.
      + rewrite (KK 8%bv ltac:(inb)); exact P8.
      + exact L9.
      + rewrite (KK 25%bv ltac:(inb)); exact P25.
      + exact L26.
      + exact L27.
      + rewrite (KK 18%bv ltac:(inb)); exact P18.
      + rewrite (KK 19%bv ltac:(inb)); exact P19.
      + rewrite L20, TablLib.zbv_add; reflexivity.
      + rewrite (KK 21%bv ltac:(inb)); exact P21.
      + rewrite (KK 22%bv ltac:(inb)); exact P22.
      + rewrite L23, TablLib.zbv_add; reflexivity.
  Qed.

  Lemma L6_c : xrun_c L6.
  Proof.
    unfold xrun_c. intros R F fc m ro g E' RP P10 GOK EB E5 EA SL S8 WV WSH.
    destruct g as [SP S1 ff v b e c].
    cbv beta iota delta [xs_pc xs_nx xs_rin xs_setslots xs_sv xs_src xs_lit xs_tk xs_pk xs_fk xs_ara xs_sra xs_c xs_rmid xs_rmid' xs_rout L6
         rinK rmidKA rmidKA' routKA rmidKB rmidKB' routKB rmidLa rmidLa' rmidLb rmidLb' routLb rmidLc rmidLc' routF
         xwa fkw fkc xslotc xcommon xg_ok v4_entry VOT_SLOW_CREF VOT_SLOW_RREF g_SP g_S1 g_ff g_v g_b g_e g_c g_end app Z.eqb XP_ONE] in *.
    destruct GOK as (S32 & S45 & SS & SPH & F64 & FLO & FHI & FB & V8 & VLO & VB & VHI & VS & VF & B0 & BE & EC & CS1 & E4 & BC & BNZ).
    apply RPl_cons in RP as [P2 RP]. apply RPl_cons in RP as [P8 RP]. apply RPl_cons in RP as [P9 RP]. apply RPl_cons in RP as [P25 RP].
    apply RPl_cons in RP as [P26 RP]. apply RPl_cons in RP as [P27 RP]. apply RPl_cons in RP as [P18 RP].
    apply RPl_cons in RP as [P19 RP]. apply RPl_cons in RP as [P21 RP]. apply RPl_cons in RP as [P22 _].
    apply (rw_cells_app asegs m (S1 + 16) [C8 (Z_to_bv 64 (sh (v + 8)))] [C8 (Z_to_bv 64 (v + 8))]) in SL as [C16 C24].
    cbn [cells_size csize] in C24. replace (S1 + 16 + Z.of_nat (8 + 0)) with (S1 + 24) in C24 by lia.
    assert (SHF : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000) by (clear - FLO FHI S45 SS SPH FB; unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    pose (E := Eseed R [Z_to_bv 64 v; Z_to_bv 64 S1; Z_to_bv 64 E'; Z_to_bv 64 ff]).
    set (SR0 := srs sr_id HTTablXPr4_2).
    assert (HR : regs_ok E SR0 R).
    { subst SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs;
        [exact P10 | exact P9 | exact P27 | exact P26]. }
    assert (EV : forall o, estart E (SA (EVar 32) o) = v + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (ES1 : forall o, estart E (SA (EVar 33) o) = S1 + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (EF : forall o, estart E (SA (EVar 35) o) = ff + o) by (intros o; unfold estart; subst E; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 33) 16) 8 (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) (ELit 2147450880));
         KWord (SA (EVar 33) 24) 8 (EAlu ALU_ADD (EVar 32) (ELit 8));
         KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) 2147450880) 1 (ELit 0);
         KWr (SA (EVar 32) 8) (ELit 8);
         KRange (EVar 32) 0x6e8000 (2 ^ 47 - 24); KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 160); KRange (EVar 34) 5 (2 ^ 47); KAlign (EVar 34) 4;
         KRange (EVar 35) 0x6f1000 (2 ^ 47 - 256) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 16) _ 0%nat (C8 (Z_to_bv 64 (sh (v + 8))))); [exact C16 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add, sh_word by lia; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E m (S1 + 24) _ 0%nat (C8 (Z_to_bv 64 (v + 8)))); [exact C24 | reflexivity | reflexivity | lia
          | rewrite ES1; lia | lia | lia | subst E; evs; rewrite TablLib.zbv_add; reflexivity]. }
      apply Forall_cons. { eapply (kshadow0 _ _ _ (v + 8)); [subst E; evs; rewrite TablLib.zbv_add; reflexivity | lia | exact S8]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WV | rewrite EV; lia | unfold elenZ; rewrite EV; subst E; evs; rewrite u64_of_Z by lia; lia
                                                | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      do 3 (apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]).
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; split; [lia | exact EA]|].
      apply Forall_cons; [cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0xff8f8 m ro HR HK 20%nat [0xff928] (SCR [] [] []) 36%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (KK : kept_in KRLbb R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KRLbb HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    split; [exact (KK 3%bv ltac:(inb))|]. split; [exact (KK 4%bv ltac:(inb))|].
    split.
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; rewrite ?EV; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. }
    split; [subst M1; apply wmono_mem_denot|]. split; [intros lo hi S; subst M1; apply stk_mem_denot; exact S|].
    split; [intros MI; exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split.
    { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | rewrite EV; lia | exact WV | reflexivity | exact I | subst E; evs; reflexivity]. }
    split; [intros X; exfalso; apply X; reflexivity|].
    rreg HR' 9%bv L9. rreg HR' 20%bv L20. rreg HR' 23%bv L23. rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    unfold RPl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    + rewrite (KK 2%bv ltac:(inb)); exact P2.
    + rewrite (KK 8%bv ltac:(inb)); exact P8.
    + exact L9.
    + rewrite (KK 25%bv ltac:(inb)); exact P25.
    + exact L26.
    + exact L27.
    + rewrite (KK 18%bv ltac:(inb)); exact P18.
    + rewrite (KK 19%bv ltac:(inb)); exact P19.
    + exact L20.
    + rewrite (KK 21%bv ltac:(inb)); exact P21.
    + rewrite (KK 22%bv ltac:(inb)); exact P22.
    + rewrite L23, TablLib.zbv_add; reflexivity.
  Qed.

  Lemma L6_runs : site_runs L6.
  Proof. exact (conj L6_a (conj L6_b L6_c)). Qed.

End XPr4.
