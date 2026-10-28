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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_DStat LbB_RGb2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_RGl LbB_TablStmt LbB_TablOS1 LbB_TablPT1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition KTP : list reg := [3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Section PT3.
  Context {HCEIL : HeapCeil}.

  Lemma pt_tail : forall (R : bvmap 5 word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (ff fp SP S1 : Z),
    getr R 8 = Z_to_bv 64 SP -> getr R 9 = Z_to_bv 64 S1 -> getr R 26 = Z_to_bv 64 (sh ff) ->
    ff mod 64 = 0 -> 0x6e8000 <= ff -> ff + 64 <= 2 ^ 47 -> (ff + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) ->
    0x6e8000 <= fp -> fp + 1 <= ff -> (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp) ->
    2 ^ 45 <= S1 -> S1 + 192 <= SP -> SP <= 2 ^ 47 -> ff + 64 <= S1 ->
    rw_cells asegs m (SP - 104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m S1 [C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 ff)] ->
    rw_cells asegs m (ff + 56) [C8 (Z_to_bv 64 fp)] ->
    wr_at asegs m ff 8 -> wr_at asegs m (sh ff) 8 -> wr_at asegs m fp 1 -> mem_inv asegs m ->
    exists R' M',
      CatSim.msteps asegs (MS R F (Z_to_bv 64 PT_EXIT) fc None m ro) (MS R' F (Z_to_bv 64 PT_RET) fc None M' ro)
      /\ getr R' 1 = ra /\ getr R' 2 = Z_to_bv 64 SP /\ getr R' 8 = s0 /\ getr R' 9 = s1
      /\ getr R' 18 = s2 /\ getr R' 19 = s3 /\ getr R' 20 = s4 /\ getr R' 21 = s5 /\ getr R' 22 = s6 /\ getr R' 23 = s7
      /\ getr R' 24 = s8 /\ getr R' 25 = s9 /\ getr R' 26 = s10 /\ getr R' 27 = s11 /\ kept_in KTP R R'
      /\ munch [(sh ff, sh ff + 8); (ff, ff + 8); (fp, fp + 1)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo hi, stk asegs m lo hi -> stk asegs M' lo hi)
      /\ mrd asegs M' (wa fp) = Some (b8 0).
  Proof.
    intros R F fc m ro ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ff fp SP S1 P8 P9 P26 F64 FLO FHI FB PLO PFF PB S45 SS SPH FS1
      CSF CS1 CFP WF WS WP MI.
    assert (Q : mul_div M_MUL (Z_to_bv 64 64) (Z_to_bv 64 (ff / 64)) = Z_to_bv 64 ff) by (apply q64; lia).
    assert (QS : 8 * (ff / 64) + SHBASE = sh ff) by (apply q8sh; lia).
    assert (SHL : 0x7fff8000 <= sh ff /\ sh ff + 8 <= 0x10007fff8000).
    { unfold sh; rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
    pose (E := Eseed R [Z_to_bv 64 (ff / 64); Z_to_bv 64 fp; Z_to_bv 64 SP; Z_to_bv 64 S1;
                        ra; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 34); (9%bv, EVar 35);
                                       (26%bv, EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 32)) (ELit 2147450880))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst E; evs.
      - exact P8.
      - exact P9.
      - rewrite P26. rewrite w_mul by (Z.div_mod_to_equations; lia). rewrite w_add by (unfold sh in *; Z.div_mod_to_equations; lia).
        f_equal. unfold SHBASE in QS. lia. }
    assert (EF : bv_unsigned (edenot E (EMd M_MUL (ELit 64) (EVar 32))) = ff) by (subst E; evs; rewrite Q, u64_of_Z by lia; reflexivity).
    assert (ES : bv_unsigned (edenot E (EMd M_MUL (ELit 8) (EVar 32))) = 8 * (ff / 64))
      by (subst E; evs; rewrite w_mul by (Z.div_mod_to_equations; lia); rewrite u64_of_Z by (Z.div_mod_to_equations; lia); reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 34)) = SP) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (EQ : bv_unsigned (edenot E (EVar 33)) = fp) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (E1 : bv_unsigned (edenot E (EVar 35)) = S1) by (subst E; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m
       [ KWord (SA (EVar 35) 0) 8 (EMd M_MUL (ELit 64) (EVar 32)); KWord (SA (EVar 35) 8) 8 (EMd M_MUL (ELit 64) (EVar 32));
         KWord (SA (EMd M_MUL (ELit 64) (EVar 32)) 56) 8 (EVar 33);
         KWord (SA (EVar 34) (-104)) 8 (EVar 48); KWord (SA (EVar 34) (-96)) 8 (EVar 47); KWord (SA (EVar 34) (-88)) 8 (EVar 46);
         KWord (SA (EVar 34) (-80)) 8 (EVar 45); KWord (SA (EVar 34) (-72)) 8 (EVar 44); KWord (SA (EVar 34) (-64)) 8 (EVar 43);
         KWord (SA (EVar 34) (-56)) 8 (EVar 42); KWord (SA (EVar 34) (-48)) 8 (EVar 41); KWord (SA (EVar 34) (-40)) 8 (EVar 40);
         KWord (SA (EVar 34) (-32)) 8 (EVar 39); KWord (SA (EVar 34) (-24)) 8 (EVar 38); KWord (SA (EVar 34) (-16)) 8 (EVar 37);
         KWord (SA (EVar 34) (-8)) 8 (EVar 36);
         KWr (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
         KWr (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
         KWr (SA (EVar 33) 0) (ELit 1);
         KRange (EVar 32) (0x6e8000 / 64) (2 ^ 41); KRange (EVar 34) (2 ^ 45) (2 ^ 47); KRange (EVar 33) 0x6e8000 (2 ^ 47);
         KRange (EVar 35) (2 ^ 45) (2 ^ 47);
         KDisj (SA (EVar 34) (-104)) (ELit 104) (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
         KDisj (SA (EVar 34) (-104)) (ELit 104) (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8);
         KDisj (SA (EVar 34) (-104)) (ELit 104) (SA (EVar 33) 0) (ELit 1);
         KDisj (SA (EVar 35) 0) (ELit 16) (SA (EMd M_MUL (ELit 64) (EVar 32)) 0) (ELit 8);
         KDisj (SA (EMd M_MUL (ELit 64) (EVar 32)) 56) (ELit 8) (SA (EMd M_MUL (ELit 8) (EVar 32)) SHBASE) (ELit 8) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m S1 _ 0%nat (C8 (Z_to_bv 64 ff))); [exact CS1 | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite E1; lia | lia | lia | subst E; evs; rewrite Q; reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m S1 _ 8%nat (C8 (Z_to_bv 64 ff))); [exact CS1 | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite E1; cbn; lia | lia | lia | subst E; evs; rewrite Q; reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m (ff + 56) _ 0%nat (C8 (Z_to_bv 64 fp))); [exact CFP | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EF; lia | lia | lia | subst E; evs; reflexivity]. }
      Ltac ktail CSF EP k c :=
        eapply (kword_of_rw_cells asegs _ _ _ _ k c); [exact CSF | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | lia | lia | HLib.evs; reflexivity].
      apply Forall_cons. { ktail CSF EP 0%nat (C8 s11). }
      apply Forall_cons. { ktail CSF EP 8%nat (C8 s10). }
      apply Forall_cons. { ktail CSF EP 16%nat (C8 s9). }
      apply Forall_cons. { ktail CSF EP 24%nat (C8 s8). }
      apply Forall_cons. { ktail CSF EP 32%nat (C8 s7). }
      apply Forall_cons. { ktail CSF EP 40%nat (C8 s6). }
      apply Forall_cons. { ktail CSF EP 48%nat (C8 s5). }
      apply Forall_cons. { ktail CSF EP 56%nat (C8 s4). }
      apply Forall_cons. { ktail CSF EP 64%nat (C8 s3). }
      apply Forall_cons. { ktail CSF EP 72%nat (C8 s2). }
      apply Forall_cons. { ktail CSF EP 80%nat (C8 s1). }
      apply Forall_cons. { ktail CSF EP 88%nat (C8 s0). }
      apply Forall_cons. { ktail CSF EP 96%nat (C8 ra). }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WF | unfold estart; cbn [a_base a_off]; rewrite EF; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EF; subst E; evs; rewrite u64_of_Z by lia; lia
                                  | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WS | unfold estart; cbn [a_base a_off]; rewrite ES; unfold SHBASE in *; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite ES; subst E; evs; rewrite u64_of_Z by lia; unfold SHBASE in *; lia
                                  | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [a_base a_off]; rewrite EQ; lia
                                  | unfold estart, elenZ; cbn [a_base a_off]; rewrite EQ; subst E; evs; rewrite u64_of_Z by lia; lia
                                  | unfold elenZ; subst E; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. subst E; evs. rewrite u64_of_Z by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations; lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EP. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite EQ. lia. }
      apply Forall_cons. { cbn [kentry_ok]. rewrite E1. lia. }
      do 5 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite ?EF, ?ES, ?EP, ?EQ, ?E1; subst E; evs;
                                rewrite ?u64_of_Z by lia; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PT_EXIT m ro HR HK 100%nat [PT_RET] (SCR [] [] []) 49%N.
    { first [apply Forall_nil | split_scs]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists R', M1. split; [exact Hms|].
    assert (KK : kept_in KTP R R') by (intros rr Hrr; eapply (syms_id_sound R _ _ R' KTP HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hrr]).
    assert (MU1 : munch [(sh ff, sh ff + 8); (ff, ff + 8); (fp, fp + 1)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off];
                                  first [rewrite EF | rewrite ES | rewrite EQ];
                                  cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; unfold SHBASE in *; lia|]).
      apply Forall_nil. }
    assert (FL : rw_cells asegs M1 fp [C1 (b8 0)]).
    { subst M1. eapply (rw_cells_log_nth _ m _ 0%nat); [exact Hlf | reflexivity | apply Forall_nil
        | unfold estart; cbn [a_base a_off]; rewrite EQ; lia | exact WP | reflexivity | exact I | reflexivity]. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (SK1 : forall lo hi, stk asegs m lo hi -> stk asegs M1 lo hi) by (intros lo hi S; subst M1; apply stk_mem_denot; exact S).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 9%bv L9. rreg HR' 18%bv L18. rreg HR' 19%bv L19.
    rreg HR' 20%bv L20. rreg HR' 21%bv L21. rreg HR' 22%bv L22. rreg HR' 23%bv L23. rreg HR' 24%bv L24. rreg HR' 25%bv L25.
    rreg HR' 26%bv L26. rreg HR' 27%bv L27.
    split; [exact L1|]. split; [first [exact L2 | rewrite L2, TablLib.zbv_add; f_equal; lia]|].
    split; [exact L8|]. split; [exact L9|]. split; [exact L18|]. split; [exact L19|]. split; [exact L20|]. split; [exact L21|].
    split; [exact L22|]. split; [exact L23|]. split; [exact L24|]. split; [exact L25|]. split; [exact L26|]. split; [exact L27|].
    split; [exact KK|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact SK1|].
    destruct FL as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B.
  Qed.
End PT3.
