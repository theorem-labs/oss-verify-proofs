(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail S1Layout
  SumMemcpyBase SumMemcpy.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac DiagS1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Definition FW_RETPC : Z := 0xd5e3c.
Definition FW_RET_MC : Z := 0xd5e0c.
Definition SN_RETPC : Z := 0xdb2a8.
Definition SN_RET_MC : Z := 0xdb22c.

Definition leaf_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma memcpy_entry_eq : s1_memcpy_entry = Z_to_bv 64 A_MEMCPY.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section Leaf.
  Context {fx : FPState}.

  Lemma fwritex_buf : forall R M (sp ret s l f wpos wend : Z) bs,
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) -> 0 <= ret < 2 ^ 64 ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 s -> getr R 11%bv = Z_to_bv 64 l -> getr R 12%bv = Z_to_bv 64 f ->
    2 ^ 16 <= sp - 64 -> sp < 2 ^ 47 -> sp mod 16 = 0 -> mdef M (sp - 64) 64 ->
    2 ^ 16 <= f -> f + 232 < 2 ^ 47 -> (f + 232 <= sp - 64 \/ sp <= f) -> mdef M f 232 ->
    fld SEGS M (f + 32) 8 wend -> fld SEGS M (f + 40) 8 wpos -> fld SEGS M (f + 144) 4 (2 ^ 32 - 1) ->
    0 <= l -> wpos + l <= wend -> 2 ^ 16 <= wpos -> wend < 2 ^ 47 -> mdef M wpos l ->
    0 <= s -> s + l < 2 ^ 47 -> rdn SEGS M (Z_to_bv 64 s) (Z.to_nat l) = Some bs ->
    (wpos + l <= s \/ s + l <= wpos) -> (wpos + l <= f \/ f + 232 <= wpos) -> (wpos + l <= sp - 64 \/ sp <= wpos) ->
    (s + l <= sp - 64 \/ sp <= s) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 A_FWRITEX) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 l
      /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
      /\ stores_in (fun a => zwin (sp - 64) sp a \/ zwin wpos (wpos + l) a \/ zwin (f + 40) (f + 48) a) M M'
      /\ fld SEGS M' (f + 40) 8 (wpos + l) /\ fld SEGS M' (f + 32) 8 wend /\ fld SEGS M' (f + 144) 4 (2 ^ 32 - 1).
  Proof using fx.
    intros R M sp ret s l f wpos wend bs Hra Hret Hretr Hsp Ha0 Ha1 Ha2 Hsplo Hsphi Hal HDst Hflo Hfhi DJf HDf F32 F40 F144
           Hl Hroom Hwlo Hwend HDw Hs0 Hsl RD DJ1 DJ2 DJ3 DJ4.
    set (E := Eseed R [Z_to_bv 64 wend; Z_to_bv 64 wpos]).
    assert (HR : regs_ok E sr_id R) by (apply regs_ok_seed).
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-64)) (ELit 64); KRange (EVar 2) (2 ^ 16 + 64) (2 ^ 47); KAlign (EVar 2) 16;
       KRange (EVar 12) (2 ^ 16) (2 ^ 47 - 233); KRange (EVar 11) 0 (2 ^ 47);
       KWord (SA (EVar 12) 32) (N.to_nat 8) (EVar 32); KWord (SA (EVar 12) 40) (N.to_nat 8) (EVar 33); KWord (SA (EVar 12) 144) (N.to_nat 4) (ELit (2 ^ 32 - 1));
       KRange (EVar 32) (2 ^ 16) (2 ^ 47); KRange (EVar 33) (2 ^ 16) (2 ^ 47);
       KDisj (SA (EVar 12) 0) (ELit 232) (SA (EVar 2) (-64)) (ELit 64)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ sp (-64) 64); [evs; exact Hsp | lia | lia | lia | lia | exact HDst].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal].
      - krv Ha2. - krv Ha1.
      - kwv F32 Ha2. - kwv F40 Ha2. - kwv F144 Ha2.
      - eapply krange_var; [evs; reflexivity | lia | lia]. - eapply krange_var; [evs; reflexivity | lia | lia].
      - kdj f 232 sp 64. lia. }
    xrun_at HR HK fx A_FWRITEX (seg_rom SEGS) 60%nat [A_MEMCPY; FW_RETPC] (SCR [true] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1.
    wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?m _) => set (M1 := m) in Hms1 end.
    assert (ST1 : stores_in (zwin (sp - 64) sp) M M1) by (subst M1; stores_tower).
    assert (SL1 : slots SEGS M1 sp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]) by (subst M1; slots_tower).
    regval HR1 (1%bv : reg) FW_RET_MC X1. regval HR1 (2%bv : reg) (sp - 64) X2.
    regval HR1 (10%bv : reg) wpos X10. regval HR1 (11%bv : reg) s X11. regval HR1 (12%bv : reg) l X12.
    regval HR1 (8%bv : reg) f X8. regval HR1 (9%bv : reg) l X9. regval HR1 (19%bv : reg) 0 X19.

    assert (MC : mcH SEGS M1 (Z_to_bv 64 wpos) (Z_to_bv 64 s) l bs).
    { pose proof (rdn_length _ _ _ _ _ RD) as Hlen. constructor.
      - lia. - exact Hlen.
      - rewrite Hlen, <- RD. apply rdn_ext; [rewrite u64_of_Z by lia; lia|]. intros x Hx. rewrite u64_of_Z in Hx by lia. rewrite ?Hlen, ?Z2Nat.id in Hx by lia.
        apply (proj1 ST1). unfold zwin. lia.
      - rewrite Hlen. replace (Z_to_bv 64 wpos) with (Z_to_bv 64 (wpos + 0)) by (f_equal; lia).
        apply (mdef_store_ok_off SEGS M1 wpos l 0 (Z.to_nat l)); [eapply stores_in_mdef; [exact ST1 | exact HDw] | lia | lia | lia | lia].
      - rewrite !u64_of_Z by lia. lia.
      - rewrite u64_of_Z by lia. lia.
      - rewrite u64_of_Z by lia. lia. }
    destruct (s1_memcpy M1 (Z_to_bv 64 wpos) (Z_to_bv 64 s) l bs (seg_rom SEGS) R1 (Z_to_bv 64 FW_RET_MC)
                MC ltac:(apply bv_eq; vm_compute; reflexivity) X1 X10 X11 X12) as (R2 & Hms2 & KP2).
    rewrite memcpy_entry_eq in Hms2.
    set (M2 := wbytes M1 (Z_to_bv 64 wpos) bs) in Hms2.
    pose proof (rdn_length _ _ _ _ _ RD) as Hlen.
    assert (ST2 : stores_in (fun a => zwin (sp - 64) sp a \/ zwin wpos (wpos + l) a) M M2).
    { subst M2. eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1 | intros a Ha; left; exact Ha] | lia | rewrite Hlen; lia | ].
      intros x Hx. rewrite Hlen in Hx. right. unfold zwin. lia. }
    assert (Y2 : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KP2 2%bv) by inl; exact X2).
    assert (Y8 : getr R2 8%bv = Z_to_bv 64 f) by (rewrite (KP2 8%bv) by inl; exact X8).
    assert (Y9 : getr R2 9%bv = Z_to_bv 64 l) by (rewrite (KP2 9%bv) by inl; exact X9).
    assert (Y19 : getr R2 19%bv = Z_to_bv 64 0) by (rewrite (KP2 19%bv) by inl; exact X19).
    assert (SL2 : slots SEGS M2 sp [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]).
    { eapply slots_agree; [exact SL1 | cbn; lia | lia | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]].
      subst M2. intros a Ha. unfold zwin in Ha. cbn in Ha. apply MemSplit.wbytes_outside; rewrite !u64_of_Z by lia; rewrite Hlen; lia. }
    assert (F40' : fld SEGS M2 (f + 40) 8 wpos).
    { unfold fld. subst M2. rewrite SumWalkTac.rdn_wbytes_out_Z by (rewrite Hlen; cbn; lia). subst M1. peel. exact F40. }

    set (E2 := Eseed R2 [Z_to_bv 64 wpos; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; getr R 20%bv; getr R 21%bv]).
    assert (HR2 : regs_ok E2 sr_id R2) by (apply regs_ok_seed).
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 2) 0) (ELit 64); KRange (EVar 2) (2 ^ 16) (2 ^ 47 - 64); KAlign (EVar 2) 16;
       KRange (EVar 8) (2 ^ 16) (2 ^ 47 - 233); KRange (EVar 9) 0 (2 ^ 47);
       KWord (SA (EVar 8) 40) (N.to_nat 8) (EVar 32); KRange (EVar 32) (2 ^ 16) (2 ^ 47);
       KDisj (SA (EVar 8) 0) (ELit 232) (SA (EVar 2) 0) (ELit 64);
       KWord (SA (EVar 2) 56) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 48) (N.to_nat 8) (EVar 34);
       KWord (SA (EVar 2) 40) (N.to_nat 8) (EVar 35); KWord (SA (EVar 2) 32) (N.to_nat 8) (EVar 36);
       KWord (SA (EVar 2) 24) (N.to_nat 8) (EVar 37); KWord (SA (EVar 2) 16) (N.to_nat 8) (EVar 38);
       KWord (SA (EVar 2) 8) (N.to_nat 8) (EVar 39)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (sp - 64) 0 64); [evs; exact Y2 | lia | lia | lia | lia | rewrite Z.add_0_r; eapply stores_in_mdef; [exact ST2 | exact HDst]].
      - krv Y2. - eapply kalign_var; [evs; exact Y2 | lia | lia | mlia].
      - krv Y8. - krv Y9.
      - kwv F40' Y8. - eapply krange_var; [evs; reflexivity | lia | lia].
      - kdj f 232 (sp - 64) 64. lia.
      - kwe (SL2 0%nat ltac:(cbn; lia)) Y2. - kwe (SL2 1%nat ltac:(cbn; lia)) Y2.
      - kwe (SL2 2%nat ltac:(cbn; lia)) Y2. - kwe (SL2 3%nat ltac:(cbn; lia)) Y2.
      - kwe (SL2 4%nat ltac:(cbn; lia)) Y2. - kwe (SL2 5%nat ltac:(cbn; lia)) Y2.
      - kwe (SL2 6%nat ltac:(cbn; lia)) Y2. }
    xrun_at HR2 HK2 fx FW_RET_MC (seg_rom SEGS) 60%nat [A_MEMCPY; FW_RETPC] (SCR [] [] []) 48%N.
    { scs_auto. eapply mdef_sub; [exact HDf | lia | cbn; lia]. }
    rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?m _) => set (M3 := m) in Hms3 end.
    regval HR' (1%bv : reg) ret Z1. regval HR' (10%bv : reg) l Z10.
    pose proof (ret_at SEGS FW_RETPC R' M3 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) Z1 Hret) as Hms4.
    exists R', M3. split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | eapply msteps_trans; [exact Hms3 | exact Hms4]]]|].
    split; [exact Z10|].
    split. { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' KP2 HR1|]). destruct Hr. }
    assert (ST3 : stores_in (fun a => zwin (sp - 64) sp a \/ zwin wpos (wpos + l) a \/ zwin (f + 40) (f + 48) a) M M3).
    { subst M3. eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST2 | intros a [Ha|Ha]; [left | right; left]; exact Ha] | lia | cbn; lia | intros x Hx; cbn in Hx; right; right; unfold zwin; lia]. }
    split; [exact ST3|].
    split; [unfold fld; subst M3; peel|].
    split.
    - eapply fld_agree; [lia | cbn; lia | exact F32 | eapply stores_in_agree; [exact ST3 | intros a Ha; cbv beta; unfold zwin in *; cbn in Ha; lia]].
    - eapply fld_agree; [lia | cbn; lia | exact F144 | eapply stores_in_agree; [exact ST3 | intros a Ha; cbv beta; unfold zwin in *; cbn in Ha; lia]].
  Qed.
End Leaf.
