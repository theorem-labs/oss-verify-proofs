(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import FpBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FpSites_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF CutVFX DecIface DecIfaceU DecScanPure DecOkDefs DecOkSem DecKinds5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatLems5_u DecfloatPre_u Pm10Leaf_scalbnl_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutHeap2 CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import DecAssume.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_decfloat5_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK. Import DFO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module DFA.

Definition hvf (regs : list expr) (R : bvmap 5 word) (n : nat) : word :=
  match find (fun r => expr_eqb (nth r regs (ELit 0)) (EVar n)) (seq 1 31) with Some r => getr R (Z_to_bv 5 (Z.of_nat r)) | None => Z_to_bv 64 0 end.
Definition ghost (Q CAN N : Z) (sv : nat -> Z) (regs : list expr) (R : bvmap 5 word) (n : nat) : word :=
  match n with
  | 32 => Z_to_bv 64 Q | 33 => Z_to_bv 64 CAN
  | 34 => Z_to_bv 64 (sv 1) | 35 => Z_to_bv 64 (sv 8) | 36 => Z_to_bv 64 (sv 9) | 37 => Z_to_bv 64 (sv 18) | 38 => Z_to_bv 64 (sv 19) | 39 => Z_to_bv 64 (sv 20)
  | 40 => Z_to_bv 64 (sv 21) | 41 => Z_to_bv 64 (sv 22) | 42 => Z_to_bv 64 (sv 23) | 43 => Z_to_bv 64 (sv 24) | 44 => Z_to_bv 64 (sv 25) | 45 => Z_to_bv 64 (sv 26)
  | 46 => Z_to_bv 64 (sv 27) | 47 => Z_to_bv 64 N
  | _ => hvf regs R n
  end%nat.
Definition mkE0 (Q CAN N : Z) (sv : nat -> Z) (regs : list expr) (R : bvmap 5 word) : env := Env (reg_ev R (ghost Q CAN N sv regs R)) (fun _ => []).

Definition kn0 : list kentry := Eval vm_compute in CC.cp_know cp0.
Definition kn1 : list kentry := Eval vm_compute in CC.cp_know cp1.
Definition kn2 : list kentry := Eval vm_compute in CC.cp_know cp2.
Definition rg0 : list expr := Eval vm_compute in CC.cp_regs cp0.
Definition rg1 : list expr := Eval vm_compute in CC.cp_regs cp1.
Definition rg2 : list expr := Eval vm_compute in CC.cp_regs cp2.

Section Final.
Context {SCFG_P : ScfgP}.

Definition entry_cp (e2 : bool) (N : Z) : CC.cutpoint := if e2 then (if N =? 1 then cp1 else cp2) else cp0.
Lemma entry_at : forall e2 R M SP F P Q CAN sv txt, PDC.dec_pre RSEGS PDCU.ubsan11 e2 R M SP F P Q CAN sv txt ->
  let N := Z.of_nat (length txt) in let c := entry_cp e2 N in
  CC.At RSEGS c (mkE0 Q CAN N sv (CC.cp_regs c) R) R M.
Proof.
  intros e2 R M SP F P Q CAN sv txt Hpre N c.
  destruct Hpre as (Rsp & Hal & Hfloor & Htop & RF & R23 & R18 & R22 & R24 & R9 & R20 & R4 & Hdef & Hwr & Hsaves & Hret & Hcan & Hguard & Hgap & Hfile & Hfs & Htext & Htap & Herrw & Himg & Hent).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  fold N in Tn, TQ2, TQ3, Td, Ta1, Ta2, Ta3. unfold PDC.STK_FLOOR, PDC.FRAME, PDC.SCR_D, PDC.apart in *. cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDCU.ubsan11] in *.
  assert (HN0 : 0 <= N) by (unfold N; lia).
  set (E0 := mkE0 Q CAN N sv (CC.cp_regs c) R).
  assert (U2 : bv_unsigned (ev E0 2) = SP) by exact Rsp.
  assert (U21 : bv_unsigned (ev E0 21) = F) by exact RF.
  assert (U32 : bv_unsigned (ev E0 32) = Q) by (change (ev E0 32) with (Z_to_bv 64 Q); apply u64_of_Z; lia).
  assert (U47 : bv_unsigned (ev E0 47) = N) by (change (ev E0 47) with (Z_to_bv 64 N); apply u64_of_Z; lia).
  assert (ES2 : forall o, estart E0 (SA (EVar 2) o) = SP + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U2; reflexivity).
  assert (ES21 : forall o, estart E0 (SA (EVar 21) o) = F + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U21; reflexivity).
  assert (ES32 : forall o, estart E0 (SA (EVar 32) o) = Q + o) by (intros o; unfold estart; cbn [a_base a_off edenot]; rewrite U32; reflexivity).
  assert (ESL : forall a o, 0 <= a < 2 ^ 64 -> estart E0 (SA (ELit a) o) = a + o) by (intros a o Ha; unfold estart; cbn [a_base a_off edenot]; rewrite u64_of_Z by lia; reflexivity).
  assert (ESQN : forall o, estart E0 (SA (EAlu ALU_ADD (EVar 32) (EVar 47)) o) = Q + N + o).
  { intros o. unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32, U47. rewrite Z.mod_small by lia. reflexivity. }
  assert (EL : forall z, 0 <= z < 2 ^ 64 -> elenZ E0 (ELit z) = z) by (intros z Hz; unfold elenZ; cbn [edenot]; apply u64_of_Z; lia).
  assert (ELN : elenZ E0 (EVar 47) = N) by exact U47.
  assert (ELN1 : elenZ E0 (EAlu ALU_ADD (EVar 47) (ELit 1)) = N + 1).
  { unfold elenZ. cbn [edenot]. rewrite u_add64, U47. rewrite u64_of_Z by lia. apply Z.mod_small. lia. }
  assert (HNUL : M (Z_to_bv 64 (Q + N)) <> None) by (apply Td; lia).

  assert (COMMON : forall nlo nhi pv tail, nlo <= N <= nhi -> bv_unsigned (edenot E0 pv) = P -> know_ok RSEGS E0 M tail ->
            know_ok RSEGS E0 M
              ([KRange (EVar 2) 140735332483328 140737488346912; KAlign (EVar 2) 16; KImg 65536 801400; KWr (SA (EVar 2) (-256)) (ELit 8672); KWr (SA (EVar 21) 8) (ELit 8);
                KWr (SA (ELit 0) 878428) (ELit 4); KRange (EVar 21) 140735332483072 140737488355072; KDisj (SA (EVar 21) 8) (ELit 192) (SA (EVar 2) (-256)) (ELit 8672);
                KRange (EVar 32) 4096 140737488355328; KRange (EVar 47) nlo nhi;
                KWord (SA (EVar 2) 8408) 8 (EVar 34); KWord (SA (EVar 2) 8400) 8 (EVar 35); KWord (SA (EVar 2) 8392) 8 (EVar 36); KWord (SA (EVar 2) 8384) 8 (EVar 37);
                KWord (SA (EVar 2) 8376) 8 (EVar 38); KWord (SA (EVar 2) 8368) 8 (EVar 39); KWord (SA (EVar 2) 8360) 8 (EVar 40); KWord (SA (EVar 2) 8352) 8 (EVar 41);
                KWord (SA (EVar 2) 8344) 8 (EVar 42); KWord (SA (EVar 2) 8336) 8 (EVar 43); KWord (SA (EVar 2) 8328) 8 (EVar 44); KWord (SA (EVar 2) 8320) 8 (EVar 45);
                KWord (SA (EVar 2) 8312) 8 (EVar 46); KWord (SA (EVar 2) 8296) 8 (EVar 33); KWord (SA (ELit 0) 1010288) 8 (EVar 33);
                KWord (SA (EVar 21) 8) 8 pv; KWord (SA (EVar 21) 184) 8 (ELit 18446744073709551615); KWord (SA (EVar 21) 192) 8 (ELit 0);
                KUnk (SA (EVar 2) (-256)) (ELit 8552); KUnk (SA (EVar 2) 8304) (ELit 8); KUnk (SA (EVar 32) 0) (EVar 47); KZero (SA (EAlu ALU_ADD (EVar 32) (EVar 47)) 0) (ELit 1);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 2) (-256)) (ELit 8672);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (EVar 21) 8) (ELit 192);
                KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (ELit 0) 878428) (ELit 4)] ++ tail)).
  { intros nlo nhi pv tail HNr Hpv Htail. unfold know_ok. cbn [app].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U2; split; [lia | exact Hal]|].
    apply Forall_cons; [cbn [kentry_ok]; split; [lia | split; [lia | exact Himg]]|].
    apply Forall_cons; [apply (kwr_of_writable RSEGS E0 M _ _ (SP - 256) 8672); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | lia | exact Hwr]|].
    apply Forall_cons; [apply (kwr_of_writable RSEGS E0 M _ _ (F + 8) 8); [rewrite ES21; lia | apply EL; lia | lia | lia | lia | lia | exact Hfw]|].
    apply Forall_cons; [apply (kwr_of_writable RSEGS E0 M _ _ (878592 - 164) 4); [rewrite ESL by lia; lia | apply EL; lia | lia | lia | lia | lia | exact Herrw]|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U21; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES21, ES2, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U32; lia|].
    apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U47; lia|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8408) (sv 1%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8408) with (SP + 6384 + 2024) by lia; apply (proj1 (Hsaves 1%nat 2024 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8400) (sv 8%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8400) with (SP + 6384 + 2016) by lia; apply (proj1 (Hsaves 8%nat 2016 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8392) (sv 9%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8392) with (SP + 6384 + 2008) by lia; apply (proj1 (Hsaves 9%nat 2008 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8384) (sv 18%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8384) with (SP + 6384 + 2000) by lia; apply (proj1 (Hsaves 18%nat 2000 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8376) (sv 19%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8376) with (SP + 6384 + 1992) by lia; apply (proj1 (Hsaves 19%nat 1992 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8368) (sv 20%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8368) with (SP + 6384 + 1984) by lia; apply (proj1 (Hsaves 20%nat 1984 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8360) (sv 21%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8360) with (SP + 6384 + 1976) by lia; apply (proj1 (Hsaves 21%nat 1976 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8352) (sv 22%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8352) with (SP + 6384 + 1968) by lia; apply (proj1 (Hsaves 22%nat 1968 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8344) (sv 23%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8344) with (SP + 6384 + 1960) by lia; apply (proj1 (Hsaves 23%nat 1960 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8336) (sv 24%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8336) with (SP + 6384 + 1952) by lia; apply (proj1 (Hsaves 24%nat 1952 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8328) (sv 25%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8328) with (SP + 6384 + 1944) by lia; apply (proj1 (Hsaves 25%nat 1944 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8320) (sv 26%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8320) with (SP + 6384 + 1936) by lia; apply (proj1 (Hsaves 26%nat 1936 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8312) (sv 27%nat)); [rewrite ES2; lia | lia | lia | reflexivity | replace (SP + 8312) with (SP + 6384 + 1928) by lia; apply (proj1 (Hsaves 27%nat 1928 ltac:(unfold PDC.SAVES; cbn; tauto)))]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (SP + 8296) CAN); [rewrite ES2; lia | lia | lia | reflexivity | exact Hcan]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ 1010288 CAN); [rewrite ESL by lia; lia | lia | lia | reflexivity | exact Hguard]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 8) P); [rewrite ES21; lia | lia | lia | rewrite <- Hpv; rewrite Z_to_bv_bv_unsigned; reflexivity | exact Hf8]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 184) (2 ^ 64 - 1)); [rewrite ES21; lia | lia | lia | reflexivity | exact Hf184]|].
    apply Forall_cons; [apply (CL5.kword64_intro RSEGS E0 M _ _ (F + 192) 0); [rewrite ES21; lia | lia | lia | reflexivity | exact Hf192]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ (SP - 256) 8552); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub M (SP - 256) (256 + 8416) (SP - 256) 8552 Hdef); lia]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ (SP + 8304) 8); [rewrite ES2; lia | apply EL; lia | lia | lia | lia | apply (L5.defined_sub M (SP - 256) (256 + 8416) (SP + 8304) 8 Hdef); lia]|].
    apply Forall_cons; [apply (CL5.kunk_intro RSEGS E0 M _ _ Q N); [rewrite ES32; lia | exact ELN | lia | lia | lia | apply (L5.defined_sub M Q (N + 1) Q N Td); lia]|].
    apply Forall_cons; [apply (kzero1_intro RSEGS E0 M _ (Q + N)); [rewrite ESQN; lia | lia | lia | exact Tn | exact HNUL]|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES2, ELN1, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ES21, ELN1, !EL by lia; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite ES32, ESL, ELN1, !EL by lia; lia|].
    exact Htail. }

  assert (REGS : forall regs, regs = CC.cp_regs c -> (regs = rg0 \/ regs = rg1 \/ regs = rg2) -> regs_ok (mkE0 Q CAN N sv regs R) regs R).
  { intros regs _ Hrg. apply regs_ok_tmpl. intros n Hn.
    pose proof (rz_word R 4 _ R4) as W4. pose proof (rz_word R 18 _ R18) as W18. pose proof (rz_word R 20 _ R20) as W20. pose proof (rz_word R 22 _ R22) as W22.
    pose proof (rz_word R 23 _ R23) as W23. pose proof (rz_word R 24 _ R24) as W24.
    destruct Hrg as [-> | [-> | ->]];
      do 32 (destruct n as [|n]; [first [lia | reflexivity | (symmetry; first [exact W4 | exact W18 | exact W20 | exact W22 | exact W23 | exact W24])]|]); lia. }
  split.
  - apply REGS; [reflexivity|]. unfold c, entry_cp. destruct e2; [destruct (N =? 1)|]; [right; left | right; right | left]; reflexivity.
  - unfold c, entry_cp in *. destruct e2.
    + destruct Hent as (HQ & r0 & Et). assert (HN1 : 1 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
      destruct (Z.eqb_spec N 1) as [E1|E1].
      * change (CC.cp_know cp1) with kn1. unfold kn1. rewrite <- (app_nil_r [KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (ELit 0) 878428) (ELit 4)]).
        apply (COMMON 1 1 (EAlu ALU_ADD (EVar 32) (ELit 2)) [] ltac:(lia)); [|constructor].
        cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
      * change (CC.cp_know cp2) with kn2. unfold kn2. rewrite <- (app_nil_r [KDisj (SA (EVar 32) 0) (EAlu ALU_ADD (EVar 47) (ELit 1)) (SA (ELit 0) 878428) (ELit 4)]).
        apply (COMMON 2 67108864 (EAlu ALU_ADD (EVar 32) (ELit 2)) [] ltac:(lia)); [|constructor].
        cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
    + destruct Hent as (HQ & c0 & r0 & Et & Hc0 & Ra0). assert (HN1 : 1 <= N) by (unfold N; rewrite Et; cbn [length]; lia).
      change (CC.cp_know cp0) with kn0. unfold kn0.
      apply (COMMON 1 67108864 (EAlu ALU_ADD (EVar 32) (ELit 1)) [KRange (EVar 48) 49 57; KWord (SA (EAlu ALU_ADD (EVar 32) (ELit (-1))) 1) 1 (EVar 48)] ltac:(lia)).
      * cbn [edenot]. rewrite u_add64, U32. rewrite u64_of_Z by lia. rewrite Z.mod_small by lia. lia.
      * assert (U48 : bv_unsigned (ev E0 48) = c0) by exact Ra0.
        apply Forall_cons; [cbn [kentry_ok edenot]; rewrite U48; lia|]. apply Forall_cons; [|constructor].
        apply (kword8_intro RSEGS E0 M _ _ Q c0); [| lia | lia | exact U48 | lia |].
        -- unfold estart. cbn [a_base a_off edenot]. rewrite u_add64, U32. change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1).
           replace (Q + (2 ^ 64 - 1)) with (Q - 1 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
        -- pose proof (Tb 0%nat ltac:(rewrite Et; cbn; lia)) as B. rewrite Et in B. cbn [nth] in B. replace (Q + Z.of_nat 0) with Q in B by lia. exact B.
Qed.

End Final.
End DFA.
