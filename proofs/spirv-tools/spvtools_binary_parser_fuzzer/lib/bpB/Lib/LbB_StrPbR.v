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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_ContStmt LbB_ContV4R.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition SPB_ENTRY : Z := 0x120000.
Definition SPB_RET : Z := 0x120130.

Definition SPBSAVED : list reg := [22; 21; 20; 19; 18; 9; 8; 1]%bv.

Definition SPBK : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma fldA_log_nth : forall E M lg (k : nat) (a : saddr) (w : nat) (v : expr) (A x : Z),
  log_flat E lg -> nth_error lg k = Some (SE a w v) ->
  Forall (fun e' => estart E (e_addr e') + Z.of_nat (e_width e') <= estart E a \/ estart E a + Z.of_nat w <= estart E (e_addr e')) (firstn k lg) ->
  estart E a = A -> edenot E v = Z_to_bv 64 x ->
  fldA (mem_denot E M lg) A w x.
Proof.
  intros E M lg k a w v A x Hf Hn Hd Hs Hv.
  assert (Hlg : lg = firstn k lg ++ SE a w v :: skipn (S k) lg).
  { clear - Hn. revert k Hn. induction lg as [|y lg IH]; intros k Hn; [destruct k; discriminate|].
    destruct k as [|k]; cbn in Hn |- *; [injection Hn as ->; reflexivity|]. f_equal. exact (IH k Hn). }
  rewrite Hlg in Hf |- *.
  pose proof (log_flat_mid E _ a w v _ Hf) as [Hw8 Hfa].
  pose proof (flat_u E a (Z.of_nat w) Hfa) as Hu. pose proof Hfa as (G1 & G2 & G3 & G4).
  unfold fldA, fld. replace (Z_to_bv 64 A) with (adenot E a).
  - rewrite <- Hv. apply rdn_mem_denot_hit; assumption.
  - apply bv_eq. rewrite Hu, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small; lia.
Qed.

Lemma dmono_mem_denot : forall E M log x, M x <> None -> mem_denot E M log x <> None.
Proof.
  intros E M log x Hx. destruct (mem_denot_cases E M log x) as [E1|(b & E1)]; rewrite E1; [exact Hx | discriminate].
Qed.

Ltac sp_dj :=
  repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; unfold wz;
                              rewrite ?w_mul, ?w_add by lia; rewrite ?u64_of_Z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]);
  apply Forall_nil.

Ltac sp_fld Hlf k :=
  eapply (fldA_log_nth _ _ _ k);
  [ exact Hlf | reflexivity | cbn [firstn]; sp_dj
  | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_mul, ?w_add by lia; rewrite ?u64_of_Z by lia; lia
  | evs; unfold wz; rewrite ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia] ].

Ltac sp_munch Hlf :=
  apply munch_mem_denot; [exact Hlf|];
  repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_mul, ?w_add by lia;
                              rewrite ?u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]);
  apply Forall_nil.

Ltac sp_exists E Hlf Hms :=
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ ?R' _ ?mm _) =>
      change mm with (mem_denot E m0 lg) in Hms; exists R', (mem_denot E m0 lg) end end.

Definition sp_sr0 : list expr := srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34)].
Definition sp_kc : list kentry :=
  [ KWr (SA (EVar 34) (-64)) (ELit 64); KWr (SA (EVar 32) 0) (ELit 24);
    KRange (EVar 34) (2 ^ 45 + 64) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 33) 0 255;
    KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 34) (-64)) (ELit 64) ].

Lemma sp_kc_ok : forall E m (p c spz lo : Z),
  ev E 32 = wz p -> ev E 33 = wz c -> ev E 34 = wz spz ->
  wr_at asegs m p 24 -> stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
  0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> (p + 24 <= spz - 64 \/ spz <= p) -> 0 <= c <= 255 ->
  know_ok asegs E m sp_kc.
Proof.
  intros E m p c spz lo E32 E33 E34 WP ST LO SPL SPH PL PH PD CR.
  unfold sp_kc, know_ok.
  apply Forall_cons.
  { eapply kwr_of_stk; [exact ST | unfold estart; cbn [edenot a_base a_off]; rewrite E34; unfold wz; rewrite u64_of_Z by lia; lia
                       | unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite E34; unfold wz; rewrite !u64_of_Z by lia; lia
                       | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; lia]. }
  apply Forall_cons.
  { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [edenot a_base a_off]; rewrite E32; unfold wz; rewrite u64_of_Z by lia; lia
                         | unfold estart, elenZ; cbn [a_base a_off edenot]; rewrite E32; unfold wz; rewrite !u64_of_Z by lia; lia
                         | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; lia]. }
  apply Forall_cons; [cbn [kentry_ok edenot]; rewrite E34; unfold wz; rewrite u64_of_Z by lia; lia|].
  apply Forall_cons; [cbn [kentry_ok edenot]; rewrite E32; unfold wz; rewrite u64_of_Z by lia; lia|].
  apply Forall_cons; [cbn [kentry_ok edenot]; rewrite E33; unfold wz; rewrite u64_of_Z by lia; lia|].
  apply Forall_cons; [|apply Forall_nil].
  cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off edenot]. rewrite E32, E34. unfold wz. rewrite !u64_of_Z by lia. lia.
Qed.

Definition sp_knS : list kentry := KWord (SA (EVar 32) 0) 1 (EMd M_MUL (ELit 2) (EVar 35)) :: KRange (EVar 35) 0 21 :: sp_kc.
Definition sp_xS := sym_exec asegs 200 true [] (SCR [] [] []) (SS SPB_ENTRY sp_sr0 [] sp_knS 40) [].
Definition sp_ssS : sym_state := Eval vm_compute in fst (fst sp_xS).
Definition sp_scsS : list sidecond := Eval vm_compute in snd (fst sp_xS).
Lemma sp_xS_eq : sp_xS = (sp_ssS, sp_scsS, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_BS : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p c size spz lo : Z),
    getr R 10 = wz p -> getr R 11 = wz c -> getr R 2 = wz spz ->
    fldA m p 1 (2 * size) -> 0 <= size <= 21 -> 0 <= c <= 255 ->
    wr_at asegs m p 24 -> stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> (p + 24 <= spz - 64 \/ spz <= p) ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz SPB_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz SPB_RET) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz); (p, p + 1); (p + 1 + size, p + 3 + size)] m M1 /\ wmono asegs m M1
      /\ (forall x, m x <> None -> M1 x <> None)
      /\ fldA M1 p 1 (2 * size + 2) /\ fldA M1 (p + 1 + size) 1 c /\ fldA M1 (p + 2 + size) 1 0
      /\ (forall r, In r SPBK -> getr R' r = getr R r).

Lemma spb_BS_ok : spb_BS.
Proof.
  intros R F fc m p c size spz lo H10 H11 H2 F0 SZ CR WP ST LO SPL SPH PL PH PD.
  set (E := Eseed R [wz p; wz c; wz spz; wz size]).
  assert (HR : regs_ok E sp_sr0 R) by (unfold sp_sr0; v4_seed).
  assert (HK : know_ok asegs E m sp_knS).
  { unfold sp_knS, know_ok.
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 1%nat p); [exact F0 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | cbn; lia
        | evs; unfold wz; rewrite w_mul by lia; reflexivity]. }
    apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
    exact (sp_kc_ok E m p c spz lo ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) WP ST LO SPL SPH PL PH PD CR). }
  assert (HS : scs_denot asegs m E sp_scsS) by (unfold sp_scsS, scs_denot; apply Forall_nil).
  pose proof sp_xS_eq as EQ. unfold sp_xS in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ssS.
  sp_exists E Hlf Hms.
  split; [exact Hms|]. split; [sp_munch Hlf|]. split; [apply wmono_mem_denot|]. split; [apply dmono_mem_denot|].
  split; [sp_fld Hlf 2%nat|]. split; [sp_fld Hlf 1%nat|]. split; [sp_fld Hlf 0%nat|].
  intros r Hr. eapply (syms_same_sound E _ R _ R' SPBK HR HR'); [vm_compute; reflexivity | exact Hr].
Qed.

Definition sp_knL : list kentry :=
  KWord (SA (EVar 32) 0) 1 (EAlu ALU_ADD (EVar 35) (ELit 1)) :: KWord (SA (EVar 32) 0) 8 (EAlu ALU_ADD (EVar 35) (ELit 1)) ::
  KWord (SA (EVar 32) 8) 8 (EVar 36) :: KWord (SA (EVar 32) 16) 8 (EVar 37) ::
  KRange (EVar 35) 48 (2 ^ 28) :: KRange (EVar 36) 0 (2 ^ 28) :: KRange (EVar 37) 0x6e8000 (2 ^ 47) ::
  KWr (SA (EAlu ALU_ADD (EVar 36) (EVar 37)) 0) (ELit 2) ::
  KDisj (SA (EAlu ALU_ADD (EVar 36) (EVar 37)) 0) (ELit 2) (SA (EVar 34) (-64)) (ELit 64) ::
  KDisj (SA (EAlu ALU_ADD (EVar 36) (EVar 37)) 0) (ELit 2) (SA (EVar 32) 0) (ELit 24) :: sp_kc.
Definition sp_xL := sym_exec asegs 200 true [] (SCR [true; true] [] []) (SS SPB_ENTRY sp_sr0 [] sp_knL 40) [].
Definition sp_ssL : sym_state := Eval vm_compute in fst (fst sp_xL).
Definition sp_scsL : list sidecond := Eval vm_compute in snd (fst sp_xL).
Lemma sp_xL_eq : sp_xL = (sp_ssL, sp_scsL, SCR [] [] []). Proof. vmeq. Qed.

Lemma w_srl1 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 1) = Z_to_bv 64 (x / 2).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu]. rewrite bv_shiftr_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x) by lia.
  replace (bv_unsigned (bv_and (Z_to_bv 64 1) (Z_to_bv 64 63))) with 1 by (vm_compute; reflexivity).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma ext_lbu : forall x, 0 <= x < 2 ^ 64 -> ext_val false 0 1 (Z_to_bv 64 x) = Z_to_bv 64 (x mod 256).
Proof.
  intros x Hx. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  change (8 * Z.of_nat 1) with 8. change (2 ^ 8) with 256. reflexivity.
Qed.

Lemma sp_half : forall asz, 0 <= asz -> asz mod 8 = 0 -> (asz + 1) / 2 = 4 * (asz / 8) /\ asz = 8 * (asz / 8).
Proof. intros asz H0 Hm. split; Z.div_mod_to_equations; lia. Qed.

Lemma sp_asz_w : forall asz, 48 <= asz <= 2 ^ 28 -> asz mod 8 = 0 ->
  mul_div M_MUL (Z_to_bv 64 2) (alu64 ALU_SRL (alu64 ALU_ADD (Z_to_bv 64 asz) (Z_to_bv 64 1)) (Z_to_bv 64 1)) = Z_to_bv 64 asz.
Proof.
  intros asz HA Hm. destruct (sp_half asz ltac:(lia) Hm) as [E1 E2]. set (k := asz / 8) in *.
  rewrite w_add, w_srl1, E1, w_mul by lia. f_equal. lia.
Qed.

Lemma sp_cap_w : forall asz, 48 <= asz <= 2 ^ 28 -> asz mod 8 = 0 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 2) (alu64 ALU_SRL (alu64 ALU_ADD (Z_to_bv 64 asz) (Z_to_bv 64 1)) (Z_to_bv 64 1)))
        (Z_to_bv 64 (-1)) = Z_to_bv 64 (asz - 1).
Proof. intros asz HA Hm. rewrite sp_asz_w by lia. rewrite w_addm by lia. reflexivity. Qed.

Lemma sp_new_w : forall asz, 48 <= asz <= 2 ^ 28 -> asz mod 8 = 0 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 8)
    (alu64 ALU_SRL (alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 4)
                                     (alu64 ALU_SRL (alu64 ALU_ADD (Z_to_bv 64 asz) (Z_to_bv 64 1)) (Z_to_bv 64 1)))
                                  (Z_to_bv 64 (-2))) (Z_to_bv 64 3))) (Z_to_bv 64 8) = Z_to_bv 64 (2 * asz).
Proof.
  intros asz HA Hm. destruct (sp_half asz ltac:(lia) Hm) as [E1 E2]. set (k := asz / 8) in *.
  rewrite w_add, w_srl1, E1, w_mul by lia. rewrite w_addm by lia. rewrite srl3_v by lia.
  assert (E3 : (4 * (4 * k) + -2) / 8 = 2 * k - 1) by (Z.div_mod_to_equations; lia).
  rewrite E3, w_mul, w_add by lia. f_equal. lia.
Qed.

Lemma sp_odd_w : forall asz, 48 <= asz <= 2 ^ 28 -> asz mod 8 = 0 ->
  alu64 ALU_AND (ext_val false 0 1 (alu64 ALU_ADD (Z_to_bv 64 asz) (Z_to_bv 64 1))) (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof.
  intros asz HA Hm. rewrite w_add, ext_lbu by lia. pose proof (Z.mod_pos_bound (asz + 1) 256 ltac:(lia)).
  rewrite w_and by lia. rewrite odd_byte0 by lia. reflexivity.
Qed.

Ltac sp_scL :=
  cbn [sc_denot]; evs; unfold wz in *;
  rewrite ?sp_cap_w, ?sp_odd_w by lia; rewrite ?w_addm by lia; rewrite ?br_ne, ?br_eq by lia; bool_lia.

Definition spb_BL : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p c asz size d spz lo : Z),
    getr R 10 = wz p -> getr R 11 = wz c -> getr R 2 = wz spz ->
    fldA m p 8 (asz + 1) -> fldA m (p + 8) 8 size -> fldA m (p + 16) 8 d ->
    asz mod 8 = 0 -> 48 <= asz <= 2 ^ 28 -> 0 <= size < asz - 1 -> 0 <= c <= 255 ->
    0x6e8000 <= d -> d + asz <= 2 ^ 47 -> wr_at asegs m (d + size) 2 ->
    (d + size + 2 <= spz - 64 \/ spz <= d + size) -> (d + size + 2 <= p \/ p + 24 <= d + size) ->
    wr_at asegs m p 24 -> stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> (p + 24 <= spz - 64 \/ spz <= p) ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz SPB_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz SPB_RET) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz); (p + 8, p + 16); (d + size, d + size + 2)] m M1 /\ wmono asegs m M1
      /\ (forall x, m x <> None -> M1 x <> None)
      /\ fldA M1 (p + 8) 8 (size + 1) /\ fldA M1 (d + size) 1 c /\ fldA M1 (d + size + 1) 1 0
      /\ (forall r, In r SPBK -> getr R' r = getr R r).

Lemma fldA8_byte0 : forall m a v, fldA m a 8 v -> fldA m a 1 v.
Proof.
  intros m a v H. unfold fldA, fld in *. pose proof (fld8_byte0 asegs m a v H) as K.
  rewrite w1_bytes. exact K.
Qed.

Lemma spb_BL_ok : spb_BL.
Proof.
  intros R F fc m p c asz size d spz lo H10 H11 H2 F0 F8 F16 AM AR SZ CR DL DH WD DJ1 DJ2 WP ST LO SPL SPH PL PH PD.
  set (E := Eseed R [wz p; wz c; wz spz; wz asz; wz size; wz d]).
  assert (HR : regs_ok E sp_sr0 R) by (unfold sp_sr0; v4_seed).
  assert (HK : know_ok asegs E m sp_knL).
  { unfold sp_knL, know_ok.
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 1%nat p); [exact (fldA8_byte0 _ _ _ F0) | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; unfold wz; rewrite w_add by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat p); [exact F0 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; unfold wz; rewrite w_add by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat (p + 8)); [exact F8 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat (p + 16)); [exact F16 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; reflexivity]. }
    do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WD | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite w_add by lia; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; evs; unfold wz; rewrite w_add by lia; rewrite !u64_of_Z by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; lia]. }
    do 2 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_add by lia;
                              rewrite !u64_of_Z by lia; lia|]).
    exact (sp_kc_ok E m p c spz lo ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) WP ST LO SPL SPH PL PH PD CR). }
  assert (HS : scs_denot asegs m E sp_scsL).
  { unfold sp_scsL, scs_denot. repeat (apply Forall_cons; [sp_scL|]). apply Forall_nil. }
  pose proof sp_xL_eq as EQ. unfold sp_xL in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ssL.
  sp_exists E Hlf Hms.
  split; [exact Hms|]. split; [sp_munch Hlf|]. split; [apply wmono_mem_denot|]. split; [apply dmono_mem_denot|].
  split; [sp_fld Hlf 2%nat|]. split; [sp_fld Hlf 1%nat|]. split; [sp_fld Hlf 0%nat|].
  intros r Hr. eapply (syms_same_sound E _ R _ R' SPBK HR HR'); [vm_compute; reflexivity | exact Hr].
Qed.

Definition SPBKG : list reg := [3; 4; 22; 23; 24; 25; 26; 27]%bv.

Ltac sp_frame E Hlf :=
  lazymatch goal with |- rw_cells _ (mem_denot _ _ ?lg) _ _ =>
    change lg with (v4_c8log (EVar 34) (-64) [EVar 22; EVar 21; EVar 20; EVar 19; EVar 18; EVar 9; EVar 8; EVar 1]);
    eapply rw_cells_mem_eq_list;
    [ apply v4_rw_cells_c8log;
      [ exact Hlf | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off a_base]; lia
      | cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; eapply wr_at_of_stk_win; [eassumption | lia | lia] ]
    | reflexivity ] end.

Ltac sp_frame_munch E Hlf :=
  lazymatch goal with |- munch _ ?m0 (mem_denot _ _ _) =>
    let MU := fresh "MU" in
    pose proof (munch_mem_denot_sb [(-64, 0)] (EVar 34) E m0 _ Hlf ltac:(vm_cast_no_check (@eq_refl bool true))) as MU;
    eapply v4_munch_eqW; [exact MU | cbn [map fst snd]; evs; rewrite u64_of_Z by lia; repeat f_equal; lia] end.

Definition sp_knGS : list kentry := KWord (SA (EVar 32) 0) 1 (ELit 44) :: sp_kc.
Definition sp_xGS := sym_exec asegs 200 true [AOPNEW] (SCR [] [] []) (SS SPB_ENTRY sp_sr0 [] sp_knGS 40) [].
Definition sp_ssGS : sym_state := Eval vm_compute in fst (fst sp_xGS).
Definition sp_scsGS : list sidecond := Eval vm_compute in snd (fst sp_xGS).
Lemma sp_xGS_eq : sp_xGS = (sp_ssGS, sp_scsGS, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_BGS : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p c spz lo : Z),
    getr R 10 = wz p -> getr R 11 = wz c -> getr R 2 = wz spz ->
    fldA m p 1 44 -> 0 <= c <= 255 ->
    wr_at asegs m p 24 -> stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> (p + 24 <= spz - 64 \/ spz <= p) ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz SPB_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz AOPNEW) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 64) (map (fun r => C8 (getr R r)) SPBSAVED)
      /\ getr R' 1 = wz 0x1200c4 /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz c /\ getr R' 9 = wz p /\ getr R' 10 = wz 48
      /\ getr R' 18 = wz (p + 1) /\ getr R' 19 = wz 48 /\ getr R' 20 = wz 22 /\ getr R' 21 = wz 23
      /\ (forall r, In r SPBKG -> getr R' r = getr R r).

Lemma spb_BGS_ok : spb_BGS.
Proof.
  intros R F fc m p c spz lo H10 H11 H2 F0 CR WP ST LO SPL SPH PL PH PD.
  set (E := Eseed R [wz p; wz c; wz spz]).
  assert (HR : regs_ok E sp_sr0 R) by (unfold sp_sr0; v4_seed).
  assert (HK : know_ok asegs E m sp_knGS).
  { unfold sp_knGS, know_ok.
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 1%nat p); [exact F0 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia | lia | cbn; lia
        | reflexivity]. }
    exact (sp_kc_ok E m p c spz lo ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) WP ST LO SPL SPH PL PH PD CR). }
  assert (HS : scs_denot asegs m E sp_scsGS) by (unfold sp_scsGS, scs_denot; apply Forall_nil).
  pose proof sp_xGS_eq as EQ. unfold sp_xGS in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ssGS.
  sp_exists E Hlf Hms.
  split; [exact Hms|].
  split; [sp_frame_munch E Hlf|]. split; [apply wmono_mem_denot|]. split; [sp_frame E Hlf|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' SPBKG HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; try reflexivity; wsolve end.
Qed.

Definition sp_knGL : list kentry :=
  KWord (SA (EVar 32) 0) 1 (EAlu ALU_ADD (EVar 35) (ELit 1)) :: KWord (SA (EVar 32) 0) 8 (EAlu ALU_ADD (EVar 35) (ELit 1)) ::
  KWord (SA (EVar 32) 8) 8 (EAlu ALU_ADD (EVar 35) (ELit (-1))) :: KWord (SA (EVar 32) 16) 8 (EVar 36) ::
  KRange (EVar 35) 48 (2 ^ 28) :: KRange (EVar 36) 0x6e8000 (2 ^ 47) :: sp_kc.
Definition sp_xGL := sym_exec asegs 200 true [AOPNEW] (SCR [true; false] [] []) (SS SPB_ENTRY sp_sr0 [] sp_knGL 40) [].
Definition sp_ssGL : sym_state := Eval vm_compute in fst (fst sp_xGL).
Definition sp_scsGL : list sidecond := Eval vm_compute in snd (fst sp_xGL).
Lemma sp_xGL_eq : sp_xGL = (sp_ssGL, sp_scsGL, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_BGL : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p c asz d spz lo : Z),
    getr R 10 = wz p -> getr R 11 = wz c -> getr R 2 = wz spz ->
    fldA m p 8 (asz + 1) -> fldA m (p + 8) 8 (asz - 1) -> fldA m (p + 16) 8 d ->
    asz mod 8 = 0 -> 48 <= asz <= 2 ^ 28 -> 0 <= c <= 255 -> 0x6e8000 <= d -> d + asz <= 2 ^ 47 ->
    wr_at asegs m p 24 -> stk asegs m lo spz -> lo <= spz - 64 -> 2 ^ 45 + 64 <= spz -> spz <= 2 ^ 47 ->
    0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> (p + 24 <= spz - 64 \/ spz <= p) ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz SPB_ENTRY) fc None m (seg_rom asegs)) (MS R' F (wz AOPNEW) fc None M1 (seg_rom asegs))
      /\ munch [(spz - 64, spz)] m M1 /\ wmono asegs m M1
      /\ rw_cells asegs M1 (spz - 64) (map (fun r => C8 (getr R r)) SPBSAVED)
      /\ getr R' 1 = wz 0x1200c4 /\ getr R' 2 = wz (spz - 64) /\ getr R' 8 = wz c /\ getr R' 9 = wz p /\ getr R' 10 = wz (2 * asz)
      /\ getr R' 18 = wz d /\ getr R' 19 = wz (2 * asz) /\ getr R' 20 = wz (asz - 1) /\ getr R' 21 = wz asz
      /\ (forall r, In r SPBKG -> getr R' r = getr R r).

Ltac sp_wsolveL :=
  unfold wz; rewrite ?sp_new_w, ?sp_cap_w, ?sp_asz_w by lia;
  repeat (first [ rewrite w_add by lia | rewrite w_addm by lia ]);
  first [ reflexivity | f_equal; lia ].

Lemma spb_BGL_ok : spb_BGL.
Proof.
  intros R F fc m p c asz d spz lo H10 H11 H2 F0 F8 F16 AM AR CR DL DH WP ST LO SPL SPH PL PH PD.
  set (E := Eseed R [wz p; wz c; wz spz; wz asz; wz d]).
  assert (HR : regs_ok E sp_sr0 R) by (unfold sp_sr0; v4_seed).
  assert (HK : know_ok asegs E m sp_knGL).
  { unfold sp_knGL, know_ok.
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 1%nat p); [exact (fldA8_byte0 _ _ _ F0) | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; unfold wz; rewrite w_add by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat p); [exact F0 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; unfold wz; rewrite w_add by lia; reflexivity]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat (p + 8)); [exact F8 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; unfold wz; rewrite w_addm by lia; f_equal; lia]. }
    apply Forall_cons.
    { eapply (kword_of_fldA E m _ _ 8%nat (p + 16)); [exact F16 | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
        | lia | cbn; lia | evs; reflexivity]. }
    do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    exact (sp_kc_ok E m p c spz lo ltac:(evs; reflexivity) ltac:(evs; reflexivity) ltac:(evs; reflexivity) WP ST LO SPL SPH PL PH PD CR). }
  assert (HS : scs_denot asegs m E sp_scsGL).
  { unfold sp_scsGL, scs_denot. repeat (apply Forall_cons; [sp_scL|]). apply Forall_nil. }
  pose proof sp_xGL_eq as EQ. unfold sp_xGL in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ssGL.
  sp_exists E Hlf Hms.
  split; [exact Hms|].
  split; [sp_frame_munch E Hlf|]. split; [apply wmono_mem_denot|]. split; [sp_frame E Hlf|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' SPBKG HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; try reflexivity; sp_wsolveL end.
Qed.

Definition SPBK2 : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27]%bv.
Definition sp_x2 := sym_exec asegs 200 true [AMEMMOVE_STUB] (SCR [] [] []) (SS 0x1200c4 sr_id [] [] 40) [].
Definition sp_ss2 : sym_state := Eval vm_compute in fst (fst sp_x2).
Definition sp_scs2 : list sidecond := Eval vm_compute in snd (fst sp_x2).
Lemma sp_x2_eq : sp_x2 = (sp_ss2, sp_scs2, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_B2 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem),
    exists R',
      CatSim.msteps asegs (MS R F (wz 0x1200c4) fc None m (seg_rom asegs)) (MS R' F (wz AMEMMOVE_STUB) fc None m (seg_rom asegs))
      /\ getr R' 1 = wz 0x1200d4 /\ getr R' 10 = getr R 10 /\ getr R' 11 = getr R 18 /\ getr R' 12 = getr R 20
      /\ getr R' 22 = getr R 10 /\ (forall r, In r SPBK2 -> getr R' r = getr R r).

Lemma spb_B2_ok : spb_B2.
Proof.
  intros R F fc m.
  set (E := Eseed R []).
  assert (HR : regs_ok E sr_id R) by apply regs_ok_seed.
  assert (HK : know_ok asegs E m []) by apply Forall_nil.
  assert (HS : scs_denot asegs m E sp_scs2) by (unfold sp_scs2, scs_denot; apply Forall_nil).
  pose proof sp_x2_eq as EQ. unfold sp_x2 in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ss2.
  lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
  exists R'. split; [exact Hms|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' SPBK2 HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; reflexivity end.
Qed.

Definition SPBK3 : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition sp_x3S := sym_exec asegs 200 true [0x1200e8] (SCR [] [] []) (SS 0x1200d4 (srs sr_id [(21%bv, ELit 23)]) [] [] 40) [].
Definition sp_ss3S : sym_state := Eval vm_compute in fst (fst sp_x3S).
Definition sp_scs3S : list sidecond := Eval vm_compute in snd (fst sp_x3S).
Lemma sp_x3S_eq : sp_x3S = (sp_ss3S, sp_scs3S, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_B3S : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem),
    getr R 21 = wz 23 ->
    exists R',
      CatSim.msteps asegs (MS R F (wz 0x1200d4) fc None m (seg_rom asegs)) (MS R' F (wz 0x1200e8) fc None m (seg_rom asegs))
      /\ (forall r, In r SPBK3 -> getr R' r = getr R r).

Lemma spb_B3S_ok : spb_B3S.
Proof.
  intros R F fc m H21.
  set (E := Eseed R []).
  assert (HR : regs_ok E (srs sr_id [(21%bv, ELit 23)]) R) by v4_seed.
  assert (HK : know_ok asegs E m []) by apply Forall_nil.
  assert (HS : scs_denot asegs m E sp_scs3S) by (unfold sp_scs3S, scs_denot; apply Forall_nil).
  pose proof sp_x3S_eq as EQ. unfold sp_x3S in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ss3S.
  lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
  exists R'. split; [exact Hms|].
  intros r Hr. eapply (syms_same_sound E _ R _ R' SPBK3 HR HR'); [vm_compute; reflexivity | exact Hr].
Qed.

Definition SPBK3L : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition sp_x3L := sym_exec asegs 200 true [AOPDEL2] (SCR [] [] []) (SS 0x1200d4 (srs sr_id [(21%bv, EVar 32)]) [] [KRange (EVar 32) 48 (2 ^ 29)] 40) [].
Definition sp_ss3L : sym_state := Eval vm_compute in fst (fst sp_x3L).
Definition sp_scs3L : list sidecond := Eval vm_compute in snd (fst sp_x3L).
Lemma sp_x3L_eq : sp_x3L = (sp_ss3L, sp_scs3L, SCR [] [] []). Proof. vmeq. Qed.

Definition spb_B3L : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (asz : Z),
    getr R 21 = wz asz -> 48 <= asz <= 2 ^ 29 ->
    exists R',
      CatSim.msteps asegs (MS R F (wz 0x1200d4) fc None m (seg_rom asegs)) (MS R' F (wz AOPDEL2) fc None m (seg_rom asegs))
      /\ getr R' 1 = wz 0x1200e8 /\ getr R' 10 = getr R 18 /\ getr R' 11 = wz asz
      /\ (forall r, In r SPBK3L -> getr R' r = getr R r).

Lemma spb_B3L_ok : spb_B3L.
Proof.
  intros R F fc m asz H21 AR.
  set (E := Eseed R [wz asz]).
  assert (HR : regs_ok E (srs sr_id [(21%bv, EVar 32)]) R) by v4_seed.
  assert (HK : know_ok asegs E m [KRange (EVar 32) 48 (2 ^ 29)]).
  { apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
  assert (HS : scs_denot asegs m E sp_scs3L) by (unfold sp_scs3L, scs_denot; apply Forall_nil).
  pose proof sp_x3L_eq as EQ. unfold sp_x3L in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ss3L.
  lazymatch type of Hms with CatSim.msteps _ (@PropExec.mkst _ _ _ ?m0 _) (@PropExec.mkst _ _ _ ?mm _) => change mm with m0 in Hms end.
  exists R'. split; [exact Hms|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' SPBK3L HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; reflexivity end.
Qed.

Definition SPBK4 : list reg := [3; 4; 23; 24; 25; 26; 27]%bv.
Definition sp_sr4 : list expr := srs sr_id [(9%bv, EVar 32); (19%bv, EVar 33); (22%bv, EVar 34); (20%bv, EVar 35); (8%bv, EVar 36); (2%bv, EVar 37)].
Definition sp_kn4 : list kentry :=
  [ KWr (SA (EVar 32) 0) (ELit 24); KWr (SA (EAlu ALU_ADD (EVar 34) (EVar 35)) 0) (ELit 2);
    KWord (SA (EVar 37) 0) 8 (EVar 40); KWord (SA (EVar 37) 8) 8 (EVar 41); KWord (SA (EVar 37) 16) 8 (EVar 42);
    KWord (SA (EVar 37) 24) 8 (EVar 43); KWord (SA (EVar 37) 32) 8 (EVar 44); KWord (SA (EVar 37) 40) 8 (EVar 45);
    KWord (SA (EVar 37) 48) 8 (EVar 46); KWord (SA (EVar 37) 56) 8 (EVar 47);
    KRange (EVar 37) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47);
    KRange (EVar 33) 48 (2 ^ 29); KRange (EVar 35) 0 (2 ^ 29); KRange (EVar 36) 0 255;
    KDisj (SA (EVar 32) 0) (ELit 24) (SA (EVar 37) 0) (ELit 64);
    KDisj (SA (EAlu ALU_ADD (EVar 34) (EVar 35)) 0) (ELit 2) (SA (EVar 37) 0) (ELit 64);
    KDisj (SA (EAlu ALU_ADD (EVar 34) (EVar 35)) 0) (ELit 2) (SA (EVar 32) 0) (ELit 24) ].
Definition sp_x4 := sym_exec asegs 200 true [] (SCR [] [] []) (SS 0x1200e8 sp_sr4 [] sp_kn4 50) [].
Definition sp_ss4 : sym_state := Eval vm_compute in fst (fst sp_x4).
Definition sp_scs4 : list sidecond := Eval vm_compute in snd (fst sp_x4).
Lemma sp_x4_eq : sp_x4 = (sp_ss4, sp_scs4, SCR [] [] []). Proof. vmeq. Qed.

Lemma sp_or1_w : forall a, 0 <= a < 2 ^ 60 -> a mod 2 = 0 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 2) (alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 1))) (Z_to_bv 64 1) = Z_to_bv 64 (a + 1).
Proof.
  intros a Ha He. assert (E2 : 2 * (a / 2) = a) by (Z.div_mod_to_equations; lia).
  assert (B2 : 0 <= a / 2 < 2 ^ 59) by (Z.div_mod_to_equations; lia).
  rewrite w_srl1, w_mul by lia. rewrite E2. rewrite w_add by lia. reflexivity.
Qed.

Definition spb_B4 : Prop :=
  forall (R F : bvmap 5 word) (fc : bv 32) (m : mem) (p asz A size c spz : Z) (x22 x21 x20 x19 x18 x9 x8 x1 : word),
    getr R 9 = wz p -> getr R 19 = wz asz -> getr R 22 = wz A -> getr R 20 = wz size -> getr R 8 = wz c -> getr R 2 = wz (spz - 64) ->
    rw_cells asegs m (spz - 64) (map (fun w => C8 w) [x22; x21; x20; x19; x18; x9; x8; x1]) ->
    wr_at asegs m p 24 -> wr_at asegs m (A + size) 2 ->
    (p + 24 <= spz - 64 \/ spz <= p) -> (A + size + 2 <= spz - 64 \/ spz <= A + size) -> (A + size + 2 <= p \/ p + 24 <= A + size) ->
    2 ^ 45 <= spz - 64 -> spz <= 2 ^ 47 -> 0x6e8000 <= p -> p + 24 <= 2 ^ 47 -> 0x6e8000 <= A -> A + asz <= 2 ^ 47 ->
    asz mod 2 = 0 -> 48 <= asz <= 2 ^ 29 -> 0 <= size -> size + 2 <= asz -> 0 <= c <= 255 ->
    exists R' M1,
      CatSim.msteps asegs (MS R F (wz 0x1200e8) fc None m (seg_rom asegs)) (MS R' F (wz SPB_RET) fc None M1 (seg_rom asegs))
      /\ munch [(p, p + 24); (A + size, A + size + 2)] m M1 /\ wmono asegs m M1
      /\ (forall x, m x <> None -> M1 x <> None)
      /\ fldA M1 p 8 (asz + 1) /\ fldA M1 (p + 8) 8 (size + 1) /\ fldA M1 (p + 16) 8 A
      /\ fldA M1 (A + size) 1 c /\ fldA M1 (A + size + 1) 1 0
      /\ getr R' 1 = x1 /\ getr R' 2 = wz spz /\ getr R' 8 = x8 /\ getr R' 9 = x9 /\ getr R' 18 = x18 /\ getr R' 19 = x19
      /\ getr R' 20 = x20 /\ getr R' 21 = x21 /\ getr R' 22 = x22
      /\ (forall r, In r SPBK4 -> getr R' r = getr R r).

Lemma spb_B4_ok : spb_B4.
Proof.
  intros R F fc m p asz A size c spz x22 x21 x20 x19 x18 x9 x8 x1 H9 H19 H22 H20 H8 H2 CF WP WD D1 D2 D3 SPL SPH PL PH AL AH AE AR S0 SA CR.
  set (E := Eseed R [wz p; wz asz; wz A; wz size; wz c; wz (spz - 64); wz 0; wz 0; x22; x21; x20; x19; x18; x9; x8; x1]).
  assert (HR : regs_ok E sp_sr4 R) by (unfold sp_sr4; v4_seed).
  assert (HK : know_ok asegs E m sp_kn4).
  { unfold sp_kn4, know_ok. cbn [map] in CF.
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WP | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; evs; unfold wz; rewrite !u64_of_Z by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_wr_at; [exact WD | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite w_add by lia; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; evs; unfold wz; rewrite w_add by lia; rewrite !u64_of_Z by lia; lia
                           | unfold elenZ; cbn [edenot]; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [kword_cell CF 0%nat (C8 x22)|]. apply Forall_cons; [kword_cell CF 8%nat (C8 x21)|].
    apply Forall_cons; [kword_cell CF 16%nat (C8 x20)|]. apply Forall_cons; [kword_cell CF 24%nat (C8 x19)|].
    apply Forall_cons; [kword_cell CF 32%nat (C8 x18)|]. apply Forall_cons; [kword_cell CF 40%nat (C8 x9)|].
    apply Forall_cons; [kword_cell CF 48%nat (C8 x8)|]. apply Forall_cons; [kword_cell CF 56%nat (C8 x1)|].
    do 6 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
    do 3 (apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; evs; unfold wz; rewrite ?w_add by lia;
                              rewrite !u64_of_Z by lia; lia|]).
    apply Forall_nil. }
  assert (HS : scs_denot asegs m E sp_scs4) by (unfold sp_scs4, scs_denot; apply Forall_nil).
  pose proof sp_x4_eq as EQ. unfold sp_x4 in EQ.
  v4_run (PropExec.mkFP F fc) EQ HR HK HS sp_ss4.
  sp_exists E Hlf Hms.
  split; [exact Hms|]. split; [sp_munch Hlf|]. split; [apply wmono_mem_denot|]. split; [apply dmono_mem_denot|].
  split.
  { eapply (fldA_log_nth _ _ _ 4%nat);
    [ exact Hlf | reflexivity | cbn [firstn]; sp_dj
    | unfold estart; cbn [a_base a_off]; evs; unfold wz; rewrite ?u64_of_Z by lia; lia
    | evs; unfold wz; rewrite sp_or1_w by lia; reflexivity ]. }
  split; [sp_fld Hlf 2%nat|]. split; [sp_fld Hlf 3%nat|]. split; [sp_fld Hlf 1%nat|]. split; [sp_fld Hlf 0%nat|].
  repeat match goal with |- _ /\ _ => split end.
  all: try (intros r Hr; eapply (syms_same_sound E _ R _ R' SPBK4 HR HR'); [vm_compute; reflexivity | exact Hr]).
  all: lazymatch goal with |- getr _ ?r = _ => rrw HR' r; evs; try reflexivity; unfold wz; rewrite w_add by lia; f_equal; lia end.
Qed.

Lemma sp_ret_ok : v4_ret_ok SPB_RET.
Proof.
  intros Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m HQ.
  step. apply evt_done. exact HQ.
Qed.
