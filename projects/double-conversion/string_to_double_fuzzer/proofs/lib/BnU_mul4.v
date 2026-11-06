(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition frame_cells (m : word -> option byte) (sp : Z) (ret s0v s1v s2v s3v s4v s5v : word) : Prop :=
  cellN SEGS_U m (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_U m (sp - 16) 8 (bv_unsigned s0v) /\
  cellN SEGS_U m (sp - 24) 8 (bv_unsigned s1v) /\ cellN SEGS_U m (sp - 32) 8 (bv_unsigned s2v) /\
  cellN SEGS_U m (sp - 40) 8 (bv_unsigned s3v) /\ cellN SEGS_U m (sp - 48) 8 (bv_unsigned s4v) /\
  cellN SEGS_U m (sp - 56) 8 (bv_unsigned s5v).

Lemma frame_cells_unch : forall m m' sp ret s0v s1v s2v s3v s4v s5v rs,
  unch m m' rs -> 64 <= sp -> sp <= 2 ^ 62 -> (forall r, In r rs -> sp <= fst r \/ snd r <= sp - 64) ->
  frame_cells m sp ret s0v s1v s2v s3v s4v s5v -> frame_cells m' sp ret s0v s1v s2v s3v s4v s5v.
Proof.
  intros m m' sp ret s0v s1v s2v s3v s4v s5v rs U Hsp1 Hsp2 Hd (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  repeat split;
    (eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; specialize (Hd rg Hrg); cbn; zwidth; lia | assumption]).
Qed.

Definition s_restored (regs' : bvmap 5 word) (s0v s1v s2v s3v s4v s5v : word) : Prop :=
  getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v /\ getr regs' 19%bv = s3v
  /\ getr regs' 20%bv = s4v /\ getr regs' 21%bv = s5v.


Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fin_keep : list Z := [3; 4; 10; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma fin_U : forall regs m (o e sp : Z) (ret s0v s1v s2v s3v s4v s5v : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 (zlen (cells b)) ->
  getr regs 13%bv = Z_to_bv 64 MASK -> getr regs 2%bv = Z_to_bv 64 (sp - 64) ->
  frame_cells m sp ret s0v s1v s2v s3v s4v s5v -> ret_ok ret ->
  1 <= e < 2048 -> bn_at SEGS_U m o b -> ok (cells b) -> cells b <> [] -> zlen (cells b) <= 127 -> ex b + e / 28 < 2 ^ 15 ->
  64 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 64 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36280) m rom) (mkst regs' ret m' rom)
    /\ bn_at SEGS_U m' o (shl e b) /\ getr regs' 2%bv = Z_to_bv 64 sp /\ s_restored regs' s0v s1v s2v s3v s4v s5v
    /\ keeps fin_keep regs regs'
    /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret s0v s1v s2v s3v s4v s5v b R10 R11 R12 R13 R2 FC Hret He Hbn Hok Hne Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range s0v) as Hs0. pose proof (u64_range s1v) as Hs1. pose proof (u64_range s2v) as Hs2.
  pose proof (u64_range s3v) as Hs3. pose proof (u64_range s4v) as Hs4. pose proof (u64_range s5v) as Hs5.
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1)]) [KC (ZV 32) 2 2 (ZV 35)] (@nil kwin))
    40%nat [0x362ac] (SCR [] []) constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (11%bv : reg, ZV 34)])
    [o; u; e; ex b] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1)]) regs m rom 0x36280.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Ce; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (15%bv : reg) as A15. fold (magic28 e) in A15. rewrite (magic28_ok e) in A15 by lia.
  zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (16%bv : reg) as A16. zx_reg ZR (14%bv : reg) as A14. zx_reg ZR (10%bv : reg) as A10.
  zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (12%bv : reg) as A12.
  assert (A13 : getr regs1 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R13]).
  assert (A2 : getr regs1 2%bv = Z_to_bv 64 (sp - 64)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact R2]).
  assert (K1 : keeps fin_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73)]) (@nil kcell) [KW (ZV 32) 0 516])
    40%nat [0x362d0] (SCR [] [])
    constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (11%bv : reg, ZV 34); (17%bv : reg, ZV 35); (15%bv : reg, ZV 36); (16%bv : reg, ZV 33);
             (14%bv : reg, ZMul (ZV 33) (ZL 281474976710656))])
    [o; u; e; ex b; e / 28] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m rom 0x362ac.
  zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(exact I). zx_name regs2.
  zx_reg ZR (11%bv : reg) as B11. zx_reg ZR (5%bv : reg) as B5. zx_reg ZR (16%bv : reg) as B16. zx_reg ZR (14%bv : reg) as B14.
  zx_reg ZR (12%bv : reg) as B12. zx_reg ZR (10%bv : reg) as B10.
  assert (B13 : getr regs2 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact A13]).
  assert (B2 : getr regs2 2%bv = Z_to_bv 64 (sp - 64)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact A2]).
  set (m2 := wbytes m _ _) in ZM.
  assert (K2 : keeps fin_keep regs1 regs2) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2.
  assert (Hs : 0 <= e mod 28 < 28) by lia.
  (* [comment removed for export] *)
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)]) (@nil kcell) (@nil kwin))
    40%nat [0x362fc] (SCR [] [])
    constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (11%bv : reg, ZV 37); (16%bv : reg, ZV 33); (5%bv : reg, ZL 28);
             (14%bv : reg, ZMul (ZV 33) (ZL 281474976710656))])
    [o; u; e; ex b; e / 28; e mod 28] constr:([Some (0, 2 ^ 62); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)]) regs2 m2 rom 0x362d0.
  zx_use ZXB ltac:(zx_pins; rewrite B11; f_equal; lia) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs2'.
  zx_reg ZR (6%bv : reg) as D6. zx_reg ZR (16%bv : reg) as D16. zx_reg ZR (5%bv : reg) as D5. zx_reg ZR (11%bv : reg) as D11.
  zx_reg ZR (15%bv : reg) as D15. zx_reg ZR (12%bv : reg) as D12. zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (14%bv : reg) as D14.
  zx_reg ZR (17%bv : reg) as D17.
  assert (D13 : getr regs2' 13%bv = Z_to_bv 64 MASK) by (etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact B13]).
  assert (D2 : getr regs2' 2%bv = Z_to_bv 64 (sp - 64)) by (etransitivity; [exact (reg_kept _ _ _ _ (2%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact B2]).
  assert (K2' : keeps fin_keep regs2 regs2') by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2'.
  (* [comment removed for export] *)
  destruct (cells b) as [|x t] eqn:El; [congruence|]. cbn [length] in Hlen'.
  assert (Harr2 : arr32 SEGS_U m2 (o + 4) ([] ++ x :: t)).
  { cbn [app]. unfold m2. apply arr32_store_other; zwidth; try lia. exact Carr. }
  pose proof Hok as Hok0.
  destruct (mshl_loop_U rom (x :: t) [] 0 regs2' m2 (o + 4) (e mod 28)) as (regs3 & m3 & M3 & Harr3 & C5 & C16 & K3 & U3 & G3);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { rewrite D6; first [reflexivity | f_equal; lia]. }
  { rewrite D16, <- Hlen'; cbn [length]. f_equal. lia. }
  { exact D5. }
  { rewrite D11; first [reflexivity | f_equal; lia]. }
  { rewrite D15; first [reflexivity | f_equal; lia]. }
  { exact D13. }
  { exact Hs. }
  { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
  { exact Hok. }
  { congruence. }
  { lia. }
  { cbn [length] in Hlen'. lia. }
  { exact Harr2. }
  { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto]; unfold m2; growsx |]. cbn [length]. cbn [length] in Hlen'. lia. }
  cbn [length app] in Harr3, C16, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in C16, U3. rewrite Hlen' in C16, U3.
  pose proof (shl_l_spec (e mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
  destruct (shl_l (e mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C5.
  destruct SPEC as (_ & Hokr & Hlenr & Hc').
  assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (e mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
  assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; cbn [length] in Hlen'; lia).
  (* [comment removed for export] *)
  assert (C12 : getr regs3 12%bv = Z_to_bv 64 u) by (etransitivity; [exact (K3 12 ltac:(cbn; tauto)) | exact D12]).
  assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K3 10 ltac:(cbn; tauto)) | exact D10]).
  assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp - 64)) by (etransitivity; [exact (K3 2 ltac:(cbn; tauto)) | exact D2]).
  assert (C14 : getr regs3 14%bv = Z_to_bv 64 (u * 281474976710656)) by (etransitivity; [exact (K3 14 ltac:(cbn; tauto)) | exact D14]).
  assert (C17 : getr regs3 17%bv = Z_to_bv 64 (o + 4)) by (etransitivity; [exact (K3 17 ltac:(cbn; tauto)) | exact D17]).
  assert (FC2 : frame_cells m2 sp ret s0v s1v s2v s3v s4v s5v).
  { apply (frame_cells_unch m m2 sp ret s0v s1v s2v s3v s4v s5v [(o + 2, o + 4)]); [unfold m2; unchx | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact FC]. }
  assert (FC3 : frame_cells m3 sp ret s0v s1v s2v s3v s4v s5v).
  { apply (frame_cells_unch m2 m3 sp ret s0v s1v s2v s3v s4v s5v _ U3); [lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact FC2]. }
  destruct FC3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
  assert (Hsto3 : RiscvSemantics.store_ok SEGS_U m3 (Z_to_bv 64 o) 516 = true).
  { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto]. unfold m2; growsx. }
  assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_U m' (o + 2) 2 (ex b + e / 28)).
  { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx. }
  assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516)]).
  { intros m' U. apply (unch_trans m m3 m'); [|exact U].
    apply (unch_trans m m2 m3); [unfold m2; unchx|].
    eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
  assert (KEEPS : forall regs4, keeps fin_keep regs3 regs4 -> keeps fin_keep regs regs4).
  { intros regs4 K4. eapply keeps_trans; [exact K1|]. eapply keeps_trans; [exact K2|]. eapply keeps_trans; [exact K2'|]. eapply keeps_trans; [|exact K4].
    eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
  assert (MS : forall st, msteps SEGS_U (mkst regs3 (Z_to_bv 64 0x3631c) m3 rom) st ->
                          msteps SEGS_U (mkst regs (Z_to_bv 64 0x36280) m rom) st).
  { intros st H. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M2'|].
    eapply msteps_trans; [exact M3|]. exact H. }
  unfold shl. rewrite El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
  destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
  + (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (64, 2 ^ 62); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
                                       Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                          [KC (ZV 34) (-8) 8 (ZV 36); KC (ZV 34) (-16) 8 (ZV 37); KC (ZV 34) (-24) 8 (ZV 38); KC (ZV 34) (-32) 8 (ZV 39);
                           KC (ZV 34) (-40) 8 (ZV 40); KC (ZV 34) (-48) 8 (ZV 41); KC (ZV 34) (-56) 8 (ZV 42)] (@nil kwin))
      40%nat (@nil Z) (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (5%bv : reg, ZL 0); (2%bv : reg, ZAdd (ZV 34) (ZL (-64)));
               (14%bv : reg, ZMul (ZV 33) (ZL 281474976710656)); (17%bv : reg, ZAdd (ZV 32) (ZL 4))])
      [o; u; sp; c'; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v; bv_unsigned s5v]
      constr:([Some (0, 2 ^ 62); Some (1, 127); Some (64, 2 ^ 62); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
               Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs3 m3 rom 0x3631c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Q1; kc1 Q2; kc1 Q3; kc1 Q4; kc1 Q5; kc1 Q6; kc1 Q7; exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as E2.
    eexists regs4, m3. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [|split; [rewrite E2; f_equal; lia | split; [| split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3]]]]]].
    2:{ repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                       unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
    split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
    unfold zlen; rewrite Hlenr'.
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellx.
  + (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 127); Some (64, 2 ^ 62); Some (1, 2 ^ 27); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
                                       Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                          [KC (ZV 34) (-8) 8 (ZV 36); KC (ZV 34) (-16) 8 (ZV 37); KC (ZV 34) (-24) 8 (ZV 38); KC (ZV 34) (-32) 8 (ZV 39);
                           KC (ZV 34) (-40) 8 (ZV 40); KC (ZV 34) (-48) 8 (ZV 41); KC (ZV 34) (-56) 8 (ZV 42)] (@nil kwin))
      40%nat (@nil Z) (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (5%bv : reg, ZV 35); (2%bv : reg, ZAdd (ZV 34) (ZL (-64)));
               (14%bv : reg, ZMul (ZV 33) (ZL 281474976710656)); (17%bv : reg, ZAdd (ZV 32) (ZL 4))])
      [o; u; sp; c'; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v; bv_unsigned s5v]
      constr:([Some (0, 2 ^ 62); Some (1, 127); Some (64, 2 ^ 62); Some (1, 2 ^ 27); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
               Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs3 m3 rom 0x3631c.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Q1; kc1 Q2; kc1 Q3; kc1 Q4; kc1 Q5; kc1 Q6; kc1 Q7; exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
    zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as E2.
    eexists regs4, _. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [|split; [rewrite E2; f_equal; lia | split; [| split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3] | growsx]]]]]].
    2:{ repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                       unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
    rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
    split; [cellx|split; [apply EXC; unchx|split; [|lia]]].
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
    apply arr32_snoc'; try lia.
    { apply arr32_store_other; zwidth; try lia. exact Harr3. }
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.
End S.
