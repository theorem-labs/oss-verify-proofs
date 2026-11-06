(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_shl BnA_mul1 BnA_au64.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition frame_cells (m : word -> option byte) (sp : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
  cellN SEGS_A m (sp - 8) 8 (bv_unsigned ret) /\ cellN SEGS_A m (sp - 16) 8 (bv_unsigned s0v) /\
  cellN SEGS_A m (sp - 24) 8 (bv_unsigned s1v) /\ cellN SEGS_A m (sp - 32) 8 (bv_unsigned s2v) /\
  cellN SEGS_A m (sp - 40) 8 (bv_unsigned s3v) /\ cellN SEGS_A m (sp - 48) 8 (bv_unsigned s4v).

Lemma frame_cells_unch : forall m m' sp ret s0v s1v s2v s3v s4v rs,
  unch m m' rs -> 48 <= sp -> sp <= HIE -> (forall r, In r rs -> sp <= fst r \/ snd r <= sp - 48) ->
  frame_cells m sp ret s0v s1v s2v s3v s4v -> frame_cells m' sp ret s0v s1v s2v s3v s4v.
Proof.
  intros m m' sp ret s0v s1v s2v s3v s4v rs U Hsp1 Hsp2 Hd (C1 & C2 & C3 & C4 & C5 & C6).
  repeat split;
    (eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; specialize (Hd rg Hrg); cbn; zwidth; lia | assumption]).
Qed.

Definition s_restored (regs' : bvmap 5 word) (s0v s1v s2v s3v s4v : word) : Prop :=
  getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v /\ getr regs' 19%bv = s3v /\ getr regs' 20%bv = s4v.

(* [comment removed for export] *)
Ltac kept1 K :=
  lazymatch goal with |- getr _ ?r = _ =>
    let rz := eval vm_compute in (bv_unsigned r) in etransitivity; [exact (K rz ltac:(in_list)) | ] end.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fin_keep : list Z := [3; 4; 10; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma fin_A : forall regs m (o e sp : Z) (ret s0v s1v s2v s3v s4v : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 16%bv = Z_to_bv 64 (zlen (cells b)) ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 13%bv = Z_to_bv 64 SHA -> getr regs 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) ->
  getr regs 2%bv = Z_to_bv 64 (sp - 48) ->
  frame_cells m sp ret s0v s1v s2v s3v s4v -> ret_ok ret ->
  1 <= e < 2048 -> bn_at SEGS_A m o b -> ok (cells b) -> cells b <> [] -> zlen (cells b) <= 126 -> ex b + e / 28 < 2 ^ 15 ->
  KHI + 48 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 48 \/ sp <= o) -> objsh m o ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa9b8) m rom) (mkst regs' ret m' rom)
    /\ bn_at SEGS_A m' o (shl e b) /\ getr regs' 2%bv = Z_to_bv 64 sp /\ s_restored regs' s0v s1v s2v s3v s4v
    /\ keeps fin_keep regs regs'
    /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret s0v s1v s2v s3v s4v b R10 R11 R16 R15 R13 R14 R2 FC Hret He Hbn Hok Hne Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj OSH Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  assert (Hl1 : 1 <= zlen (cells b)) by (destruct (cells b); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen (cells b)) as u eqn:Eu. assert (Hlen' : Z.of_nat (length (cells b)) = u) by (rewrite Eu; reflexivity).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range s0v) as Hs0. pose proof (u64_range s1v) as Hs1. pose proof (u64_range s2v) as Hs2.
  pose proof (u64_range s3v) as Hs3. pose proof (u64_range s4v) as Hs4.
  hide Hdisj.
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (KHI + 48, HIE)])
       [KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0); KC (ZV 32) 2 2 (ZV 35)] (@nil kwin))
    40%nat [0x0aa9f8] (SCR [] []) constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (11%bv : reg, ZV 34); (13%bv : reg, ZL SHA);
             (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (15%bv : reg, ZL 268435455); (2%bv : reg, ZAdd (ZV 36) (ZL (-48)))])
    [o; u; e; ex b; sp] constr:([Some (IMG, HIE - 516); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (KHI + 48, HIE)]) regs m rom 0x0aa9b8.
  zx_use2 ZXB ltac:(unfold MASK in *; zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Ce; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (6%bv : reg) as A6. fold (magic28A e) in A6. rewrite (magic28A_ok e) in A6 by lia.
  zx_reg ZR (5%bv : reg) as A5. zx_reg ZR (17%bv : reg) as A17. zx_reg ZR (12%bv : reg) as A12.
  assert (K1 : keeps [2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  rename ZM into M1. clear ZE ZR ZF.
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (KHI + 48, HIE); Some (0, 73)]) (@nil kcell) [KW (ZV 32) 0 516])
    40%nat [0x0aaa24] (SCR [] [])
    constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (11%bv : reg, ZV 34); (6%bv : reg, ZV 37); (5%bv : reg, ZV 35); (17%bv : reg, ZV 33);
             (12%bv : reg, ZAdd (ZV 32) (ZL 2))])
    [o; u; e; ex b; sp; e / 28] constr:([Some (IMG, HIE - 516); Some (1, 127); Some (1, 2047); Some (0, 2 ^ 15 - 1); Some (KHI + 48, HIE); Some (0, 73)]) regs1 m rom 0x0aa9f8.
  zx_use2 ZXB ltac:(zx_pins; kept1 K1; assumption) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(exact I). zx_name regs2.
  zx_reg ZR (17%bv : reg) as B17. zx_reg ZR (12%bv : reg) as B12. zx_reg ZR (5%bv : reg) as B5.
  set (m2 := wbytes m _ _) in ZM.
  assert (K2 : keeps [2; 3; 4; 8; 9; 10; 11; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs1 regs2) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2.
  assert (Hs : 0 <= e mod 28 < 28) by lia.
  (* [comment removed for export] *)
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 127); Some (0, 27)]) (@nil kcell) (@nil kwin))
    40%nat [0x0aaa38] (SCR [] [])
    constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (17%bv : reg, ZV 34); (12%bv : reg, ZAdd (ZV 32) (ZL 4)); (5%bv : reg, ZL 0)])
    [o; u; e mod 28] constr:([Some (IMG, HIE - 516); Some (1, 127); Some (0, 27)]) regs2 m2 rom 0x0aaa24.
  zx_use2 ZXB ltac:(zx_pins; try (kept1 K2); try (kept1 K1); first [assumption | rewrite B17; f_equal; lia]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs2'.
  zx_reg ZR (11%bv : reg) as D11. zx_reg ZR (7%bv : reg) as D7. zx_reg ZR (28%bv : reg) as D28. zx_reg ZR (5%bv : reg) as D5.
  zx_reg ZR (17%bv : reg) as D17. zx_reg ZR (6%bv : reg) as D6. zx_reg ZR (12%bv : reg) as D12.
  assert (K2' : keeps [2; 3; 4; 8; 9; 10; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs2 regs2') by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2'.
  assert (K02' : keeps [2; 3; 4; 8; 9; 10; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs2').
  { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity| exact K2']. }
  (* [comment removed for export] *)
  unhide.
  destruct (cells b) as [|x t] eqn:El; [congruence|]. cbn [length] in Hlen'.
  assert (Harr2 : arr32 SEGS_A m2 (o + 4) ([] ++ x :: t)).
  { cbn [app]. unfold m2. apply arr32_store_other; zwidth; try lia. exact Carr. }
  assert (OSH2 : objsh m2 o).
  { unfold m2. eapply (objsh_unch m _ [(o, o + 516)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  pose proof Hok as Hok0.
  destruct (mshl_loop_A rom (x :: t) [] 0 regs2' m2 (o + 4) (e mod 28)) as (regs3 & m3 & M3 & Harr3 & C29 & K3 & U3 & G3);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { rewrite D11; first [reflexivity | f_equal; lia]. }
  { rewrite D7; first [reflexivity | f_equal; lia]. }
  { etransitivity; [exact D28|]; f_equal; lia. }
  { exact D5. }
  { exact D17. }
  { rewrite D6; first [reflexivity | f_equal; lia]. }
  { etransitivity; [exact (K02' 15 ltac:(in_list)) | exact R15]. }
  { etransitivity; [exact (K02' 13 ltac:(in_list)) | exact R13]. }
  { exact Hs. }
  { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
  { exact Hok. }
  { congruence. }
  { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. } { replace (o + 4 - 4) with o by lia. exact OSH2. }
  { cbn [length] in Hlen'. lia. }
  { exact Harr2. }
  { eapply sc_store_in; [eapply store_ok_grows; [|exact Hsto]; unfold m2; growsx |]. cbn [length]. cbn [length] in Hlen'. lia. }
  cbn [length app] in Harr3, U3. rewrite ?Z.mul_0_r, ?Z.add_0_r in U3. rewrite Hlen' in U3.
  pose proof (shl_l_spec (e mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
  destruct (shl_l (e mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr3, C29.
  destruct SPEC as (_ & Hokr & Hlenr & Hc').
  assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (e mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
  assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; cbn [length] in Hlen'; lia).
  (* [comment removed for export] *)
  assert (K03 : keeps [2; 3; 4; 8; 9; 10; 13; 14; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs3).
  { eapply keeps_trans; [exact K02'|]. eapply keeps_sub_dec; [exact K3|]. vm_compute. reflexivity. }
  assert (C16 : getr regs3 16%bv = Z_to_bv 64 u) by (etransitivity; [exact (K03 16 ltac:(in_list)) | exact R16]).
  assert (C10 : getr regs3 10%bv = Z_to_bv 64 o) by (etransitivity; [exact (K03 10 ltac:(in_list)) | exact R10]).
  assert (C2 : getr regs3 2%bv = Z_to_bv 64 (sp - 48)) by (etransitivity; [exact (K03 2 ltac:(in_list)) | exact R2]).
  assert (C14 : getr regs3 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (etransitivity; [exact (K03 14 ltac:(in_list)) | exact R14]).
  assert (C13 : getr regs3 13%bv = Z_to_bv 64 SHA) by (etransitivity; [exact (K03 13 ltac:(in_list)) | exact R13]).
  assert (C12 : getr regs3 12%bv = Z_to_bv 64 (o + 4)) by (etransitivity; [exact (K3 12 ltac:(in_list)) | exact D12]).
  assert (FC2 : frame_cells m2 sp ret s0v s1v s2v s3v s4v).
  { apply (frame_cells_unch m m2 sp ret s0v s1v s2v s3v s4v [(o + 2, o + 4)]); [unfold m2; unchx | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact FC]. }
  assert (FC3 : frame_cells m3 sp ret s0v s1v s2v s3v s4v).
  { apply (frame_cells_unch m2 m3 sp ret s0v s1v s2v s3v s4v _ U3); [lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact FC2]. }
  destruct FC3 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  assert (Hsto3 : RiscvSemantics.store_ok SEGS_A m3 (Z_to_bv 64 o) 516 = true).
  { eapply store_ok_grows; [exact G3|]. eapply store_ok_grows; [|exact Hsto]. unfold m2; growsx. }
  assert (OSH3 : objsh m3 o).
  { eapply (objsh_unch m2 _ _); [exact U3 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH2]. }
  assert (EXC : forall m', unch m3 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_A m' (o + 2) 2 (ex b + e / 28)).
  { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellN_go. }
  assert (UNCH : forall m', unch m3 m' [(o, o + 516)] -> unch m m' [(o, o + 516)]).
  { intros m' U. apply (unch_trans m m3 m'); [|exact U].
    apply (unch_trans m m2 m3); [unfold m2; unchx|].
    eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
  assert (KEEPS : forall regs4, keeps fin_keep regs3 regs4 -> keeps fin_keep regs regs4).
  { intros regs4 K4. eapply keeps_trans; [|exact K4]. eapply keeps_sub_dec; [exact K03|]. vm_compute. reflexivity. }
  assert (MS : forall st, msteps SEGS_A (mkst regs3 (Z_to_bv 64 0x0aaa8c) m3 rom) st ->
                          msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa9b8) m rom) st).
  { intros st H. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M2'|].
    eapply msteps_trans; [exact M3|]. exact H. }
  unfold shl. rewrite El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
  clear M1 M2 M2' M3 K1 K2 K2' K02' K3 A6 A5 A17 A12 B17 B12 B5 D11 D7 D28 D5 D17 D6 D12.
  destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
  + (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 127); Some (KHI + 48, HIE); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
                                       Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                          [KC (ZV 34) (-8) 8 (ZV 36); KC (ZV 34) (-16) 8 (ZV 37); KC (ZV 34) (-24) 8 (ZV 38); KC (ZV 34) (-32) 8 (ZV 39);
                           KC (ZV 34) (-40) 8 (ZV 40); KC (ZV 34) (-48) 8 (ZV 41)] (@nil kwin))
      40%nat (@nil Z) (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (29%bv : reg, ZV 35); (2%bv : reg, ZAdd (ZV 34) (ZL (-48)));
               (12%bv : reg, ZAdd (ZV 32) (ZL 4))])
      [o; u; sp; c'; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v]
      constr:([Some (IMG, HIE - 516); Some (1, 127); Some (KHI + 48, HIE); Some (0, 0); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
               Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs3 m3 rom 0x0aaa8c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Q1; kc1 Q2; kc1 Q3; kc1 Q4; kc1 Q5; kc1 Q6; exact I) ltac:(exact I) ltac:(exact I). zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as E2.
    eexists regs4, m3. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split; [|split; [rewrite E2; f_equal; lia | split; [| split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3]]]]]].
    2:{ repeat split; (etransitivity; [apply ZR|]; match goal with |- ZXA.wd _ (ZXA.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with ee end;
                       unfold ZXA.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
    split; [|split; [apply EXC; apply unch_refl|split; [exact Harr3|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
    unfold zlen; rewrite Hlenr'.
    eapply cellN_unch; [exact U3 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m2. cellN_go.
  + (* [comment removed for export] *)
    zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 127); Some (KHI + 48, HIE); Some (1, 2 ^ 27); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
                                       Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)])
                          [KC (ZV 34) (-8) 8 (ZV 36); KC (ZV 34) (-16) 8 (ZV 37); KC (ZV 34) (-24) 8 (ZV 38); KC (ZV 34) (-32) 8 (ZV 39);
                           KC (ZV 34) (-40) 8 (ZV 40); KC (ZV 34) (-48) 8 (ZV 41);
                           KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4))) 3) SHA 1 (ZL 0)] (@nil kwin))
      40%nat (@nil Z) (SCR [] [])
      constr:([(10%bv : reg, ZV 32); (16%bv : reg, ZV 33); (29%bv : reg, ZV 35); (2%bv : reg, ZAdd (ZV 34) (ZL (-48)));
               (12%bv : reg, ZAdd (ZV 32) (ZL 4)); (13%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
      [o; u; sp; c'; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v]
      constr:([Some (IMG, HIE - 516); Some (1, 127); Some (KHI + 48, HIE); Some (1, 2 ^ 27); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1);
               Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)]) regs3 m3 rom 0x0aaa8c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 Q1; kc1 Q2; kc1 Q3; kc1 Q4; kc1 Q5; kc1 Q6; kcsh OSH3 0; kcsh OSH3 ((4 + 4 * u) / 8); exact I) ltac:(exact I)
      ltac:(unhide; zx_scs ltac:(eapply sc_store_in; [exact Hsto3 | zwidth; lia])).
    zx_name regs4.
    assert (R1' : getr regs4 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    zx_reg ZR (2%bv : reg) as E2.
    eexists regs4, _. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split; [|split; [rewrite E2; f_equal; lia | split; [| split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m2 m3); [unfold m2; growsx | exact G3] | growsx]]]]]].
    2:{ repeat split; (etransitivity; [apply ZR|]; match goal with |- ZXA.wd _ (ZXA.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with ee end;
                       unfold ZXA.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
    rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
    split; [cellN_go|split; [apply EXC; unchx|split; [|lia]]].
    replace (o + 4 + u * 4) with (o + 4 + 4 * Z.of_nat (length r)) by lia.
    apply arr32_store_other; [lia | rewrite length_app; zwidth; lia | lia | zwidth; lia | rewrite length_app; zwidth; lia |].
    apply arr32_snoc'; try lia; [exact Harr3|].
    rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia.
Qed.
End S.
