(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
 BnModel BnMath BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_shl BnA_mul3 BnA_mul4
 BnB_lib BnB_mul2 BnB_mul4 BnB_mul5.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].
Abbreviation big := (Some (0, 18446744073709551615)).

(* [comment removed for export] *)
Definition frame_cellsB (m : word -> option byte) (sp : Z) (rav v8 v9 v18 v19 v20 v21 v22 : Z) : Prop :=
  cellN SEGS_B m (sp + -8) 8 rav /\ cellN SEGS_B m (sp + -16) 8 v8 /\ cellN SEGS_B m (sp + -24) 8 v9 /\ cellN SEGS_B m (sp + -32) 8 v18
  /\ cellN SEGS_B m (sp + -40) 8 v19 /\ cellN SEGS_B m (sp + -48) 8 v20 /\ cellN SEGS_B m (sp + -56) 8 v21 /\ cellN SEGS_B m (sp + -64) 8 v22.
Definition s_restoredB (regs : bvmap 5 word) (v8 v9 v18 v19 v20 v21 v22 : Z) : Prop :=
  getr regs 8%bv = Z_to_bv 64 v8 /\ getr regs 9%bv = Z_to_bv 64 v9 /\ getr regs 18%bv = Z_to_bv 64 v18 /\ getr regs 19%bv = Z_to_bv 64 v19
  /\ getr regs 20%bv = Z_to_bv 64 v20 /\ getr regs 21%bv = Z_to_bv 64 v21 /\ getr regs 22%bv = Z_to_bv 64 v22.

Lemma frame_cellsB_unch : forall m m' sp rs rav v8 v9 v18 v19 v20 v21 v22,
  unch m m' rs -> (forall r, In r rs -> snd r <= sp - 64 \/ sp <= fst r) -> KHI + 64 <= sp -> sp <= HIE ->
  frame_cellsB m sp rav v8 v9 v18 v19 v20 v21 v22 -> frame_cellsB m' sp rav v8 v9 v18 v19 v20 v21 v22.
Proof.
  intros m m' sp rs rav v8 v9 v18 v19 v20 v21 v22 U HR H1 H2 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold frame_cellsB.
  repeat split; (eapply cellN_unch; [exact U | lia | cbn; lia | intros r Hr; specialize (HR r Hr); cbn; lia | assumption]).
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tblB_keep : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma tbl_B : forall regs m (o r sp : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 r -> getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 sp -> getr regs 20%bv = Z_to_bv 64 SHA ->
  0 <= r < 13 -> bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  arr32 SEGS_B m 145376 five_tbl -> tblshB m ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa8dc) m rom) (mkst regs' (Z_to_bv 64 0x0aa918) m' rom)
    /\ (let b' := (if 0 <? r then mul32 (kFive r) b else b) in
        bn_at SEGS_B m' o b' /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b /\ val (cells b') < B ^ 124)
    /\ keeps tblB_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o r sp b R10 R8 R2 R20 Hr Hbn Hok Hn Hne Hv Htbl TSH Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj SC OSH Hsto Hsts.
  assert (Hv0 : val (cells b) < B ^ 124) by (pose proof (val_nonneg _ Hok); pose proof (Z.pow_pos_nonneg 5 r ltac:(lia) ltac:(lia)); nia).
  remember (B ^ 124) as TOP eqn:ETOP.
  destruct (Z.eq_dec r 0) as [-> | Hr0].
  - (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX vi_regs (@nil kcell) (@nil kwin)) 5%nat [0x0aa918] (SCR [] []) constr:([(10%bv : reg, ZL 0)])
      (@nil Z) constr:(@nil (option (Z * Z))) regs m rom 0x0aa8dc.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
    eexists regs1, m. split; [exact ZM|]. replace (0 <? 0) with false by reflexivity. cbn zeta.
    split; [|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
    split; [exact Hbn|]. repeat split; auto.
  - (* [comment removed for export] *)
    replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia). cbn zeta. unfold kFive.
    assert (HF5 : 5 <= 5 ^ r) by (change 5 with (5 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    assert (HF12 : 5 ^ r <= 244140625) by (change 244140625 with (5 ^ 12); apply Z.pow_le_mono_r; lia).
    assert (Hcell : exists bs, rdn SEGS_B m (Z_to_bv 64 (145372 + 4 * r)) 4 = Some bs /\ bytes_le_to_Z bs = 5 ^ r).
    { rewrite <- (five_tbl_nth r) by lia. eapply (kc_of_arr32_i _ _ _ _ (Z.to_nat (r - 1))); [exact Htbl | cbn; lia | lia | reflexivity]. }
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 12); Some (5, 244140625)]) (@nil kcell) (@nil kwin))
      30%nat [0x0ab304; 0x0aa918] (SCR [] [ZL 0; ZV 34])
      constr:([(10%bv : reg, ZV 33); (8%bv : reg, ZV 32); (20%bv : reg, ZL SHA)]) [o; r; 5 ^ r]
      constr:([Some (IMG, HIE - 516); Some (1, 12); Some (5, 244140625)]) regs m rom 0x0aa8dc.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I)
      ltac:(idtac; zx_scs ltac:(first [ destruct Hcell as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                     | apply (cellN_eqa _ _ _ _ _ _ _ (TSH ((145372 + 4 * r) / 8 - 18172) ltac:(lia))); [lia|reflexivity] ])).
    zx_name regs1.
    assert (K1 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    destruct b as [l exb]; cbn [cells BnModel.ex] in *.
    destruct (mulu32_B rom regs1 m o (5 ^ r) sp (Z_to_bv 64 0x0aa918) l exb) as (regs2 & m2 & M2 & K2 & Hbn2 & U2 & G2);
      [zx_regv ZR | zx_regv ZR | kept K1 2 R2 | zx_regv ZR | vm_compute; reflexivity | lia | exact Hbn | exact Hok | exact Hne | | lia | lia | lia | lia
      | exact Ho8 | exact Hdisj | exact SC | exact OSH | exact Hsto | exact Hsts | ].
    { pose proof (cap_bound l r 0 Hok Hn ltac:(lia) ltac:(lia) ltac:(subst TOP; exact Hv) (five0_ge r ltac:(lia))). lia. }
    eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    pose proof (mul32_spec (5 ^ r) (BN l exb) Hok Hn ltac:(lia)) as (S1 & S2 & S3 & S4). cbn [cells BnModel.ex] in S1, S2, S3, S4.
    split.
    { split; [exact Hbn2|]. split; [exact S1|]. split; [exact S2|].
      split; [intros HH; apply (proj1 (mul32_cells_nil (5 ^ r) (BN l exb) ltac:(lia))) in HH; exact (Hne HH)|].
      split; [apply S4; lia|]. rewrite S3. pose proof (val_nonneg _ Hok). nia. }
    split; [eapply keeps_trans; [exact K1 | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]|].
    split; [exact U2 | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition finB_keep : list Z := [3; 4; 23; 24; 25; 26; 27].

#[using="Type"] Lemma fin_B : forall regs m (o e sp : Z) (ret : word) (rav v8 v9 v18 v19 v20 v21 v22 : Z) (b : bn),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 9%bv = Z_to_bv 64 e -> getr regs 2%bv = Z_to_bv 64 (sp - 64) ->
  getr regs 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 20%bv = Z_to_bv 64 SHA ->
  frame_cellsB m sp rav v8 v9 v18 v19 v20 v21 v22 -> Z_to_bv 64 rav = ret -> ret_ok ret ->
  1 <= e < 2048 -> bn_at SEGS_B m o b -> ok (cells b) -> cells b <> [] -> zlen (cells b) <= 126 -> ex b + e / 28 < 2 ^ 15 ->
  KHI + 64 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 64 \/ sp <= o) -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa918) m rom) (mkst regs' ret m' rom)
    /\ bn_at SEGS_B m' o (shl e b) /\ getr regs' 2%bv = Z_to_bv 64 sp /\ s_restoredB regs' v8 v9 v18 v19 v20 v21 v22
    /\ keeps finB_keep regs regs'
    /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret rav v8 v9 v18 v19 v20 v21 v22 b R8 R9 R2 R19 R20 FC Hrav Hret He Hbn Hok Hne Hlen Hex Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj OSH Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _).
  pose proof FC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  pose proof (cellN_range _ _ _ _ _ F1) as W1. pose proof (cellN_range _ _ _ _ _ F2) as W2. pose proof (cellN_range _ _ _ _ _ F3) as W3.
  pose proof (cellN_range _ _ _ _ _ F4) as W4. pose proof (cellN_range _ _ _ _ _ F5) as W5. pose proof (cellN_range _ _ _ _ _ F6) as W6.
  pose proof (cellN_range _ _ _ _ _ F7) as W7. pose proof (cellN_range _ _ _ _ _ F8) as W8.
  cbn [Z.of_nat Z.mul Pos.mul] in W1, W2, W3, W4, W5, W6, W7, W8. zwidth.
  remember (cells b) as l eqn:El.
  destruct l as [|x t]; [congruence|].
  apply ok_cons in Hok as Hok0. destruct Hok0 as [Hx Hokt].
  assert (Hus : 1 <= zlen (x :: t) <= 126) by (rewrite zlen_cons in *; pose proof (zlen_nonneg t); lia).
  remember (zlen (x :: t)) as u eqn:Hu. unfold zlen in Hu. cbn [length] in Hu.
  hide Hdisj.
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)])
        [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 35); KC (ZDivP (ZAdd (ZV 32) (ZL 2)) 3) SHA 1 (ZL 0); KC (ZV 32) 2 2 (ZV 36)] (@nil kwin))
    40%nat [0x0aa960] (SCR [] []) constr:([(8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-64)));
      (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (20%bv : reg, ZL SHA)])
    [o; e; sp; u; ex b] constr:([Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1)]) regs m rom 0x0aa918.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; kc1 Cu; kcsh OSH 0; kc1 Ce; exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  zx_reg ZR (12%bv : reg) as A12. fold (magic28A e) in A12. rewrite (magic28A_ok e) in A12 by lia.
  zx_reg ZR (13%bv : reg) as A13. zx_reg ZR (11%bv : reg) as A11. zx_reg ZR (10%bv : reg) as A10.
  zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (2%bv : reg) as A2. zx_reg ZR (19%bv : reg) as A19. zx_reg ZR (20%bv : reg) as A20.
  assert (K1 : keeps [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] regs regs1)
    by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M1.
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)])
        (@nil kcell) [KW (ZV 32) 0 516])
    40%nat [0x0aa988] (SCR [] []) constr:([(12%bv : reg, ZV 37); (13%bv : reg, ZV 36); (11%bv : reg, ZV 35); (10%bv : reg, ZAdd (ZV 32) (ZL 2));
      (8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-64))); (20%bv : reg, ZL SHA); (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
    [o; e; sp; u; ex b; e / 28] constr:([Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73)]) regs1 m rom 0x0aa960.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I) ltac:(exact I). zx_name regs2.
  zx_reg ZR (12%bv : reg) as B12. zx_reg ZR (13%bv : reg) as B13. zx_reg ZR (11%bv : reg) as B11.
  zx_reg ZR (8%bv : reg) as B8. zx_reg ZR (9%bv : reg) as B9. zx_reg ZR (2%bv : reg) as B2. zx_reg ZR (19%bv : reg) as B19. zx_reg ZR (20%bv : reg) as B20.
  set (m1 := wbytes m _ _) in ZM.
  assert (K2 : keeps [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] regs1 regs2)
    by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M2.
  assert (Hs : 0 <= e mod 28 < 28) by lia.
  assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [|exact Hsto]; unfold m1; growsx).
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)])
        (@nil kcell) (@nil kwin))
    40%nat [0x0aa9b4] (SCR [] []) constr:([(12%bv : reg, ZV 38); (13%bv : reg, ZSub (ZL 28) (ZV 38)); (11%bv : reg, ZV 35);
      (8%bv : reg, ZV 32); (9%bv : reg, ZV 33); (2%bv : reg, ZAdd (ZV 34) (ZL (-64))); (20%bv : reg, ZL SHA); (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
    [o; e; sp; u; ex b; e / 28; e mod 28] constr:([Some (IMG, HIE - 516); Some (1, 2047); Some (KHI + 64, HIE); Some (1, 126); Some (0, 2 ^ 15 - 1); Some (0, 73); Some (0, 27)]) regs2 m1 rom 0x0aa988.
  zx_use2 ZXB ltac:(zx_pins; first [rewrite B12; f_equal; lia | rewrite B13; f_equal; lia]) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
  zx_reg ZR (10%bv : reg) as D10. zx_reg ZR (17%bv : reg) as D17. zx_reg ZR (5%bv : reg) as D5. zx_reg ZR (16%bv : reg) as D16.
  zx_reg ZR (12%bv : reg) as D12. zx_reg ZR (13%bv : reg) as D13. zx_reg ZR (15%bv : reg) as D15. zx_reg ZR (20%bv : reg) as D20.
  zx_reg ZR (14%bv : reg) as D14. zx_reg ZR (8%bv : reg) as D8. zx_reg ZR (2%bv : reg) as D2. zx_reg ZR (19%bv : reg) as D19. zx_reg ZR (11%bv : reg) as D11.
  assert (K3 : keeps [1; 2; 3; 4; 8; 9; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] regs2 regs3)
    by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  clear ZE ZR ZF. rename ZM into M3.
  (* [comment removed for export] *)
  unhide.
  assert (Harr1 : arr32 SEGS_B m1 (o + 4) ([] ++ x :: t)).
  { cbn [app]. unfold m1. apply arr32_store_other; zwidth; try lia. exact Carr. }
  assert (OSH1 : objshB m1 o).
  { unfold m1. eapply (objshB_unch m _ [(o, o + 516)]); [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  destruct (fshl_loop_B rom (x :: t) [] 0 regs3 m1 (o + 4) (e mod 28)) as (regs4 & m4 & M4 & Harr4 & C6 & K4 & U4 & G4);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { rewrite D10; first [reflexivity | f_equal; lia]. }
  { rewrite D17; first [reflexivity | f_equal; lia]. }
  { rewrite D5. f_equal. lia. }
  { exact D16. }
  { exact D12. }
  { rewrite D13; first [reflexivity | f_equal; lia]. }
  { exact D15. }
  { exact D20. }
  { exact Hs. }
  { split; [lia|]. apply Z.pow_pos_nonneg; lia. }
  { exact Hok. }
  { congruence. }
  { lia. }
  { lia. }
  { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH1. }
  { lia. }
  { exact Harr1. }
  { eapply sc_store_in; [exact Hsto1|]. cbn [length]. lia. }
  cbn [length app] in Harr4, U4. rewrite ?Z.mul_0_r, ?Z.add_0_r in U4.
  pose proof (shl_l_spec (e mod 28) (x :: t) 0 Hok Hs ltac:(split; [lia|apply Z.pow_pos_nonneg; lia])) as SPEC.
  destruct (shl_l (e mod 28) 0 (x :: t)) as [r c'] eqn:Eshl. cbn [fst snd] in Harr4, C6.
  destruct SPEC as (_ & Hokr & Hlenr & Hc').
  assert (Hc'27 : c' < 2 ^ 27) by (assert (2 ^ (e mod 28) <= 2 ^ 27) by (apply Z.pow_le_mono_r; lia); lia).
  assert (Hlenr' : Z.of_nat (length r) = u) by (unfold zlen in Hlenr; cbn [length] in Hlenr; lia).
  (* [comment removed for export] *)
  assert (E11 : getr regs4 11%bv = Z_to_bv 64 u) by (kept K4 11 D11).
  assert (E8 : getr regs4 8%bv = Z_to_bv 64 o) by (kept K4 8 D8).
  assert (E2 : getr regs4 2%bv = Z_to_bv 64 (sp + -64)) by (kept K4 2 D2).
  assert (E14 : getr regs4 14%bv = Z_to_bv 64 (o + 4)) by (kept K4 14 D14).
  assert (E20 : getr regs4 20%bv = Z_to_bv 64 SHA) by (kept K4 20 D20).
  assert (E19 : getr regs4 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K4 19 D19).
  assert (FC1 : frame_cellsB m1 sp rav v8 v9 v18 v19 v20 v21 v22).
  { eapply (frame_cellsB_unch m m1 sp [(o, o + 516)]); [unfold m1; unchx | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia | lia | lia | exact FC]. }
  assert (FC4 : frame_cellsB m4 sp rav v8 v9 v18 v19 v20 v21 v22).
  { eapply frame_cellsB_unch; [exact U4 | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; unhide; lia | lia | lia | exact FC1]. }
  destruct FC4 as (G1 & G2 & G3 & G4' & G5 & G6 & G7 & G8).
  assert (OSH4 : objshB m4 o).
  { eapply (objshB_unch m1 _ _); [exact U4 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH1]. }
  assert (Hsto4 : RiscvSemantics.store_ok SEGS_B m4 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G4 | exact Hsto1]).
  (* [comment removed for export] *)
  assert (EXC : forall m', unch m4 m' [(o, o + 2); (o + 4 + 4 * u, o + 8 + 4 * u)] -> cellN SEGS_B m' (o + 2) 2 (ex b + e / 28)).
  { intros m' U. eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia |].
    eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
    unfold m1. cellN_go. }
  assert (UNCH : forall m', unch m4 m' [(o, o + 516)] -> unch m m' [(o, o + 516)]).
  { intros m' U. apply (unch_trans m m4 m'); [|exact U].
    apply (unch_trans m m1 m4); [unfold m1; unchx|].
    eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|cbn; lia]. }
  assert (KEEPS : forall regs5, keeps finB_keep regs4 regs5 -> keeps finB_keep regs regs5).
  { intros regs5 K5.
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|]. exact K5. }
  assert (MS : forall st, msteps SEGS_B (mkst regs4 (Z_to_bv 64 0x0aaa0c) m4 rom) st ->
                          msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa918) m rom) st).
  { intros st H. eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2|]. eapply msteps_trans; [exact M3|].
    eapply msteps_trans; [exact M4|]. exact H. }
  unfold shl. rewrite <- El, Eshl. unfold bn_at. cbn [cells BnModel.ex].
  clear M1 M2 M3 M4 Harr1 OSH1 K1 K2 K3 K4.
  clear A12 A13 A11 A10 A8 A9 A2 A19 A20 B12 B13 B11 B8 B9 B2 B19 B20 D10 D17 D5 D16 D12 D13 D15 D20 D14 D8 D2 D19 D11.
  destruct (Z.eqb_spec c' 0) as [Hc0|Hc0].
  + (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 64, HIE); Some (1, 126); Some (0, 0); big; big; big; big; big; big; big; big])
        [KC (ZV 33) (-8) 8 (ZV 36); KC (ZV 33) (-16) 8 (ZV 37); KC (ZV 33) (-24) 8 (ZV 38); KC (ZV 33) (-32) 8 (ZV 39); KC (ZV 33) (-40) 8 (ZV 40);
         KC (ZV 33) (-48) 8 (ZV 41); KC (ZV 33) (-56) 8 (ZV 42); KC (ZV 33) (-64) 8 (ZV 43)] (@nil kwin))
      40%nat (@nil Z) (SCR [] []) constr:([(6%bv : reg, ZV 35); (11%bv : reg, ZV 34); (14%bv : reg, ZAdd (ZV 32) (ZL 4)); (8%bv : reg, ZV 32);
        (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (20%bv : reg, ZL SHA); (2%bv : reg, ZAdd (ZV 33) (ZL (-64)))])
      [o; sp; u; c'; rav; v8; v9; v18; v19; v20; v21; v22]
      constr:([Some (IMG, HIE - 516); Some (KHI + 64, HIE); Some (1, 126); Some (0, 0); big; big; big; big; big; big; big; big]) regs4 m4 rom 0x0aaa0c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 G1; kc1 G2; kc1 G3; kc1 G4'; kc1 G5; kc1 G6; kc1 G7; kc1 G8; exact I) ltac:(exact I) ltac:(exact I). zx_name regs5.
    assert (R1' : getr regs5 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; exact Hrav).
    eexists regs5, m4. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split.
    { split; [|split; [apply EXC; apply unch_refl|split; [exact Harr4|split; [lia| unfold zlen; rewrite Hlenr'; lia]]]].
      unfold zlen; rewrite Hlenr'.
      eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
      unfold m1. cellN_go. }
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [unfold s_restoredB; repeat split; zx_regv ZR|].
    split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [apply UNCH; apply unch_refl | apply (mem_grows_trans m m1 m4); [unfold m1; growsx | exact G4]].
  + (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (KHI + 64, HIE); Some (1, 126); Some (1, 2 ^ 27); big; big; big; big; big; big; big; big])
        [KC (ZV 33) (-8) 8 (ZV 36); KC (ZV 33) (-16) 8 (ZV 37); KC (ZV 33) (-24) 8 (ZV 38); KC (ZV 33) (-32) 8 (ZV 39); KC (ZV 33) (-40) 8 (ZV 40);
         KC (ZV 33) (-48) 8 (ZV 41); KC (ZV 33) (-56) 8 (ZV 42); KC (ZV 33) (-64) 8 (ZV 43);
         KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZDivP (ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 34) (ZL 4))) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 516])
      40%nat (@nil Z) (SCR [] []) constr:([(6%bv : reg, ZV 35); (11%bv : reg, ZV 34); (14%bv : reg, ZAdd (ZV 32) (ZL 4)); (8%bv : reg, ZV 32);
        (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (20%bv : reg, ZL SHA); (2%bv : reg, ZAdd (ZV 33) (ZL (-64)))])
      [o; sp; u; c'; rav; v8; v9; v18; v19; v20; v21; v22]
      constr:([Some (IMG, HIE - 516); Some (KHI + 64, HIE); Some (1, 126); Some (1, 2 ^ 27); big; big; big; big; big; big; big; big]) regs4 m4 rom 0x0aaa0c.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia)
      ltac:(kc1 G1; kc1 G2; kc1 G3; kc1 G4'; kc1 G5; kc1 G6; kc1 G7; kc1 G8; kcsh OSH4 0; kcsh OSH4 ((4 + 4 * u) / 8); exact I) ltac:(kw1 Hsto4; exact I)
      ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto4 | zwidth; lia])). zx_name regs5.
    assert (R1' : getr regs5 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; exact Hrav).
    eexists regs5, _. split; [apply MS; eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split.
    { rewrite zlen_app. unfold zlen. cbn [length]. rewrite Hlenr'.
      split; [cellN_go|split; [apply EXC; unchx|split; [|lia]]].
      apply arr32_store_other; [lia | rewrite length_app; zwidth; lia | lia | zwidth; lia | rewrite length_app; zwidth; lia |].
      eapply arr32_snoc_eq; [exact Harr4 | lia | lia | lia |].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. apply Z.mod_small. lia. }
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [unfold s_restoredB; repeat split; zx_regv ZR|].
    split; [apply KEEPS; eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [apply UNCH; unchx | eapply mem_grows_trans; [apply (mem_grows_trans m m1 m4); [unfold m1; growsx | exact G4] | growsx]].
Qed.
End S.
