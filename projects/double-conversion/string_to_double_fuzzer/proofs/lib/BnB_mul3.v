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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_mul2 BnA_mul3 BnB_lib BnB_mul1.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].
Definition K27keep : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27].

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

#[using="Type"] Lemma loop27_B : forall f regs m (o r sp : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 r -> getr regs 8%bv = Z_to_bv 64 o -> getr regs 18%bv = Z_to_bv 64 7450580596923828125 ->
  getr regs 21%bv = Z_to_bv 64 53 -> getr regs 2%bv = Z_to_bv 64 sp ->
  27 <= r < 2048 -> r - 27 < 27 * (Z.of_nat f + 1) ->
  bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  KHI + 16 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 16 \/ sp <= o) ->
  shcellsB m -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 16)) 16 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa774) m rom) (mkst regs' (Z_to_bv 64 0x0aa78c) m' rom)
    /\ (let b' := fst (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        let r' := snd (pow27_loop f (r - 27) (mul64 kFive27_lo kFive27_hi b)) in
        bn_at SEGS_B m' o b' /\ getr regs' 10%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 27)
    /\ keeps K27keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r sp b R10 R8 R18 R21 R2 Hr Hf Hbn Hok Hn Hne Hv Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj SC OSH Hsto Hsts.
  all: pose proof (cap_bound (cells b) r 2 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five27_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  (* [comment removed for export] *)
  all: zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (27, 2047); Some (IMG, HIE - 516)]) (@nil kcell) (@nil kwin)) 10%nat [0x0ab4ec] (SCR [] [])
         constr:([(10%bv : reg, ZV 32); (8%bv : reg, ZV 33); (18%bv : reg, ZL 7450580596923828125)]) [r; o]
         constr:([Some (27, 2047); Some (IMG, HIE - 516)]) regs m rom 0x0aa774.
  all: zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I); zx_name regs0.
  all: assert (K0 : keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] regs regs0) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  all: zx_reg ZR (22%bv : reg) as A22.
  all: destruct (mulu64_B rom regs0 m o sp (Z_to_bv 64 0x0aa784) l exb) as (regs1 & m1 & M1 & K1 & Hbn1 & U1 & G1);
       [zx_regv ZR | zx_regv ZR | kept K0 2 R2 | zx_regv ZR | vm_compute; reflexivity | exact Hbn | exact Hok | exact Hne | lia
       | lia | lia | lia | lia | exact Ho8 | exact Hdisj | exact SC | exact OSH | exact Hsto | exact Hsts | ].
  all: rename ZM into M0; clear ZE ZR ZF.
  all: pose proof (mul64_spec (BN l exb) Hok Hn) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: assert (Hne1 : cells (mul64 kFive27_lo kFive27_hi (BN l exb)) <> []) by (intros HH; apply (proj1 (mul64_cells_nil _)) in HH; exact (Hne HH)).
  all: remember (mul64 kFive27_lo kFive27_hi (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 27) < B ^ 124)
        by (rewrite Hv1; replace (5 ^ r) with (5 ^ 27 * 5 ^ (r - 27)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C22 : getr regs1 22%bv = Z_to_bv 64 r) by (kept K1 22 A22).
  all: assert (B21 : getr regs0 21%bv = Z_to_bv 64 53) by (kept K0 21 R21).
  all: assert (C21 : getr regs1 21%bv = Z_to_bv 64 53) by (kept K1 21 B21).
  all: assert (HR1 : forall q, In q [(o, o + 2); (o + 4, o + 516); (sp - 16, sp)] -> KHI <= fst q \/ (IMG <= fst q /\ snd q <= LOSH)) by (intros q Hq; cbn in Hq; destruct Hq as [<-|[<-|[<-|[]]]]; cbn; lia).
  all: assert (SC1 : shcellsB m1) by (eapply shcellsB_unch; [exact U1 | exact HR1 | exact SC]).
  all: assert (OSH1 : objshB m1 o) by (eapply (objshB_unch m _ _); [exact U1 | exact HR1 | lia | lia | exact OSH]).
  all: assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
  all: assert (Hsts1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 (sp - 16)) 16 = true) by (eapply store_ok_grows; [exact G1 | exact Hsts]).
  - (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa774; 0x0aa78c] (SCR [false] [])
      constr:([(22%bv : reg, ZV 32); (21%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x0aa784.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M0|]; eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow27_loop fst snd].
    split; [|split; [| split; [exact U1 | exact G1]]].
    2:{ eapply keeps_trans; [eapply keeps_sub_dec; [exact K0|]; vm_compute; reflexivity|].
        eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
    split; [exact Hbn1|]. split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 53) as [Hle|Hgt].
    + (* [comment removed for export] *)
      zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (27, 53)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa774; 0x0aa78c] (SCR [false] [])
        constr:([(22%bv : reg, ZV 32); (21%bv : reg, ZL 53)]) [r] constr:([Some (27, 53)]) regs1 m1 rom 0x0aa784.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M0|]; eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow27_loop]. replace (r - 27 <? 27) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [| split; [exact U1 | exact G1]]].
      2:{ eapply keeps_trans; [eapply keeps_sub_dec; [exact K0|]; vm_compute; reflexivity|].
          eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
          eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
      split; [exact Hbn1|]. split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
    + (* [comment removed for export] *)
      zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (54, 2047)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa774; 0x0aa78c] (SCR [true] [])
        constr:([(22%bv : reg, ZV 32); (21%bv : reg, ZL 53)]) [r] constr:([Some (54, 2047)]) regs1 m1 rom 0x0aa784.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps K27keep regs regs2).
      { eapply keeps_trans; [eapply keeps_sub_dec; [exact K0|]; vm_compute; reflexivity|].
        eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
        eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
      cbn [pow27_loop]. replace (r - 27 <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (IH regs2 m1 o (r - 27) sp b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { etransitivity; [zx_regv ZR|]; f_equal; lia. }
      { kept K2 8 R8. } { kept K2 18 R18. } { kept K2 21 R21. } { kept K2 2 R2. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { lia. } { lia. }
      { exact Ho8. } { exact Hdisj. } { exact SC1. } { exact OSH1. } { exact Hsto1. } { exact Hsts1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M0|]; eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 27 - 27) with (r - 54) in POST by lia. replace (r - 27 - 27) with (r - 54) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.
End S.
