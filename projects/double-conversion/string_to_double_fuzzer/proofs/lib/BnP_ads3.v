(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_mul2 BnP_mul3 BnP_ads1 BnP_ads2.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition sv13 (m : word -> option byte) (sp : Z) (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) : Prop :=
  cellN SEGS_P m (sp - 8) 8 (bv_unsigned RA) /\
  cellN SEGS_P m (sp - 16) 8 (bv_unsigned S0) /\
  cellN SEGS_P m (sp - 24) 8 (bv_unsigned S1) /\
  cellN SEGS_P m (sp - 32) 8 (bv_unsigned S2) /\
  cellN SEGS_P m (sp - 40) 8 (bv_unsigned S3) /\
  cellN SEGS_P m (sp - 48) 8 (bv_unsigned S4) /\
  cellN SEGS_P m (sp - 56) 8 (bv_unsigned S5) /\
  cellN SEGS_P m (sp - 64) 8 (bv_unsigned S6) /\
  cellN SEGS_P m (sp - 72) 8 (bv_unsigned S7) /\
  cellN SEGS_P m (sp - 80) 8 (bv_unsigned S8) /\
  cellN SEGS_P m (sp - 88) 8 (bv_unsigned S9) /\
  cellN SEGS_P m (sp - 96) 8 (bv_unsigned S10) /\
  cellN SEGS_P m (sp - 104) 8 (bv_unsigned S11).

Lemma sv13_unch : forall m m' sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 rs,
  unch m m' rs -> 104 <= sp -> sp <= 2 ^ 62 -> (forall r, In r rs -> sp <= fst r \/ snd r <= sp - 104) ->
  sv13 m sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 -> sv13 m' sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
Proof.
  intros until rs. intros U Hsp1 Hsp2 Hd W. unfold sv13 in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cellN _ _ ?a _ _ => eapply cellN_unch; [exact U | lia | zwidth; lia | intros rg Hrg; specialize (Hd rg Hrg); cbn; zwidth; lia | tauto] end.
Qed.

Definition s12_rest (regs' : bvmap 5 word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word) : Prop :=
  getr regs' 8%bv = S0 /\ getr regs' 9%bv = S1 /\ getr regs' 18%bv = S2 /\ getr regs' 19%bv = S3 /\ getr regs' 20%bv = S4 /\ getr regs' 21%bv = S5 /\ getr regs' 22%bv = S6 /\ getr regs' 23%bv = S7 /\ getr regs' 24%bv = S8 /\ getr regs' 25%bv = S9 /\ getr regs' 26%bv = S10 /\ getr regs' 27%bv = S11.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.
Hypothesis ADD : add_P_spec rom.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation rt_pins := [(9%bv : reg, ZV 32); (19%bv : reg, ZV 33); (18%bv : reg, ZV 34); (10%bv : reg, ZV 35); (12%bv : reg, ZL 10)].
Abbreviation rt_uvi := [Some (1, 2 ^ 62); Some (0, 780); Some (0, 10 ^ 18); Some (0, 780); Some (48, 57)].
Definition rt_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma rdtail_loop_P : forall t regs m (buf idx acc e : Z),
  getr regs 9%bv = Z_to_bv 64 buf -> getr regs 19%bv = Z_to_bv 64 idx -> getr regs 18%bv = Z_to_bv 64 acc ->
  getr regs 10%bv = Z_to_bv 64 e -> getr regs 12%bv = Z_to_bv 64 10 ->
  e = idx + zlen t -> t <> [] -> digits_ok t ->
  (forall k, (k < length t)%nat -> cellN SEGS_P m (buf + idx + Z.of_nat k) 1 (nth k t 0)) ->
  0 <= acc -> (acc + 1) * 10 ^ zlen t <= 10 ^ 18 ->
  1 <= buf -> buf + e <= 2 ^ 62 -> 0 <= idx -> e <= 780 ->
  exists regs',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35a00) m rom) (mkst regs' (Z_to_bv 64 0x35a1c) m rom)
    /\ getr regs' 18%bv = Z_to_bv 64 (read_digits t acc) /\ getr regs' 19%bv = Z_to_bv 64 e
    /\ keeps rt_keep regs regs'.
Proof.
  induction t as [|d t IH]; intros regs m buf idx acc e R9 R19 R18 R10 R12 He Hne Hds Hcells Hacc Hacc2 Hb1 Hb2 Hi He2; [congruence|].
  rewrite zlen_cons in *. pose proof (zlen_nonneg t) as Ht0.
  apply Forall_cons_iff in Hds. destruct Hds as [Hd Hds].
  pose proof (Hcells 0%nat ltac:(cbn; lia)) as D0. cbn [nth] in D0. rewrite Z.add_0_r in D0.
  assert (Hp : 10 ^ (zlen t + 1) = 10 ^ zlen t * 10) by (rewrite Z.pow_add_r by lia; lia).
  rewrite Hp in Hacc2. assert (Hp1 : 1 <= 10 ^ zlen t) by (apply Z.pow_le_mono_r with (a := 10) (b := 0) in Ht0; lia || (pose proof (Z.pow_pos_nonneg 10 (zlen t)); lia)).
  assert (Hacc3 : acc < 10 ^ 18) by nia.
  cbn [read_digits].
  destruct t as [|d2 t'].
  - rewrite zlen_nil in *.
    zx_run SEGS_P constr:(CTX (vi_regs ++ rt_uvi) [KC (ZAdd (ZV 32) (ZV 33)) 0 1 (ZV 36)] (@nil kwin)) 10%nat [0x35a00; 0x35a1c] (SCR [false] [])
      constr:(rt_pins) [buf; idx; acc; e; d] constr:(rt_uvi) regs m rom 0x35a00.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 D0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    exists regs1. split; [exact ZM|]. cbn [read_digits].
    split; [zx_regv ZR|]. split; [zx_regv ZR|]. eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
  - rewrite zlen_cons in *. pose proof (zlen_nonneg t') as Ht1.
    zx_run SEGS_P constr:(CTX (vi_regs ++ rt_uvi) [KC (ZAdd (ZV 32) (ZV 33)) 0 1 (ZV 36)] (@nil kwin)) 10%nat [0x35a00; 0x35a1c] (SCR [true] [])
      constr:(rt_pins) [buf; idx; acc; e; d] constr:(rt_uvi) regs m rom 0x35a00.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 D0; exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs1.
    assert (Hp' : 10 ^ (zlen t' + 1) = 10 ^ zlen t' * 10) by (rewrite Z.pow_add_r by lia; lia).
    destruct (IH regs1 m buf (idx + 1) (acc * 10 + (d - 48)) e) as (regs2 & M2 & C18 & C19 & K2).
    { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
    { lia. } { congruence. } { exact Hds. }
    { intros k Hk. specialize (Hcells (S k) ltac:(cbn in Hk |- *; lia)). cbn [nth] in Hcells. eapply cellN_eqa; [exact Hcells | lia | reflexivity]. }
    { lia. } { rewrite Hp'. nia. } { lia. } { lia. } { lia. } { lia. }
    exists regs2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [exact C18|]. split; [exact C19|].
    eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation big := (Some (0, 18446744073709551615)).
(* [comment removed for export] *)
Abbreviation cf_kn := [KC (ZV 32) 0 2 (ZV 33); KC (ZV 34) (-8) 8 (ZV 36); KC (ZV 34) (-16) 8 (ZV 37); KC (ZV 34) (-24) 8 (ZV 38); KC (ZV 34) (-32) 8 (ZV 39); KC (ZV 34) (-40) 8 (ZV 40); KC (ZV 34) (-48) 8 (ZV 41); KC (ZV 34) (-56) 8 (ZV 42); KC (ZV 34) (-64) 8 (ZV 43); KC (ZV 34) (-72) 8 (ZV 44); KC (ZV 34) (-80) 8 (ZV 45); KC (ZV 34) (-88) 8 (ZV 46); KC (ZV 34) (-96) 8 (ZV 47); KC (ZV 34) (-104) 8 (ZV 48)].
Abbreviation cf_uvi0 := [Some (0, 2 ^ 62); Some (0, 0); Some (832, 2 ^ 62); Some (0, 0); big; big; big; big; big; big; big; big; big; big; big; big; big].
Abbreviation cf_uvi1 := [Some (0, 2 ^ 62); Some (1, 128); Some (832, 2 ^ 62); Some (1, 2 ^ 28 - 1); big; big; big; big; big; big; big; big; big; big; big; big; big].
Abbreviation cf_pins := [(8%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 34) (ZL (-736)))].

#[using="Type"] Lemma last_nth : forall (l : list Z) d, l <> [] -> nth (length l - 1) l d = last l d.
Proof.
  induction l as [|x t IH]; intros d Hne; [congruence|].
  destruct t as [|y t']; [reflexivity|].
  change (last (x :: y :: t') d) with (last (y :: t') d). rewrite <- IH by congruence.
  cbn [length]. replace (S (S (length t')) - 1)%nat with (S (length t')) by lia.
  replace (S (length t') - 1)%nat with (length t') by lia. reflexivity.
Qed.

#[using="Type"] Lemma clampfin_P : forall (p : Z) regs m (o sp : Z) (l : list Z) (e : Z) (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word),
  (p = 0x35a64 \/ p = 0x35ab8) ->
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 736) ->
  bn_at SEGS_P m o (BN l e) -> ok l -> norm l -> sv13 m sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 -> ret_ok RA ->
  832 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 816 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 p) m rom) (mkst regs' RA m' rom)
    /\ bn_at SEGS_P m' o (clamp (BN l e)) /\ getr regs' 2%bv = Z_to_bv 64 sp
    /\ s12_rest regs' S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 /\ keeps [3; 4] regs regs'
    /\ unch m m' [(o, o + 516)] /\ mem_grows m m'.
Proof.
  intros p regs m o sp l e RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 Hp R8 R2 Hbn Hok Hn W Hret Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & H128). cbn [cells BnModel.ex] in *.
  pose proof (u64_range RA) as U_RA. pose proof (u64_range S0) as U_S0. pose proof (u64_range S1) as U_S1. pose proof (u64_range S2) as U_S2. pose proof (u64_range S3) as U_S3. pose proof (u64_range S4) as U_S4. pose proof (u64_range S5) as U_S5. pose proof (u64_range S6) as U_S6. pose proof (u64_range S7) as U_S7. pose proof (u64_range S8) as U_S8. pose proof (u64_range S9) as U_S9. pose proof (u64_range S10) as U_S10. pose proof (u64_range S11) as U_S11.
  destruct W as (W0 & W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12).
  unfold clamp. cbn [cells BnModel.ex]. rewrite (clamp_l_norm _ _ Hn).
  pose proof (zlen_nonneg l) as Hl0.
  destruct l as [|x t] eqn:El.
  - (* [comment removed for export] *)
    rewrite zlen_nil in Cu.
    assert (RUN : forall pc, (pc = 0x35a64 \/ pc = 0x35ab8) -> pc = p ->
      exists regs' m', msteps SEGS_P (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' RA m' rom)
        /\ bn_at SEGS_P m' o (BN [] 0) /\ getr regs' 2%bv = Z_to_bv 64 sp
        /\ s12_rest regs' S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 /\ keeps [3; 4] regs regs'
        /\ unch m m' [(o, o + 516)] /\ mem_grows m m').
    2:{ exact (RUN p Hp eq_refl). }
    intros pc Hpc _. destruct Hpc as [-> | ->].
    + zx_run SEGS_P constr:(CTX (vi_regs ++ cf_uvi0) cf_kn [KW (ZV 32) 0 516]) 30%nat (@nil Z) (SCR [] [])
        constr:(cf_pins) [o; 0; sp; 0; bv_unsigned RA; bv_unsigned S0; bv_unsigned S1; bv_unsigned S2; bv_unsigned S3; bv_unsigned S4; bv_unsigned S5; bv_unsigned S6; bv_unsigned S7; bv_unsigned S8; bv_unsigned S9; bv_unsigned S10; bv_unsigned S11] constr:(cf_uvi0) regs m rom 0x35a64.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Cu; kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I) ltac:(kw1 Hsto; exact I) ltac:(zx_lia). zx_name regs1.
      assert (R1' : getr regs1 1%bv = RA) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [|split; [zx_regv ZR; f_equal; lia|split; [| split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [unchx | growsx]]]]].
      2:{ unfold s12_rest. repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                       unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
      clear ZM ZE ZR ZF. unfold bn_at. cbn [cells BnModel.ex]. rewrite ?zlen_nil.
      split; [cellx|]. split; [cellx|]. split; [apply arr32_nil|]. lia.
    + zx_run SEGS_P constr:(CTX (vi_regs ++ cf_uvi0) cf_kn [KW (ZV 32) 0 516]) 30%nat (@nil Z) (SCR [] [])
        constr:(cf_pins) [o; 0; sp; 0; bv_unsigned RA; bv_unsigned S0; bv_unsigned S1; bv_unsigned S2; bv_unsigned S3; bv_unsigned S4; bv_unsigned S5; bv_unsigned S6; bv_unsigned S7; bv_unsigned S8; bv_unsigned S9; bv_unsigned S10; bv_unsigned S11] constr:(cf_uvi0) regs m rom 0x35ab8.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Cu; kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I) ltac:(kw1 Hsto; exact I) ltac:(zx_lia). zx_name regs1.
      assert (R1' : getr regs1 1%bv = RA) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [|split; [zx_regv ZR; f_equal; lia|split; [| split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [unchx | growsx]]]]].
      2:{ unfold s12_rest. repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                       unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned). }
      clear ZM ZE ZR ZF. unfold bn_at. cbn [cells BnModel.ex]. rewrite ?zlen_nil.
      split; [cellx|]. split; [cellx|]. split; [apply arr32_nil|]. lia.
  - (* [comment removed for export] *)
    rewrite <- El in *.
    assert (Hne : l <> []) by (rewrite El; congruence).
    assert (Hl1 : 1 <= zlen l) by (rewrite El, zlen_cons; pose proof (zlen_nonneg t); lia).
    remember (zlen l) as u eqn:Eu.
    assert (Htop : exists bs, rdn SEGS_P m (Z_to_bv 64 (o + 4 + 4 * (u - 1))) 4 = Some bs /\ bytes_le_to_Z bs = last l 0).
    { rewrite <- (last_nth l 0 Hne). eapply (kc_of_arr32_i _ _ _ _ (length l - 1)%nat); [exact Carr | unfold zlen in Eu; lia | unfold zlen in Eu; lia | reflexivity]. }
    assert (Htr : 1 <= last l 0 < B).
    { destruct Hn as [Hn|Hn]; [congruence|]. rewrite <- (last_nth l 0 Hne) in Hn |- *.
      pose proof (proj1 (Forall_nth _ _) Hok (length l - 1)%nat 0 ltac:(unfold zlen in Eu; lia)) as Hx. cbn beta in Hx. lia. }
    unfold B in Htr.
    assert (RUN : forall pc, (pc = 0x35a64 \/ pc = 0x35ab8) -> pc = p ->
      exists regs' m', msteps SEGS_P (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' RA m' rom)
        /\ bn_at SEGS_P m' o (BN l e) /\ getr regs' 2%bv = Z_to_bv 64 sp
        /\ s12_rest regs' S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 /\ keeps [3; 4] regs regs'
        /\ unch m m' [(o, o + 516)] /\ mem_grows m m').
    2:{ exact (RUN p Hp eq_refl). }
    intros pc Hpc _. destruct Hpc as [-> | ->].
    + zx_run SEGS_P constr:(CTX (vi_regs ++ cf_uvi1) cf_kn (@nil kwin)) 30%nat (@nil Z) (SCR [] [ZV 35])
        constr:(cf_pins) [o; u; sp; last l 0; bv_unsigned RA; bv_unsigned S0; bv_unsigned S1; bv_unsigned S2; bv_unsigned S3; bv_unsigned S4; bv_unsigned S5; bv_unsigned S6; bv_unsigned S7; bv_unsigned S8; bv_unsigned S9; bv_unsigned S10; bv_unsigned S11] constr:(cf_uvi1) regs m rom 0x35a64.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Cu; kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I) ltac:(exact I)
        ltac:(idtac; zx_scs ltac:(destruct Htop as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv])).
      zx_name regs1.
      assert (R1' : getr regs1 1%bv = RA) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      eexists regs1, m. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [unfold bn_at; cbn [cells BnModel.ex]; rewrite <- Eu; split; [exact Cu|split; [exact Ce|split; [exact Carr|split; [exact Hexr| lia]]]]|].
      split; [zx_regv ZR; f_equal; lia|]. split; [| split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
      unfold s12_rest. repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                     unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned).
    + zx_run SEGS_P constr:(CTX (vi_regs ++ cf_uvi1) cf_kn (@nil kwin)) 30%nat (@nil Z) (SCR [] [ZV 35])
        constr:(cf_pins) [o; u; sp; last l 0; bv_unsigned RA; bv_unsigned S0; bv_unsigned S1; bv_unsigned S2; bv_unsigned S3; bv_unsigned S4; bv_unsigned S5; bv_unsigned S6; bv_unsigned S7; bv_unsigned S8; bv_unsigned S9; bv_unsigned S10; bv_unsigned S11] constr:(cf_uvi1) regs m rom 0x35ab8.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 Cu; kc1 W0; kc1 W1; kc1 W2; kc1 W3; kc1 W4; kc1 W5; kc1 W6; kc1 W7; kc1 W8; kc1 W9; kc1 W10; kc1 W11; kc1 W12; exact I) ltac:(exact I)
        ltac:(idtac; zx_scs ltac:(destruct Htop as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv])).
      zx_name regs1.
      assert (R1' : getr regs1 1%bv = RA) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
      eexists regs1, m. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
      split; [unfold bn_at; cbn [cells BnModel.ex]; rewrite <- Eu; split; [exact Cu|split; [exact Ce|split; [exact Carr|split; [exact Hexr| lia]]]]|].
      split; [zx_regv ZR; f_equal; lia|]. split; [| split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | split; [apply unch_refl | apply mem_grows_refl]]].
      unfold s12_rest. repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                     unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned).
Qed.
End S.
