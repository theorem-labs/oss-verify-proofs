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

Section AR.
Context {fx : FPState}.
(* [comment removed for export] *)
#[using="Type"] Lemma arr32_snoc_eq : forall m A l a (w : word) v,
  arr32 SEGS_B m A l -> a = A + 4 * Z.of_nat (length l) -> 0 <= A -> A + 4 * Z.of_nat (length l) + 4 <= M64 ->
  bv_unsigned w mod 2 ^ 32 = v ->
  arr32 SEGS_B (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 4 w)) A (l ++ [v]).
Proof. intros m A l a w v H -> Ha Hb Hv. apply arr32_snoc'; assumption. Qed.
End AR.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Ltac loop_obls ZXB Hcell Hst OSH g :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(unfold B in *; zx_lia) ltac:(kc1 Hcell; kcsh OSH g; exact I) ltac:(kw1 Hst; exact I) ltac:(zx_lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation m13_pins := [(10%bv : reg, ZV 32); (29%bv : reg, ZV 32); (31%bv : reg, ZV 33); (28%bv : reg, ZV 34); (30%bv : reg, ZV 36);
                          (17%bv : reg, ZL 1220703125); (14%bv : reg, ZL 268435455); (20%bv : reg, ZL SHA)].
Abbreviation m13_uvi clo chi := [Some (IMG, HIE - 8); Some (clo, chi); Some (0, 2 ^ 32); Some (0, 2 ^ 28 - 1); Some (2 ^ 60, 2 ^ 62)].
Definition m13B_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma m13_loop_B : forall t done c regs m (A g : Z),
  let p := A + 4 * Z.of_nat (length done) in
  let pend := A + 4 * Z.of_nat (length done) + 4 * Z.of_nat (length t) in
  getr regs 10%bv = Z_to_bv 64 p -> getr regs 29%bv = Z_to_bv 64 p -> getr regs 31%bv = Z_to_bv 64 (Z.of_nat (length t)) ->
  getr regs 28%bv = Z_to_bv 64 c -> getr regs 30%bv = Z_to_bv 64 g ->
  getr regs 17%bv = Z_to_bv 64 kFive13 -> getr regs 14%bv = Z_to_bv 64 MASK -> getr regs 20%bv = Z_to_bv 64 SHA ->
  0 <= c <= kFive13 -> ok t -> t <> [] -> 2 ^ 60 + Z.of_nat (length t) <= g <= 2 ^ 62 ->
  APP (A - 4) 520 -> A + 516 <= HIE -> (A - 4) mod 8 = 0 -> objshB m (A - 4) ->
  Z.of_nat (length done) + Z.of_nat (length t) <= 126 ->
  arr32 SEGS_B m A (done ++ t) ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 p) (4 * length t)%nat = true ->
  exists regs' m' tmp,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa810) m rom) (mkst regs' (Z_to_bv 64 0x0aa864) m' rom)
    /\ arr32 SEGS_B m' A (done ++ fst (mul32_l kFive13 c t))
    /\ getr regs' 28%bv = Z_to_bv 64 (snd (mul32_l kFive13 c t))
    /\ getr regs' 18%bv = Z_to_bv 64 tmp /\ tmp / 2 ^ 28 = snd (mul32_l kFive13 c t) /\ 0 <= tmp < 2 ^ 60
    /\ keeps m13B_keep regs regs'
    /\ unch m m' [(p, pend)] /\ mem_grows m m'.
Proof.
  induction t as [|x t IH]; intros done c regs m A g p pend RP RP' RN RC RG RF R14 R20 Hc Hok Hne Hg HA1 HA2 HA8 OSH Hlen Harr Hst; [congruence|].
  subst p pend. unfold kFive13 in *. apply ok_cons in Hok as [Hx Hok].
  assert (Hcell : exists bs, rdn SEGS_B m (Z_to_bv 64 (A + 4 * Z.of_nat (length done))) 4 = Some bs /\ bytes_le_to_Z bs = x)
    by (eapply kc_of_arr32; [exact Harr | lia]).
  pose proof (mul32_step_bounds 1220703125 x c ltac:(lia) Hx Hc) as (Hp1 & Hp2 & Hp3).
  cbn [mul32_l]. destruct (mul32_l 1220703125 ((1220703125 * x + c) / B) t) as [r c''] eqn:Hrec.
  cbn [fst snd]. unfold MASK, B in *.
  destruct t as [|y t']; cbn [length] in *.
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m13_uvi 1 1) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0aa810; 0x0aa864] (SCR [] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); 1; c; x; g] constr:(m13_uvi 1 1) regs m rom 0x0aa810.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs0.
    cbn in Hrec. injection Hrec as <- <-.
    eexists regs0, _, (x * 1220703125 + c). split; [exact ZM|].
    split.
    { apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|].
    split; [f_equal; lia|]. split; [nia|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]].
  - zx_run SEGS_B constr:(CTX (vi_regs ++ m13_uvi 2 128) [KC (ZV 32) 0 4 (ZV 35); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] [KW (ZV 32) 0 4]) 40%nat [0x0aa810; 0x0aa864] (SCR [] [])
      constr:(m13_pins) [A + 4 * Z.of_nat (length done); Z.of_nat (S (S (length t'))); c; x; g] constr:(m13_uvi 2 128) regs m rom 0x0aa810.
    loop_obls ZXB Hcell Hst OSH ((4 + 4 * Z.of_nat (length done)) / 8). zx_name regs1.
    set (m1 := wbytes m _ _) in ZM.
    set (v := (1220703125 * x + c) mod 268435456).
    assert (Harr1 : arr32 SEGS_B m1 A ((done ++ [v]) ++ y :: t')).
    { rewrite <- app_assoc. cbn [app]. unfold m1.
      apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr | ].
      rewrite u_Z2bv64. unfold v. rewrite (Z.mod_small _ 18446744073709551616) by lia. lia. }
    specialize (IH (done ++ [v]) ((1220703125 * x + c) / 268435456) regs1 m1 A (g - 1)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
    destruct IH as (regs2 & m2 & tmp & M2 & Harr2 & COUT & CT & HT1 & HT2 & K2 & U2 & G2);
      [ etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | etransitivity; [zx_regv ZR|]; f_equal; lia | etransitivity; [zx_regv ZR|]; f_equal; lia
      | zx_regv ZR | zx_regv ZR | zx_regv ZR | lia | exact Hok | congruence | lia | lia | lia | lia | | lia | exact Harr1 | | ].
    { unfold m1. eapply (objshB_unch m _ [(A + 4 * Z.of_nat (length done), A + 4 * Z.of_nat (length done) + 4)]);
        [unchx | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
    { unfold m1. eapply store_ok_grows; [apply grows_store|].
      eapply sc_store_in; [exact Hst|]. zwidth. lia. }
    eexists regs2, m2, tmp. split; [eapply msteps_trans; [exact ZM | exact M2]|].
    split; [rewrite <- app_assoc in Harr2; exact Harr2|].
    split; [exact COUT|]. split; [exact CT|]. split; [exact HT1|]. split; [exact HT2|].
    split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
    split.
    + apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
      intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
    + apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation car13_pins := [(28%bv : reg, ZV 34); (11%bv : reg, ZV 33); (12%bv : reg, ZAdd (ZV 32) (ZL 4));
   (16%bv : reg, ZSub (ZL 18446744073709551615) (ZAdd (ZV 32) (ZL 4))); (13%bv : reg, ZL 128); (14%bv : reg, ZL 268435455); (8%bv : reg, ZV 32);
   (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (20%bv : reg, ZL SHA)].
Abbreviation car13_kw := [KW (ZV 32) 0 2; KW (ZAdd (ZV 32) (ZMul (ZV 33) (ZL 4))) 4 16].
Definition car13B_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31].

Ltac car13_obls ZXB OSH Hsto u :=
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH 0; exact I) ltac:(kw1 Hsto; kw1 Hsto; exact I)
    ltac:(idtac; zx_scs ltac:(first [shread OSH u | eapply sc_store_in; [exact Hsto|zwidth; lia]])).

#[using="Type"] Lemma car13_B : forall regs m (o u c : Z) (l : list Z) (clo chi : Z),
  getr regs 28%bv = Z_to_bv 64 c -> getr regs 11%bv = Z_to_bv 64 u -> getr regs 12%bv = Z_to_bv 64 (o + 4) ->
  getr regs 16%bv = Z_to_bv 64 (18446744073709551611 - o) -> getr regs 13%bv = Z_to_bv 64 128 -> getr regs 14%bv = Z_to_bv 64 MASK ->
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 20%bv = Z_to_bv 64 SHA ->
  clo <= c <= chi -> ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1)) ->
  zlen l = u -> 0 <= u -> u + 3 <= 127 -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objshB m o ->
  arr32 SEGS_B m (o + 4) l ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa86c) m rom) (mkst regs' (Z_to_bv 64 0x0aa7e4) m' rom)
    /\ arr32 SEGS_B m' (o + 4) (l ++ chunks 3 c)
    /\ cellN SEGS_B m' o 2 (u + zlen (chunks 3 c))
    /\ getr regs' 11%bv = Z_to_bv 64 (u + zlen (chunks 3 c))
    /\ keeps car13B_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4 + 4 * u, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o u c l clo chi RC R11 R12 R16 R13 R14 R8 R19 R20 Hc Hcase Hlen Hu0 Hu Ho1 Ho2 Ho8 OSH Harr Hsto.
  unfold MASK, B in *.
  assert (Hlen' : Z.of_nat (length l) = u) by (unfold zlen in Hlen; lia).
  destruct Hcase as [[-> ->] | [-> ->]].
  - rewrite chunks_1 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car13_kw)
      60%nat [0x0aa7e4] (SCR [] [ZL 0]) constr:(car13_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (1, 2 ^ 28 - 1)]) regs m rom 0x0aa86c.
    car13_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    eapply arr32_snoc_eq; [exact Harr | lia | lia | lia | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
  - rewrite chunks_2 by (unfold B; lia). unfold B.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0)] car13_kw)
      90%nat [0x0aa7e4] (SCR [] [ZL 0; ZL 0]) constr:(car13_pins) [o; u; c]
      constr:([Some (IMG, HIE - 516); Some (0, 124); Some (2 ^ 28, 2 ^ 56 - 1)]) regs m rom 0x0aa86c.
    car13_obls ZXB OSH Hsto u. zx_name regs0.
    eexists regs0, _. split; [exact ZM|]. unfold zlen. cbn [length]. zwidth.
    split; [|split; [cellN_go|split; [zx_regv ZR|split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|split; [unchx|growsx]]]]].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    replace (l ++ [c mod 268435456; c / 268435456]) with ((l ++ [c mod 268435456]) ++ [c / 268435456]) by (rewrite <- app_assoc; reflexivity).
    eapply arr32_snoc_eq; [| rewrite length_app; cbn [length]; lia | lia | rewrite length_app; cbn [length]; lia | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; apply Z.mod_small; lia].
    apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia.
    eapply arr32_snoc_eq; [exact Harr | lia | lia | lia | rewrite u_Z2bv64; rewrite (Z.mod_small _ 18446744073709551616) by lia; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition it13B_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27].

#[using="Type"] Lemma it13_B : forall regs m (o r : Z) (l : list Z) (exb : Z),
  getr regs 10%bv = Z_to_bv 64 r -> getr regs 11%bv = Z_to_bv 64 (zlen l) -> getr regs 12%bv = Z_to_bv 64 (o + 4) ->
  getr regs 15%bv = Z_to_bv 64 ((18446744073709551615 - o) / 2 ^ 2) -> getr regs 16%bv = Z_to_bv 64 (18446744073709551611 - o) ->
  getr regs 17%bv = Z_to_bv 64 kFive13 -> getr regs 13%bv = Z_to_bv 64 128 -> getr regs 14%bv = Z_to_bv 64 MASK ->
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 20%bv = Z_to_bv 64 SHA ->
  0 <= r < 2048 -> bn_at SEGS_B m o (BN l exb) -> ok l -> l <> [] -> zlen l + 3 <= 126 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa7ec) m rom) (mkst regs' (Z_to_bv 64 0x0aa7e4) m' rom)
    /\ bn_at SEGS_B m' o (mul32 kFive13 (BN l exb))
    /\ getr regs' 11%bv = Z_to_bv 64 (zlen (cells (mul32 kFive13 (BN l exb))))
    /\ getr regs' 7%bv = Z_to_bv 64 r
    /\ keeps it13B_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  intros regs m o r l exb R10 R11 R12 R15 R16 R17 R13 R14 R8 R19 R20 Hr Hbn Hok Hne Hlen Ho1 Ho2 Ho8 OSH Hsto.
  destruct Hbn as (Cu & Ce & Carr & Hexr & _). cbn [cells BnModel.ex] in *.
  assert (Hl1 : 1 <= zlen l) by (destruct l; [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  remember (zlen l) as u eqn:Eu. assert (Hlen' : Z.of_nat (length l) = u) by (rewrite Eu; reflexivity).
  (* [comment removed for export] *)
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) (@nil kcell) (@nil kwin))
    20%nat [0x0aa810] (SCR [] []) constr:([(10%bv : reg, ZV 34); (11%bv : reg, ZV 33); (12%bv : reg, ZAdd (ZV 32) (ZL 4));
      (15%bv : reg, ZDivP (ZSub (ZL 18446744073709551615) (ZV 32)) 2)])
    [o; u; r] constr:([Some (IMG, HIE - 516); Some (1, 123); Some (0, 2047)]) regs m rom 0x0aa7ec.
  zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs1.
  assert (K1 : keeps [1; 2; 3; 4; 5; 6; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs1)
    by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
  zx_reg ZR (7%bv : reg) as A7. zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (29%bv : reg) as A29. zx_reg ZR (31%bv : reg) as A31.
  zx_reg ZR (28%bv : reg) as A28. zx_reg ZR (30%bv : reg) as A30.
  rename ZM into M1. clear ZE ZR ZF.
  assert (B17 : getr regs1 17%bv = Z_to_bv 64 kFive13) by (kept K1 17 R17).
  assert (B14 : getr regs1 14%bv = Z_to_bv 64 MASK) by (kept K1 14 R14).
  assert (B20 : getr regs1 20%bv = Z_to_bv 64 SHA) by (kept K1 20 R20).
  (* [comment removed for export] *)
  unfold mul32. cbn [cells BnModel.ex Z.eqb kFive13 Pos.eqb]. destruct l as [|x t] eqn:El; [congruence|]. rewrite <- El in *.
  pose proof (mul32_l_spec kFive13 l 0 Hok ltac:(unfold kFive13; lia) ltac:(lia)) as SP.
  unfold kFive13 in *.
  destruct (mul32_l 1220703125 0 l) as [rr c] eqn:Em. destruct SP as (_ & Hokr & Hlenr & Hc0' & HcF). specialize (HcF ltac:(lia)).
  destruct (m13_loop_B l [] 0 regs1 m (o + 4) ((18446744073709551615 - o) / 2 ^ 2)) as (regs2 & m2 & tmp & M2 & Harr2 & C28 & C18 & HT1 & HT2 & K2 & U2 & G2);
    cbn [length app]; rewrite ?Z.mul_0_r, ?Z.add_0_r.
  { exact A10. } { exact A29. } { rewrite A31. f_equal. lia. } { exact A28. } { exact A30. } { exact B17. } { exact B14. } { exact B20. }
  { unfold kFive13. lia. } { exact Hok. } { exact Hne. } { lia. } { lia. } { lia. } { replace (o + 4 - 4) with o by lia. exact Ho8. }
  { replace (o + 4 - 4) with o by lia. exact OSH. } { lia. } { exact Carr. }
  { eapply sc_store_in; [exact Hsto|]. zwidth. lia. }
  unfold kFive13 in *.
  rewrite Em in *. cbn [fst snd] in *. rewrite Hlen' in *.
  cbn [length app Z.of_nat] in U2, Harr2. rewrite ?Z.mul_0_r, ?Z.add_0_r in U2.
  assert (B11 : getr regs1 11%bv = Z_to_bv 64 u) by (kept K1 11 R11). assert (C11 : getr regs2 11%bv = Z_to_bv 64 u) by (kept K2 11 B11).
  assert (B12 : getr regs1 12%bv = Z_to_bv 64 (o + 4)) by (kept K1 12 R12). assert (C12 : getr regs2 12%bv = Z_to_bv 64 (o + 4)) by (kept K2 12 B12).
  assert (B16 : getr regs1 16%bv = Z_to_bv 64 (18446744073709551611 - o)) by (kept K1 16 R16). assert (C16 : getr regs2 16%bv = Z_to_bv 64 (18446744073709551611 - o)) by (kept K2 16 B16).
  assert (B13 : getr regs1 13%bv = Z_to_bv 64 128) by (kept K1 13 R13). assert (C13 : getr regs2 13%bv = Z_to_bv 64 128) by (kept K2 13 B13).
  assert (C14 : getr regs2 14%bv = Z_to_bv 64 MASK) by (kept K2 14 B14).
  assert (B8 : getr regs1 8%bv = Z_to_bv 64 o) by (kept K1 8 R8). assert (C8 : getr regs2 8%bv = Z_to_bv 64 o) by (kept K2 8 B8).
  assert (B19 : getr regs1 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K1 19 R19). assert (C19 : getr regs2 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 19 B19).
  assert (C20 : getr regs2 20%bv = Z_to_bv 64 SHA) by (kept K2 20 B20).
  assert (C7 : getr regs2 7%bv = Z_to_bv 64 r) by (kept K2 7 A7).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_B m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Cu2 : cellN SEGS_B m2 o 2 u).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Cu]. }
  assert (Ce2 : cellN SEGS_B m2 (o + 2) 2 exb).
  { eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia | exact Ce]. }
  assert (OSH2 : objshB m2 o).
  { eapply (objshB_unch m _ _); [exact U2 | intros r0 [<-|[]]; cbn; lia | lia | lia | exact OSH]. }
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* [comment removed for export] *)
    rewrite Hc0 in *. rewrite chunks_0, app_nil_r.
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 2 ^ 28 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa86c; 0x0aa7e4] (SCR [] [])
      constr:([(18%bv : reg, ZV 32)]) [tmp] constr:([Some (0, 2 ^ 28 - 1)]) regs2 m2 rom 0x0aa864.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    eexists regs3, m2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact ZM]|].
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite Hlenr, <- Eu. exact Cu2.
      - exact Ce2.
      - exact Harr2. }
    split; [cbn [cells]; rewrite Hlenr, <- Eu; etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C11]|].
    split; [etransitivity; [exact (reg_kept _ _ _ _ (7%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C7]|].
    split; [eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|];
            eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|];
            eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [|exact G2].
    eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
  - (* [comment removed for export] *)
    zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (2 ^ 28, 2 ^ 60 - 1)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa86c; 0x0aa7e4] (SCR [] [])
      constr:([(18%bv : reg, ZV 32)]) [tmp] constr:([Some (2 ^ 28, 2 ^ 60 - 1)]) regs2 m2 rom 0x0aa864.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
    assert (K3 : keeps [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] regs2 regs3)
      by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M3. clear ZE ZR ZF.
    assert (Hcls : exists clo chi, clo <= c <= chi /\ ((clo = 1 /\ chi = B - 1) \/ (clo = B /\ chi = B * B - 1))).
    { unfold B. destruct (Z_lt_dec c 268435456); [exists 1, (268435456 - 1); lia|].
      exists 268435456, (268435456 * 268435456 - 1); lia. }
    destruct Hcls as (clo & chi & Hcc & Hcls).
    destruct (car13_B regs3 m2 o u c rr clo chi) as (regs4 & m4 & M4 & Harr4 & Cu4 & D11 & K4 & U4 & G4).
    { kept K3 28 C28. } { kept K3 11 C11. } { kept K3 12 C12. } { kept K3 16 C16. } { kept K3 13 C13. } { kept K3 14 C14. } { kept K3 8 C8. }
    { kept K3 19 C19. } { kept K3 20 C20. }
    { exact Hcc. } { exact Hcls. } { lia. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Harr2. } { exact Hsto2. }
    eexists regs4, m4. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M3 | exact M4]|].
    assert (Hck : zlen (chunks 3 c) <= 3).
    { pose proof (chunks_spec 3 c ltac:(change (B ^ Z.of_nat 3) with (2 ^ 84); lia)) as (_ & _ & _ & H). exact H. }
    split.
    { split; [|split; [|split; [|split; [cbn [BnModel.ex]; lia | cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; lia]]]]; cbn [cells BnModel.ex].
      - rewrite zlen_app, Hlenr, <- Eu. exact Cu4.
      - eapply cellN_unch; [exact U4 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; zwidth; lia | exact Ce2].
      - exact Harr4. }
    split; [cbn [cells]; rewrite zlen_app, Hlenr, <- Eu; exact D11|].
    assert (D7 : getr regs3 7%bv = Z_to_bv 64 r) by (kept K3 7 C7). split; [kept K4 7 D7|].
    split.
    { eapply keeps_trans; [eapply keeps_sub_dec; [exact K1|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity. }
    split; [|eapply mem_grows_trans; [exact G2 | exact G4]].
    apply (unch_trans m m2 m4).
    + eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity|cbn; lia].
    + eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]].
      * eexists; split; [left; reflexivity|cbn; lia].
      * eexists; split; [right; left; reflexivity|cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma loop13_B : forall f regs m (o r : Z) (b : bn),
  getr regs 10%bv = Z_to_bv 64 r -> getr regs 11%bv = Z_to_bv 64 (zlen (cells b)) -> getr regs 12%bv = Z_to_bv 64 (o + 4) ->
  getr regs 15%bv = Z_to_bv 64 ((18446744073709551615 - o) / 2 ^ 2) -> getr regs 16%bv = Z_to_bv 64 (18446744073709551611 - o) ->
  getr regs 17%bv = Z_to_bv 64 kFive13 -> getr regs 13%bv = Z_to_bv 64 128 -> getr regs 14%bv = Z_to_bv 64 MASK ->
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA) -> getr regs 20%bv = Z_to_bv 64 SHA ->
  getr regs 6%bv = Z_to_bv 64 25 ->
  13 <= r < 2048 -> r - 13 < 13 * (Z.of_nat f + 1) ->
  bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) -> cells b <> [] ->
  val (cells b) * 5 ^ r < B ^ 124 ->
  APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> objshB m o ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa7ec) m rom) (mkst regs' (Z_to_bv 64 0x0aa8dc) m' rom)
    /\ (let b' := fst (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        let r' := snd (pow13_loop f (r - 13) (mul32 kFive13 b)) in
        bn_at SEGS_B m' o b' /\ getr regs' 11%bv = Z_to_bv 64 (zlen (cells b')) /\ getr regs' 10%bv = Z_to_bv 64 r'
        /\ ok (cells b') /\ norm (cells b') /\ cells b' <> [] /\ ex b' = ex b
        /\ val (cells b') * 5 ^ r' < B ^ 124 /\ 0 <= r' < 13)
    /\ keeps it13B_keep regs regs'
    /\ unch m m' [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m m'.
Proof.
  induction f as [|f IH]; intros regs m o r b R10 R11 R12 R15 R16 R17 R13 R14 R8 R19 R20 R6 Hr Hf Hbn Hok Hn Hne Hv Ho1 Ho2 Ho8 OSH Hsto.
  all: pose proof (cap_bound (cells b) r 1 Hok Hn ltac:(lia) ltac:(lia) Hv ltac:(eapply Z.le_trans; [apply five13_ge | apply Z.pow_le_mono_r; lia])) as Hcap.
  all: destruct b as [l exb]; cbn [cells BnModel.ex] in *.
  all: destruct (it13_B regs m o r l exb R10 R11 R12 R15 R16 R17 R13 R14 R8 R19 R20 ltac:(lia) Hbn Hok Hne ltac:(lia) Ho1 Ho2 Ho8 OSH Hsto)
      as (regs1 & m1 & M1 & Hbn1 & C11 & C7 & K1 & U1 & G1).
  all: pose proof (mul32_spec kFive13 (BN l exb) Hok Hn ltac:(unfold kFive13; lia)) as SP1; cbn zeta in SP1; destruct SP1 as (Hok1 & Hn1 & Hv1 & Hex1).
  all: specialize (Hex1 ltac:(unfold kFive13; lia)).
  all: assert (Hne1 : cells (mul32 kFive13 (BN l exb)) <> []) by (intros HH; apply (proj1 (mul32_cells_nil kFive13 _ ltac:(unfold kFive13; lia))) in HH; exact (Hne HH)).
  all: remember (mul32 kFive13 (BN l exb)) as b1 eqn:Eb1; cbn [BnModel.cells BnModel.ex] in *.
  all: assert (Hv1' : val (cells b1) * 5 ^ (r - 13) < B ^ 124)
        by (rewrite Hv1, kFive13_eq; replace (5 ^ r) with (5 ^ 13 * 5 ^ (r - 13)) in Hv by (rewrite <- Z.pow_add_r by lia; f_equal; lia); lia).
  all: assert (C6 : getr regs1 6%bv = Z_to_bv 64 25) by (kept K1 6 R6).
  all: assert (OSH1 : objshB m1 o) by (eapply (objshB_unch m _ _); [exact U1 | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]).
  - zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7ec; 0x0aa8dc] (SCR [true] [])
      constr:([(7%bv : reg, ZV 32); (6%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x0aa7e4.
    zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
    eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
    cbn [pow13_loop fst snd].
    split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
    split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C11]|].
    split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
  - destruct (Z_le_dec r 25) as [Hle|Hgt].
    + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (13, 25)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7ec; 0x0aa8dc] (SCR [true] [])
        constr:([(7%bv : reg, ZV 32); (6%bv : reg, ZL 25)]) [r] constr:([Some (13, 25)]) regs1 m1 rom 0x0aa7e4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      eexists regs2, m1. split; [eapply msteps_trans; [exact M1 | exact ZM]|].
      cbn [pow13_loop]. replace (r - 13 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split; [|split; [eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity] | split; [exact U1 | exact G1]]].
      split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C11]|].
      split; [etransitivity; [zx_regv ZR|]; f_equal; lia|]. repeat split; auto; lia.
    + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (26, 2047)]) (@nil kcell) (@nil kwin)) 5%nat [0x0aa7ec; 0x0aa8dc] (SCR [false] [])
        constr:([(7%bv : reg, ZV 32); (6%bv : reg, ZL 25)]) [r] constr:([Some (26, 2047)]) regs1 m1 rom 0x0aa7e4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(zx_lia). zx_name regs2.
      assert (K2 : keeps it13B_keep regs regs2) by (eapply keeps_trans; [exact K1 | eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity]).
      cbn [pow13_loop]. replace (r - 13 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G1 | exact Hsto]).
      destruct (IH regs2 m1 o (r - 13) b1) as (regs3 & m3 & M3 & POST & K3 & U3 & G3).
      { etransitivity; [zx_regv ZR|]; f_equal; lia. }
      { etransitivity; [exact (reg_kept _ _ _ _ (11%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C11]. }
      { kept K2 12 R12. } { kept K2 15 R15. } { kept K2 16 R16. } { kept K2 17 R17. } { kept K2 13 R13. } { kept K2 14 R14. } { kept K2 8 R8. }
      { kept K2 19 R19. } { kept K2 20 R20. } { kept K2 6 R6. }
      { lia. } { lia. } { subst b1; exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1'. } { lia. } { lia. } { lia. }
      { exact OSH1. } { exact Hsto1. }
      eexists regs3, m3. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact ZM | exact M3]|].
      subst b1. replace (r - 13 - 13) with (r - 26) in POST by lia. replace (r - 13 - 13) with (r - 26) by lia.
      split; [cbn zeta in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [exact K2 | exact K3]|].
      split; [eapply unch_trans; [exact U1 | exact U3] | eapply mem_grows_trans; [exact G1 | exact G3]].
Qed.
End S.
