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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA AsRtLib AsZX AsZXTac AsZXDefs BnA_lib BnA_mul3 BnA_mul4 BnA_mul5 BnA_au64.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition CS6 : list Z := [3; 4; 21; 22; 23; 24; 25; 26; 27].
(* [comment removed for export] *)
Definition ph_keep : list Z := [1; 2; 3; 4; 10; 11; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma keeps_CS_of6 : forall regs regs' (s0v s1v s2v s3v s4v : word),
  keeps CS6 regs regs' -> getr regs' 2%bv = getr regs 2%bv ->
  s_restored regs' s0v s1v s2v s3v s4v ->
  getr regs 8%bv = s0v -> getr regs 9%bv = s1v -> getr regs 18%bv = s2v -> getr regs 19%bv = s3v -> getr regs 20%bv = s4v ->
  keeps CS regs regs'.
Proof.
  intros regs regs' s0v s1v s2v s3v s4v K H2 (A8 & A9 & A18 & A19 & A20) B8 B9 B18 B19 B20 r Hr. cbn in Hr.
  rewrite <- B8 in A8. rewrite <- B9 in A9. rewrite <- B18 in A18. rewrite <- B19 in A19. rewrite <- B20 in A20.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]];
    [exact H2 | apply K; in_list | apply K; in_list | exact A8 | exact A9 | exact A18 | exact A19 | exact A20 | apply K; cbn; tauto].
Qed.

Ltac zx_pins2 := zx_pins; try (rewrite Z_to_bv_bv_unsigned; reflexivity).

(* [comment removed for export] *)
Definition frame6 (m : word -> option byte) (sp v1 v2 v3 v4 v5 v6 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1)))
    (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2)))
    (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3)))
    (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4)))
    (Z_to_bv 64 (sp + -40)) (word_to_le_bytes 8 (Z_to_bv 64 v5)))
    (Z_to_bv 64 (sp + -48)) (word_to_le_bytes 8 (Z_to_bv 64 v6)).

Lemma frame6_unch : forall m sp v1 v2 v3 v4 v5 v6, 48 <= sp -> sp <= HIE ->
  unch m (frame6 m sp v1 v2 v3 v4 v5 v6) [(sp - 48, sp)].
Proof. intros. unfold frame6. unchx. Qed.

Lemma frame6_unch2 : forall m sp v1 v2 v3 v4 v5 v6 rg, 48 <= sp -> sp <= HIE ->
  unch m (frame6 m sp v1 v2 v3 v4 v5 v6) [rg; (sp - 48, sp)].
Proof.
  intros. eapply unch_widen; [apply frame6_unch; assumption|].
  intros r Hr; cbn in Hr; destruct Hr as [<-|[]]. eexists; split; [right; left; reflexivity | cbn; lia].
Qed.

Lemma frame6_grows : forall m sp v1 v2 v3 v4 v5 v6, mem_grows m (frame6 m sp v1 v2 v3 v4 v5 v6).
Proof. intros. unfold frame6. growsx. Qed.

Lemma frame6_cells : forall m sp (ret s0v s1v s2v s3v s4v : word), 48 <= sp -> sp <= HIE ->
  frame_cells (frame6 m sp (bv_unsigned ret) (bv_unsigned s0v) (bv_unsigned s1v) (bv_unsigned s2v) (bv_unsigned s3v) (bv_unsigned s4v))
              sp ret s0v s1v s2v s3v s4v.
Proof.
  intros m sp ret s0v s1v s2v s3v s4v Hsp1 Hsp2. unfold frame6.
  pose proof (u64_range ret). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
  pose proof (u64_range s3v). pose proof (u64_range s4v).
  repeat split; cellN_go.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Abbreviation big := (Some (0, 18446744073709551615)).
(* [comment removed for export] *)
Abbreviation E_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37);
   (9%bv : reg, ZV 38); (18%bv : reg, ZV 39); (19%bv : reg, ZV 40); (20%bv : reg, ZV 41)].
Abbreviation E_kn := [KC (ZL 0) 0x129ea8 8 (ZL 0x132278); KC (ZL 0) 0x132278 8 (ZL SHA); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 35)].

Ltac E_run ie iu regs m rom o e sp u ret :=
  zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); ie; Some (KHI + 48, HIE); iu; big; big; big; big; big; big]) E_kn [KW (ZV 34) (-48) 0])
    60%nat [0x0aa6ac; 0x0aa7a4] (SCR [] []) constr:(E_pins)
    constr:([o; e; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv);
             bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv)])
    constr:([Some (IMG, HIE - 516); ie; Some (KHI + 48, HIE); iu; big; big; big; big; big; big]) regs m rom 0x0aa610.

Ltac s_rest ZR :=
  repeat split; (etransitivity; [apply ZR|]; match goal with |- ZXA.wd _ (ZXA.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with ee end;
                 unfold ZXA.wd; zx_cbn; apply Z_to_bv_bv_unsigned).

#[using="Type"] Theorem mulpow10_A : forall regs m (o e sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= e < 2048 -> bn_at SEGS_A m o b -> ok (cells b) -> norm (cells b) ->
  val (cells b) * 5 ^ e < B ^ 124 -> ex b + e / 28 < 2 ^ 15 ->
  arr32 SEGS_A m 145344 five_tbl -> tblsh m -> shcells m -> objsh m o ->
  KHI + 48 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 48 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_A m (Z_to_bv 64 (sp - 48)) 48 = true ->
  exists regs' m',
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa610) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_A m' o (mulpow10 e b)
    /\ arr32 SEGS_A m' 145344 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 48, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret b R10 R11 R2 R1 Hret He Hbn Hok Hn Hv Hex Htbl TSH [SC1 SC2] OSH Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj Hsto Hsts.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & H128).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range (getr regs 8%bv)) as Hs0r. pose proof (u64_range (getr regs 9%bv)) as Hs1r.
  pose proof (u64_range (getr regs 18%bv)) as Hs2r. pose proof (u64_range (getr regs 19%bv)) as Hs3r.
  pose proof (u64_range (getr regs 20%bv)) as Hs4r.
  assert (TBL : forall m', unch m m' [(o, o + 516); (sp - 48, sp)] -> arr32 SEGS_A m' 145344 five_tbl).
  { intros m' U. eapply arr32_unch; [exact U | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  assert (TSHu : forall m', unch m m' [(o, o + 516); (sp - 48, sp)] -> tblsh m').
  { intros m' U g Hg. eapply cellN_unch; [exact U | lia | cbn; lia | | exact (TSH g Hg)]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  assert (OSHu : forall m', unch m m' [(o, o + 516); (sp - 48, sp)] -> objsh m' o).
  { intros m' U. eapply (objsh_unch m _ _); [exact U | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]. }
  remember (zlen (cells b)) as u eqn:Eu.
  assert (Hu0 : 0 <= u <= 128) by (pose proof (zlen_nonneg (cells b)); lia).
  hide Hdisj.
  destruct (Z.eq_dec e 0) as [-> | He0].
  { (* [comment removed for export] *)
    E_run (Some (0, 0)) (Some (0, 128)) regs m rom o 0 sp u ret.
    zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_of6; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | | reflexivity ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame6_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
    pose proof (frame6_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame6_grows]]].
    unfold mulpow10. cbn [Z.eqb]. unhide. eapply (bn_at_unch SEGS_A _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  destruct (cells b) as [|x t] eqn:El.
  { (* [comment removed for export] *)
    cbn in Eu. subst u.
    E_run (Some (1, 2047)) (Some (0, 0)) regs m rom o e sp 0 ret.
    zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_A; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_of6; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | | reflexivity ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame6_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
    pose proof (frame6_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame6_grows]]].
    unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
    unhide. eapply (bn_at_unch SEGS_A _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  (* [comment removed for export] *)
  rewrite <- El in *.
  assert (Hne : cells b <> []) by (rewrite El; congruence).
  assert (Hu1 : 1 <= u <= 124).
  { pose proof (cap_bound (cells b) e 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge e ltac:(lia))) as Hc. rewrite El, zlen_cons in Hc. rewrite El, zlen_cons in Eu. pose proof (zlen_nonneg t). lia. }
  (* [comment removed for export] *)
  assert (AB : exists regs2 m2,
    msteps SEGS_A (mkst regs (Z_to_bv 64 0x0aa610) m rom) (mkst regs2 (Z_to_bv 64 0x0aa7a4) m2 rom)
    /\ (let b1 := fst (pow27_loop (Z.to_nat (e / 27)) e b) in
        let r1 := snd (pow27_loop (Z.to_nat (e / 27)) e b) in
        bn_at SEGS_A m2 o b1 /\ getr regs2 12%bv = Z_to_bv 64 r1
        /\ ok (cells b1) /\ norm (cells b1) /\ cells b1 <> [] /\ ex b1 = ex b
        /\ val (cells b1) * 5 ^ r1 < B ^ 124 /\ 0 <= r1 < 27)
    /\ getr regs2 10%bv = Z_to_bv 64 o /\ getr regs2 11%bv = Z_to_bv 64 e /\ getr regs2 15%bv = Z_to_bv 64 MASK
    /\ getr regs2 13%bv = Z_to_bv 64 SHA /\ getr regs2 14%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)
    /\ getr regs2 2%bv = Z_to_bv 64 (sp - 48)
    /\ frame_cells m2 sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv)
    /\ keeps CS6 regs regs2
    /\ unch m m2 [(o, o + 516); (sp - 48, sp)] /\ mem_grows m m2).
  { destruct (Z_lt_dec e 27) as [Hlt | Hge].
    - (* [comment removed for export] *)
      E_run (Some (1, 26)) (Some (1, 124)) regs m rom o e sp u ret.
      zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
      set (m1 := wbytes _ _ _) in ZM.
      pose proof (frame6_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
      pose proof (frame6_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
      pose proof (frame6_cells m sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) ltac:(lia) Hsp2
                    : frame_cells m1 _ _ _ _ _ _ _) as FC1.
      eexists regs1, m1. split; [exact ZM|].
      replace (Z.to_nat (e / 27)) with 0%nat by lia. cbn [pow27_loop fst snd].
      split.
      { split; [unhide; eapply (bn_at_unch SEGS_A _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
        split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [exact FC1|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [exact U | apply frame6_grows].
    - (* [comment removed for export] *)
      E_run (Some (27, 2047)) (Some (1, 124)) regs m rom o e sp u ret.
      zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
      set (m1 := wbytes _ _ _) in ZM.
      pose proof (frame6_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
      pose proof (frame6_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
      pose proof (frame6_cells m sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) ltac:(lia) Hsp2
                    : frame_cells m1 _ _ _ _ _ _ _) as FC1.
      assert (Hbn1 : bn_at SEGS_A m1 o b).
      { unhide. eapply (bn_at_unch SEGS_A _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_A m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [| exact Hsto]; apply frame6_grows).
      destruct (Z.to_nat (e / 27)) as [|f] eqn:Ef; [lia|].
      cbn [pow27_loop]. replace (e <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop27_A rom f regs1 m1 o e b) as (regs2 & m2 & M2 & POST & K2 & U2 & G2);
        try (rewrite <- ?Eu; zx_regv ZR).
      { lia. } { lia. } { exact Hbn1. } { exact Hok. } { exact Hn. } { exact Hne. } { exact Hv. } { lia. } { lia. } { lia. }
      { apply OSHu. exact U. } { exact Hsto1. }
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [destruct POST as (P1 & P2 & P3 & P4); split; [exact P1 | exact (conj P3 P4)] || (cbn zeta in POST |- *; tauto)|].
      split; [etransitivity; [exact (K2 10 ltac:(in_list)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 11 ltac:(in_list)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 15 ltac:(in_list)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 13 ltac:(in_list)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 14 ltac:(in_list)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 2 ltac:(in_list)) | zx_regv ZR]|].
      unhide.
      assert (U2' : unch m1 m2 [(o, o + 516); (sp - 48, sp)]).
      { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
      split; [eapply (frame_cells_unch m1 m2); [exact U2 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact FC1]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]|].
      split; [eapply unch_trans; [exact U | exact U2'] | eapply mem_grows_trans; [| exact G2]; apply frame6_grows]. }
  clear Cu Ce Carr.
  unhide.
  destruct AB as (regs2 & m2 & M2 & POST2 & C10 & C11 & C15 & C13 & C14 & C2 & FC2 & K2 & U2 & G2).
  unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
  destruct (pow27_loop (Z.to_nat (e / 27)) e b) as [b1 r1]. cbn [fst snd] in POST2.
  destruct POST2 as (Hbn1 & C12 & Hok1 & Hn1 & Hne1 & Hex1 & Hv1 & Hr1).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_A m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  pose proof (cap_bound (cells b1) r1 0 Hok1 Hn1 ltac:(lia) ltac:(lia) Hv1 (five0_ge r1 ltac:(lia))) as Hcap1.
  assert (Hu1' : 1 <= zlen (cells b1)) by (destruct (cells b1); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  pose proof (OSHu m2 U2) as OSH2.
  (* [comment removed for export] *)
  assert (CD : exists regs4 m4,
    msteps SEGS_A (mkst regs2 (Z_to_bv 64 0x0aa7a4) m2 rom) (mkst regs4 (Z_to_bv 64 0x0aa8c0) m4 rom)
    /\ (let b2 := fst (pow13_loop 2 r1 b1) in
        let r2 := snd (pow13_loop 2 r1 b1) in
        bn_at SEGS_A m4 o b2 /\ getr regs4 12%bv = Z_to_bv 64 r2
        /\ ok (cells b2) /\ norm (cells b2) /\ cells b2 <> [] /\ ex b2 = ex b
        /\ val (cells b2) * 5 ^ r2 < B ^ 124 /\ 0 <= r2 < 13)
    /\ keeps ph_keep regs2 regs4
    /\ unch m2 m4 [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m2 m4).
  { destruct Hbn1 as (Cu1 & Ce1 & Carr1 & Hexr1 & _).
    destruct (Z_lt_dec r1 13) as [Hlt | Hge].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (0, 12)]) (@nil kcell) (@nil kwin)) 20%nat [0x0aa7e0; 0x0aa8c0] (SCR [] [])
        constr:([(12%bv : reg, ZV 32)]) [r1] constr:([Some (0, 12)]) regs2 m2 rom 0x0aa7a4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [exact ZM|].
      cbn [pow13_loop]. replace (r1 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split.
      { split; [split; [exact Cu1|split; [exact Ce1|split; [exact Carr1|split; [exact Hexr1|lia]]]]|].
        split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - zx_run SEGS_A constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (13, 26); Some (1, 124)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 34)] (@nil kwin))
        30%nat [0x0aa7e0; 0x0aa8c0] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (12%bv : reg, ZV 33); (13%bv : reg, ZL SHA); (14%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA))])
        [o; r1; zlen (cells b1)] constr:([Some (IMG, HIE - 516); Some (13, 26); Some (1, 124)]) regs2 m2 rom 0x0aa7a4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH2 0; kc1 Cu1; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      cbn [pow13_loop]. replace (r1 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop13_A rom 1%nat regs3 m2 o r1 b1) as (regs4 & m4 & M4 & POST & K4 & U4 & G4).
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (15%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C15]. }
      { zx_regv ZR. } { etransitivity; [zx_regv ZR|]; f_equal; lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { cbn. lia. } { split; [exact Cu1|split; [exact Ce1|split; [exact Carr1|split; [exact Hexr1|lia]]]]. }
      { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [cbn [pow13_loop] in POST |- *; rewrite Hex1 in POST; destruct POST as (P1 & P2 & P3 & P4); split; [exact P1 | exact (conj P3 P4)]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
      split; [exact U4 | exact G4]. }
  destruct CD as (regs4 & m4 & M4 & POST4 & K4 & U4 & G4).
  destruct (pow13_loop 2 r1 b1) as [b2 r2]. cbn [fst snd] in POST4.
  destruct POST4 as (Hbn2 & D12 & Hok2 & Hn2 & Hne2 & Hex2 & Hv2 & Hr2).
  assert (U4' : unch m2 m4 [(o, o + 516); (sp - 48, sp)]).
  { eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (Hsto4 : RiscvSemantics.store_ok SEGS_A m4 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G4 | exact Hsto2]).
  assert (U04 : unch m m4 [(o, o + 516); (sp - 48, sp)]) by (eapply unch_trans; [exact U2 | exact U4']).
  (* [comment removed for export] *)
  destruct (tbl_A rom regs4 m4 o r2 b2) as (regs5 & m5 & M5 & POST5 & K5 & U5 & G5).
  { etransitivity; [exact (K4 10 ltac:(in_list)) | exact C10]. }
  { exact D12. }
  { etransitivity; [exact (K4 15 ltac:(in_list)) | exact C15]. }
  { etransitivity; [exact (K4 13 ltac:(in_list)) | exact C13]. }
  { etransitivity; [exact (K4 14 ltac:(in_list)) | exact C14]. }
  { lia. } { exact Hbn2. } { exact Hok2. } { exact Hn2. } { exact Hne2. } { exact Hv2. }
  { apply TBL. exact U04. } { apply TSHu. exact U04. }
  { lia. } { lia. } { exact Ho8. } { apply OSHu. exact U04. } { exact Hsto4. }
  cbn zeta in POST5. destruct POST5 as (Hbn3 & E16 & Hok3 & Hn3 & Hne3 & Hex3 & Hv3).
  remember (if 0 <? r2 then mul32 (kFive r2) b2 else b2) as b3 eqn:Eb3.
  assert (U5' : unch m4 m5 [(o, o + 516); (sp - 48, sp)]).
  { eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (U25 : unch m2 m5 [(o, o + 516); (sp - 48, sp)]) by (eapply unch_trans; [exact U4' | exact U5']).
  assert (U25n : unch m2 m5 [(o, o + 2); (o + 4, o + 516)]) by (eapply unch_trans; [exact U4 | exact U5]).
  assert (U05 : unch m m5 [(o, o + 516); (sp - 48, sp)]) by (eapply unch_trans; [exact U2 | exact U25]).
  assert (Hsto5 : RiscvSemantics.store_ok SEGS_A m5 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G5 | exact Hsto4]).
  pose proof (cap_bound (cells b3) 0 0 Hok3 Hn3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.pow_0_r, Z.mul_1_r; exact Hv3) ltac:(rewrite !Z.pow_0_r; lia)) as Hcap3.
  (* [comment removed for export] *)
  destruct (fin_A rom regs5 m5 o e sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) b3)
    as (regs6 & m6 & M6 & Hbn6 & F2 & F8 & K6 & U6 & G6).
  { etransitivity; [exact (K5 10 ltac:(in_list)) |]. etransitivity; [exact (K4 10 ltac:(in_list)) | exact C10]. }
  { etransitivity; [exact (K5 11 ltac:(in_list)) |]. etransitivity; [exact (K4 11 ltac:(in_list)) | exact C11]. }
  { exact E16. }
  { etransitivity; [exact (K5 15 ltac:(in_list)) |]. etransitivity; [exact (K4 15 ltac:(in_list)) | exact C15]. }
  { etransitivity; [exact (K5 13 ltac:(in_list)) |]. etransitivity; [exact (K4 13 ltac:(in_list)) | exact C13]. }
  { etransitivity; [exact (K5 14 ltac:(in_list)) |]. etransitivity; [exact (K4 14 ltac:(in_list)) | exact C14]. }
  { etransitivity; [exact (K5 2 ltac:(in_list)) |]. etransitivity; [exact (K4 2 ltac:(in_list)) | exact C2]. }
  { eapply (frame_cells_unch m2 m5); [exact U25n | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact FC2]. }
  { exact Hret. } { lia. } { exact Hbn3. } { exact Hok3. } { exact Hne3. } { lia. } { rewrite Hex3. lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { exact Hdisj. } { apply OSHu. exact U05. } { exact Hsto5. }
  assert (U6' : unch m5 m6 [(o, o + 516); (sp - 48, sp)]).
  { eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (UU : unch m m6 [(o, o + 516); (sp - 48, sp)]) by (eapply unch_trans; [exact U05 | exact U6']).
  eexists regs6, m6. split; [eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M4|]; eapply msteps_trans; [exact M5 | exact M6]|].
  split.
  { eapply (keeps_CS_of6 _ _ (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv)); [| rewrite F2, R2; reflexivity | exact F8 | reflexivity ..].
    eapply keeps_trans; [exact K2|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity. }
  split; [subst b3; exact Hbn6|].
  split; [apply TBL; exact UU|].
  split; [exact UU|].
  eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G4|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.

End S.
