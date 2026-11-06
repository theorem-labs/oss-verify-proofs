(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul BnU_mul1 BnU_mul2 BnU_mul3 BnU_mul4.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Definition CS6 : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
(* [comment removed for export] *)
Definition ph_keep : list Z := [1; 2; 3; 4; 10; 11; 13; 22; 23; 24; 25; 26; 27].

Lemma keeps_CS_of6 : forall regs regs' (s0v s1v s2v s3v s4v s5v : word),
  keeps CS6 regs regs' -> getr regs' 2%bv = getr regs 2%bv ->
  s_restored regs' s0v s1v s2v s3v s4v s5v ->
  getr regs 8%bv = s0v -> getr regs 9%bv = s1v -> getr regs 18%bv = s2v -> getr regs 19%bv = s3v -> getr regs 20%bv = s4v -> getr regs 21%bv = s5v ->
  keeps CS regs regs'.
Proof.
  intros regs regs' s0v s1v s2v s3v s4v s5v K H2 (A8 & A9 & A18 & A19 & A20 & A21) B8 B9 B18 B19 B20 B21 r Hr. cbn in Hr.
  rewrite <- B8 in A8. rewrite <- B9 in A9. rewrite <- B18 in A18. rewrite <- B19 in A19. rewrite <- B20 in A20. rewrite <- B21 in A21.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hr]]]]]]]]];
    [exact H2 | apply K; cbn; tauto | apply K; cbn; tauto | exact A8 | exact A9 | exact A18 | exact A19 | exact A20 | exact A21 | apply K; cbn; tauto].
Qed.

Ltac zx_pins2 := zx_pins; try (rewrite Z_to_bv_bv_unsigned; reflexivity).

(* [comment removed for export] *)
Definition frame7 (m : word -> option byte) (sp v1 v2 v3 v4 v5 v6 v7 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1)))
    (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2)))
    (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3)))
    (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4)))
    (Z_to_bv 64 (sp + -40)) (word_to_le_bytes 8 (Z_to_bv 64 v5)))
    (Z_to_bv 64 (sp + -48)) (word_to_le_bytes 8 (Z_to_bv 64 v6)))
    (Z_to_bv 64 (sp + -56)) (word_to_le_bytes 8 (Z_to_bv 64 v7)).

Lemma frame7_unch : forall m sp v1 v2 v3 v4 v5 v6 v7, 64 <= sp -> sp <= 2 ^ 62 ->
  unch m (frame7 m sp v1 v2 v3 v4 v5 v6 v7) [(sp - 64, sp)].
Proof. intros. unfold frame7. unchx. Qed.

Lemma frame7_unch2 : forall m sp v1 v2 v3 v4 v5 v6 v7 rg, 64 <= sp -> sp <= 2 ^ 62 ->
  unch m (frame7 m sp v1 v2 v3 v4 v5 v6 v7) [rg; (sp - 64, sp)].
Proof.
  intros. eapply unch_widen; [apply frame7_unch; assumption|].
  intros r Hr; cbn in Hr; destruct Hr as [<-|[]]. eexists; split; [right; left; reflexivity | cbn; lia].
Qed.

Lemma frame7_grows : forall m sp v1 v2 v3 v4 v5 v6 v7, mem_grows m (frame7 m sp v1 v2 v3 v4 v5 v6 v7).
Proof. intros. unfold frame7. growsx. Qed.

Lemma frame7_cells : forall m sp (ret s0v s1v s2v s3v s4v s5v : word), 64 <= sp -> sp <= 2 ^ 62 ->
  frame_cells (frame7 m sp (bv_unsigned ret) (bv_unsigned s0v) (bv_unsigned s1v) (bv_unsigned s2v) (bv_unsigned s3v) (bv_unsigned s4v) (bv_unsigned s5v))
              sp ret s0v s1v s2v s3v s4v s5v.
Proof.
  intros m sp ret s0v s1v s2v s3v s4v s5v Hsp1 Hsp2. unfold frame7.
  pose proof (u64_range ret). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
  pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v).
  repeat split; match goal with |- cellN _ _ (sp - ?k) _ _ => let k' := eval compute in (- k) in replace (sp - k) with (sp + k') by lia end; cellx.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Abbreviation big := (Some (0, 18446744073709551615)).
(* [comment removed for export] *)
Abbreviation E_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37);
   (9%bv : reg, ZV 38); (18%bv : reg, ZV 39); (19%bv : reg, ZV 40); (20%bv : reg, ZV 41); (21%bv : reg, ZV 42)].

Ltac E_run ie iu regs m rom o e sp u ret :=
  zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); ie; Some (64, 2 ^ 62); iu; big; big; big; big; big; big; big])
                          [KC (ZV 32) 0 2 (ZV 35)] [KW (ZV 34) (-64) 0])
    60%nat [0x36034; 0x360f0] (SCR [] []) constr:(E_pins)
    constr:([o; e; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv);
             bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv)])
    constr:([Some (0, 2 ^ 62); ie; Some (64, 2 ^ 62); iu; big; big; big; big; big; big; big]) regs m rom 0x35fb4.

Ltac s_rest ZR :=
  repeat split; (etransitivity; [apply ZR|]; match goal with |- ZX.wd _ (ZX.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZX.sr_get rs rr) in change (ZX.sr_get rs rr) with ee end;
                 unfold ZX.wd; zx_cbn; apply Z_to_bv_bv_unsigned).

#[using="Type"] Theorem mulpow10_U : forall regs m (o e sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= e < 2048 -> bn_at SEGS_U m o b -> ok (cells b) -> norm (cells b) ->
  val (cells b) * 5 ^ e < B ^ 124 -> ex b + e / 28 < 2 ^ 15 ->
  arr32 SEGS_U m 80520 five_tbl ->
  64 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 64 \/ sp <= o) -> 80568 <= sp - 64 ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 64)) 64 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35fb4) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_U m' o (mulpow10 e b)
    /\ arr32 SEGS_U m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 64, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret b R10 R11 R2 R1 Hret He Hbn Hok Hn Hv Hex Htbl Hsp1 Hsp2 Ho1 Ho2 Hdisj Hspt Hsto Hsts.
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & H128).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range (getr regs 8%bv)) as Hs0r. pose proof (u64_range (getr regs 9%bv)) as Hs1r.
  pose proof (u64_range (getr regs 18%bv)) as Hs2r. pose proof (u64_range (getr regs 19%bv)) as Hs3r.
  pose proof (u64_range (getr regs 20%bv)) as Hs4r. pose proof (u64_range (getr regs 21%bv)) as Hs5r.
  assert (TBL : forall m', unch m m' [(o, o + 516); (sp - 64, sp)] -> arr32 SEGS_U m' 80520 five_tbl).
  { intros m' U. eapply arr32_unch; [exact U | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  remember (zlen (cells b)) as u eqn:Eu.
  assert (Hu0 : 0 <= u <= 128) by (pose proof (zlen_nonneg (cells b)); lia).
  destruct (Z.eq_dec e 0) as [-> | He0].
  { (* [comment removed for export] *)
    E_run (Some (0, 0)) (Some (0, 128)) regs m rom o 0 sp u ret.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_of6; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | | reflexivity ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame7_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) Hsp1 Hsp2 : unch m m1 _) as U0.
    pose proof (frame7_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (o, o + 516) Hsp1 Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame7_grows]]].
    unfold mulpow10. cbn [Z.eqb]. eapply (bn_at_unch SEGS_U _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  destruct (cells b) as [|x t] eqn:El.
  { (* [comment removed for export] *)
    cbn in Eu. subst u.
    E_run (Some (1, 2047)) (Some (0, 0)) regs m rom o e sp 0 ret.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_of6; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; reflexivity | | reflexivity ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame7_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) Hsp1 Hsp2 : unch m m1 _) as U0.
    pose proof (frame7_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (o, o + 516) Hsp1 Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame7_grows]]].
    unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
    eapply (bn_at_unch SEGS_U _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  (* [comment removed for export] *)
  rewrite <- El in *.
  assert (Hne : cells b <> []) by (rewrite El; congruence).
  assert (Hu1 : 1 <= u <= 124).
  { pose proof (cap_bound (cells b) e 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge e ltac:(lia))) as Hc. rewrite El, zlen_cons in Hc. rewrite El, zlen_cons in Eu. pose proof (zlen_nonneg t). lia. }
  (* [comment removed for export] *)
  assert (AB : exists regs2 m2,
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35fb4) m rom) (mkst regs2 (Z_to_bv 64 0x360f0) m2 rom)
    /\ (let b1 := fst (pow27_loop (Z.to_nat (e / 27)) e b) in
        let r1 := snd (pow27_loop (Z.to_nat (e / 27)) e b) in
        bn_at SEGS_U m2 o b1 /\ getr regs2 12%bv = Z_to_bv 64 (zlen (cells b1)) /\ getr regs2 30%bv = Z_to_bv 64 r1
        /\ ok (cells b1) /\ norm (cells b1) /\ cells b1 <> [] /\ ex b1 = ex b
        /\ val (cells b1) * 5 ^ r1 < B ^ 124 /\ 0 <= r1 < 27)
    /\ getr regs2 10%bv = Z_to_bv 64 o /\ getr regs2 11%bv = Z_to_bv 64 e /\ getr regs2 13%bv = Z_to_bv 64 MASK
    /\ getr regs2 2%bv = Z_to_bv 64 (sp - 64)
    /\ frame_cells m2 sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv)
    /\ keeps CS6 regs regs2
    /\ unch m m2 [(o, o + 516); (sp - 64, sp)] /\ mem_grows m m2).
  { destruct (Z_lt_dec e 27) as [Hlt | Hge].
    - (* [comment removed for export] *)
      E_run (Some (1, 26)) (Some (1, 124)) regs m rom o e sp u ret.
      zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
      set (m1 := wbytes _ _ _) in ZM.
      pose proof (frame7_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) Hsp1 Hsp2 : unch m m1 _) as U0.
      pose proof (frame7_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (o, o + 516) Hsp1 Hsp2 : unch m m1 _) as U.
      pose proof (frame7_cells m sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) Hsp1 Hsp2
                    : frame_cells m1 _ _ _ _ _ _ _ _) as FC1.
      eexists regs1, m1. split; [exact ZM|].
      replace (Z.to_nat (e / 27)) with 0%nat by lia. cbn [pow27_loop fst snd].
      split.
      { split; [eapply (bn_at_unch SEGS_U _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
        split; [rewrite <- Eu; zx_regv ZR|]. split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [exact FC1|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [exact U | apply frame7_grows].
    - (* [comment removed for export] *)
      E_run (Some (27, 2047)) (Some (1, 124)) regs m rom o e sp u ret.
      zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 Cu; exact I) ltac:(kw1 Hsts; exact I) ltac:(zwidth; lia). zx_name regs1.
      set (m1 := wbytes _ _ _) in ZM.
      pose proof (frame7_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) Hsp1 Hsp2 : unch m m1 _) as U0.
      pose proof (frame7_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (o, o + 516) Hsp1 Hsp2 : unch m m1 _) as U.
      pose proof (frame7_cells m sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) Hsp1 Hsp2
                    : frame_cells m1 _ _ _ _ _ _ _ _) as FC1.
      assert (Hbn1 : bn_at SEGS_U m1 o b).
      { eapply (bn_at_unch SEGS_U _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_U m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [| exact Hsto]; apply frame7_grows).
      destruct (Z.to_nat (e / 27)) as [|f] eqn:Ef; [lia|].
      cbn [pow27_loop]. replace (e <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop27_U rom f regs1 m1 o e ((18446744073709551615 - o) / 2 ^ 2) b) as (regs2 & m2 & M2 & POST & K2 & U2 & G2);
        try (rewrite <- ?Eu; zx_regv ZR).
      { lia. } { lia. } { lia. } { exact Hbn1. } { exact Hok. } { exact Hn. } { exact Hne. } { exact Hv. } { lia. } { lia. } { exact Hsto1. }
      eexists regs2, m2. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split; [exact POST|].
      split; [etransitivity; [exact (K2 10 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 11 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 13 ltac:(cbn; tauto)) | zx_regv ZR]|].
      split; [etransitivity; [exact (K2 2 ltac:(cbn; tauto)) | zx_regv ZR]|].
      assert (U2' : unch m1 m2 [(o, o + 516); (sp - 64, sp)]).
      { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
      split; [eapply (frame_cells_unch m1 m2); [exact U2 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact FC1]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity]|].
      split; [eapply unch_trans; [exact U | exact U2'] | eapply mem_grows_trans; [| exact G2]; apply frame7_grows]. }
  clear Cu Ce Carr.
  destruct AB as (regs2 & m2 & M2 & POST2 & C10 & C11 & C13 & C2 & FC2 & K2 & U2 & G2).
  unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
  destruct (pow27_loop (Z.to_nat (e / 27)) e b) as [b1 r1]. cbn [fst snd] in POST2.
  destruct POST2 as (Hbn1 & C12 & C30 & Hok1 & Hn1 & Hne1 & Hex1 & Hv1 & Hr1).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_U m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  pose proof (cap_bound (cells b1) r1 0 Hok1 Hn1 ltac:(lia) ltac:(lia) Hv1 (five0_ge r1 ltac:(lia))) as Hcap1.
  assert (Hu1' : 1 <= zlen (cells b1)) by (destruct (cells b1); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  (* [comment removed for export] *)
  assert (CD : exists regs4 m4,
    msteps SEGS_U (mkst regs2 (Z_to_bv 64 0x360f0) m2 rom) (mkst regs4 (Z_to_bv 64 0x361cc) m4 rom)
    /\ (let b2 := fst (pow13_loop 2 r1 b1) in
        let r2 := snd (pow13_loop 2 r1 b1) in
        bn_at SEGS_U m4 o b2 /\ getr regs4 12%bv = Z_to_bv 64 (zlen (cells b2)) /\ getr regs4 30%bv = Z_to_bv 64 r2
        /\ ok (cells b2) /\ norm (cells b2) /\ cells b2 <> [] /\ ex b2 = ex b
        /\ val (cells b2) * 5 ^ r2 < B ^ 124 /\ 0 <= r2 < 13)
    /\ keeps ph_keep regs2 regs4
    /\ unch m2 m4 [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m2 m4).
  { destruct (Z_lt_dec r1 13) as [Hlt | Hge].
    - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 12)]) (@nil kcell) (@nil kwin)) 20%nat [0x36128; 0x361cc] (SCR [] [])
        constr:([(30%bv : reg, ZV 32)]) [r1] constr:([Some (0, 12)]) regs2 m2 rom 0x360f0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      eexists regs3, m2. split; [exact ZM|].
      cbn [pow13_loop]. replace (r1 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split.
      { split; [exact Hbn1|]. split; [etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]|].
        split; [zx_regv ZR|]. repeat split; auto; lia. }
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [apply unch_refl | apply mem_grows_refl].
    - zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (13, 26)]) (@nil kcell) (@nil kwin)) 20%nat [0x36128; 0x361cc] (SCR [] [])
        constr:([(10%bv : reg, ZV 32); (30%bv : reg, ZV 33)]) [o; r1] constr:([Some (0, 2 ^ 62); Some (13, 26)]) regs2 m2 rom 0x360f0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      cbn [pow13_loop]. replace (r1 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop13_U rom 1%nat regs3 m2 o r1 ((18446744073709551615 - o) / 2 ^ 2) b1) as (regs4 & m4 & M4 & POST & K4 & U4 & G4).
      { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (12%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C12]. }
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { etransitivity; [exact (reg_kept _ _ _ _ (13%bv : reg) ZR ltac:(vm_compute; reflexivity)) | exact C13]. }
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { cbn. lia. } { exact Hbn1. } { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1. } { lia. } { lia. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [cbn [pow13_loop] in POST |- *; rewrite Hex1 in POST; exact POST|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
      split; [exact U4 | exact G4]. }
  destruct CD as (regs4 & m4 & M4 & POST4 & K4 & U4 & G4).
  destruct (pow13_loop 2 r1 b1) as [b2 r2]. cbn [fst snd] in POST4.
  destruct POST4 as (Hbn2 & D12 & D30 & Hok2 & Hn2 & Hne2 & Hex2 & Hv2 & Hr2).
  assert (U4' : unch m2 m4 [(o, o + 516); (sp - 64, sp)]).
  { eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (Hsto4 : RiscvSemantics.store_ok SEGS_U m4 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G4 | exact Hsto2]).
  (* [comment removed for export] *)
  destruct (tbl_U rom regs4 m4 o r2 b2) as (regs5 & m5 & M5 & POST5 & K5 & U5 & G5).
  { etransitivity; [exact (K4 10 ltac:(cbn; tauto)) | exact C10]. }
  { exact D12. } { exact D30. }
  { etransitivity; [exact (K4 13 ltac:(cbn; tauto)) | exact C13]. }
  { lia. } { exact Hbn2. } { exact Hok2. } { exact Hn2. } { exact Hne2. } { exact Hv2. }
  { apply TBL. eapply unch_trans; [exact U2 | exact U4']. }
  { lia. } { lia. } { exact Hsto4. }
  cbn zeta in POST5. destruct POST5 as (Hbn3 & E12 & Hok3 & Hn3 & Hne3 & Hex3 & Hv3).
  remember (if 0 <? r2 then mul32 (kFive r2) b2 else b2) as b3 eqn:Eb3.
  assert (U5' : unch m4 m5 [(o, o + 516); (sp - 64, sp)]).
  { eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (U25 : unch m2 m5 [(o, o + 516); (sp - 64, sp)]) by (eapply unch_trans; [exact U4' | exact U5']).
  assert (U25n : unch m2 m5 [(o, o + 2); (o + 4, o + 516)]) by (eapply unch_trans; [exact U4 | exact U5]).
  assert (Hsto5 : RiscvSemantics.store_ok SEGS_U m5 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G5 | exact Hsto4]).
  pose proof (cap_bound (cells b3) 0 0 Hok3 Hn3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.pow_0_r, Z.mul_1_r; exact Hv3) ltac:(rewrite !Z.pow_0_r; lia)) as Hcap3.
  (* [comment removed for export] *)
  destruct (fin_U rom regs5 m5 o e sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) b3)
    as (regs6 & m6 & M6 & Hbn6 & F2 & F8 & K6 & U6 & G6).
  { etransitivity; [exact (K5 10 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 10 ltac:(cbn; tauto)) | exact C10]. }
  { etransitivity; [exact (K5 11 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 11 ltac:(cbn; tauto)) | exact C11]. }
  { exact E12. }
  { etransitivity; [exact (K5 13 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 13 ltac:(cbn; tauto)) | exact C13]. }
  { etransitivity; [exact (K5 2 ltac:(cbn; tauto)) |]. etransitivity; [exact (K4 2 ltac:(cbn; tauto)) | exact C2]. }
  { eapply (frame_cells_unch m2 m5); [exact U25n | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact FC2]. }
  { exact Hret. } { lia. } { exact Hbn3. } { exact Hok3. } { exact Hne3. } { lia. } { rewrite Hex3. lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Hdisj. } { exact Hsto5. }
  assert (U6' : unch m5 m6 [(o, o + 516); (sp - 64, sp)]).
  { eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (UU : unch m m6 [(o, o + 516); (sp - 64, sp)]).
  { eapply unch_trans; [exact U2|]. eapply unch_trans; [exact U25 | exact U6']. }
  eexists regs6, m6. split; [eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M4|]; eapply msteps_trans; [exact M5 | exact M6]|].
  split.
  { eapply (keeps_CS_of6 _ _ (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv)); [| rewrite F2, R2; reflexivity | exact F8 | reflexivity ..].
    eapply keeps_trans; [exact K2|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|]. eapply keeps_sub_dec; [exact K6|]; vm_compute; reflexivity. }
  split; [subst b3; exact Hbn6|].
  split; [apply TBL; exact UU|].
  split; [exact UU|].
  eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G4|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.

End S.
