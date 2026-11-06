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
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LibIfaceA LibIfaceB AsRtLib AsRtLibB AsZX AsZXTac AsZXDefs BnA_lib BnA_au64 BnA_mul3
 BnB_lib BnB_mul3 BnB_mul4 BnB_mul6.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZXA BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac kept K n H := etransitivity; [exact (K n ltac:(in_list)) | exact H].
Ltac zx_pins2 := zx_pins; try (rewrite Z_to_bv_bv_unsigned; reflexivity).

(* [comment removed for export] *)
Lemma k27_intro : forall m, ro_ok SEGS_B RO_B m -> cellN SEGS_B m 66408 8 7450580596923828125.
Proof. intros m RO. eapply cellN_ro_B; [exact RO | vm_compute; reflexivity | vm_compute; reflexivity | lia | cbn; lia]. Qed.

(* [comment removed for export] *)
Definition frame8 (m : word -> option byte) (sp v1 v2 v3 v4 v5 v6 v7 v8 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (sp + -8)) (word_to_le_bytes 8 (Z_to_bv 64 v1)))
    (Z_to_bv 64 (sp + -16)) (word_to_le_bytes 8 (Z_to_bv 64 v2)))
    (Z_to_bv 64 (sp + -24)) (word_to_le_bytes 8 (Z_to_bv 64 v3)))
    (Z_to_bv 64 (sp + -32)) (word_to_le_bytes 8 (Z_to_bv 64 v4)))
    (Z_to_bv 64 (sp + -40)) (word_to_le_bytes 8 (Z_to_bv 64 v5)))
    (Z_to_bv 64 (sp + -48)) (word_to_le_bytes 8 (Z_to_bv 64 v6)))
    (Z_to_bv 64 (sp + -56)) (word_to_le_bytes 8 (Z_to_bv 64 v7)))
    (Z_to_bv 64 (sp + -64)) (word_to_le_bytes 8 (Z_to_bv 64 v8)).

Lemma frame8_unch : forall m sp v1 v2 v3 v4 v5 v6 v7 v8, 80 <= sp -> sp <= HIE ->
  unch m (frame8 m sp v1 v2 v3 v4 v5 v6 v7 v8) [(sp - 80, sp)].
Proof. intros. unfold frame8. unchx. Qed.

Lemma frame8_unch2 : forall m sp v1 v2 v3 v4 v5 v6 v7 v8 rg, 80 <= sp -> sp <= HIE ->
  unch m (frame8 m sp v1 v2 v3 v4 v5 v6 v7 v8) [rg; (sp - 80, sp)].
Proof.
  intros. eapply unch_widen; [apply frame8_unch; assumption|].
  intros r Hr; cbn in Hr; destruct Hr as [<-|[]]. eexists; split; [right; left; reflexivity | cbn; lia].
Qed.

Lemma frame8_grows : forall m sp v1 v2 v3 v4 v5 v6 v7 v8, mem_grows m (frame8 m sp v1 v2 v3 v4 v5 v6 v7 v8).
Proof. intros. unfold frame8. growsx. Qed.

Lemma frame8_cells : forall m sp (ret s0v s1v s2v s3v s4v s5v s6v : word), 80 <= sp -> sp <= HIE ->
  frame_cellsB (frame8 m sp (bv_unsigned ret) (bv_unsigned s0v) (bv_unsigned s1v) (bv_unsigned s2v) (bv_unsigned s3v) (bv_unsigned s4v)
                           (bv_unsigned s5v) (bv_unsigned s6v))
               sp (bv_unsigned ret) (bv_unsigned s0v) (bv_unsigned s1v) (bv_unsigned s2v) (bv_unsigned s3v) (bv_unsigned s4v)
                  (bv_unsigned s5v) (bv_unsigned s6v).
Proof.
  intros m sp ret s0v s1v s2v s3v s4v s5v s6v Hsp1 Hsp2. unfold frame8, frame_cellsB.
  pose proof (u64_range ret). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
  pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v). pose proof (u64_range s6v).
  repeat split; cellN_go.
Qed.

Lemma keeps_CS_ofB : forall regs regs' (v8 v9 v18 v19 v20 v21 v22 : Z),
  keeps finB_keep regs regs' -> getr regs' 2%bv = getr regs 2%bv ->
  s_restoredB regs' v8 v9 v18 v19 v20 v21 v22 ->
  getr regs 8%bv = Z_to_bv 64 v8 -> getr regs 9%bv = Z_to_bv 64 v9 -> getr regs 18%bv = Z_to_bv 64 v18 -> getr regs 19%bv = Z_to_bv 64 v19 ->
  getr regs 20%bv = Z_to_bv 64 v20 -> getr regs 21%bv = Z_to_bv 64 v21 -> getr regs 22%bv = Z_to_bv 64 v22 ->
  keeps CS regs regs'.
Proof.
  intros regs regs' v8 v9 v18 v19 v20 v21 v22 K H2 (A8 & A9 & A18 & A19 & A20 & A21 & A22) B8 B9 B18 B19 B20 B21 B22 r Hr. unfold CS in Hr. cbn in Hr.
  rewrite <- B8 in A8. rewrite <- B9 in A9. rewrite <- B18 in A18. rewrite <- B19 in A19. rewrite <- B20 in A20. rewrite <- B21 in A21. rewrite <- B22 in A22.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
    first [exact H2 | exact A8 | exact A9 | exact A18 | exact A19 | exact A20 | exact A21 | exact A22 | apply K; in_list].
Qed.

(* [comment removed for export] *)
Lemma s_frame_unch : forall m m' sp rs rav v8 v9 v18 v19 v20 v21 v22,
  unch m m' rs -> KHI + 64 <= sp -> sp <= HIE -> (forall r, In r rs -> snd r <= sp - 64 \/ sp <= fst r) ->
  frame_cellsB m sp rav v8 v9 v18 v19 v20 v21 v22 -> frame_cellsB m' sp rav v8 v9 v18 v19 v20 v21 v22.
Proof. intros. eapply frame_cellsB_unch; eauto. Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

Abbreviation big := (Some (0, 18446744073709551615)).
(* [comment removed for export] *)
Abbreviation E_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (2%bv : reg, ZV 34); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37);
   (9%bv : reg, ZV 38); (18%bv : reg, ZV 39); (19%bv : reg, ZV 40); (20%bv : reg, ZV 41); (21%bv : reg, ZV 42); (22%bv : reg, ZV 43)].
Abbreviation E_kn := [KC (ZL 0) 0x12a380 8 (ZL 0x132738); KC (ZL 0) 0x132738 8 (ZL SHA); KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 35);
   KC (ZL 0) 66408 8 (ZL 7450580596923828125)].

Ltac E_run ie iu stops regs m rom o e sp u ret :=
  zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); ie; Some (KHI + 80, HIE); iu; big; big; big; big; big; big; big; big]) E_kn [KW (ZV 34) (-64) 0])
    60%nat stops (SCR [] []) constr:(E_pins)
    constr:([o; e; sp; u; bv_unsigned ret; bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv);
             bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv); bv_unsigned (getr regs 22%bv)])
    constr:([Some (IMG, HIE - 516); ie; Some (KHI + 80, HIE); iu; big; big; big; big; big; big; big; big]) regs m rom 0x0aa708.

Ltac s_rest ZR :=
  repeat split; (etransitivity; [apply ZR|]; match goal with |- ZXA.wd _ (ZXA.sr_get ?rs ?rr) = _ => let ee := eval vm_compute in (ZXA.sr_get rs rr) in change (ZXA.sr_get rs rr) with ee end;
                 unfold ZXA.wd; zx_cbn; reflexivity).

Abbreviation FR8 m sp regs ret := (frame8 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv))).

#[using="Type"] Theorem mulpow10_B : forall regs m (o e sp : Z) (ret : word) (b : bn),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 e -> getr regs 2%bv = Z_to_bv 64 sp ->
  getr regs 1%bv = ret -> ret_ok ret ->
  0 <= e < 2048 -> bn_at SEGS_B m o b -> ok (cells b) -> norm (cells b) ->
  val (cells b) * 5 ^ e < B ^ 124 -> ex b + e / 28 < 2 ^ 15 ->
  arr32 SEGS_B m 145376 five_tbl -> tblshB m -> shcellsB m -> objshB m o -> cellN SEGS_B m 66408 8 7450580596923828125 ->
  KHI + 80 <= sp -> sp <= HIE -> APP o 516 -> o + 516 <= HIE -> o mod 8 = 0 -> (o + 516 <= sp - 80 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_B m (Z_to_bv 64 (sp - 80)) 80 = true ->
  exists regs' m',
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa708) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_B m' o (mulpow10 e b)
    /\ arr32 SEGS_B m' 145376 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 80, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o e sp ret b R10 R11 R2 R1 Hret He Hbn Hok Hn Hv Hex Htbl TSH SC OSH K27C Hsp1 Hsp2 Ho1 Ho2 Ho8 Hdisj Hsto Hsts.
  pose proof SC as [SC1 SC2].
  pose proof Hbn as Hbn0. destruct Hbn as (Cu & Ce & Carr & Hexr & H128).
  pose proof (u64_range ret) as Hrr. pose proof (u64_range (getr regs 8%bv)) as Hs0r. pose proof (u64_range (getr regs 9%bv)) as Hs1r.
  pose proof (u64_range (getr regs 18%bv)) as Hs2r. pose proof (u64_range (getr regs 19%bv)) as Hs3r.
  pose proof (u64_range (getr regs 20%bv)) as Hs4r. pose proof (u64_range (getr regs 21%bv)) as Hs5r. pose proof (u64_range (getr regs 22%bv)) as Hs6r.
  assert (TBL : forall m', unch m m' [(o, o + 516); (sp - 80, sp)] -> arr32 SEGS_B m' 145376 five_tbl).
  { intros m' U. eapply arr32_unch; [exact U | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  assert (TSHu : forall m', unch m m' [(o, o + 516); (sp - 80, sp)] -> tblshB m').
  { intros m' U g Hg. eapply cellN_unch; [exact U | lia | cbn; lia | | exact (TSH g Hg)]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  assert (OSHu : forall m', unch m m' [(o, o + 516); (sp - 80, sp)] -> objshB m' o).
  { intros m' U. eapply (objshB_unch m _ _); [exact U | intros r0 [<-|[<-|[]]]; cbn; lia | lia | lia | exact OSH]. }
  assert (SCu : forall m', unch m m' [(o, o + 516); (sp - 80, sp)] -> shcellsB m').
  { intros m' U. eapply shcellsB_unch; [exact U | intros r0 [<-|[<-|[]]]; cbn; lia | exact SC]. }
  remember (zlen (cells b)) as u eqn:Eu.
  assert (Hu0 : 0 <= u <= 128) by (pose proof (zlen_nonneg (cells b)); lia).
  hide Hdisj.
  destruct (Z.eq_dec e 0) as [-> | He0].
  { (* [comment removed for export] *)
    E_run (Some (0, 0)) (Some (0, 128)) (@nil Z) regs m rom o 0 sp u ret.
    zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; kc1 K27C; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_ofB; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; f_equal; lia | | symmetry; apply Z_to_bv_bv_unsigned ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame8_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
    pose proof (frame8_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame8_grows]]].
    unfold mulpow10. cbn [Z.eqb]. unhide. eapply (bn_at_unch SEGS_B _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  destruct (cells b) as [|x t] eqn:El.
  { (* [comment removed for export] *)
    cbn in Eu. subst u.
    E_run (Some (1, 2047)) (Some (0, 0)) (@nil Z) regs m rom o e sp 0 ret.
    zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; kc1 K27C; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as H; rewrite H; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_B; [exact R1' | exact Hret]|].
    split.
    { eapply keeps_CS_ofB; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | zx_reg ZR (2%bv : reg) as H; rewrite H, R2; f_equal; lia | | symmetry; apply Z_to_bv_bv_unsigned ..]. s_rest ZR. }
    set (m1 := wbytes _ _ _).
    pose proof (frame8_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
    pose proof (frame8_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                  (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
    split; [|split; [apply TBL; exact U | split; [exact U | apply frame8_grows]]].
    unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
    unhide. eapply (bn_at_unch SEGS_B _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
  (* [comment removed for export] *)
  rewrite <- El in *.
  assert (Hne : cells b <> []) by (rewrite El; congruence).
  assert (Hu1 : 1 <= u <= 124).
  { pose proof (cap_bound (cells b) e 0 Hok Hn ltac:(lia) ltac:(lia) Hv (five0_ge e ltac:(lia))) as Hc. rewrite El, zlen_cons in Hc. rewrite El, zlen_cons in Eu. pose proof (zlen_nonneg t). lia. }
  (* [comment removed for export] *)
  assert (AB : exists regs2 m2 p2,
    msteps SEGS_B (mkst regs (Z_to_bv 64 0x0aa708) m rom) (mkst regs2 (Z_to_bv 64 p2) m2 rom)
    /\ (let b1 := fst (pow27_loop (Z.to_nat (e / 27)) e b) in
        let r1 := snd (pow27_loop (Z.to_nat (e / 27)) e b) in
        bn_at SEGS_B m2 o b1 /\ getr regs2 10%bv = Z_to_bv 64 r1
        /\ ok (cells b1) /\ norm (cells b1) /\ cells b1 <> [] /\ ex b1 = ex b
        /\ val (cells b1) * 5 ^ r1 < B ^ 124 /\ 0 <= r1 < 27
        /\ ((p2 = 0x0aa7a4 /\ 13 <= r1) \/ (p2 = 0x0aa8dc /\ r1 < 13)))
    /\ getr regs2 8%bv = Z_to_bv 64 o /\ getr regs2 9%bv = Z_to_bv 64 e /\ getr regs2 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)
    /\ getr regs2 20%bv = Z_to_bv 64 SHA /\ getr regs2 2%bv = Z_to_bv 64 (sp - 64)
    /\ frame_cellsB m2 sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                       (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv))
    /\ keeps finB_keep regs regs2
    /\ unch m m2 [(o, o + 516); (sp - 80, sp)] /\ mem_grows m m2).
  { destruct (Z_lt_dec e 27) as [Hlt | Hge].
    - (* [comment removed for export] *)
      destruct (Z_lt_dec e 13) as [Hlt13 | Hge13].
      + E_run (Some (1, 12)) (Some (1, 124)) [0x0aa8dc] regs m rom o e sp u ret.
        zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; kc1 K27C; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
        set (m1 := wbytes _ _ _) in ZM.
        eexists regs1, m1, 0x0aa8dc. split; [exact ZM|].
        replace (Z.to_nat (e / 27)) with 0%nat by lia. cbn [pow27_loop fst snd].
        pose proof (frame8_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                      (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
        pose proof (frame8_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                      (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
        split.
        { split; [unhide; eapply (bn_at_unch SEGS_B _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
          split; [zx_regv ZR|]. repeat split; auto; try lia. all: right; split; [reflexivity | lia]. }
        split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        split; [apply frame8_cells; lia|].
        split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
        split; [exact U | apply frame8_grows].
      + E_run (Some (13, 26)) (Some (1, 124)) [0x0aa7a4] regs m rom o e sp u ret.
        zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; kc1 K27C; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
        set (m1 := wbytes _ _ _) in ZM.
        eexists regs1, m1, 0x0aa7a4. split; [exact ZM|].
        replace (Z.to_nat (e / 27)) with 0%nat by lia. cbn [pow27_loop fst snd].
        pose proof (frame8_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                      (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
        pose proof (frame8_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                      (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
        split.
        { split; [unhide; eapply (bn_at_unch SEGS_B _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]; intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia|].
          split; [zx_regv ZR|]. repeat split; auto; try lia. all: left; split; [reflexivity | lia]. }
        split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
        split; [apply frame8_cells; lia|].
        split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
        split; [exact U | apply frame8_grows].
    - (* [comment removed for export] *)
      E_run (Some (27, 2047)) (Some (1, 124)) [0x0aa774] regs m rom o e sp u ret.
      zx_use2 ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(kc1 SC1; kc1 SC2; kcsh OSH 0; kc1 Cu; kc1 K27C; exact I) ltac:(kw1 Hsts; exact I) ltac:(unhide; zx_scs ltac:(lia)). zx_name regs1.
      set (m1 := wbytes _ _ _) in ZM.
      zx_reg ZR (8%bv : reg) as A8. zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (19%bv : reg) as A19. zx_reg ZR (20%bv : reg) as A20. zx_reg ZR (2%bv : reg) as A2.
      zx_reg ZR (10%bv : reg) as A10. zx_reg ZR (18%bv : reg) as A18. zx_reg ZR (21%bv : reg) as A21.
      assert (K1 : keeps finB_keep regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
      rename ZM into M1. clear ZE ZR ZF.
      pose proof (frame8_unch m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) ltac:(lia) Hsp2 : unch m m1 _) as U0.
      pose proof (frame8_unch2 m sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                    (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (o, o + 516) ltac:(lia) Hsp2 : unch m m1 _) as U.
      assert (FC1 : frame_cellsB m1 sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                       (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv))) by (apply frame8_cells; lia).
      assert (Hbn1 : bn_at SEGS_B m1 o b).
      { unhide. eapply (bn_at_unch SEGS_B _ _ o _ _ U0); [lia | cbn; lia | | exact Hbn0]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
      assert (Hsto1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [| exact Hsto]; apply frame8_grows).
      assert (Hsts1 : RiscvSemantics.store_ok SEGS_B m1 (Z_to_bv 64 (sp - 64 - 16)) 16 = true).
      { eapply store_ok_grows; [apply frame8_grows|]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
      destruct (Z.to_nat (e / 27)) as [|f] eqn:Ef; [lia|].
      cbn [pow27_loop]. replace (e <? 27) with false by (symmetry; apply Z.ltb_ge; lia).
      unhide.
      destruct (loop27_B rom f regs1 m1 o e (sp - 64) b) as (regs2 & m2 & M2 & POST & K2 & U2 & G2).
      { exact A10. } { exact A8. } { exact A18. } { exact A21. } { rewrite A2. f_equal; lia. }
      { lia. } { lia. } { exact Hbn1. } { exact Hok. } { exact Hn. } { exact Hne. } { exact Hv. } { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { lia. }
      { apply SCu. exact U. } { apply OSHu. exact U. } { exact Hsto1. } { exact Hsts1. }
      cbn zeta in POST. destruct POST as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
      remember (fst (pow27_loop f (e - 27) (mul64 kFive27_lo kFive27_hi b))) as b1 eqn:Eb1.
      remember (snd (pow27_loop f (e - 27) (mul64 kFive27_lo kFive27_hi b))) as r1 eqn:Er1.
      assert (U2' : unch m1 m2 [(o, o + 516); (sp - 80, sp)]).
      { eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]];
          [eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [left; reflexivity|cbn; lia] | eexists; split; [right; left; reflexivity|cbn; lia]]. }
      assert (FC2 : frame_cellsB m2 sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                       (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv))).
      { eapply s_frame_unch; [exact U2 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia | exact FC1]. }
      assert (B8 : getr regs2 8%bv = Z_to_bv 64 o) by (kept K2 8 A8).
      assert (B9 : getr regs2 9%bv = Z_to_bv 64 e) by (kept K2 9 A9).
      assert (B19 : getr regs2 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K2 19 A19).
      assert (B20 : getr regs2 20%bv = Z_to_bv 64 SHA) by (kept K2 20 A20).
      assert (A2' : getr regs1 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite A2; f_equal; lia).
      assert (B2 : getr regs2 2%bv = Z_to_bv 64 (sp - 64)) by (kept K2 2 A2').
      (* [comment removed for export] *)
      assert (T13 : exists regs3 p2, msteps SEGS_B (mkst regs2 (Z_to_bv 64 0x0aa78c) m2 rom) (mkst regs3 (Z_to_bv 64 p2) m2 rom)
                /\ getr regs3 10%bv = Z_to_bv 64 r1 /\ ((p2 = 0x0aa7a4 /\ 13 <= r1) \/ (p2 = 0x0aa8dc /\ r1 < 13))
                /\ keeps [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs2 regs3).
      { destruct (Z_lt_dec r1 13) as [Hlt13 | Hge13].
        + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (0, 12)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa7a4; 0x0aa8dc] (SCR [] [])
            constr:([(10%bv : reg, ZV 32)]) [r1] constr:([Some (0, 12)]) regs2 m2 rom 0x0aa78c.
          zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
          eexists regs3, 0x0aa8dc. split; [exact ZM|]. split; [zx_regv ZR|]. split; [right; split; [reflexivity | lia]|].
          eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity.
        + zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (13, 26)]) (@nil kcell) (@nil kwin)) 10%nat [0x0aa7a4; 0x0aa8dc] (SCR [] [])
            constr:([(10%bv : reg, ZV 32)]) [r1] constr:([Some (13, 26)]) regs2 m2 rom 0x0aa78c.
          zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
          eexists regs3, 0x0aa7a4. split; [exact ZM|]. split; [zx_regv ZR|]. split; [left; split; [reflexivity | lia]|].
          eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity. }
      destruct T13 as (regs3 & p2 & M3 & C10 & Hp2 & K3).
      eexists regs3, m2, p2. split; [eapply msteps_trans; [exact M1|]; eapply msteps_trans; [exact M2 | exact M3]|].
      split.
      { subst b1 r1. split; [exact P1|]. split; [exact C10|]. repeat split; auto; lia. }
      split; [kept K3 8 B8|]. split; [kept K3 9 B9|]. split; [kept K3 19 B19|]. split; [kept K3 20 B20|]. split; [kept K3 2 B2|].
      split; [exact FC2|].
      split; [eapply keeps_trans; [exact K1|]; eapply keeps_trans; [eapply keeps_sub_dec; [exact K2|]; vm_compute; reflexivity | eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity]|].
      split; [eapply unch_trans; [exact U | exact U2'] | eapply mem_grows_trans; [apply frame8_grows | exact G2]]. }
  clear Cu Ce Carr.
  unhide.
  destruct AB as (regs2 & m2 & p2 & M2 & POST2 & C8 & C9 & C19 & C20 & C2 & FC2 & K2 & U2 & G2).
  unfold mulpow10. replace (e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite El.
  destruct (pow27_loop (Z.to_nat (e / 27)) e b) as [b1 r1]. cbn [fst snd] in POST2.
  destruct POST2 as (Hbn1 & C10 & Hok1 & Hn1 & Hne1 & Hex1 & Hv1 & Hr1 & Hp2).
  assert (Hsto2 : RiscvSemantics.store_ok SEGS_B m2 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G2 | exact Hsto]).
  assert (Hsts2 : RiscvSemantics.store_ok SEGS_B m2 (Z_to_bv 64 (sp - 64 - 16)) 16 = true).
  { eapply store_ok_grows; [exact G2|]. eapply sc_store_in; [exact Hsts|]. zwidth. lia. }
  pose proof (cap_bound (cells b1) r1 0 Hok1 Hn1 ltac:(lia) ltac:(lia) Hv1 (five0_ge r1 ltac:(lia))) as Hcap1.
  assert (Hu1' : 1 <= zlen (cells b1)) by (destruct (cells b1); [congruence|rewrite zlen_cons; pose proof (zlen_nonneg l); lia]).
  pose proof (OSHu m2 U2) as OSH2.
  (* [comment removed for export] *)
  assert (CD : exists regs4 m4,
    msteps SEGS_B (mkst regs2 (Z_to_bv 64 p2) m2 rom) (mkst regs4 (Z_to_bv 64 0x0aa8dc) m4 rom)
    /\ (let b2 := fst (pow13_loop 2 r1 b1) in
        let r2 := snd (pow13_loop 2 r1 b1) in
        bn_at SEGS_B m4 o b2 /\ getr regs4 10%bv = Z_to_bv 64 r2
        /\ ok (cells b2) /\ norm (cells b2) /\ cells b2 <> [] /\ ex b2 = ex b
        /\ val (cells b2) * 5 ^ r2 < B ^ 124 /\ 0 <= r2 < 13)
    /\ keeps [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs2 regs4
    /\ unch m2 m4 [(o, o + 2); (o + 4, o + 516)] /\ mem_grows m2 m4).
  { destruct Hbn1 as (Cu1 & Ce1 & Carr1 & Hexr1 & _).
    destruct Hp2 as [[-> Hge] | [-> Hlt]].
    - (* [comment removed for export] *)
      zx_run SEGS_B constr:(CTX (vi_regs ++ [Some (IMG, HIE - 516); Some (13, 26); Some (1, 124)]) [KC (ZDivP (ZV 32) 3) SHA 1 (ZL 0); KC (ZV 32) 0 2 (ZV 34)] (@nil kwin))
        30%nat [0x0aa7ec] (SCR [] [])
        constr:([(10%bv : reg, ZV 33); (8%bv : reg, ZV 32); (19%bv : reg, ZAdd (ZDivP (ZV 32) 3) (ZL SHA)); (20%bv : reg, ZL SHA)])
        [o; r1; zlen (cells b1)] constr:([Some (IMG, HIE - 516); Some (13, 26); Some (1, 124)]) regs2 m2 rom 0x0aa7a4.
      zx_use2 ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kcsh OSH2 0; kc1 Cu1; exact I) ltac:(exact I) ltac:(exact I). zx_name regs3.
      cbn [pow13_loop]. replace (r1 <? 13) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (loop13_B rom 1%nat regs3 m2 o r1 b1) as (regs4 & m4 & M4 & POST & K4 & U4 & G4).
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { etransitivity; [zx_regv ZR|]; f_equal; lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { cbn. lia. } { split; [exact Cu1|split; [exact Ce1|split; [exact Carr1|split; [exact Hexr1|lia]]]]. }
      { exact Hok1. } { exact Hn1. } { exact Hne1. } { exact Hv1. } { lia. } { lia. } { exact Ho8. } { exact OSH2. } { exact Hsto2. }
      eexists regs4, m4. split; [eapply msteps_trans; [exact ZM | exact M4]|].
      split; [cbn [pow13_loop] in POST |- *; rewrite Hex1 in POST; destruct POST as (Q1 & Q2 & Q3 & Q4); split; [exact Q1 | exact (conj Q3 Q4)]|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity]|].
      split; [exact U4 | exact G4].
    - (* [comment removed for export] *)
      eexists regs2, m2. split; [apply mst_refl|].
      cbn [pow13_loop]. replace (r1 <? 13) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
      split.
      { split; [split; [exact Cu1|split; [exact Ce1|split; [exact Carr1|split; [exact Hexr1|lia]]]]|].
        split; [exact C10|]. repeat split; auto; lia. }
      split; [apply keeps_refl|].
      split; [apply unch_refl | apply mem_grows_refl]. }
  destruct CD as (regs4 & m4 & M4 & POST4 & K4 & U4 & G4).
  destruct (pow13_loop 2 r1 b1) as [b2 r2]. cbn [fst snd] in POST4.
  destruct POST4 as (Hbn2 & D10 & Hok2 & Hn2 & Hne2 & Hex2 & Hv2 & Hr2).
  assert (U4' : unch m2 m4 [(o, o + 516); (sp - 80, sp)]).
  { eapply unch_widen; [exact U4|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (Hsto4 : RiscvSemantics.store_ok SEGS_B m4 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G4 | exact Hsto2]).
  assert (Hsts4 : RiscvSemantics.store_ok SEGS_B m4 (Z_to_bv 64 (sp - 64 - 16)) 16 = true) by (eapply store_ok_grows; [exact G4 | exact Hsts2]).
  assert (U04 : unch m m4 [(o, o + 516); (sp - 80, sp)]) by (eapply unch_trans; [exact U2 | exact U4']).
  (* [comment removed for export] *)
  destruct (tbl_B rom regs4 m4 o r2 (sp - 64) b2) as (regs5 & m5 & M5 & POST5 & K5 & U5 & G5).
  { exact D10. } { kept K4 8 C8. } { kept K4 2 C2. } { kept K4 20 C20. }
  { lia. } { exact Hbn2. } { exact Hok2. } { exact Hn2. } { exact Hne2. } { exact Hv2. }
  { apply TBL. exact U04. } { apply TSHu. exact U04. }
  { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { lia. } { apply SCu. exact U04. } { apply OSHu. exact U04. } { exact Hsto4. } { exact Hsts4. }
  cbn zeta in POST5. destruct POST5 as (Hbn3 & Hok3 & Hn3 & Hne3 & Hex3 & Hv3).
  remember (if 0 <? r2 then mul32 (kFive r2) b2 else b2) as b3 eqn:Eb3.
  assert (U5' : unch m4 m5 [(o, o + 516); (sp - 80, sp)]).
  { eapply unch_widen; [exact U5|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; (eexists; split; [left; reflexivity|cbn; lia]) || (eexists; split; [right; left; reflexivity|cbn; lia]). }
  assert (U25 : unch m2 m5 [(o, o + 516); (sp - 80, sp)]) by (eapply unch_trans; [exact U4' | exact U5']).
  assert (U05 : unch m m5 [(o, o + 516); (sp - 80, sp)]) by (eapply unch_trans; [exact U2 | exact U25]).
  assert (Hsto5 : RiscvSemantics.store_ok SEGS_B m5 (Z_to_bv 64 o) 516 = true) by (eapply store_ok_grows; [exact G5 | exact Hsto4]).
  pose proof (cap_bound (cells b3) 0 0 Hok3 Hn3 ltac:(lia) ltac:(lia) ltac:(rewrite Z.pow_0_r, Z.mul_1_r; exact Hv3) ltac:(rewrite !Z.pow_0_r; lia)) as Hcap3.
  assert (FC5 : frame_cellsB m5 sp (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
                   (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv))).
  { eapply s_frame_unch; [exact U5 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]]; cbn; lia |].
    eapply s_frame_unch; [exact U4 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia | exact FC2]. }
  assert (D8 : getr regs4 8%bv = Z_to_bv 64 o) by (kept K4 8 C8).
  assert (D9 : getr regs4 9%bv = Z_to_bv 64 e) by (kept K4 9 C9).
  assert (D2 : getr regs4 2%bv = Z_to_bv 64 (sp - 64)) by (kept K4 2 C2).
  assert (D19 : getr regs4 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K4 19 C19).
  assert (D20 : getr regs4 20%bv = Z_to_bv 64 SHA) by (kept K4 20 C20).
  assert (E8 : getr regs5 8%bv = Z_to_bv 64 o) by (kept K5 8 D8).
  assert (E9 : getr regs5 9%bv = Z_to_bv 64 e) by (kept K5 9 D9).
  assert (E2 : getr regs5 2%bv = Z_to_bv 64 (sp - 64)) by (kept K5 2 D2).
  assert (E19 : getr regs5 19%bv = Z_to_bv 64 (o / 2 ^ 3 + SHA)) by (kept K5 19 D19).
  assert (E20 : getr regs5 20%bv = Z_to_bv 64 SHA) by (kept K5 20 D20).
  (* [comment removed for export] *)
  destruct (fin_B rom regs5 m5 o e sp ret (bv_unsigned ret) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv))
              (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) b3)
    as (regs6 & m6 & M6 & Hbn6 & F2 & F8 & K6 & U6 & G6).
  { exact E8. } { exact E9. } { exact E2. } { exact E19. } { exact E20. }
  { exact FC5. } { apply Z_to_bv_bv_unsigned. } { exact Hret. } { lia. } { exact Hbn3. } { exact Hok3. } { exact Hne3. } { lia. } { rewrite Hex3. lia. }
  { lia. } { lia. } { lia. } { lia. } { exact Ho8. } { lia. } { apply OSHu. exact U05. } { exact Hsto5. }
  assert (U6' : unch m5 m6 [(o, o + 516); (sp - 80, sp)]).
  { eapply unch_widen; [exact U6|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; (eexists; split; [left; reflexivity|cbn; lia]). }
  assert (UU : unch m m6 [(o, o + 516); (sp - 80, sp)]) by (eapply unch_trans; [exact U05 | exact U6']).
  eexists regs6, m6. split; [eapply msteps_trans; [exact M2|]; eapply msteps_trans; [exact M4|]; eapply msteps_trans; [exact M5 | exact M6]|].
  split.
  { eapply (keeps_CS_ofB _ _ (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv))
              (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)));
      [| rewrite F2, R2; reflexivity | exact F8 | symmetry; apply Z_to_bv_bv_unsigned ..].
    eapply keeps_trans; [exact K2|]. eapply keeps_trans; [eapply keeps_sub_dec; [exact K4|]; vm_compute; reflexivity|].
    eapply keeps_trans; [eapply keeps_sub_dec; [exact K5|]; vm_compute; reflexivity|]. exact K6. }
  split; [subst b3; exact Hbn6|].
  split; [apply TBL; exact UU|].
  split; [exact UU|].
  eapply mem_grows_trans; [exact G2|]. eapply mem_grows_trans; [exact G4|]. eapply mem_grows_trans; [exact G5 | exact G6].
Qed.
End S.
