(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnU_mul3 BnU_mul5 BnU_add BnU_add2 BnP_ads1 BnP_ads2 BnP_ads3 BnP_ads5
  BnU_ads1 BnU_ads2 BnU_ads3 BnU_ads4.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma frame13_sv13U : forall m sp (RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word), 104 <= sp -> sp <= 2 ^ 62 ->
  sv13U (frame13 m sp (bv_unsigned RA) (bv_unsigned S0) (bv_unsigned S1) (bv_unsigned S2) (bv_unsigned S3) (bv_unsigned S4) (bv_unsigned S5) (bv_unsigned S6) (bv_unsigned S7) (bv_unsigned S8) (bv_unsigned S9) (bv_unsigned S10) (bv_unsigned S11)) sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11.
Proof.
  intros m sp RA S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 Hsp1 Hsp2. unfold frame13, sv13U.
  pose proof (u64_range RA). pose proof (u64_range S0). pose proof (u64_range S1). pose proof (u64_range S2). pose proof (u64_range S3). pose proof (u64_range S4). pose proof (u64_range S5). pose proof (u64_range S6). pose proof (u64_range S7). pose proof (u64_range S8). pose proof (u64_range S9). pose proof (u64_range S10). pose proof (u64_range S11).
  repeat split; match goal with |- cellN _ _ (sp - ?k) _ _ => let k' := eval compute in (- k) in replace (sp - k) with (sp + k') by lia end; cellx.
Qed.

(* [comment removed for export] *)
Definition tbl16 (m : word -> option byte) (sp buf : Z) : word -> option byte := (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m (Z_to_bv 64 (sp + -632)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 1)))) (Z_to_bv 64 (sp + -640)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 2)))) (Z_to_bv 64 (sp + -648)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 3)))) (Z_to_bv 64 (sp + -656)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 4)))) (Z_to_bv 64 (sp + -664)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 5)))) (Z_to_bv 64 (sp + -672)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 6)))) (Z_to_bv 64 (sp + -680)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 7)))) (Z_to_bv 64 (sp + -688)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 8)))) (Z_to_bv 64 (sp + -696)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 9)))) (Z_to_bv 64 (sp + -704)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 10)))) (Z_to_bv 64 (sp + -712)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 11)))) (Z_to_bv 64 (sp + -720)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 12)))) (Z_to_bv 64 (sp + -728)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 13)))) (Z_to_bv 64 (sp + -736)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 14)))) (Z_to_bv 64 (sp + -744)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 15)))) (Z_to_bv 64 (sp + -752)) (word_to_le_bytes 8 (Z_to_bv 64 (buf + 16)))).

Lemma tbl16_unch : forall m sp buf, 832 <= sp -> sp <= 2 ^ 62 -> unch m (tbl16 m sp buf) [(sp - 752, sp - 624)].
Proof. intros. unfold tbl16. unchx. Qed.

Lemma tbl16_grows : forall m sp buf, mem_grows m (tbl16 m sp buf).
Proof. intros. unfold tbl16. growsx. Qed.

Lemma tbl16_ptr : forall m sp buf, 832 <= sp -> sp <= 2 ^ 62 -> 0 <= buf -> buf + 16 < 2 ^ 64 -> ptr_tblU (tbl16 m sp buf) sp buf.
Proof.
  intros m sp buf Hsp1 Hsp2 Hb1 Hb2. unfold tbl16, ptr_tblU.
  repeat split; match goal with |- cellN _ _ (sp - ?k) _ _ => let k' := eval compute in (- k) in replace (sp - k) with (sp + k') by lia end; cellx.
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Abbreviation E_pins := [(10%bv : reg, ZV 32); (11%bv : reg, ZV 33); (12%bv : reg, ZV 34); (2%bv : reg, ZV 35); (1%bv : reg, ZV 36); (8%bv : reg, ZV 37); (9%bv : reg, ZV 38); (18%bv : reg, ZV 39); (19%bv : reg, ZV 40); (20%bv : reg, ZV 41); (21%bv : reg, ZV 42); (22%bv : reg, ZV 43); (23%bv : reg, ZV 44); (24%bv : reg, ZV 45); (25%bv : reg, ZV 46); (26%bv : reg, ZV 47); (27%bv : reg, ZV 48)].

#[using="Type"] Theorem ads_U : forall regs m (o buf len sp : Z) (ret : word) (ds : list Z),
  getr regs 10%bv = Z_to_bv 64 o -> getr regs 11%bv = Z_to_bv 64 buf -> getr regs 12%bv = Z_to_bv 64 len ->
  getr regs 2%bv = Z_to_bv 64 sp -> getr regs 1%bv = ret -> ret_ok ret ->
  zlen ds = len -> 1 <= len <= 780 -> digits_ok ds -> digsU m buf ds ->
  arr32 SEGS_U m 80520 five_tbl ->
  1 <= buf -> buf + len <= 2 ^ 62 -> 81384 <= sp -> sp <= 2 ^ 62 -> 80568 <= o -> o + 516 <= 2 ^ 62 ->
  (o + 516 <= sp - 816 \/ sp <= o) -> (buf + len <= sp - 816 \/ sp <= buf) -> (buf + len <= o \/ o + 516 <= buf) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 (sp - 816)) 816 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ae0) m rom) (mkst regs' ret m' rom)
    /\ keeps CS regs regs' /\ bn_at SEGS_U m' o (assign_decimal ds)
    /\ arr32 SEGS_U m' 80520 five_tbl
    /\ unch m m' [(o, o + 516); (sp - 816, sp)] /\ mem_grows m m'.
Proof.
  intros regs m o buf len sp ret ds R10 R11 R12 R2 R1 Hret Hlen Hlen1 DOK DG Htbl Hb1 Hb2 Hsp1 Hsp2 Ho1 Ho2 Hdo Hdb Hbo Hsto Hsts.
  pose proof (add_U rom) as ADD.
  assert (Elen : len = Z.of_nat (length ds)) by (rewrite <- Hlen; reflexivity).
  (* [comment removed for export] *)
  assert (POST1 :
    let m1 := wbytes (frame13 m sp (bv_unsigned (getr regs 1%bv)) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (bv_unsigned (getr regs 23%bv)) (bv_unsigned (getr regs 24%bv)) (bv_unsigned (getr regs 25%bv)) (bv_unsigned (getr regs 26%bv)) (bv_unsigned (getr regs 27%bv))) (Z_to_bv 64 o) (word_to_le_bytes 4 (Z_to_bv 64 0)) in
    sv13U m1 sp ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv) (getr regs 25%bv) (getr regs 26%bv) (getr regs 27%bv)
    /\ bn_at SEGS_U m1 o (BN [] 0) /\ digsU m1 buf ds /\ arr32 SEGS_U m1 80520 five_tbl
    /\ unch m m1 [(o, o + 516); (sp - 816, sp)] /\ mem_grows m m1
    /\ RiscvSemantics.store_ok SEGS_U m1 (Z_to_bv 64 o) 516 = true /\ RiscvSemantics.store_ok SEGS_U m1 (Z_to_bv 64 (sp - 816)) 816 = true).
  { intros m1.
    assert (U0 : unch m (frame13 m sp (bv_unsigned (getr regs 1%bv)) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (bv_unsigned (getr regs 23%bv)) (bv_unsigned (getr regs 24%bv)) (bv_unsigned (getr regs 25%bv)) (bv_unsigned (getr regs 26%bv)) (bv_unsigned (getr regs 27%bv))) [(sp - 104, sp)]) by (apply frame13_unch; lia).
    assert (U1 : unch (frame13 m sp (bv_unsigned (getr regs 1%bv)) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (bv_unsigned (getr regs 23%bv)) (bv_unsigned (getr regs 24%bv)) (bv_unsigned (getr regs 25%bv)) (bv_unsigned (getr regs 26%bv)) (bv_unsigned (getr regs 27%bv))) m1 [(o, o + 4)]) by (unfold m1; unchx).
    assert (U : unch m m1 [(o, o + 516); (sp - 816, sp)]).
    { apply (unch_trans m (frame13 m sp (bv_unsigned (getr regs 1%bv)) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (bv_unsigned (getr regs 23%bv)) (bv_unsigned (getr regs 24%bv)) (bv_unsigned (getr regs 25%bv)) (bv_unsigned (getr regs 26%bv)) (bv_unsigned (getr regs 27%bv))) m1).
      - eapply unch_widen; [exact U0|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; left; reflexivity | cbn; lia].
      - eapply unch_widen; [exact U1|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity | cbn; lia]. }
    assert (G : mem_grows m m1) by (unfold m1; eapply mem_grows_trans; [| apply grows_store]; apply frame13_grows).
    split; [|split; [|split; [|split; [|split; [exact U|split; [exact G|split; [eapply store_ok_grows; [exact G | exact Hsto] | eapply store_ok_grows; [exact G | exact Hsts]]]]]]]].
    - eapply (sv13U_unch _ m1 sp); [exact U1 | lia | lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia |].
      rewrite <- R1. apply frame13_sv13U; lia.
    - pose proof (bn_ctor_store SEGS_U (frame13 m sp (bv_unsigned (getr regs 1%bv)) (bv_unsigned (getr regs 8%bv)) (bv_unsigned (getr regs 9%bv)) (bv_unsigned (getr regs 18%bv)) (bv_unsigned (getr regs 19%bv)) (bv_unsigned (getr regs 20%bv)) (bv_unsigned (getr regs 21%bv)) (bv_unsigned (getr regs 22%bv)) (bv_unsigned (getr regs 23%bv)) (bv_unsigned (getr regs 24%bv)) (bv_unsigned (getr regs 25%bv)) (bv_unsigned (getr regs 26%bv)) (bv_unsigned (getr regs 27%bv))) o ltac:(lia) ltac:(lia)) as [C0 C2].
      unfold bn_at; cbn [cells BnModel.ex]. rewrite zlen_nil. split; [exact C0|]. split; [exact C2|]. split; [apply arr32_nil|]. lia.
    - eapply digsU_unch; [exact U | lia | rewrite Hlen; lia | | exact DG]. intros rg Hrg; cbn in Hrg; rewrite Hlen; destruct Hrg as [<-|[<-|[]]]; cbn; lia.
    - eapply arr32_unch; [exact U | lia | cbn; lia | | exact Htbl]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[]]]; cbn; lia. }
  (* [comment removed for export] *)
  assert (FIN : forall regs9 m1 m9 (b9 : bn),
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ae0) m rom) (mkst regs9 ret m9 rom) ->
    bn_at SEGS_U m9 o b9 -> b9 = assign_decimal ds -> getr regs9 2%bv = Z_to_bv 64 sp ->
    s12_rest regs9 (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv) (getr regs 25%bv) (getr regs 26%bv) (getr regs 27%bv) -> keeps [3; 4] regs regs9 ->
    arr32 SEGS_U m9 80520 five_tbl -> unch m m1 [(o, o + 516); (sp - 816, sp)] -> mem_grows m m1 ->
    unch m1 m9 [(o, o + 516); (sp - 816, sp - 752); (sp - 752, sp - 624); (sp - 620, sp - 104)] -> mem_grows m1 m9 ->
    exists regs' m',
      msteps SEGS_U (mkst regs (Z_to_bv 64 0x35ae0) m rom) (mkst regs' ret m' rom)
      /\ keeps CS regs regs' /\ bn_at SEGS_U m' o (assign_decimal ds)
      /\ arr32 SEGS_U m' 80520 five_tbl
      /\ unch m m' [(o, o + 516); (sp - 816, sp)] /\ mem_grows m m').
  { intros regs9 m1 m9 b9 M9 Hbn9 -> E2 SR K9 T9 U1 G1 U9 G9.
    eexists regs9, m9. split; [exact M9|].
    split; [eapply keeps_CS_of12; [exact K9 | rewrite E2, R2; reflexivity | exact SR]|].
    split; [exact Hbn9|]. split; [exact T9|].
    split; [|eapply mem_grows_trans; [exact G1 | exact G9]].
    eapply unch_trans; [exact U1|]. eapply unch_widen; [exact U9|].
    intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[<-|[]]]]];
      [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia] ..]. }
  destruct (Z_lt_dec len 19) as [Hlt | Hge].
  - (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 18); Some (832, 2 ^ 62); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z)]) (@nil kcell) [KW (ZV 35) (-816) 0; KW (ZV 32) 0 516])
      40%nat [0x35e7c; 0x35b34] (SCR [] []) constr:(E_pins)
      [o; buf; len; sp; bv_unsigned (getr regs 1%bv); bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv); bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv); bv_unsigned (getr regs 22%bv); bv_unsigned (getr regs 23%bv); bv_unsigned (getr regs 24%bv); bv_unsigned (getr regs 25%bv); bv_unsigned (getr regs 26%bv); bv_unsigned (getr regs 27%bv)] constr:([Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (1, 18); Some (832, 2 ^ 62); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z)]) regs m rom 0x35ae0.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; kw1 Hsto; exact I) ltac:(exact I). zx_name regs1.
    destruct POST1 as (SV1 & Hbn1 & DG1 & T1 & U1 & G1 & Hsto1 & Hsts1).
    set (m1 := wbytes _ (Z_to_bv 64 o) _) in ZM, SV1, Hbn1, DG1, T1, U1, G1, Hsto1, Hsts1.
    destruct (tail_U rom ADD regs1 m1 o buf sp [] ds (BN [] 0) ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv) (getr regs 25%bv) (getr regs 26%bv) (getr regs 27%bv)) as (regs9 & m9 & M9 & Hbn9 & E2 & SR & K9 & T9 & U9 & G9);
      try (cbn [app]; rewrite ?zlen_nil; first [exact SV1 | exact Hbn1 | exact DG1 | exact DOK | exact T1 | exact Hret | exact Hsto1 | exact Hsts1 | apply ok_nil | apply norm_nil | zx_regv ZR | idtac]).
    { lia. } { rewrite Hlen. lia. } { reflexivity. } { replace (zlen (@nil Z)) with 0 by reflexivity. cbn [val cells]. lia. }
    { lia. } { rewrite Hlen. lia. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. } { rewrite Hlen. exact Hdb. } { rewrite Hlen. exact Hbo. }
    eapply (FIN regs9 m1 m9); [eapply msteps_trans; [exact ZM | exact M9] | exact Hbn9 | | exact E2 | exact SR | | exact T9 | exact U1 | exact G1 | | exact G9].
    { unfold assign_decimal. replace (Nat.div (length ds) 19) with 0%nat by (symmetry; apply Nat.div_small; lia). reflexivity. }
    { eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K9]. }
    { eapply unch_widen; [exact U9|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]];
        [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia] | eexists; split; [right; right; right; left; reflexivity | cbn; lia]]. }
  - (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (19, 780); Some (832, 2 ^ 62); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z)]) (@nil kcell) [KW (ZV 35) (-816) 0; KW (ZV 32) 0 516])
      40%nat [0x35e7c; 0x35b34] (SCR [] []) constr:(E_pins)
      [o; buf; len; sp; bv_unsigned (getr regs 1%bv); bv_unsigned (getr regs 8%bv); bv_unsigned (getr regs 9%bv); bv_unsigned (getr regs 18%bv); bv_unsigned (getr regs 19%bv); bv_unsigned (getr regs 20%bv); bv_unsigned (getr regs 21%bv); bv_unsigned (getr regs 22%bv); bv_unsigned (getr regs 23%bv); bv_unsigned (getr regs 24%bv); bv_unsigned (getr regs 25%bv); bv_unsigned (getr regs 26%bv); bv_unsigned (getr regs 27%bv)] constr:([Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (19, 780); Some (832, 2 ^ 62); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z); @None (Z * Z)]) regs m rom 0x35ae0.
    zx_use ZXB ltac:(zx_pins2) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts; kw1 Hsto; exact I) ltac:(exact I). zx_name regs1.
    destruct POST1 as (SV1 & Hbn1 & DG1 & T1 & U1 & G1 & Hsto1 & Hsts1).
    set (m1 := wbytes _ (Z_to_bv 64 o) _) in ZM, SV1, Hbn1, DG1, T1, U1, G1, Hsto1, Hsts1.
    zx_reg ZR (9%bv : reg) as A9. zx_reg ZR (12%bv : reg) as A12. zx_reg ZR (2%bv : reg) as A2. zx_reg ZR (8%bv : reg) as A8.
    assert (K1 : keeps [3; 4] regs regs1) by (eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity).
    rename ZM into M1. clear ZE ZR ZF.
    (* [comment removed for export] *)
    zx_run SEGS_U constr:(CTX (vi_regs ++ [Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (19, 780); Some (832, 2 ^ 62)]) (@nil kcell) [KW (ZV 35) (-816) 0])
      60%nat [0x35bf0] (SCR [] []) constr:([(9%bv : reg, ZV 33); (12%bv : reg, ZV 34); (2%bv : reg, ZAdd (ZV 35) (ZL (-752))); (8%bv : reg, ZV 32)])
      [o; buf; len; sp] constr:([Some (0, 2 ^ 62); Some (1, 2 ^ 62); Some (19, 780); Some (832, 2 ^ 62)]) regs1 m1 rom 0x35b34.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsts1; exact I) ltac:(exact I). zx_name regs2.
    change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m1 _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _)
      with (tbl16 m1 sp buf) in ZM.
    assert (U2 : unch m1 (tbl16 m1 sp buf) [(sp - 752, sp - 624)]) by (apply tbl16_unch; lia).
    pose proof (tbl16_grows m1 sp buf) as G2.
    assert (PT2 : ptr_tblU (tbl16 m1 sp buf) sp buf) by (apply tbl16_ptr; lia).
    set (m2 := tbl16 m1 sp buf) in *.
    assert (RD2 : rd_regsU regs2 buf) by (unfold rd_regsU, MASK; repeat split; zx_regv ZR).
    destruct (loop19_U rom ADD (Nat.div (length ds) 19) regs2 m2 o buf sp [] ds (BN [] 0)) as (regs3 & m3 & M3 & POST3 & K3 & PT3 & T3 & U3 & G3);
      try (cbn [app]; rewrite ?zlen_nil; first [exact PT2 | exact DOK | apply ok_nil | apply norm_nil | zx_regv ZR | idtac]).
    { exact RD2. }
    { eapply digsU_unch; [exact U2 | lia | rewrite Hlen; lia | | exact DG1]. intros rg Hrg; cbn in Hrg; rewrite Hlen; destruct Hrg as [<-|[]]; cbn; lia. }
    { rewrite Hlen. lia. } { rewrite Hlen. lia. } { lia. }
    { eapply (bn_at_unch SEGS_U m1 m2 o _ _ U2); [lia | cbn; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia | exact Hbn1]. }
    { reflexivity. } { replace (zlen (@nil Z)) with 0 by reflexivity. cbn [val cells]. lia. }
    { eapply arr32_unch; [exact U2 | lia | cbn; lia | | exact T1]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; lia. }
    { lia. } { rewrite Hlen. lia. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. } { rewrite Hlen. exact Hdb. } { rewrite Hlen. exact Hbo. }
    { eapply store_ok_grows; [exact G2 | exact Hsto1]. } { eapply store_ok_grows; [exact G2 | exact Hsts1]. }
    destruct (ads_loop (Nat.div (length ds) 19) ds (BN [] 0)) as [b3 rest3] eqn:Eal. cbn [fst snd] in POST3.
    replace (zlen (@nil Z)) with 0 in POST3 by reflexivity. rewrite Hlen in POST3.
    destruct POST3 as (Hbn3 & Hok3 & Hn3 & Hex3 & Hval3 & Hr3 & (mid & Hmid) & C19 & C18 & C11).
    assert (Hzm : zlen mid = len - zlen rest3) by (rewrite <- Hlen, Hmid, zlen_app; lia).
    assert (U13 : unch m1 m3 [(o, o + 516); (sp - 816, sp - 752); (sp - 752, sp - 624); (sp - 620, sp - 104)]).
    { apply (unch_trans m1 m2 m3).
      - eapply unch_widen; [exact U2|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]. eexists; split; [right; right; left; reflexivity | cbn; lia].
      - eapply unch_widen; [exact U3|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]];
          [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia] | eexists; split; [right; right; right; left; reflexivity | cbn; lia]]. }
    destruct (tail_U rom ADD regs3 m3 o buf sp mid rest3 b3 ret (getr regs 8%bv) (getr regs 9%bv) (getr regs 18%bv) (getr regs 19%bv) (getr regs 20%bv) (getr regs 21%bv) (getr regs 22%bv) (getr regs 23%bv) (getr regs 24%bv) (getr regs 25%bv) (getr regs 26%bv) (getr regs 27%bv)) as (regs9 & m9 & M9 & Hbn9 & E2 & SR & K9 & T9 & U9 & G9);
      try (rewrite <- ?Hmid; first [exact Hbn3 | exact Hok3 | exact Hn3 | exact Hex3 | exact DOK | exact T3 | exact Hret | idtac]).
    { etransitivity; [exact (K3 8 ltac:(inl)) | zx_regv ZR]. }
    { etransitivity; [exact (K3 9 ltac:(inl)) | zx_regv ZR]. }
    { rewrite C19. f_equal. lia. }
    { exact C11. }
    { etransitivity; [exact (K3 2 ltac:(inl)) | zx_regv ZR]. }
    { eapply digsU_unch; [exact U13 | lia | rewrite Hlen; lia | | exact DG1]. intros rg Hrg; cbn in Hrg; rewrite Hlen; destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia. }
    { lia. } { lia. }
    { rewrite Hzm. replace (0 + len - zlen rest3) with (len - zlen rest3) in Hval3 by lia. exact Hval3. }
    { eapply (sv13U_unch m1 m3); [exact U13 | lia | lia | | exact SV1]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia. }
    { lia. } { rewrite Hlen. lia. } { lia. } { lia. } { lia. } { lia. } { exact Hdo. } { rewrite Hlen. exact Hdb. } { rewrite Hlen. exact Hbo. }
    { eapply store_ok_grows; [| exact Hsto1]. eapply mem_grows_trans; [exact G2 | exact G3]. }
    { eapply store_ok_grows; [| exact Hsts1]. eapply mem_grows_trans; [exact G2 | exact G3]. }
    eapply (FIN regs9 m1 m9); [ | exact Hbn9 | unfold assign_decimal; change bn_zero with (BN [] 0); rewrite Eal; reflexivity | exact E2 | exact SR | | exact T9 | exact U1 | exact G1 | | ].
    { eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact ZM|]. eapply msteps_trans; [exact M3 | exact M9]. }
    { eapply keeps_trans; [exact K1|]. eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      eapply keeps_trans; [eapply keeps_sub_dec; [exact K3|]; vm_compute; reflexivity | exact K9]. }
    { eapply unch_trans; [exact U13|]. eapply unch_widen; [exact U9|]. intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[<-|[<-|[]]]];
        [eexists; split; [left; reflexivity | cbn; lia] | eexists; split; [right; left; reflexivity | cbn; lia] | eexists; split; [right; right; right; left; reflexivity | cbn; lia]]. }
    { eapply mem_grows_trans; [exact G2 |]. eapply mem_grows_trans; [exact G3 | exact G9]. }
Qed.

End S.
