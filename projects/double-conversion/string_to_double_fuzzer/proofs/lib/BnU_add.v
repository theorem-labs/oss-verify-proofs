(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface BnP_add.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
Ltac xchk :=
  repeat lazymatch goal with |- context [if ?a <? ?b then _ else _] =>
    first [ replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia)
          | replace (a <? b) with true by (symmetry; apply Z.ltb_lt; lia) ] end;
  first [ intros HH; vm_compute in HH; discriminate HH | vm_compute; reflexivity | lia ].

Section GenSegs.
Variable segs : list Segment.
#[using="Type"] Lemma arr32_tail_g : forall m a x l, arr32 segs m a (x :: l) -> arr32 segs m (a + 4) l.
Proof.
  intros m a x l H i Hi. specialize (H (S i) ltac:(cbn; lia)). cbn [nth] in H.
  replace (a + 4 + 4 * Z.of_nat i) with (a + 4 * Z.of_nat (S i)) by lia. exact H.
Qed.
#[using="Type"] Lemma arr32_cons_g : forall m a x l, cellN segs m a 4 x -> arr32 segs m (a + 4) l -> arr32 segs m a (x :: l).
Proof.
  intros m a x l Hc H i Hi. destruct i as [|i].
  - cbn [nth]. replace (a + 4 * Z.of_nat 0%nat) with a by lia. exact Hc.
  - cbn [nth]. specialize (H i ltac:(cbn in Hi; lia)). replace (a + 4 * Z.of_nat (S i)) with (a + 4 + 4 * Z.of_nat i) by lia. exact H.
Qed.
#[using="Type"] Lemma arr32_skip_g : forall m a l1 l2, arr32 segs m a (l1 ++ l2) -> arr32 segs m (a + 4 * Z.of_nat (length l1)) l2.
Proof.
  intros m a l1 l2 H i Hi. specialize (H (length l1 + i)%nat ltac:(rewrite length_app; lia)).
  rewrite app_nth2 in H by lia. replace (length l1 + i - length l1)%nat with i in H by lia.
  replace (a + 4 * Z.of_nat (length l1) + 4 * Z.of_nat i) with (a + 4 * Z.of_nat (length l1 + i)) by lia. exact H.
Qed.
#[using="Type"] Lemma arr32_app_g : forall m a l1 l2, arr32 segs m a l1 -> arr32 segs m (a + 4 * Z.of_nat (length l1)) l2 -> arr32 segs m a (l1 ++ l2).
Proof.
  intros m a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hr].
  - rewrite app_nth1 by lia. apply H1. lia.
  - rewrite app_nth2 by lia. specialize (H2 (i - length l1)%nat ltac:(lia)).
    replace (a + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (i - length l1)) with (a + 4 * Z.of_nat i) in H2 by lia. exact H2.
Qed.
End GenSegs.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addL_pins :=
  [(7%bv : reg, ZAdd (ZV 32) (ZL 4)); (16%bv : reg, ZMul (ZV 34) (ZL 4)); (14%bv : reg, ZV 34);
   (6%bv : reg, ZAdd (ZV 32) (ZL 4)); (10%bv : reg, ZV 36); (11%bv : reg, ZAdd (ZV 32) (ZL 4));
   (5%bv : reg, ZSub (ZDivP (ZSub (ZL 18446744073709551615) (ZV 33)) 2) (ZV 34)); (17%bv : reg, ZAdd (ZV 33) (ZL 4));
   (13%bv : reg, ZV 35); (15%bv : reg, ZL 268435455); (28%bv : reg, ZL 8589934588); (29%bv : reg, ZMul (ZV 37) (ZL 4))].
Abbreviation addL_uvi := [Some (1, 2 ^ 62); Some (1, 2 ^ 62); Some (0, 130); Some (0, 1); Some (0, 127); Some (1, 130); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1)].
Definition addL_keep : list Z := [1; 2; 3; 4; 6; 7; 8; 10; 11; 12; 15; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29].

#[using="Type"] Lemma add_loop_U : forall ot odone lt done c regs m (o q u : Z),
  let i := Z.of_nat (length odone) in
  let n := Z.of_nat (length odone) + Z.of_nat (length ot) in
  Z.of_nat (length done) = i ->
  getr regs 7%bv = Z_to_bv 64 (o + 4) -> getr regs 17%bv = Z_to_bv 64 (q + 4) -> getr regs 16%bv = Z_to_bv 64 (i * 4) ->
  getr regs 14%bv = Z_to_bv 64 i -> getr regs 6%bv = Z_to_bv 64 (o + 4) -> getr regs 11%bv = Z_to_bv 64 (o + 4) ->
  getr regs 13%bv = Z_to_bv 64 c -> getr regs 10%bv = Z_to_bv 64 u -> getr regs 29%bv = Z_to_bv 64 (n * 4) ->
  getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 5%bv = Z_to_bv 64 ((18446744073709551615 - q) / 2 ^ 2 - i) ->
  getr regs 28%bv = Z_to_bv 64 8589934588 ->
  Z.max u i = i + zlen lt -> 0 <= u <= 127 -> n <= 127 -> ok lt -> ok ot -> ot <> [] -> 0 <= c <= 1 ->
  1 <= o -> o + 516 <= 2 ^ 62 -> 1 <= q -> q + 516 <= 2 ^ 62 -> (q + 516 <= o \/ o + 516 <= q) ->
  arr32 SEGS_U m (o + 4) (done ++ lt) -> arr32 SEGS_U m (q + 4) (odone ++ ot) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' S,
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x364bc) m rom) (mkst regs' (Z_to_bv 64 0x36534) m' rom)
    /\ arr32 SEGS_U m' (o + 4) (done ++ fst (addm c lt ot) ++ skipn (length ot) lt)
    /\ getr regs' 13%bv = Z_to_bv 64 (snd (addm c lt ot)) /\ getr regs' 31%bv = Z_to_bv 64 S
    /\ S / 2 ^ 28 = snd (addm c lt ot) /\ 0 <= S < 2 ^ 30
    /\ getr regs' 14%bv = Z_to_bv 64 n /\ getr regs' 16%bv = Z_to_bv 64 (n * 4)
    /\ keeps addL_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * i, o + 4 + 4 * n)] /\ mem_grows m m'.
Proof.
  induction ot as [|y ot IH]; intros odone lt done c regs m o q u i n Hdone R7 R17 R16 R14 R6 R11 R13 R10 R29 R15 R5 R28
    Hmax Hu Hn Hokl Hoko Hne Hc Ho1 Ho2 Hq1 Hq2 Hdj Harr Harro Hsto; [congruence|].
  subst i n. apply ok_cons in Hoko as [Hy Hoko]. cbn [length] in *. unfold MASK in R15. unfold B in *.
  set (i := Z.of_nat (length odone)) in *.
  assert (Hidef : i = Z.of_nat (length odone)) by reflexivity.
  assert (Hi : 0 <= i) by lia.
  assert (Hcy : exists bs, rdn SEGS_U m (Z_to_bv 64 (q + 4 + i * 4 + 0)) 4 = Some bs /\ bytes_le_to_Z bs = y).
  { eapply kc_of_arr32; [exact Harro | lia]. }
  pose proof (zlen_nonneg lt) as Hlt0.
  cbn [addm]. 
  destruct lt as [|x t].
  - (* [comment removed for export] *)
    cbn [hd tl skipn]. unfold B in *. rewrite zlen_nil in Hmax.
    destruct (addm ((0 + y + c) / 268435456) [] ot) as [r c'] eqn:Hrec. cbn [fst snd].
    destruct ot as [|y2 ot'].
    + (* [comment removed for export] *)
      cbn [length] in *. change (Z.of_nat 1) with 1 in *.
      zx_run SEGS_U constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x364bc; 0x36534] (SCR [true; false; false] [ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + 1; 0; y] constr:(addL_uvi) regs m rom 0x364bc.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia] | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv] | xchk])).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (y + c). split; [exact ZM|].
      split.
      { rewrite ?app_nil_r. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc' ; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_U constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x364bc; 0x36534] (SCR [true; false; true] [ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); 0; y] constr:(addL_uvi) regs m rom 0x364bc.
      zx_use ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia] | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv] | xchk])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_U m1 (o + 4) ((done ++ [(y + c) mod 268435456]) ++ [])).
      { rewrite !app_nil_r. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc'; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_U m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      specialize (IH (odone ++ [y]) [] (done ++ [(y + c) mod 268435456]) ((0 + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C28 & HS & HS2 & C21 & C13 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { rewrite zlen_nil. lia. } { lia. } { lia. } { apply ok_nil. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Hdj. } { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      cbn [skipn app] in Harr2. rewrite <- app_assoc in Harr2. cbn [app] in Harr2. rewrite ?app_nil_r in Harr2.
      split; [rewrite ?app_nil_r; replace (0 + y + c) with (y + c) by lia; exact Harr2|].
      split; [exact C12|]. split; [exact C28|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C21; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
  - (* [comment removed for export] *)
    cbn [hd tl skipn]. unfold B in *. rewrite zlen_cons in Hmax. apply ok_cons in Hokl as [Hx Hokt]. unfold B in Hx. pose proof (zlen_nonneg t) as Hlt1. assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity.
    assert (Hcx : exists bs, rdn SEGS_U m (Z_to_bv 64 (o + 4 + i * 4 + 0)) 4 = Some bs /\ bytes_le_to_Z bs = x).
    { eapply kc_of_arr32; [exact Harr | lia]. }
    destruct (addm ((x + y + c) / 268435456) t ot) as [r c'] eqn:Hrec. cbn [fst snd].
    destruct ot as [|y2 ot'].
    + (* [comment removed for export] *)
      cbn [length] in *. change (Z.of_nat 1) with 1 in *.
      zx_run SEGS_U constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x364bc; 0x36534] (SCR [false; false; false; false] [ZV 38; ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + 1; x; y] constr:(addL_uvi) regs m rom 0x364bc.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | xchk])).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (x + c + y). split; [exact ZM|].
      split.
      { replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_U constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x364bc; 0x36534] (SCR [false; false; false; true] [ZV 38; ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); x; y] constr:(addL_uvi) regs m rom 0x364bc.
      zx_use ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | xchk])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_U m1 (o + 4) ((done ++ [(x + y + c) mod 268435456]) ++ t)).
      { rewrite <- app_assoc. cbn [app]. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_U m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      specialize (IH (odone ++ [y]) t (done ++ [(x + y + c) mod 268435456]) ((x + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C28 & HS & HS2 & C21 & C13 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { exact Hokt. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Hdj. } { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      rewrite <- app_assoc in Harr2. cbn [app] in Harr2.
      split; [exact Harr2|].
      split; [exact C12|]. split; [exact C28|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C21; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addC_pins :=
  [(17%bv : reg, ZV 33); (10%bv : reg, ZV 35); (14%bv : reg, ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4)));
   (11%bv : reg, ZAdd (ZV 32) (ZL 4)); (16%bv : reg, ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4)));
   (13%bv : reg, ZV 34); (15%bv : reg, ZL 268435455); (12%bv : reg, ZV 33)].
Abbreviation addC_uvi := [Some (1, 2 ^ 62); Some (0, 130); Some (1, 1); Some (0, 127); Some (0, 2 ^ 28 - 1)].
Definition addC_keep : list Z := [1; 2; 3; 4; 8; 9; 10; 11; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma addc_loop_U : forall lt (pos c : Z) regs m (o u : Z),
  getr regs 17%bv = Z_to_bv 64 pos -> getr regs 10%bv = Z_to_bv 64 u -> getr regs 14%bv = Z_to_bv 64 (o + 4 + pos * 4) ->
  getr regs 11%bv = Z_to_bv 64 (o + 4) -> getr regs 16%bv = Z_to_bv 64 (o + 4 + pos * 4) ->
  getr regs 13%bv = Z_to_bv 64 c -> getr regs 15%bv = Z_to_bv 64 MASK -> getr regs 12%bv = Z_to_bv 64 pos ->
  Z.max u pos = pos + zlen lt -> 0 <= u <= 127 -> 0 <= pos -> pos + zlen lt + 1 <= 128 -> ok lt -> 0 < c <= 1 ->
  1 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_U m (o + 4 + 4 * pos) lt ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' k,
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x36550) m rom) (mkst regs' (Z_to_bv 64 0x365c4) m' rom)
    /\ arr32 SEGS_U m' (o + 4 + 4 * pos) (addc_l c lt)
    /\ 1 <= k /\ zlen (addc_l c lt) = Z.max (zlen lt) k
    /\ getr regs' 12%bv = Z_to_bv 64 (pos + k)
    /\ keeps addC_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * pos, o + 4 + 4 * (pos + zlen (addc_l c lt)))] /\ mem_grows m m'.
Proof.
  induction lt as [|x t IH]; intros pos c regs m o u R17 R10 R14 R11 R16 R13 R15 R12 Hmax Hu Hpos Hcap Hok Hc Ho1 Ho2 Harr Hsto.
  - (* [comment removed for export] *)
    rewrite zlen_nil in *. unfold MASK in R15.
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zx_run SEGS_U constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x36550; 0x365c4] (SCR [true; false; false] [])
      constr:(addC_pins) [o; pos; c; u; 0] constr:(addC_uvi) regs m rom 0x36550.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
      ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia] | xchk])).
    zx_name regs1.
    eexists regs1, _, 1. split; [exact ZM|].
    split.
    { change [c] with ([] ++ [c]). replace (o + 4 + pos * 4) with (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z [])) by (cbn; lia).
      apply arr32_snoc'; [lia | cbn; lia | exact Harr |]. rewrite u_Z2bv64. rewrite Z.mod_small by lia. apply Z.mod_small. lia. }
    split; [lia|]. split; [rewrite zlen_cons, zlen_nil; lia|]. split; [zx_regv ZR|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite zlen_cons, zlen_nil. split; [unchx | growsx].
  - apply ok_cons in Hok as [Hx Hok]. rewrite zlen_cons in *. pose proof (zlen_nonneg t) as Ht0.
    assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity. unfold MASK in R15. unfold B in Hx.
    assert (Hcx : exists bs, rdn SEGS_U m (Z_to_bv 64 (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z []))) 4 = Some bs /\ bytes_le_to_Z bs = x).
    { eapply (kc_of_arr32 _ _ _ []); [exact Harr | reflexivity]. }
    cbn [length] in Hcx.
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold addc_l. unfold B in *.
    destruct (Z.eq_dec ((x + c) / 268435456) 0) as [Hz | Hnz].
    + (* [comment removed for export] *)
      zx_run SEGS_U constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x36550; 0x365c4] (SCR [false; false; false; false; false] [ZV 36])
        constr:(addC_pins) [o; pos; c; u; x] constr:(addC_uvi) regs m rom 0x36550.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | lia | xchk])).
      zx_name regs1.
      rewrite Hz. replace (addc_l 0 t) with t by (destruct t; reflexivity).
      eexists regs1, _, 1. split; [exact ZM|].
      split.
      { change ((x + c) mod 268435456 :: t) with ([] ++ (x + c) mod 268435456 :: t). replace (o + 4 + pos * 4) with (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z [])) by (cbn; lia).
        apply arr32_store' with (x := x); [lia | cbn [app length]; lia | exact Harr |]. rewrite u_Z2bv64. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. reflexivity. }
      split; [lia|]. split; [rewrite zlen_cons; lia|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      rewrite zlen_cons. split; [unchx | growsx].
    + (* [comment removed for export] *)
      assert (Hc1 : (x + c) / 268435456 = 1) by lia.
      replace ((x + c) / 268435456) with 1 by lia.
      zx_run SEGS_U constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 40%nat [0x36550; 0x365c4] (SCR [false; false; false; false; true] [ZV 36])
        constr:(addC_pins) [o; pos; c; u; x] constr:(addC_uvi) regs m rom 0x36550.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | lia | xchk])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_U m1 (o + 4 + 4 * (pos + 1)) t).
      { unfold m1. apply arr32_store_other; zwidth; try lia. replace (o + 4 + 4 * (pos + 1)) with (o + 4 + 4 * pos + 4) by lia. eapply arr32_tail_g. exact Harr. }
      destruct (IH (pos + 1) 1 regs1 m1 o u) as (regs2 & m2 & k & M2 & Harr2 & Hk & Hlen2 & C21 & K2 & U2 & G2).
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { lia. } { exact Hok. } { lia. } { lia. } { lia. } { exact Harr1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, (k + 1). split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split.
      { apply arr32_cons_g; [|replace (o + 4 + 4 * pos + 4) with (o + 4 + 4 * (pos + 1)) by lia; exact Harr2].
        eapply cellN_unch; [exact U2 | lia | zwidth; lia | intros rg Hrg; cbn in Hrg; destruct Hrg as [<-|[]]; cbn; zwidth; lia |].
        unfold m1. replace (o + 4 + pos * 4) with (o + 4 + 4 * pos) by lia. cellx; try (rewrite Z.mod_small by lia); try reflexivity. }
      split; [lia|]. split; [rewrite zlen_cons, Hlen2; lia|]. split; [rewrite C21; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; rewrite zlen_cons; pose proof (zlen_nonneg (addc_l 1 t)); unchx|].
        eapply unch_widen; [exact U2|]. intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. rewrite zlen_cons. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation finA_kn := [KC (ZV 33) (-8) 8 (ZV 36); KC (ZV 33) (-16) 8 (ZV 37); KC (ZV 33) (-24) 8 (ZV 38); KC (ZV 33) (-32) 8 (ZV 39)].
Abbreviation finA_pins := [(12%bv : reg, ZV 35); (10%bv : reg, ZV 34); (8%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-32)))].
Abbreviation finA_uvi := [Some (1, 2 ^ 62); Some (64, 2 ^ 62); Some (0, 127); Some (0, 130); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)].

#[using="Type"] Lemma fin_add_U : forall regs m (o sp u p : Z) (ret s0v s1v s2v : word),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 32) -> getr regs 10%bv = Z_to_bv 64 u -> getr regs 12%bv = Z_to_bv 64 p ->
  cellN SEGS_U m (sp - 8) 8 (bv_unsigned ret) -> cellN SEGS_U m (sp - 16) 8 (bv_unsigned s0v) ->
  cellN SEGS_U m (sp - 24) 8 (bv_unsigned s1v) -> cellN SEGS_U m (sp - 32) 8 (bv_unsigned s2v) ->
  ret_ok ret -> 0 <= u <= 127 -> 0 <= p <= 130 ->
  64 <= sp -> sp <= 2 ^ 62 -> 1 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 48 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_U m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_U (mkst regs (Z_to_bv 64 0x365c4) m rom) (mkst regs' ret m' rom)
    /\ cellN SEGS_U m' o 2 (Z.max u p)
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v
    /\ keeps [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] regs regs'
    /\ unch m m' [(o, o + 2)] /\ mem_grows m m'.
Proof.
  intros regs m o sp u p ret s0v s1v s2v R8 R2 R10 R12 C1 C2 C3 C4 Hret Hu Hp Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto.
  pose proof (u64_range ret) as U1. pose proof (u64_range s0v) as U2. pose proof (u64_range s1v) as U3. pose proof (u64_range s2v) as U4.
  destruct (Z_lt_dec u p) as [Hlt | Hge].
  - zx_run SEGS_U constr:(CTX (vi_regs ++ finA_uvi) finA_kn [KW (ZV 32) 0 516])
      40%nat [0x365e8] (SCR [true] []) constr:(finA_pins)
      [o; sp; u; p; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v] constr:(finA_uvi) regs m rom 0x365c4.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C1; kc1 C2; kc1 C3; kc1 C4; exact I) ltac:(kw1 Hsto; exact I) ltac:(zwidth; zx_lia).
    zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [rewrite Z.max_r by lia; cellx|].
    split; [zx_regv ZR|].
    split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [unchx | growsx].
  - zx_run SEGS_U constr:(CTX (vi_regs ++ finA_uvi) finA_kn [KW (ZV 32) 0 516])
      40%nat [0x365e8] (SCR [false] []) constr:(finA_pins)
      [o; sp; u; p; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v] constr:(finA_uvi) regs m rom 0x365c4.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C1; kc1 C2; kc1 C3; kc1 C4; exact I) ltac:(kw1 Hsto; exact I) ltac:(zwidth; zx_lia).
    zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_U; [exact R1' | exact Hret]|].
    split; [rewrite Z.max_l by lia; cellx|].
    split; [zx_regv ZR|].
    split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [unchx | growsx].
Qed.

End S.
