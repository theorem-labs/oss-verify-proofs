(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
  BnModel BnMath BnZX BnZXTac BnMem BnDefs LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast.
Import ListNotations. Import ZX BM. Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint addm (c : Z) (l o : list Z) : list Z * Z :=
  match o with
  | [] => ([], c)
  | y :: o' => let s := hd 0 l + y + c in
               let (r, c') := addm (s / B) (tl l) o' in ((s mod B) :: r, c')
  end.

Lemma add_l_addm : forall o l c,
  add_l c l o = fst (addm c l o) ++ addc_l (snd (addm c l o)) (skipn (length o) l).
Proof.
  induction o as [|y o IH]; intros l c; cbn [addm add_l fst snd length skipn]; [reflexivity|].
  destruct l as [|x t]; cbn [hd tl].
  - rewrite Z.add_0_l. specialize (IH [] ((y + c) / B)). destruct (addm ((y + c) / B) [] o) as [r c']. cbn [fst snd] in *.
    rewrite IH. destruct o; reflexivity.
  - specialize (IH t ((x + y + c) / B)). destruct (addm ((x + y + c) / B) t o) as [r c']. cbn [fst snd] in *.
    rewrite IH. reflexivity.
Qed.

Lemma addm_length : forall o l c, length (fst (addm c l o)) = length o.
Proof.
  induction o as [|y o IH]; intros l c; cbn [addm fst length]; [reflexivity|].
  specialize (IH (tl l) ((hd 0 l + y + c) / B)). destruct (addm _ (tl l) o) as [r c']. cbn [fst length] in *. rewrite <- IH. reflexivity.
Qed.

Lemma addm_bounds : forall o l c, ok l -> ok o -> 0 <= c <= 1 ->
  ok (fst (addm c l o)) /\ 0 <= snd (addm c l o) <= 1.
Proof.
  induction o as [|y o IH]; intros l c Hl Ho Hc; cbn [addm fst snd]; [split; [apply ok_nil|lia]|].
  apply ok_cons in Ho as [Hy Ho].
  assert (Hx : 0 <= hd 0 l < B) by (destruct l as [|x t]; cbn; [unfold B; lia | apply ok_cons in Hl as [Hx _]; exact Hx]).
  assert (Htl : ok (tl l)) by (destruct l as [|x t]; cbn; [apply ok_nil | apply ok_cons in Hl as [_ Ht]; exact Ht]).
  assert (Hc' : 0 <= (hd 0 l + y + c) / B <= 1) by (unfold B in *; lia).
  specialize (IH (tl l) _ Htl Ho Hc'). destruct (addm _ (tl l) o) as [r c']. cbn [fst snd] in *.
  destruct IH as [Hr Hc'']. split; [|exact Hc'']. apply ok_cons. split; [apply mod_B_range | exact Hr].
Qed.

Lemma addc_l_len_cases : forall l c, ok l -> 0 < c <= 1 ->
  exists k, 1 <= k /\ zlen (addc_l c l) = Z.max (zlen l) k /\ k <= zlen l + 1.
Proof.
  induction l as [|x t IH]; intros c Hl Hc.
  - cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). exists 1. rewrite zlen_cons, !zlen_nil. lia.
  - cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply ok_cons in Hl as [Hx Ht].
    destruct (Z.eq_dec ((x + c) / B) 0) as [Hz|Hnz].
    + rewrite Hz. exists 1. rewrite !zlen_cons.
      destruct t as [|z t']; cbn [addc_l Z.eqb]; rewrite ?zlen_cons, ?zlen_nil; [lia|]. pose proof (zlen_nonneg t'). lia.
    + destruct (IH ((x + c) / B) Ht ltac:(unfold B in *; lia)) as (k & Hk & Hlen & Hkb).
      exists (k + 1). rewrite !zlen_cons, Hlen. pose proof (zlen_nonneg t). lia.
Qed.

Lemma addc_l_ok : forall l c, ok l -> 0 <= c < B -> ok (addc_l c l).
Proof.
  induction l as [|x t IH]; intros c Hl Hc; cbn [addc_l]; destruct (Z.eqb_spec c 0); auto.
  - apply ok_cons. split; [lia | apply ok_nil].
  - apply ok_cons in Hl as [Hx Ht]. apply ok_cons. split; [apply mod_B_range | apply IH; [exact Ht | unfold B in *; lia]].
Qed.

Section S.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addL_pins :=
  [(5%bv : reg, ZAdd (ZV 32) (ZL 4)); (9%bv : reg, ZAdd (ZV 33) (ZL 4)); (13%bv : reg, ZMul (ZV 34) (ZL 4));
   (21%bv : reg, ZV 34); (15%bv : reg, ZSub (ZL 0) (ZV 34)); (16%bv : reg, ZSub (ZL 0) (ZV 34)); (12%bv : reg, ZV 35);
   (11%bv : reg, ZV 36); (6%bv : reg, ZMul (ZV 37) (ZL 4)); (10%bv : reg, ZL 268435455)].
Abbreviation addL_uvi := [Some (0, 2 ^ 62); Some (0, 2 ^ 62); Some (0, 130); Some (0, 1); Some (0, 127); Some (1, 130); Some (0, 2 ^ 28 - 1); Some (0, 2 ^ 28 - 1)].
Definition addL_keep : list Z := [1; 2; 3; 4; 5; 6; 8; 9; 10; 11; 14; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 30; 31].

#[using="Type"] Lemma add_loop_P : forall ot odone lt done c regs m (o q u : Z),
  let i := Z.of_nat (length odone) in
  let n := Z.of_nat (length odone) + Z.of_nat (length ot) in
  Z.of_nat (length done) = i ->
  getr regs 5%bv = Z_to_bv 64 (o + 4) -> getr regs 9%bv = Z_to_bv 64 (q + 4) -> getr regs 13%bv = Z_to_bv 64 (i * 4) ->
  getr regs 21%bv = Z_to_bv 64 i -> getr regs 15%bv = Z_to_bv 64 (0 - i) -> getr regs 16%bv = Z_to_bv 64 (0 - i) ->
  getr regs 12%bv = Z_to_bv 64 c -> getr regs 11%bv = Z_to_bv 64 u -> getr regs 6%bv = Z_to_bv 64 (n * 4) ->
  getr regs 10%bv = Z_to_bv 64 MASK ->
  Z.max u i = i + zlen lt -> 0 <= u <= 127 -> n <= 127 -> ok lt -> ok ot -> ot <> [] -> 0 <= c <= 1 ->
  0 <= o -> o + 516 <= 2 ^ 62 -> 0 <= q -> q + 516 <= 2 ^ 62 -> (q + 516 <= o \/ o + 516 <= q) ->
  arr32 SEGS_P m (o + 4) (done ++ lt) -> arr32 SEGS_P m (q + 4) (odone ++ ot) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' S,
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35fb0) m rom) (mkst regs' (Z_to_bv 64 0x35fc0) m' rom)
    /\ arr32 SEGS_P m' (o + 4) (done ++ fst (addm c lt ot) ++ skipn (length ot) lt)
    /\ getr regs' 12%bv = Z_to_bv 64 (snd (addm c lt ot)) /\ getr regs' 28%bv = Z_to_bv 64 S
    /\ S / 2 ^ 28 = snd (addm c lt ot) /\ 0 <= S < 2 ^ 30
    /\ getr regs' 21%bv = Z_to_bv 64 n /\ getr regs' 15%bv = Z_to_bv 64 (0 - n) /\ getr regs' 16%bv = Z_to_bv 64 (0 - n)
    /\ getr regs' 13%bv = Z_to_bv 64 (n * 4)
    /\ keeps addL_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * i, o + 4 + 4 * n)] /\ mem_grows m m'.
Proof.
  induction ot as [|y ot IH]; intros odone lt done c regs m o q u i n Hdone R5 R9 R13 R21 R15 R16 R12 R11 R6 R10
    Hmax Hu Hn Hokl Hoko Hne Hc Ho1 Ho2 Hq1 Hq2 Hdj Harr Harro Hsto; [congruence|].
  subst i n. apply ok_cons in Hoko as [Hy Hoko]. cbn [length] in *. unfold MASK in R10. unfold B in *.
  set (i := Z.of_nat (length odone)) in *.
  assert (Hidef : i = Z.of_nat (length odone)) by reflexivity.
  assert (Hi : 0 <= i) by lia.
  assert (Hcy : exists bs, rdn SEGS_P m (Z_to_bv 64 (q + 4 + i * 4 + 0)) 4 = Some bs /\ bytes_le_to_Z bs = y).
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
      zx_run SEGS_P constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x35fb0; 0x35fc0] (SCR [false; true] [ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + 1; 0; y] constr:(addL_uvi) regs m rom 0x35fb0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia] | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]])).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (y + c). split; [exact ZM|].
      split.
      { rewrite ?app_nil_r. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc' ; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_P constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x35fb0; 0x35fc0] (SCR [false; false] [ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); 0; y] constr:(addL_uvi) regs m rom 0x35fb0.
      zx_use ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia] | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_P m1 (o + 4) ((done ++ [(y + c) mod 268435456]) ++ [])).
      { rewrite !app_nil_r. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_snoc'; [lia | lia | rewrite app_nil_r in Harr; exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_P m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      specialize (IH (odone ++ [y]) [] (done ++ [(y + c) mod 268435456]) ((0 + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C28 & HS & HS2 & C21 & C15 & C16 & C13 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { rewrite zlen_nil. lia. } { lia. } { lia. } { apply ok_nil. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Hdj. } { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      cbn [skipn app] in Harr2. rewrite <- app_assoc in Harr2. cbn [app] in Harr2. rewrite ?app_nil_r in Harr2.
      split; [rewrite ?app_nil_r; replace (0 + y + c) with (y + c) by lia; exact Harr2|].
      split; [exact C12|]. split; [exact C28|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C21; f_equal; lia|]. split; [rewrite C15; f_equal; lia|]. split; [rewrite C16; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
  - (* [comment removed for export] *)
    cbn [hd tl skipn]. unfold B in *. rewrite zlen_cons in Hmax. apply ok_cons in Hokl as [Hx Hokt]. unfold B in Hx. pose proof (zlen_nonneg t) as Hlt1. assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity.
    assert (Hcx : exists bs, rdn SEGS_P m (Z_to_bv 64 (o + 4 + i * 4 + 0)) 4 = Some bs /\ bytes_le_to_Z bs = x).
    { eapply kc_of_arr32; [exact Harr | lia]. }
    destruct (addm ((x + y + c) / 268435456) t ot) as [r c'] eqn:Hrec. cbn [fst snd].
    destruct ot as [|y2 ot'].
    + (* [comment removed for export] *)
      cbn [length] in *. change (Z.of_nat 1) with 1 in *.
      zx_run SEGS_P constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x35fb0; 0x35fc0] (SCR [true; true] [ZV 38; ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + 1; x; y] constr:(addL_uvi) regs m rom 0x35fb0.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]])).
      zx_name regs1.
      cbn in Hrec. injection Hrec as <- <-. cbn [app skipn length]. rewrite ?skipn_O.
      eexists regs1, _, (x + c + y). split; [exact ZM|].
      split.
      { replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      split; [zx_regv ZR; f_equal; lia|]. split; [zx_regv ZR|]. split; [f_equal; lia|]. split; [lia|].
      split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|]. split; [zx_regv ZR|].
      split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
      split; [unchx | growsx].
    + (* [comment removed for export] *)
      cbn [length] in *.
      zx_run SEGS_P constr:(CTX (vi_regs ++ addL_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x35fb0; 0x35fc0] (SCR [true; false] [ZV 38; ZV 39])
        constr:(addL_pins) [o; q; i; c; u; i + Z.of_nat (S (S (length ot'))); x; y] constr:(addL_uvi) regs m rom 0x35fb0.
      zx_use ZXB ltac:(zx_pins) ltac:(cbn [length] in *; zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcy as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_P m1 (o + 4) ((done ++ [(x + y + c) mod 268435456]) ++ t)).
      { rewrite <- app_assoc. cbn [app]. unfold m1. replace (o + 4 + i * 4) with (o + 4 + 4 * Z.of_nat (length done)) by lia.
        apply arr32_store' with (x := x); [lia | rewrite length_app; cbn [length]; lia | exact Harr |].
        rewrite u_Z2bv64. rewrite (Z.mod_small _ 18446744073709551616) by lia. rewrite Z.mod_small by lia. f_equal; lia. }
      assert (Harro1 : arr32 SEGS_P m1 (q + 4) ((odone ++ [y]) ++ y2 :: ot')).
      { rewrite <- app_assoc. cbn [app]. unfold m1. apply arr32_store_other; zwidth; rewrite ?length_app; cbn [length]; try lia. exact Harro. }
      specialize (IH (odone ++ [y]) t (done ++ [(x + y + c) mod 268435456]) ((x + y + c) / 268435456) regs1 m1 o q u).
      rewrite !length_app in IH. cbn [length] in IH. rewrite Hrec in IH. cbn [fst snd] in IH.
      destruct IH as (regs2 & m2 & S & M2 & Harr2 & C12 & C28 & HS & HS2 & C21 & C15 & C16 & C13 & K2 & U2 & G2).
      { lia. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { exact Hokt. } { exact Hoko. } { congruence. } { lia. }
      { lia. } { lia. } { lia. } { lia. } { exact Hdj. } { exact Harr1. } { exact Harro1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, S. split; [eapply msteps_trans; [exact ZM | exact M2]|].
      rewrite <- app_assoc in Harr2. cbn [app] in Harr2.
      split; [exact Harr2|].
      split; [exact C12|]. split; [exact C28|]. split; [exact HS|]. split; [exact HS2|].
      split; [rewrite C21; f_equal; lia|]. split; [rewrite C15; f_equal; lia|]. split; [rewrite C16; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
      split; [eapply keeps_trans; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity | exact K2]|].
      split.
      * apply (unch_trans m m1 m2); [unfold m1; unchx|]. eapply unch_widen; [exact U2|].
        intros rg Hrg. cbn in Hrg. destruct Hrg as [<-|[]]. eexists; split; [left; reflexivity|]. cbn. lia.
      * apply (mem_grows_trans m m1 m2); [unfold m1; growsx | exact G2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma arr32_tail : forall m a x l, arr32 SEGS_P m a (x :: l) -> arr32 SEGS_P m (a + 4) l.
Proof.
  intros m a x l H i Hi. specialize (H (S i) ltac:(cbn; lia)). cbn [nth] in H.
  replace (a + 4 + 4 * Z.of_nat i) with (a + 4 * Z.of_nat (S i)) by lia. exact H.
Qed.

#[using="Type"] Lemma arr32_cons : forall m a x l, cellN SEGS_P m a 4 x -> arr32 SEGS_P m (a + 4) l -> arr32 SEGS_P m a (x :: l).
Proof.
  intros m a x l Hc H i Hi. destruct i as [|i].
  - cbn [nth]. replace (a + 4 * Z.of_nat 0%nat) with a by lia. exact Hc.
  - cbn [nth]. specialize (H i ltac:(cbn in Hi; lia)). replace (a + 4 * Z.of_nat (S i)) with (a + 4 + 4 * Z.of_nat i) by lia. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Abbreviation addC_pins :=
  [(14%bv : reg, ZV 33); (11%bv : reg, ZV 35); (13%bv : reg, ZAdd (ZAdd (ZV 32) (ZL 4)) (ZMul (ZV 33) (ZL 4)));
   (12%bv : reg, ZV 34); (10%bv : reg, ZL 268435455); (21%bv : reg, ZV 33)].
Abbreviation addC_uvi := [Some (0, 2 ^ 62); Some (0, 130); Some (1, 1); Some (0, 127); Some (0, 2 ^ 28 - 1)].
Definition addC_keep : list Z := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].

#[using="Type"] Lemma addc_loop_P : forall lt (pos c : Z) regs m (o u : Z),
  getr regs 14%bv = Z_to_bv 64 pos -> getr regs 11%bv = Z_to_bv 64 u -> getr regs 13%bv = Z_to_bv 64 (o + 4 + pos * 4) ->
  getr regs 12%bv = Z_to_bv 64 c -> getr regs 10%bv = Z_to_bv 64 MASK -> getr regs 21%bv = Z_to_bv 64 pos ->
  Z.max u pos = pos + zlen lt -> 0 <= u <= 127 -> 0 <= pos -> pos + zlen lt + 1 <= 128 -> ok lt -> 0 < c <= 1 ->
  0 <= o -> o + 516 <= 2 ^ 62 ->
  arr32 SEGS_P m (o + 4 + 4 * pos) lt ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m' k,
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x36054) m rom) (mkst regs' (Z_to_bv 64 0x35fd8) m' rom)
    /\ arr32 SEGS_P m' (o + 4 + 4 * pos) (addc_l c lt)
    /\ 1 <= k /\ zlen (addc_l c lt) = Z.max (zlen lt) k
    /\ getr regs' 21%bv = Z_to_bv 64 (pos + k)
    /\ keeps addC_keep regs regs'
    /\ unch m m' [(o + 4 + 4 * pos, o + 4 + 4 * (pos + zlen (addc_l c lt)))] /\ mem_grows m m'.
Proof.
  induction lt as [|x t IH]; intros pos c regs m o u R14 R11 R13 R12 R10 R21 Hmax Hu Hpos Hcap Hok Hc Ho1 Ho2 Harr Hsto.
  - (* [comment removed for export] *)
    rewrite zlen_nil in *. unfold MASK in R10.
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    zx_run SEGS_P constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x36054; 0x35fd8] (SCR [false] [])
      constr:(addC_pins) [o; pos; c; u; 0] constr:(addC_uvi) regs m rom 0x36054.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
      ltac:(idtac; zx_scs ltac:(eapply sc_store_in; [exact Hsto|zwidth; lia])).
    zx_name regs1.
    eexists regs1, _, 1. split; [exact ZM|].
    split.
    { change [c] with ([] ++ [c]). replace (o + 4 + pos * 4) with (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z [])) by (cbn; lia).
      apply arr32_snoc'; [lia | cbn; lia | exact Harr |]. rewrite u_Z2bv64. rewrite Z.mod_small by lia. apply Z.mod_small. lia. }
    split; [lia|]. split; [rewrite zlen_cons, zlen_nil; lia|]. split; [zx_regv ZR|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    rewrite zlen_cons, zlen_nil. split; [unchx | growsx].
  - apply ok_cons in Hok as [Hx Hok]. rewrite zlen_cons in *. pose proof (zlen_nonneg t) as Ht0.
    assert (Hzt : zlen t = Z.of_nat (length t)) by reflexivity. unfold MASK in R10. unfold B in Hx.
    assert (Hcx : exists bs, rdn SEGS_P m (Z_to_bv 64 (o + 4 + 4 * pos + 4 * Z.of_nat (@length Z []))) 4 = Some bs /\ bytes_le_to_Z bs = x).
    { eapply (kc_of_arr32 _ _ _ []); [exact Harr | reflexivity]. }
    cbn [length] in Hcx.
    cbn [addc_l]. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold addc_l. unfold B in *.
    destruct (Z.eq_dec ((x + c) / 268435456) 0) as [Hz | Hnz].
    + (* [comment removed for export] *)
      zx_run SEGS_P constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x36054; 0x35fd8] (SCR [true; true] [ZV 36])
        constr:(addC_pins) [o; pos; c; u; x] constr:(addC_uvi) regs m rom 0x36054.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | lia])).
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
      zx_run SEGS_P constr:(CTX (vi_regs ++ addC_uvi) (@nil kcell) [KW (ZV 32) 0 516]) 30%nat [0x36054; 0x35fd8] (SCR [true; false] [ZV 36])
        constr:(addC_pins) [o; pos; c; u; x] constr:(addC_uvi) regs m rom 0x36054.
      zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(exact I) ltac:(kw1 Hsto; exact I)
        ltac:(idtac; zx_scs ltac:(first [eapply sc_store_in; [exact Hsto|zwidth; lia]
                                 | destruct Hcx as (bs & Hbs & Hbv); exists bs; split; [etransitivity; [|exact Hbs]; f_equal; f_equal; lia | exact Hbv]
                                 | lia])).
      zx_name regs1.
      set (m1 := wbytes m _ _) in ZM.
      assert (Harr1 : arr32 SEGS_P m1 (o + 4 + 4 * (pos + 1)) t).
      { unfold m1. apply arr32_store_other; zwidth; try lia. replace (o + 4 + 4 * (pos + 1)) with (o + 4 + 4 * pos + 4) by lia. eapply arr32_tail. exact Harr. }
      destruct (IH (pos + 1) 1 regs1 m1 o u) as (regs2 & m2 & k & M2 & Harr2 & Hk & Hlen2 & C21 & K2 & U2 & G2).
      { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. } { zx_regv ZR. }
      { lia. } { lia. } { lia. } { lia. } { exact Hok. } { lia. } { lia. } { lia. } { exact Harr1. }
      { unfold m1. eapply store_ok_grows; [apply grows_store | exact Hsto]. }
      eexists regs2, m2, (k + 1). split; [eapply msteps_trans; [exact ZM | exact M2]|].
      split.
      { apply arr32_cons; [|replace (o + 4 + 4 * pos + 4) with (o + 4 + 4 * (pos + 1)) by lia; exact Harr2].
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
Abbreviation finA_kn := [KC (ZV 33) (-8) 8 (ZV 36); KC (ZV 33) (-16) 8 (ZV 37); KC (ZV 33) (-24) 8 (ZV 38); KC (ZV 33) (-32) 8 (ZV 39);
                         KC (ZV 33) (-40) 8 (ZV 40); KC (ZV 33) (-48) 8 (ZV 41); KC (ZV 33) (-56) 8 (ZV 42); KC (ZV 33) (-64) 8 (ZV 43);
                         KC (ZV 33) (-72) 8 (ZV 44); KC (ZV 33) (-80) 8 (ZV 45)].
Abbreviation finA_pins := [(8%bv : reg, ZV 32); (2%bv : reg, ZAdd (ZV 33) (ZL (-80))); (20%bv : reg, ZV 34); (21%bv : reg, ZV 35)].
Abbreviation finA_uvi := [Some (0, 2 ^ 62); Some (96, 2 ^ 62); Some (0, 127); Some (0, 130); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1); Some (0, 2 ^ 64 - 1)].

#[using="Type"] Lemma fin_add_P : forall regs m (o sp u p : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v : word),
  getr regs 8%bv = Z_to_bv 64 o -> getr regs 2%bv = Z_to_bv 64 (sp - 80) -> getr regs 20%bv = Z_to_bv 64 u -> getr regs 21%bv = Z_to_bv 64 p ->
  cellN SEGS_P m (sp - 8) 8 (bv_unsigned ret) -> cellN SEGS_P m (sp - 16) 8 (bv_unsigned s0v) ->
  cellN SEGS_P m (sp - 24) 8 (bv_unsigned s1v) -> cellN SEGS_P m (sp - 32) 8 (bv_unsigned s2v) ->
  cellN SEGS_P m (sp - 40) 8 (bv_unsigned s3v) -> cellN SEGS_P m (sp - 48) 8 (bv_unsigned s4v) ->
  cellN SEGS_P m (sp - 56) 8 (bv_unsigned s5v) -> cellN SEGS_P m (sp - 64) 8 (bv_unsigned s6v) ->
  cellN SEGS_P m (sp - 72) 8 (bv_unsigned s7v) -> cellN SEGS_P m (sp - 80) 8 (bv_unsigned s8v) ->
  ret_ok ret -> 0 <= u <= 127 -> 0 <= p <= 130 ->
  96 <= sp -> sp <= 2 ^ 62 -> 0 <= o -> o + 516 <= 2 ^ 62 -> (o + 516 <= sp - 80 \/ sp <= o) ->
  RiscvSemantics.store_ok SEGS_P m (Z_to_bv 64 o) 516 = true ->
  exists regs' m',
    msteps SEGS_P (mkst regs (Z_to_bv 64 0x35fd8) m rom) (mkst regs' ret m' rom)
    /\ cellN SEGS_P m' o 2 (Z.max u p)
    /\ getr regs' 2%bv = Z_to_bv 64 sp /\ getr regs' 8%bv = s0v /\ getr regs' 9%bv = s1v /\ getr regs' 18%bv = s2v
    /\ getr regs' 19%bv = s3v /\ getr regs' 20%bv = s4v /\ getr regs' 21%bv = s5v /\ getr regs' 22%bv = s6v
    /\ getr regs' 23%bv = s7v /\ getr regs' 24%bv = s8v
    /\ keeps [3; 4; 25; 26; 27] regs regs'
    /\ unch m m' [(o, o + 2)] /\ mem_grows m m'.
Proof.
  intros regs m o sp u p ret s0v s1v s2v s3v s4v s5v s6v s7v s8v R8 R2 R20 R21 C1 C2 C3 C4 C5 C6 C7 C8 C9 C10
    Hret Hu Hp Hsp1 Hsp2 Ho1 Ho2 Hdisj Hsto.
  pose proof (u64_range ret) as U1. pose proof (u64_range s0v) as U2. pose proof (u64_range s1v) as U3. pose proof (u64_range s2v) as U4. pose proof (u64_range s3v) as U5.
  pose proof (u64_range s4v) as U6. pose proof (u64_range s5v) as U7. pose proof (u64_range s6v) as U8. pose proof (u64_range s7v) as U9. pose proof (u64_range s8v) as U10.
  destruct (Z_lt_dec u p) as [Hlt | Hge].
  - zx_run SEGS_P constr:(CTX (vi_regs ++ finA_uvi) finA_kn [KW (ZV 32) 0 516])
      60%nat [0x36010] (SCR [true] []) constr:(finA_pins)
      [o; sp; u; p; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v; bv_unsigned s5v; bv_unsigned s6v; bv_unsigned s7v; bv_unsigned s8v]
      constr:(finA_uvi) regs m rom 0x35fd8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C1; kc1 C2; kc1 C3; kc1 C4; kc1 C5; kc1 C6; kc1 C7; kc1 C8; kc1 C9; kc1 C10; exact I) ltac:(kw1 Hsto; exact I) ltac:(zwidth; zx_lia).
    zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [rewrite Z.max_r by lia; cellx|].
    split; [zx_regv ZR|].
    split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (19%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (20%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (21%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (22%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (23%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (24%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [unchx | growsx].
  - zx_run SEGS_P constr:(CTX (vi_regs ++ finA_uvi) finA_kn [KW (ZV 32) 0 516])
      60%nat [0x36010] (SCR [false] []) constr:(finA_pins)
      [o; sp; u; p; bv_unsigned ret; bv_unsigned s0v; bv_unsigned s1v; bv_unsigned s2v; bv_unsigned s3v; bv_unsigned s4v; bv_unsigned s5v; bv_unsigned s6v; bv_unsigned s7v; bv_unsigned s8v]
      constr:(finA_uvi) regs m rom 0x35fd8.
    zx_use ZXB ltac:(zx_pins) ltac:(zx_lia) ltac:(kc1 C1; kc1 C2; kc1 C3; kc1 C4; kc1 C5; kc1 C6; kc1 C7; kc1 C8; kc1 C9; kc1 C10; exact I) ltac:(kw1 Hsto; exact I) ltac:(zwidth; zx_lia).
    zx_name regs1.
    assert (R1' : getr regs1 1%bv = ret) by (zx_reg ZR (1%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned).
    eexists regs1, _. split; [eapply msteps_trans; [exact ZM|]; zx_ret SEGS_P; [exact R1' | exact Hret]|].
    split; [rewrite Z.max_l by lia; cellx|].
    split; [zx_regv ZR|].
    split; [zx_reg ZR (8%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (9%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (18%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (19%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (20%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (21%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (22%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (23%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [zx_reg ZR (24%bv : reg) as HH; rewrite HH; apply Z_to_bv_bv_unsigned|].
    split; [eapply (keeps_of_zx _ _ _ _ _ _ ZE ZR); vm_compute; reflexivity|].
    split; [unchx | growsx].
Qed.

#[using="Type"] Lemma arr32_skip : forall m a l1 l2, arr32 SEGS_P m a (l1 ++ l2) -> arr32 SEGS_P m (a + 4 * Z.of_nat (length l1)) l2.
Proof.
  intros m a l1 l2 H i Hi. specialize (H (length l1 + i)%nat ltac:(rewrite length_app; lia)).
  rewrite app_nth2 in H by lia. replace (length l1 + i - length l1)%nat with i in H by lia.
  replace (a + 4 * Z.of_nat (length l1) + 4 * Z.of_nat i) with (a + 4 * Z.of_nat (length l1 + i)) by lia. exact H.
Qed.

#[using="Type"] Lemma arr32_app : forall m a l1 l2, arr32 SEGS_P m a l1 -> arr32 SEGS_P m (a + 4 * Z.of_nat (length l1)) l2 -> arr32 SEGS_P m a (l1 ++ l2).
Proof.
  intros m a l1 l2 H1 H2 i Hi. rewrite length_app in Hi.
  destruct (Nat.lt_ge_cases i (length l1)) as [Hl|Hr].
  - rewrite app_nth1 by lia. apply H1. lia.
  - rewrite app_nth2 by lia. specialize (H2 (i - length l1)%nat ltac:(lia)).
    replace (a + 4 * Z.of_nat (length l1) + 4 * Z.of_nat (i - length l1)) with (a + 4 * Z.of_nat i) in H2 by lia. exact H2.
Qed.


End S.
