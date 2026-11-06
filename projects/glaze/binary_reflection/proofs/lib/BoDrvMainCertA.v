(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvBridgeLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.
   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AzImageBoth.
Import ListNotations. Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
#[local] Notation u := bv_unsigned.

Lemma elenZ_lit : forall E z, 0 <= z < 2 ^ 64 -> elenZ E (ELit z) = z.
Proof. intros E z Hz. unfold elenZ. cbn [edenot]. apply u64_lit. exact Hz. Qed.

Lemma flat_lit : forall E o n, 0 <= o -> 0 <= n -> o < 2 ^ 64 -> o + n <= 2 ^ 64 -> n < 2 ^ 64 -> flat E (SA (ELit 0) o) (elenZ E (ELit n)).
Proof. intros E o n H1 H2 H3 H4 H5. unfold flat. rewrite estart_lit0, elenZ_lit by lia. lia. Qed.

Lemma kzero_lit_sub : forall segs E M o n o' n',
  kentry_ok segs E M (KZero (SA (ELit 0) o) (ELit n)) -> 0 <= n < 2 ^ 64 -> o <= o' < 2 ^ 64 -> 0 <= n' -> o' + n' <= o + n ->
  kentry_ok segs E M (KZero (SA (ELit 0) o') (ELit n')).
Proof.
  intros segs E M o n o' n' [HF HZ] Hn Ho Hn' Hle. cbn [kentry_ok]. unfold flat in HF. rewrite estart_lit0, elenZ_lit in HF, HZ by lia.
  split; [apply flat_lit; lia|]. rewrite estart_lit0, elenZ_lit by lia.
  intros i Hi. replace (o' + i) with (o + (o' - o + i)) by lia. apply HZ. lia.
Qed.




(* [comment removed for export] *)
Definition perm_wseg_b : bool :=
  forallb (fun w => match fst w, snd w with
                    | ELit a, ELit n => (Z.leb 0 a && Z.leb 0 n && Z.ltb (a + n) (2 ^ 64) && wseg_ok BSEGS (Z_to_bv 64 a) (Z.to_nat n))%bool
                    | _, _ => false end) PERM_A.
Lemma perm_wseg_ok : perm_wseg_b = true.
Proof.   (* [comment removed for export] *)
  assert (F : forallb (fun w => match fst w, snd w with
                    | ELit a, ELit n => (Z.leb 0 a && Z.leb 0 n && Z.ltb (a + n) (2 ^ 64) && StoreOk.WsegFast.wseg_fast BSEGS (Z_to_bv 64 a) (Z.to_nat n))%bool
                    | _, _ => false end) PERM_A = true) by (vm_cast_no_check (eq_refl true)).
  unfold perm_wseg_b. apply forallb_forall. intros [wa wn] Hw. pose proof (proj1 (forallb_forall _ _) F (wa, wn) Hw) as X. cbn [fst snd] in X |- *.
  destruct wa; destruct wn; try discriminate X. apply andb_prop in X as [X1 X2]. rewrite X1. cbn [andb]. exact (StoreOk.WsegFast.wseg_fast_ok _ _ _ X2).
Qed.
Lemma PERM_A_kwr : forall E M, know_ok BSEGS E M (map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A).
Proof.
  intros E M. unfold know_ok. apply Forall_forall. intros K HK. apply in_map_iff in HK as (w & <- & Hw).
  pose proof (proj1 (forallb_forall _ _) perm_wseg_ok w Hw) as X. cbv beta in X.
  destruct w as [wa wn]. cbn [fst snd] in X |- *. destruct wa as [a| | | | | | |]; try discriminate X. destruct wn as [n| | | | | | |]; try discriminate X.
  apply andb_prop in X as [X HW]. apply andb_prop in X as [X H3]. apply andb_prop in X as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  (* [comment removed for export] *)
  cbn [kentry_ok]. assert (Hst : estart E (SA (ELit a) 0) = a) by (unfold estart; cbn [a_base a_off edenot]; rewrite u64_lit by lia; lia).
  split; [unfold flat; rewrite Hst, elenZ_lit by lia; lia|]. rewrite Hst, elenZ_lit by lia.
  intros d m Hd Hdm.
  apply (store_ok_sub BSEGS M (Z_to_bv 64 a) (Z_to_bv 64 (a + d)) (Z.to_nat n) m); [rewrite u64_lit by lia; lia | exact (store_ok_wseg BSEGS M _ _ HW) | |];
    rewrite !u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kshok_lit_of_kzero : forall segs E M so sn a n,
  kentry_ok segs E M (KZero (SA (ELit 0) so) (ELit sn)) -> 0 <= sn < 2 ^ 64 ->
  0 <= a -> 0 <= n -> a + n <= 2 ^ 47 ->
  (forall z, a <= z < a + n -> so <= SB + z / 8 < so + sn) ->
  kentry_ok segs E M (KShOk (SA (ELit 0) a) (ELit n)).
Proof.
  intros segs E M so sn a n [HF HZ] Hsn Ha Hn H47 Hcov. cbn [kentry_ok]. rewrite estart_lit0, elenZ_lit in HZ by lia.
  split; [apply flat_lit; lia|]. rewrite estart_lit0, elenZ_lit by lia. split; [exact H47|].
  intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
  pose proof (Hcov z Hz) as Hc. replace (SB + z / 8) with (so + (SB + z / 8 - so)) by lia. apply HZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BOOT_SH : list kentry :=
  [KZero (SA (ELit 0) 0x7fffa000) (ELit 0x255c);      (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x7fffcd58) (ELit 0x1c7c0);     (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x80019560) (ELit 0xab0a0);     (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x7fffc570) (ELit 0x7bc);       (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x7fffcd58) (ELit 0x1c7c0);     (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x7fffc560) (ELit 1); KWord (SA (ELit 0) 0x7fffc561) 1 (ELit 4);    (* [comment removed for export] *)
   KZero (SA (ELit 0) 0x7fffc564) (ELit 3)].          (* [comment removed for export] *)

Lemma rdn1_shadow_byte : forall (M : word -> option byte) (a : Z) (v : Z),
  g_img_hi GBOTH <= a < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdn BSEGS M (Z_to_bv 64 a) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 v)) -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Ha Hv H. cbn [rdn] in H.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:Hm.
  - injection H as H. rewrite H. rewrite u64_lit by lia. reflexivity.
  - exfalso. unfold seg_rom, memory_read in H. change (Z.of_N 1) with 1 in H.
    rewrite (both_segs_hi (Z_to_bv 64 a)) in H by (rewrite u64_lit by (cbn [g_img_hi GBOTH] in Ha; lia); lia). discriminate H.
Qed.

Ltac zc := repeat split; vm_compute; first [reflexivity | let X := fresh in intro X; discriminate X].
Lemma LOWSH_GLZSH_of_boot : forall E M, know_ok BSEGS E M BOOT_SH -> know_ok BSEGS E M (LOWSH ++ GLZSH).
Proof.
  intros E M HK. unfold know_ok in HK. unfold BOOT_SH in HK.
  apply Forall_cons_iff in HK as [Z0 HK]. apply Forall_cons_iff in HK as [Z1 HK]. apply Forall_cons_iff in HK as [Z2 HK].
  apply Forall_cons_iff in HK as [ZA HK]. apply Forall_cons_iff in HK as [ZB HK]. apply Forall_cons_iff in HK as [ZH HK].
  apply Forall_cons_iff in HK as [WH HK]. apply Forall_cons_iff in HK as [ZR _].
  unfold know_ok, LOWSH, GLZSH. cbn [app].
  repeat apply Forall_cons; try apply Forall_nil.
  - exact Z0.
  - apply (kzero_lit_sub BSEGS E M 0x7fffcd58 0x1c7c0); [exact Z1 | lia | lia | lia | lia].
  - apply (kzero_lit_sub BSEGS E M 0x80019560 0xab0a0); [exact Z2 | lia | lia | lia | lia].
  - exact ZA.
  - apply (kshok_lit_of_kzero BSEGS E M 0x7fffc570 0x7bc); [exact ZA | lia | lia | lia | lia |].
    intros z Hz. unfold SB. Z.div_mod_to_equations. lia.
  - apply (kzero_lit_sub BSEGS E M 0x7fffcd58 0x1c7c0); [exact ZB | zc | zc | zc | zc].
  - apply (kshok_lit_of_kzero BSEGS E M (SB + 0x26ac0 / 8) ((0x31340 - 0x26ac0) / 8)); [apply (kzero_lit_sub BSEGS E M 0x7fffcd58 0x1c7c0); [exact ZB | zc | zc | zc | zc] | vm_compute; split; [intro X; discriminate X | reflexivity] | lia | lia | lia |].
    intros z Hz. unfold SB. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    destruct ZH as [_ ZHz]. destruct WH as (_ & _ & WHr).
    rewrite estart_lit0, elenZ_lit in ZHz by lia.
    assert (B0 : M (Z_to_bv 64 0x7fffc560) = Some (Z_to_bv 8 0)) by (specialize (ZHz 0 ltac:(lia)); rewrite Z.add_0_r in ZHz; exact ZHz).
    assert (B1 : M (Z_to_bv 64 0x7fffc561) = Some (Z_to_bv 8 4)).
    { apply rdn1_shadow_byte; [cbn [g_img_hi GBOTH]; lia | lia |].
      replace (adenot E (SA (ELit 0) 0x7fffc561)) with (Z_to_bv 64 0x7fffc561) in WHr by (symmetry; apply bv_eq; reflexivity). exact WHr. }
    cbn [kentry_ok]. split; [apply flat_lit; lia|]. rewrite estart_lit0, elenZ_lit by lia. split; [lia|].
    intros z Hz. destruct (Z_lt_ge_dec z 0x22b08) as [Hlt|Hge].
    + exists (Z_to_bv 8 0). split; [|left; reflexivity]. replace (SB + z / 8) with 0x7fffc560 by (unfold SB; Z.div_mod_to_equations; lia). exact B0.
    + exists (Z_to_bv 8 4). split; [replace (SB + z / 8) with 0x7fffc561 by (unfold SB; Z.div_mod_to_equations; lia); exact B1|].
      right. change (bv_unsigned (Z_to_bv 8 4)) with 4. Z.div_mod_to_equations. lia.
  - exact Z0.
  - apply (kshok_lit_of_kzero BSEGS E M 0x7fffa000 0x255c); [exact Z0 | lia | lia | lia | lia |].
    intros z Hz. unfold SB. Z.div_mod_to_equations. lia.
  - apply (kshok_lit_of_kzero BSEGS E M 0x7fffc564 3); [exact ZR | lia | lia | lia | lia |].
    intros z Hz. unfold SB. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma store_ok1_defined : forall (M : word -> option byte) (a : word),
  g_img_hi GBOTH <= u a -> store_ok BSEGS M a 1 = true -> M a <> None.
Proof.
  intros M a Ha H. cbn [store_ok] in H. unfold wview in H. intros Hn. rewrite Hn in H.
  rewrite (both_segs_hi a Ha) in H. discriminate H.
Qed.

Lemma stack_trio : forall E E' (M : word -> option byte) (eb0 esh : expr) (s0 : Z),
  kentry_ok BSEGS E M (KWr (SA eb0 (-8388608)) (ELit 8388608)) ->
  kentry_ok BSEGS E M (KZero (SA esh 0x7FEF8000) (ELit 1048576)) ->
  u (edenot E eb0) = s0 -> 8 * u (edenot E esh) = s0 -> u (edenot E' SP0) = s0 - 48 ->
  0x7fff80000000 <= s0 <= 2 ^ 47 ->
  know_ok BSEGS E' M [KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO); KShOk (SA SP0 (- YLO)) (ELit (YLO + 48))].
Proof.
  intros E E' M eb0 esh s0 [FW HW] [FZ HZ] Hs0 Hsh Hsp Hr.
  assert (L1 : elenZ E (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
  assert (L2 : elenZ E (ELit 1048576) = 1048576) by (apply elenZ_lit; lia).
  assert (L3 : elenZ E' (ELit YLO) = YLO) by (apply elenZ_lit; unfold YLO; lia).
  assert (L4 : elenZ E' (ELit (YLO + 48)) = YLO + 48) by (apply elenZ_lit; unfold YLO; lia).
  assert (S1 : estart E (SA eb0 (-8388608)) = s0 - 8388608) by (unfold estart; cbn [a_base a_off]; lia).
  assert (S2 : estart E (SA esh 0x7FEF8000) = u (edenot E esh) + 0x7FEF8000) by (unfold estart; cbn [a_base a_off]; lia).
  assert (S3 : estart E' (SA SP0 (- YLO)) = s0 - 8388608) by (unfold estart; cbn [a_base a_off]; unfold YLO; lia).
  rewrite L1, S1 in HW. rewrite L2, S2 in HZ.
  assert (FL : forall n, 0 <= n <= 8388608 -> flat E' (SA SP0 (- YLO)) n) by (intros n Hn; unfold flat; rewrite S3; lia).
  unfold know_ok. repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok].
  - rewrite L3, S3. split; [apply FL; unfold YLO; lia|]. intros d m Hd Hdm. apply HW; unfold YLO in *; lia.
  - rewrite L3, S3. split; [apply FL; unfold YLO; lia|]. intros i Hi. unfold YLO in Hi.
    apply store_ok1_defined; [rewrite u64_lit by lia; cbn [g_img_hi GBOTH]; lia|].
    exact (HW i 1%nat ltac:(lia) ltac:(lia)).
  - rewrite L4, S3. split; [apply FL; unfold YLO; lia|]. split; [unfold YLO; lia|].
    intros z Hz. exists (Z_to_bv 8 0). split; [|left; reflexivity].
    replace (SB + z / 8) with (u (edenot E esh) + 0x7FEF8000 + (z / 8 - (s0 - 8388608) / 8)).
    + apply HZ. unfold YLO in Hz. Z.div_mod_to_equations. lia.
    + unfold SB. unfold YLO in Hz. Z.div_mod_to_equations. lia.
Qed.
End BoDrvBridgeLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoStartupTabs.BoStartupHSc OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA.BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.BoDrvHooksA OSSVerify.Proofs.glaze.binary_reflection.lib.AsDrvMainCertA.AsDrvBridgeEnv BoDrvBridgeLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP.
Open Scope Z_scope.

Definition hregh (hs : acs) (r : nat) : expr := nth r (s_regs (a_ss hs)) (ELit 0).
Definition D0th : expr := eadd (escale 8 (EVar 1)) (eadd (escale 8 (EVar 2)) (ELit 232)).
(* [comment removed for export] *)
Definition thA (hs : acs) : list expr :=
  [ hregh hs 2; EVar 1; D0th; EVar 3; ELit 0; eadd D0th (eaddz (EVar 3) 1); EVar 7; EVar 46; EVar 64;
    ELit 0; hregh hs 5; hregh hs 6; hregh hs 7; ELit 0; ELit 0; hregh hs 13; hregh hs 14; hregh hs 15; hregh hs 16; hregh hs 17;
    ELit 0; hregh hs 28; hregh hs 29; hregh hs 30; hregh hs 31; hregh hs 12; ELit 0; ELit 0; ELit 0 ].

Definition pass1 (hs : acs) (K : kentry) : bool :=
  let K' := ktsubst (thA hs) K in if kn_incl1_h AT_B (kn hs) K' then true else kpure_entails (kn hs) K'.
Definition TKsyn : list kentry := Eval vm_compute in filter (pass1 HS_1) (knM ++ knO).

(* [comment removed for export] *)
Definition e_shb : expr := eadd (escale 4096 (EVar 0)) (escale 2 (EVar 6)).                     (* [comment removed for export] *)
Definition e_b64 : expr :=                                                                       (* [comment removed for export] *)
  EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0))
    (EAlu Instr.ALU_ADD (EVar 1) (EAlu Instr.ALU_ADD (EVar 2) (EAlu Instr.ALU_ADD (EVar 4) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 2) (EVar 6)) (EVar 12))))).
Definition BOOTF : list kentry :=
  BOOT_SH ++
  [ KWr (SA e_sp0 (-8388608)) (ELit 8388608); KZero (SA e_shb 0x7FEF8000) (ELit 1048576);
    KZero (SA e_b64 2146926617) (ELit 524288); kw_argv1 e_argv1w ].

Definition POV (n : nat) : bool := negb (existsb (Nat.eqb n) [4; 13; 14; 26; 27]%nat).
Definition hull_b (k : list kentry) : bool :=
  forallb (fun K => match K with KImg lo hi => (img_lo AT_B <=? lo) && (hi <=? img_hi AT_B) | _ => true end) k.

Lemma ent_syn_1 : kn_ent AT_B (kn HS_1) (map (ktsubst (thA HS_1)) TKsyn) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ent_syn_2 : kn_ent AT_B (kn HS_2) (map (ktsubst (thA HS_2)) TKsyn) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ent_boot_1 : kn_ent AT_B (kn HS_1) BOOTF = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma ent_boot_2 : kn_ent AT_B (kn HS_2) BOOTF = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma regs_1 : regs_ent (kn HS_1) 0 (map (tsubst (thA HS_1)) regsM) (s_regs (a_ss HS_1)) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma regs_2 : regs_ent (kn HS_2) 0 (map (tsubst (thA HS_2)) regsM) (s_regs (a_ss HS_2)) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hull_1 : hull_b (kn HS_1) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma hull_2 : hull_b (kn HS_2) = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma okb_syn : forallb (kentry_okb POV) TKsyn = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma okb_regs : forallb (expr_okb POV) regsM = true. Proof. vm_cast_no_check (eq_refl true). Qed.

