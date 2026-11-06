(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 604 of its 627 lines of code are new or changed and 122 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/check_step.v, with its module paths and module names changed; 89 of its 131 lines of code are new or changed and 585 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/A/P_check_step_S3_aux.v, with its module paths changed; 137 of its 159 lines of code are new or changed and 109 lines of the source are left out. *)
(* Facts for segment S2 of the ASan walk of check_step (fuzz_scene.asan-ubsan): the bytes the two bcmp calls
   compare. The same text as lib/A/P_check_step_S2_aux.v over lib.AU (YCbq and the kit from lib.AU, gate 6o); the
   two globals sit at the same addresses in both images (AU/P_check_step_cut.v:100-101, objects 7 and 8).
   - s2_payload_nth (pure): C3's bcmp compares blk + (k ? 7 : 9) with body + scene_off k over scene_len k bytes; the
     block's bytes there are the body's.
   - s2_trailer_nth (pure): C4's bcmp (k = 342) compares blk + 21 with check_step.trailer over 12 bytes; the block's
     bytes there are scene_trailer.
   - s2_trailer_shadow (kit): check_step.trailer [0x20d80, +12) is addressable and its shadow hull is mapped in every
     AR state, from the named B facts: shadow 0x7fffc1b0 = 0 (the trailer's zero range, al_zshadow through
     SceneRo.zs_zero), 0x7fffc1b1 = 4 and 0x7fffc1b2, 0x7fffc1b3 = 0xf9 (constant cells, am_const, as cgif
     A/AE2m.v:27-33), 0x7fffc1b4 .. 0x7fffc1b7 = 0 (the frame's zero range). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YCbq.  (* image-specific: lib.AU (gate 6o) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaRun PaShadow SceneSyms SceneList ScenePa.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import PaJournal ScenePaLib SceneBase SceneRo SceneFrame YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import SceneBlock RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU.Prog Require Import P_reac_ctrl_checksum_verify P_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import P_check_step_cut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.
(* ---- pure ---- *)
Lemma s2_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s2_nth_skipn : forall {A} (l : list A) m n d, nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A l m. revert l. induction m as [|m IH]; intros l n d; [reflexivity|].
  destruct l as [|x l]; [destruct n; reflexivity|]. cbn [skipn]. exact (IH l n d).
Qed.
(* The block after its 7-byte head (magic, type, segment, 0, length, 0) is the payload, then the checksum byte. *)
Lemma s2_sb_nth : forall b k m d, nth (7 + m) (scene_block b k) d =
  nth m (scene_payload b k ++ [Z_to_bv 8 ((256 - byte_sum (scene_fields b k) mod 256) mod 256)]) d.
Proof. intros b k m d. reflexivity. Qed.
Lemma s2_payload_nth : forall b k i, length b = 8904%nat -> 0 <= k <= 342 -> 0 <= i < scene_len k ->
  nth (Z.to_nat ((if k =? 0 then 9 else 7) + i)) (scene_block b k) (Z_to_bv 8 0) =
  nth (Z.to_nat (scene_off k + i)) b (Z_to_bv 8 0).
Proof.
  intros b k i Hb Hk Hi. norm_nat_lits.
  destruct (Z.eq_dec k 0) as [->|H0].
  - replace (if 0 =? 0 then 9 else 7) with 9 by reflexivity.
    change (scene_len 0) with 24 in Hi. change (scene_off 0) with 0. rewrite Z.add_0_l.
    replace (Z.to_nat (9 + i)) with (7 + (2 + Z.to_nat i))%nat by lia.
    rewrite s2_sb_nth. change (scene_payload b 0) with ([Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b).
    rewrite app_nth1 by (rewrite length_app, length_firstn, Hb; cbn [length]; lia).
    cbn [nth app Nat.add]. rewrite s2_nth_firstn by lia. reflexivity.
  - assert (Eif : (if k =? 0 then 9 else 7) = 7) by (rewrite (proj2 (Z.eqb_neq k 0) H0); reflexivity).
    rewrite Eif. replace (Z.to_nat (7 + i)) with (7 + Z.to_nat i)%nat by lia. rewrite s2_sb_nth.
    destruct (Z.eq_dec k 342) as [->|H1].
    + change (scene_len 342) with 14 in Hi. change (scene_off 342) with 8890.
      change (scene_payload b 342) with (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer).
      rewrite app_nth1 by (rewrite length_app, length_firstn, length_skipn, Hb; unfold scene_trailer;
        rewrite length_map; cbn [length]; lia).
      rewrite app_nth1 by (rewrite length_firstn, length_skipn, Hb; lia).
      rewrite s2_nth_firstn by lia. rewrite s2_nth_skipn. rewrite Z2Nat.inj_add by lia. reflexivity.
    + assert (EL : scene_len k = 26)
        by (unfold scene_len; rewrite (proj2 (Z.eqb_neq k 0) H0), (proj2 (Z.eqb_neq k 342) H1); reflexivity).
      assert (EO : scene_off k = 24 + 26 * (k - 1))
        by (unfold scene_off; rewrite (proj2 (Z.eqb_neq k 0) H0), (proj2 (Z.eqb_neq k 342) H1); reflexivity).
      assert (EP : scene_payload b k = firstn 26 (skipn (Z.to_nat (scene_off k)) b))
        by (unfold scene_payload; rewrite (proj2 (Z.eqb_neq k 0) H0), (proj2 (Z.eqb_neq k 342) H1); reflexivity).
      rewrite EL in Hi. rewrite EP.
      rewrite app_nth1 by (rewrite length_firstn, length_skipn, Hb, EO; lia).
      rewrite s2_nth_firstn by lia. rewrite s2_nth_skipn. rewrite Z2Nat.inj_add by (rewrite ?EO; lia). reflexivity.
Qed.
Lemma s2_trailer_nth : forall b i, length b = 8904%nat -> 0 <= i < 12 ->
  nth (Z.to_nat (21 + i)) (scene_block b 342) (Z_to_bv 8 0) = nth (Z.to_nat i) scene_trailer (Z_to_bv 8 0).
Proof.
  intros b i Hb Hi. norm_nat_lits.
  replace (Z.to_nat (21 + i)) with (7 + (14 + Z.to_nat i))%nat by lia.
  rewrite s2_sb_nth. change (scene_payload b 342) with (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer).
  assert (LT : length scene_trailer = 12%nat) by reflexivity.
  rewrite app_nth1 by (rewrite length_app, length_firstn, length_skipn, Hb, LT; lia).
  rewrite app_nth2 by (rewrite length_firstn, length_skipn, Hb; lia).
  rewrite length_firstn, length_skipn, Hb.
  lazymatch goal with |- nth ?x scene_trailer _ = _ => replace x with (Z.to_nat i) by lia end.
  reflexivity.
Qed.
Lemma s2_le_byte1 : forall v, 0 <= v < 256 -> YG0f.le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.
(* ---- kit ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg scene_listing}.
#[local] Notation SEGS := (@pa_segs _ scene_listing PI).
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Lemma s2_trailer_shadow :
  Exists (zr_sub (A_CS_TRAILER, 8)) (as_zero_shadow B) ->
  Exists (zr_sub (A_CS_CFRAME, 48)) (as_zero_shadow B) ->
  (forall ly, In (z1 (ANum (shadow_addr A_CS_TRAILER + 1)) 4) (as_const B ly) /\
    In (z1 (ANum (shadow_addr A_CS_TRAILER + 2)) 0xf9) (as_const B ly) /\
    In (z1 (ANum (shadow_addr A_CS_TRAILER + 3)) 0xf9) (as_const B ly) /\
    In (z1 (ANum (shadow_addr A_CS_CFRAME + 6)) 2) (as_const B ly) /\
    Forall (fun i => In (z1 (ANum (shadow_addr A_CS_CFRAME + i)) 0xf9) (as_const B ly)) [7; 8; 9; 10; 11]) ->
  A_CS_TRAILER = 0x20d80 /\ A_CS_CFRAME = 0x20da0 ->
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF A_CS_TRAILER 12 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) A_CS_TRAILER 12.
Proof.
  intros HZT HZC HC [ET EC] ly S W mem md HAR.
  set (rd := aview SEGS (w_H W) mem).
  (* a byte of a zero range has shadow 0 *)
  assert (ZR : forall a n x s, Exists (zr_sub (a, n)) (as_zero_shadow B) -> a <= x < a + n ->
    s = SHADOW_OFF + x / 8 -> rd s = Some 0).
  { intros a n x s HE Hx ->. apply Exists_exists in HE as ((q & m) & Hin & Hsub).
    unfold zr_sub in Hsub. cbn [fst snd] in Hsub.
    destruct (zs_range _ _ q m Hin _ _ _ _ _ HAR) as (Hq0 & Hm0 & Hq8 & Hm8 & Hhi).
    pose proof (zs_zero _ _ LAWS q m Hin _ _ _ _ _ HAR) as Hz.
    replace (SHADOW_OFF + x / 8) with (shadow_of_addr SHADOW_OFF (q + (x - q)))
      by (unfold shadow_of_addr; f_equal; f_equal; lia).
    rewrite shadow_of_addr_aligned_off by exact Hq8. apply Hz.
    pose proof (Z.div_mod m 8 ltac:(lia)) as Dm.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  (* a constant one-byte cell *)
  assert (CL : forall a a' v, a = a' -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> rd a' = Some v).
  { intros a a' v <- Hin Hv. pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as X.
    unfold cell_holds in X. cbn [z1 c1 c_at c_val c_w aeval] in X.
    specialize (X 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X.
    unfold rd. rewrite X. rewrite s2_le_byte1 by exact Hv. reflexivity. }
  destruct (HC ly) as (C1 & C2 & C3 & _ & _).
  pose proof (ZR _ _ 0x20d80 0x7fffc1b0 HZT ltac:(rewrite ET; lia) eq_refl) as R0.
  pose proof (CL (shadow_addr A_CS_TRAILER + 1) 0x7fffc1b1 4 ltac:(rewrite ET; reflexivity) C1 ltac:(lia)) as R1.
  pose proof (CL (shadow_addr A_CS_TRAILER + 2) 0x7fffc1b2 0xf9 ltac:(rewrite ET; reflexivity) C2 ltac:(lia)) as R2.
  pose proof (CL (shadow_addr A_CS_TRAILER + 3) 0x7fffc1b3 0xf9 ltac:(rewrite ET; reflexivity) C3 ltac:(lia)) as R3.
  pose proof (ZR _ _ 0x20da0 0x7fffc1b4 HZC ltac:(rewrite EC; lia) eq_refl) as R4.
  pose proof (ZR _ _ 0x20da8 0x7fffc1b5 HZC ltac:(rewrite EC; lia) eq_refl) as R5.
  pose proof (ZR _ _ 0x20db0 0x7fffc1b6 HZC ltac:(rewrite EC; lia) eq_refl) as R6.
  pose proof (ZR _ _ 0x20db8 0x7fffc1b7 HZC ltac:(rewrite EC; lia) eq_refl) as R7.
  rewrite ET. split.
  - intros x Hx. destruct (Z_lt_ge_dec x 0x20d88) as [Lx|Gx].
    + assert (E : shadow_of_addr SHADOW_OFF x = 0x7fffc1b0)
        by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
      exists 0. rewrite E. split; [exact R0 | unfold saddr_ok; left; reflexivity].
    + assert (E : shadow_of_addr SHADOW_OFF x = 0x7fffc1b1)
        by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
      exists 4. rewrite E. split; [exact R1 | unfold saddr_ok; right; split; Z.div_mod_to_equations; lia].
  - intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs.
    assert (Es : s = 0x7fffc1b0 \/ s = 0x7fffc1b1 \/ s = 0x7fffc1b2 \/ s = 0x7fffc1b3 \/
                 s = 0x7fffc1b4 \/ s = 0x7fffc1b5 \/ s = 0x7fffc1b6 \/ s = 0x7fffc1b7)
      by (revert Hs; Z.div_mod_to_equations; lia).
    destruct Es as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      first [rewrite R0 | rewrite R1 | rewrite R2 | rewrite R3 | rewrite R4 | rewrite R5 | rewrite R6 | rewrite R7];
      discriminate.
Qed.
End f.
End d.
