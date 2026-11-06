(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147, for
   libreac/fuzz_identity's ASan build (lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC81 YC4b YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition p6_regs (i c : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 14%bv (SLit 7)) 11%bv (SLit 48)) 23%bv (SLit i)) 16%bv (SLit c).
Definition p6_dnreg : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 1 [].
Definition p6_mem : smem :=
  [ YP09.mkRegion (Some 13%nat) 0 7 0 0
      [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 105));
       YP09.mkChunk 2 (CVal 1 (SLit 110)); YP09.mkChunk 3 (CVal 1 (SLit 32));
       YP09.mkChunk 4 (CVal 1 (SLit 47)); YP09.mkChunk 5 (CVal 1 (SLit 32));
       YP09.mkChunk 6 (CVal 1 (SLit 0))];
    YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
    YP09.mkRegion (Some 9%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 32 0))] ].
Definition p6_facts : facts :=
  mkFacts [ (22%nat, mkAF SB SB 0); (13%nat, mkAF IMG_LO IMG_TOP 3);
            (32%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 4096 (2 ^ 47 - 8) 0);
            (34%nat, mkAF 0 7 0); (15%nat, mkAF 0 47 0) ]
    []
    [ (SAlu ALU_ADD (SOff 32 0) (SOff 15 0), SOff 33 0);
      (SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 22 0), SOff 35 0) ].
Definition p6_ss (i c : Z) : sstate :=
  mkSS (AF_reac_box_name + RBN_L6) (p6_regs i c) p6_mem None p6_facts.
Definition P6BX : sv := SOff 22 0.
Definition P6SPAN : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition P6SH : list shent := [ mkSHE 33 0 1 ].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition E6 (regsE : bvmap 5 word) (Dv dn sv sa : Z) : env :=
  Eimg (Ereg regsE (map (Z_to_bv 64) [Dv; dn; sv; sa])).
Lemma p_val_mem_eq : forall (H : word -> bool) (m m' : word -> option byte) a (nn : nat) v,
  (forall x, a <= x < a + Z.of_nat nn -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a nn v -> val_mem SEGS (mrestrict H m') a nn v.
Proof.
intros H m m' a nn v Heq Hv j Hj.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (Heq (a + Z.of_nat j) ltac:(lia))).
apply Hv. exact Hj.
Qed.
Lemma p_garr8_eq : forall (H : word -> bool) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H m' x = aview SEGS H m x) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l Heq Hg j Hj. split; [|exact (proj2 (Hg j Hj))].
apply (p_val_mem_eq H m m' (a + Z.of_nat j) 1 (nth j l 0)).
- intros x Hx. apply Heq. lia.
- exact (proj1 (Hg j Hj)).
Qed.
Lemma p_ra_eq : forall (H : word -> bool) (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview SEGS H m' (SHADOW_OFF + x / 8) = aview SEGS H m (SHADOW_OFF + x / 8)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n ->
  range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
intros H m m' a n Heq Hra x Hx. destruct (Hra x Hx) as (s & Hs & Hok).
exists s. split; [|exact Hok]. unfold shadow_of_addr in *. rewrite (Heq x Hx). exact Hs.
Qed.
Lemma p_val_mem1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v /\ 0 <= v < 256.
Proof.
intros H m a v Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; cbn in Hv; [|discriminate].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Hr.
change (bv_modulus 8) with 256 in Hr. split; [|exact Hr].
intros j Hj. assert (Hj0 : (j = 0)%nat) by lia. subst j.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r, Hb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small (bv_unsigned b) 256) by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma p_rd_aview : forall (H : word -> bool) (m : word -> option byte),
  rd_of SEGS (mrestrict H m) = aview SEGS H m.
Proof. intros H m. reflexivity. Qed.
Lemma p_sh_apart : forall Dv x, in_app Dv 48 -> Dv <= x < Dv + 48 ->
  SHADOW_OFF + x / 8 < Dv \/ Dv + 48 <= SHADOW_OFF + x / 8.
Proof.
intros Dv x [H0 Hz] Hx.
pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma p_dnreg_ok : forall E' (m : word -> option byte) (dn : Z),
  bv_unsigned (ew E' 33) = dn -> 0 <= dn -> dn + 1 <= 2 ^ 64 ->
  writable_at SEGS m dn -> region_ok SEGS E' m p6_dnreg.
Proof.
intros E' m dn H0 H1 H2 Hw. unfold region_ok, p6_dnreg.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H0. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. replace (dn + o) with dn by lia. exact Hw.
Qed.
Lemma p_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' lo hi HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma p_garr8_snoc : forall (H : word -> bool) (m : word -> option byte) a l v,
  garr8 SEGS (mrestrict H m) a l ->
  val_mem SEGS (mrestrict H m) (a + Z.of_nat (length l)) 1 v -> 0 <= v < 256 ->
  garr8 SEGS (mrestrict H m) a (l ++ [v]).
Proof.
intros H m a l v Hg Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by exact Hlt. exact (Hg j Hlt).
- assert (Hje : j = length l) by lia. subst j.
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. split; [exact Hv | exact Hr].
Qed.
Ltac p6_awr_store E33h dn HBWh :=
  lazymatch goal with
  | |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in
    change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0);
    eapply (awr_ok_cons_gen E0 _ _ stk s0 fp b0 bc ly0 own0 33%nat dn);
      [ reflexivity
      | cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33h; apply unsigned_lit_small; lia
      | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply (HBWh a ltac:(lia))
      | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ]
  end.
Ltac p6_awr_ro :=
  lazymatch goal with
  | |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in
    change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0);
    repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil
  end.
Ltac p6_frame HFrh lo hi E33h E13h E35h E9h Kname :=
  pose proof (p_kept_frame _ _ _ _ _ lo hi HFrh
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with
          | In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr
          end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?ew_ewset_other in Hw by lia;
          rewrite ?E33h, ?E13h, ?E35h, ?E9h in Hw; rewrite ?unsigned_lit_small in Hw by lia; lia)) as Kname.
Ltac p6_efact HS n En G :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ecur _ _ =>
    lazymatch type of En with
    | ew _ _ = ?v =>
      assert (G : ew Ecur n = v) by
        (cbn [extK]; rewrite ?ew_ewset_other by lia; exact En)
    end
  end.
Ltac p6_agree HAE :=
  lazymatch goal with
  | |- env_agree 32 _ (ewset ?X ?m ?v) =>
      apply (env_agree_trans 32 _ X);
      [p6_agree HAE | apply (YP03.env_agree_le 32 m); [lia | apply env_agree_ewset]]
  | |- _ => exact HAE
  end.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma p6_entry : forall (W : world SEGS) (regsE : bvmap 5 word) memE (i c n ov Dv A1 s : Z),
  getr regsE 15 = w64 n -> getr regsE 12 = w64 ov -> getr regsE 16 = w64 c ->
  getr regsE 23 = w64 i -> getr regsE 14 = w64 7 -> getr regsE 11 = w64 48 ->
  getr regsE 13 = w64 (VAL (A_OBJ 23)) -> getr regsE 9 = w64 A1 -> getr regsE 22 = w64 SHADOW_OFF ->
  0 <= i < 8 -> 0 <= c < 256 -> 0 <= n <= 47 ->
  in_app Dv 48 -> Dv + 48 <= 2 ^ 47 ->
  VAL (A_OBJ 23) mod 8 = 0 ->
  (VAL (A_OBJ 23) + 7 <= Dv \/ Dv + 48 <= VAL (A_OBJ 23)) ->
  alloc_ceiling <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 23) \/ VAL (A_OBJ 23) + 7 <= A1 + 120) ->
  (A1 + 128 <= Dv \/ Dv + 48 <= A1 + 120) ->
  val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 Dv ->
  garr8 SEGS (mrestrict (w_H W) memE) (VAL (A_OBJ 23)) (rbn_lit6 ++ [0]) ->
  aview SEGS (w_H W) memE (SHADOW_OFF + VAL (A_OBJ 23) / 8) = Some s -> 0 <= s <= 7 ->
  st_ok_pi SEGS VAL (E6 regsE Dv (Dv + n) s (SHADOW_OFF + VAL (A_OBJ 23) / 8)) (p6_ss i c)
    (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6))) memE (seg_rom SEGS))).
Proof.
intros W regsE memE i c n ov Dv A1 s R15 R12 R16 R23 R14 R11 R13 R9 R22
  Hi Hc Hn Happ H47 Hal HSEP HA1lo HA1hi HA1lit HA1D HSLOT HG HS Hs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
destruct Happ as (HD0 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
assert (HDn : 4096 <= Dv + n <= 2 ^ 47 - 8) by lia.
rewrite restrict_mkst_fx.
set (E := E6 regsE Dv (Dv + n) s sa).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regsE (map (Z_to_bv 64) [Dv; Dv + n; s; sa])) m)
  by (intros m Hm; subst E; unfold E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; subst E; unfold E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 Dv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Dv + n))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 s)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E15 : ew E 15 = Z_to_bv 64 n) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (VB : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v).
{ intros m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. }
unfold p6_ss, p6_mem, p6_facts. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [| intros X; discriminate X | rewrite R16; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R23; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R11; cbn [sv_denot]; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X | rewrite R14; cbn [sv_denot]; reflexivity].
  apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite (VB 13%nat lit E13) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ lit 0 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
      pose proof (proj1 (HG 0%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 1 1 (SLit 105) 105); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 1%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 1) with 1 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 2 1 (SLit 110) 110); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 2%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 2) with 2 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 3 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 3%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 3) with 3 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 4 1 (SLit 47) 47); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 4%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 4) with 4 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 5 1 (SLit 32) 32); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 5%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 5) with 5 in Hb. exact Hb.
    * apply (chunk_ok_val SEGS E _ lit 6 1 (SLit 0) 0); [reflexivity | zside | zside |].
      change (N.to_nat 1) with 1%nat.
      pose proof (proj1 (HG 6%nat ltac:(cbn; lia))) as Hb.
      cbn [rbn_lit6 app nth] in Hb. change (Z.of_nat 6) with 6 in Hb. exact Hb.
  + rewrite (VB 35%nat sa E35) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sa 0 1 (SOff 34 0) s);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    change (N.to_nat 1) with 1%nat. rewrite Z.add_0_r.
    exact (proj1 (p_val_mem1_of_aview (w_H W) memE sa s HS)).
  + rewrite (VB 9%nat A1 E9) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ A1 120 8 (SOff 32 0) Dv);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
    change (N.to_nat 8) with 8%nat. exact HSLOT.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB 13%nat lit E13) by lia. rewrite (VB 35%nat sa E35) by lia.
  rewrite (VB 9%nat A1 E9) by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E22, unsigned_lit_small by (unfold SHADOW_OFF; lia);
            rewrite Z.pow_0_r, Z.mod_1_r; unfold SB, SHADOW_OFF; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E13, unsigned_lit_small by lia;
            change (2 ^ 3) with 8; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E32, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E34, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia|].
    split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E15, unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia | exact I].
  + cbn [f_alias alias_ok]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 32 Dv E32 ltac:(lia)), (U_atom E 15 n E15 ltac:(lia)),
        (U_atom E 33 (Dv + n) E33 ltac:(lia)).
      unfold zcanon, M64. apply Z.mod_small. lia.
    * apply (shadow_decl_ok E 13 22 35 lit SHADOW_OFF E13 ltac:(lia) E22).
      rewrite E35. unfold sa. reflexivity.
Qed.
Definition p6_cnt (n0 i : Z) : Z := Z.min (i - 1) (47 - n0).
Definition p6_nn (n0 i : Z) : Z := n0 + p6_cnt n0 i.
Definition p6_ovv (n0 ov0 i : Z) : Z := if n0 + i - 1 <=? 47 then ov0 else 1.
Definition p6_wrl (n0 i : Z) : list Z := firstn (Z.to_nat (p6_cnt n0 i)) rbn_lit6.
Definition P6KEPT : list (bv 5) :=
  [1; 2; 3; 4; 6; 7; 8; 9; 13; 18; 19; 20; 21; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma p6_kreg : forall (r1 r2 : bvmap 5 word) (rb : bv 5) (z : Z) v,
  Z_to_bv 5 z = rb -> getr r2 rb = v -> getr r1 rb = v ->
  getr r2 (Z_to_bv 5 z) = getr r1 (Z_to_bv 5 z).
Proof. intros r1 r2 rb z v Hb H2 H1. subst rb. rewrite H2, H1. reflexivity. Qed.
Lemma p6_keep_of : forall (r1 r2 : bvmap 5 word),
  (forall r : bv 5, In r P6KEPT -> getr r2 r = getr r1 r) ->
  getr r2 (Z_to_bv 5 0) = getr r1 (Z_to_bv 5 0) ->
  getr r2 (Z_to_bv 5 11) = getr r1 (Z_to_bv 5 11) ->
  getr r2 (Z_to_bv 5 14) = getr r1 (Z_to_bv 5 14) ->
  rbn_keep_regs r1 r2 [5; 10; 12; 15; 16; 17; 23].
Proof.
intros r1 r2 H H0 H11 H14 z Hz Hnin.
assert (Hc : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/
  z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/
  z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/
  z = 30 \/ z = 31) by lia.
repeat (destruct Hc as [-> | Hc]); try subst z;
  first [ solve [exfalso; apply Hnin; cbn [In]; repeat first [left; reflexivity | right]]
        | exact H0 | exact H11 | exact H14
        | solve [apply H; unfold P6KEPT; cbn [In];
                 repeat first [left; apply bv_eq; vm_compute; reflexivity | right]] ].
Qed.
Section S6.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world SEGS) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word) (A1 D n0 ov0 : Z).
Hypothesis HSRC : rbn_lsrc W memc (VAL (A_OBJ 23)) (rbn_lit6 ++ [0]).
Hypothesis HAL : VAL (A_OBJ 23) mod 8 = 0.
Hypothesis HA1lo : alloc_ceiling <= A1 + 120.
Hypothesis HA1hi : A1 + 128 <= 2 ^ 47.
Hypothesis HA1lit : A1 + 128 <= VAL (A_OBJ 23) \/ VAL (A_OBJ 23) + 7 <= A1 + 120.
Hypothesis HBUF : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48.
Hypothesis HSEP : VAL (A_OBJ 23) + 7 <= D \/ D + 48 <= VAL (A_OBJ 23).
Hypothesis HSLOT : val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D.
Hypothesis HA1D : A1 + 128 <= D \/ D + 48 <= A1 + 120.
Hypothesis HN0 : 0 <= n0 <= 47.
Hypothesis HOV0 : ov0 = 0 \/ ov0 = 1.
Definition p6_pkg (i : Z) (regsE : bvmap 5 word) (memE : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + Z.of_nat (length (p6_wrl n0 i))) ->
     aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a) /\
  garr8 SEGS (mrestrict (w_H W) memE) (D + n0) (p6_wrl n0 i) /\
  (forall a, D <= a < D + 48 -> apresent (w_H W) memE a) /\
  rbn_keep_regs regs regsE [5; 10; 12; 15; 16; 17; 23] /\
  getr regsE 15 = w64 (p6_nn n0 i) /\ getr regsE 12 = w64 (p6_ovv n0 ov0 i) /\
  getr regsE 16 = w64 (nth (Z.to_nat (i - 1)) rbn_lit6 0) /\
  getr regsE 23 = w64 i /\ getr regsE 14 = w64 7 /\ getr regsE 11 = w64 48 /\
  getr regsE 13 = w64 (VAL (A_OBJ 23)) /\ getr regsE 9 = w64 A1 /\ getr regsE 22 = w64 SHADOW_OFF.
Definition p6_next (i : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = cfg_at SEGS (BASE + (if i <=? 6 then 10800 else 10912)) regs2 mem2 md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\ p6_pkg i regs2 mem2.
Definition p6_stmt (i : Z) : Prop :=
  forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p6_pkg i regsE memE ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_L6) regsE memE mdE) (p6_next (i + 1)).
Lemma p6_it1 : p6_stmt 1.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 1)) = p6_cnt n0 1)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 1 <= 0) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 1 = n0 + p6_cnt n0 1) by reflexivity.
assert (HnR : 0 <= p6_nn n0 1 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 1) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 1) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 1) mod 8 = 1)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 1) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (1 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 1 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 32) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 1 32 (p6_nn n0 1) (p6_ovv n0 ov0 1) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 1) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 1; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 1; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 1))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 1)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 1) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 1) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 1) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 1 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = 1).
    { unfold p6_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = 1).
    { unfold p6_ovv. replace (n0 + 2 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 1) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 1 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 1) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 1) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 2 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 1) HBW. }
    p6_frame HFr (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 1 = 0) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = p6_ovv n0 ov0 1).
    { unfold p6_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p6_nn n0 1) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 1) HBW. }
    p6_frame HFr (D + p6_nn n0 1) (D + p6_nn n0 1 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 1) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 1 = 0) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 2 = p6_nn n0 1 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 2 = p6_ovv n0 ov0 1).
    { unfold p6_ovv.
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 2 = p6_wrl n0 1 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (1 + 1) with 2. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 1)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 0) with (D + p6_nn n0 1) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_it2 : p6_stmt 2.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 2)) = p6_cnt n0 2)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 2 <= 1) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 2 = n0 + p6_cnt n0 2) by reflexivity.
assert (HnR : 0 <= p6_nn n0 2 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 2) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 2) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 2) mod 8 = 2)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 2) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (2 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 2 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 105) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 2 105 (p6_nn n0 2) (p6_ovv n0 ov0 2) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 2) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 2; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 2; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 2))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 2)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 2) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 2) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 2) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 2 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = 1).
    { unfold p6_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = 1).
    { unfold p6_ovv. replace (n0 + 3 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 2) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 2 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 2) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 2) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 3 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 2) HBW. }
    p6_frame HFr (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 2) _ 0 1 0 1 0 1%N (SLit 105) 105 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = p6_ovv n0 ov0 2).
    { unfold p6_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2 ++ [105]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p6_nn n0 2) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 2) HBW. }
    p6_frame HFr (D + p6_nn n0 2) (D + p6_nn n0 2 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 2) _ 0 1 0 1 0 1%N (SLit 105) 105 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 2 = 1) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 3 = p6_nn n0 2 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 3 = p6_ovv n0 ov0 2).
    { unfold p6_ovv.
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 2 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 3 = p6_wrl n0 2 ++ [105]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (2 + 1) with 3. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 2)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 1) with (D + p6_nn n0 2) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_it3 : p6_stmt 3.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 3)) = p6_cnt n0 3)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 3 <= 2) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 3 = n0 + p6_cnt n0 3) by reflexivity.
assert (HnR : 0 <= p6_nn n0 3 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 3) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 3) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 3) mod 8 = 3)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 3) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (3 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 3 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 110) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 3 110 (p6_nn n0 3) (p6_ovv n0 ov0 3) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 3) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 3; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 3; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 3))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 3)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 3) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 3) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 3) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 3 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = 1).
    { unfold p6_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = 1).
    { unfold p6_ovv. replace (n0 + 4 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 3) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 3 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 3) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 3) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 4 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 3) HBW. }
    p6_frame HFr (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 3) _ 0 1 0 1 0 1%N (SLit 110) 110 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = p6_ovv n0 ov0 3).
    { unfold p6_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3 ++ [110]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p6_nn n0 3) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 3) HBW. }
    p6_frame HFr (D + p6_nn n0 3) (D + p6_nn n0 3 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 3) _ 0 1 0 1 0 1%N (SLit 110) 110 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 3 = 2) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 4 = p6_nn n0 3 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 4 = p6_ovv n0 ov0 3).
    { unfold p6_ovv.
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 3 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 4 = p6_wrl n0 3 ++ [110]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (3 + 1) with 4. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 3)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 2) with (D + p6_nn n0 3) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_it4 : p6_stmt 4.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 4)) = p6_cnt n0 4)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 4 <= 3) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 4 = n0 + p6_cnt n0 4) by reflexivity.
assert (HnR : 0 <= p6_nn n0 4 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 4) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 4) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 4) mod 8 = 4)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 4) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (4 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 4 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 32) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 4 32 (p6_nn n0 4) (p6_ovv n0 ov0 4) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 4) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 4; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 4; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 4))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 4)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 4) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 4) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 4) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 4 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = 1).
    { unfold p6_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = 1).
    { unfold p6_ovv. replace (n0 + 5 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 4) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 4 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 4) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 4) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 5 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 4) HBW. }
    p6_frame HFr (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 4) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = p6_ovv n0 ov0 4).
    { unfold p6_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p6_nn n0 4) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 4) HBW. }
    p6_frame HFr (D + p6_nn n0 4) (D + p6_nn n0 4 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 4) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 4 = 3) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 5 = p6_nn n0 4 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 5 = p6_ovv n0 ov0 4).
    { unfold p6_ovv.
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 4 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 5 = p6_wrl n0 4 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (4 + 1) with 5. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 4)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 3) with (D + p6_nn n0 4) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_it5 : p6_stmt 5.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 5)) = p6_cnt n0 5)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 5 <= 4) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 5 = n0 + p6_cnt n0 5) by reflexivity.
assert (HnR : 0 <= p6_nn n0 5 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 5) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 5) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 5) mod 8 = 5)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 5) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (5 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 5 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 47) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 5 47 (p6_nn n0 5) (p6_ovv n0 ov0 5) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 5) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 5; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 5; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 5))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 5)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 5) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 5) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 5) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 5 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = 1).
    { unfold p6_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = 1).
    { unfold p6_ovv. replace (n0 + 6 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 5) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 5 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 5) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 5) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 6 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 5) HBW. }
    p6_frame HFr (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 5) _ 0 1 0 1 0 1%N (SLit 47) 47 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = p6_ovv n0 ov0 5).
    { unfold p6_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5 ++ [47]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p6_nn n0 5) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6).
    { p6_awr_store E33 (D + p6_nn n0 5) HBW. }
    p6_frame HFr (D + p6_nn n0 5) (D + p6_nn n0 5 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 5) _ 0 1 0 1 0 1%N (SLit 47) 47 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 5 = 4) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 6 = p6_nn n0 5 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 6 = p6_ovv n0 ov0 5).
    { unfold p6_ovv.
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 5 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 6 = p6_wrl n0 5 ++ [47]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (5 + 1) with 6. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 5)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 4) with (D + p6_nn n0 5) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_it6 : p6_stmt 6.
Proof.
unfold p6_stmt, p6_pkg.
intros regsE memE mdE HJ (HEQ & HWR & HPR & HKEEP & R15 & R12 & R16 & R23 & R14 & R11 & R13 & R9 & R22).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (pa_obj_img 23%nat ltac:(lia)) as HOB.
pose proof HSRC as (HGC & HP0 & HP63 & HP47 & HRA).
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
pose proof HAPP as (HD4096 & HDz). unfold kLowShadowBeg, kHighMemBeg in HDz.
set (lit := VAL (A_OBJ 23)) in *.
set (sa := SHADOW_OFF + lit / 8) in *.
assert (Hdiv : 0 <= lit / 8 <= lit) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HsaV : 2147450880 <= sa <= 2153734144) by (unfold sa, SHADOW_OFF; lia).
assert (Hlen : Z.of_nat (length (rbn_lit6 ++ [0])) = 7) by reflexivity.
assert (Hwr2 : Z.of_nat (length (p6_wrl n0 6)) = p6_cnt n0 6)
  by (unfold p6_wrl, p6_cnt; rewrite length_firstn; cbn [length rbn_lit6]; lia).
assert (Hc2 : 0 <= p6_cnt n0 6 <= 5) by (unfold p6_cnt; lia).
assert (HnB : p6_nn n0 6 = n0 + p6_cnt n0 6) by reflexivity.
assert (HnR : 0 <= p6_nn n0 6 <= 47) by (unfold p6_nn, p6_cnt; lia).
assert (HOUT : forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n0 + p6_cnt n0 6) ->
  aview SEGS (w_H W) memE a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hn; apply HEQ; [exact Ha | rewrite Hwr2; exact Hn]).
assert (HRA2 : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF lit 7).
{ apply (p_ra_eq (w_H W) memc memE lit 7); [|rewrite <- Hlen; exact HRA]. intros x Hx.
  assert (Hxd : 0 <= x / 8 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]). apply HOUT.
  - unfold SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF in *. lia. }
assert (HBRAE : range_addressable (aview SEGS (w_H W) memE) SHADOW_OFF D 48).
{ apply (p_ra_eq (w_H W) memc memE D 48); [|exact HBRA].
  intros x Hx. apply HOUT.
  - pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
    unfold SHADOW_OFF in *. lia.
  - pose proof (p_sh_apart D x HAPP Hx) as Hap. lia. }
assert (HGE : garr8 SEGS (mrestrict (w_H W) memE) lit (rbn_lit6 ++ [0])).
{ apply (p_garr8_eq (w_H W) memc memE lit (rbn_lit6 ++ [0])); [|exact HGC].
  intros x Hx. rewrite Hlen in Hx. apply HOUT; lia. }
assert (HSLOTE : val_mem SEGS (mrestrict (w_H W) memE) (A1 + 120) 8 D).
{ apply (p_val_mem_eq (w_H W) memc memE (A1 + 120) 8%nat D); [|exact HSLOT].
  intros x Hx. apply HOUT; cbn [Z.of_nat] in Hx; lia. }
destruct (HRA2 (lit + 6) ltac:(lia)) as (sv & Hsv & Hok).
assert (Hmod : (lit + 6) mod 8 = 6)
  by (rewrite <- Z.add_mod_idemp_l by lia; rewrite HAL; reflexivity).
assert (Hdv : (8 | lit)) by (apply Z.mod_divide; [lia | exact HAL]).
destruct Hdv as [q Hq].
assert (Hsha : SHADOW_OFF + (lit + 6) / 8 = sa).
{ unfold sa. rewrite Hq, Z.div_add_l by lia. rewrite Z.div_mul by lia.
  replace (6 / 8) with 0 by reflexivity. lia. }
unfold shadow_of_addr in Hsv. rewrite Hsha in Hsv.
destruct (p_val_mem1_of_aview (w_H W) memE sa sv Hsv) as (Hsvm & Hsvr0).
assert (Hsvr : 0 <= sv <= 7)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; lia).
assert (Hok2 : sv = 0 \/ 6 < sv)
  by (unfold saddr_ok in Hok; destruct Hok as [-> | (Hm & Hlt)]; [left; reflexivity | right; lia]).
assert (R16' : getr regsE 16 = w64 32) by (rewrite R16; f_equal; vm_compute; reflexivity).
pose proof (p6_entry W regsE memE 6 32 (p6_nn n0 6) (p6_ovv n0 ov0 6) D A1 sv
  R15 R12 R16' R23 R14 R11 R13 R9 R22 ltac:(lia) ltac:(lia) HnR HAPP ltac:(lia) HAL HSEP
  HA1lo HA1hi HA1lit HA1D HSLOTE HGE Hsv Hsvr) as HS.
fold lit in HS. fold sa in HS.
pose proof (paj_run B LAWS) as RUN.
pose proof (paj_run_to B LAWS) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
set (E := E6 regsE D (D + p6_nn n0 6) sv sa) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, E6; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 6; sv; sa])) E)
  by (unfold E, E6; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m, (m < A_TEXT)%nat ->
    ew E m = ew (Ereg regsE (map (Z_to_bv 64) [D; D + p6_nn n0 6; sv; sa])) m)
  by (intros m Hm; unfold E, E6; apply Eimg_low; exact Hm).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regsE r)
  by (intros m r Hm; unfold E, E6; apply ew_Eimg_Ereg_nat; exact Hm).
assert (E32 : ew E 32 = Z_to_bv 64 D)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (D + p6_nn n0 6))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sv)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sa)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E15 : ew E 15 = Z_to_bv 64 (p6_nn n0 6)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E13 : ew E 13 = Z_to_bv 64 lit) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (B33 : bv_unsigned (ew E 33) = D + p6_nn n0 6) by (rewrite E33; apply unsigned_lit_small; lia).
assert (B13 : bv_unsigned (ew E 13) = lit) by (rewrite E13; apply unsigned_lit_small; lia).
assert (B35 : bv_unsigned (ew E 35) = sa) by (rewrite E35; apply unsigned_lit_small; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U33 : U E (SOff 33 0) = D + p6_nn n0 6) by (apply (U_atom E 33 _ E33); lia).
assert (U22 : U E P6BX = SHADOW_OFF) by (apply (U_atom E 22 _ E22); unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok SEGS P6BX P6SH E (mrestrict (w_H W) memE)).
{ unfold sh_ok, P6SH. apply Forall_cons; [|apply Forall_nil]. split.
  - cbn [she_m she_lo she_hi]. rewrite p_rd_aview, U33, U22, Z.add_0_r.
    intros x Hx. apply (HBRAE x ltac:(unfold p6_nn, p6_cnt in *; lia)).
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite U33, U22.
    intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF, p6_nn, p6_cnt in *. lia. }
prreg HS (0%bv : bv 5) Q0E.
unfold cfg_at.
replace (w64 (BASE + AF_reac_box_name + RBN_L6)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L6)))
  by (unfold w64; f_equal; lia).
paj_run_tok RUN HS HJ SHOK P6SPAN.
{ p6_awr_ro. }
p6_frame HFr 0 0 E33 E13 E35 E9 K1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK P6SPAN.
- rewrite branch_geu_U in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 6) 1 E15) in Hc by lia.
  assert (Hn47 : p6_nn n0 6 = 47) by lia. clear Hc.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_ro. }
  p6_frame HFr 0 0 E33 E13 E35 E9 K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 7 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = 1).
    { unfold p6_ovv. replace (n0 + 7 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p6_awr_ro. }
    p6_frame HFr 0 0 E33 E13 E35 E9 K3. rename HG into HG3. clear HF HFr.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6) by (unfold p6_wrl, p6_cnt in *; f_equal; f_equal; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = 1).
    { unfold p6_ovv. replace (n0 + 7 - 1 <=? 47) with false;
      [reflexivity | symmetry; apply Z.leb_gt; unfold p6_nn, p6_cnt in Hn47; lia]. }
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Hw3, Ho3.
    split.
    { intros a Ha Hn. rewrite (K3 a Ha ltac:(lia)), (K2 a Ha ltac:(lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | exact Hn]. }
    split.
    { apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
      intros x Hx. rewrite Hwr2 in Hx.
      rewrite (K3 x ltac:(lia) ltac:(lia)), (K2 x ltac:(lia) ltac:(lia)),
        (K1 x ltac:(lia) ltac:(lia)). reflexivity. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15; reflexivity|].
    split; [rewrite Q12; reflexivity|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
- rewrite branch_geu_U in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (U_lit E 48) in Hc by lia.
  rewrite (U_atom_off E 15 (p6_nn n0 6) 1 E15) in Hc by lia.
  assert (Hn46 : p6_nn n0 6 <= 46) by lia. clear Hc.
  pose proof (st_ok_pi_add_region E _ _ p6_dnreg HS ltac:(vm_compute; reflexivity)
    ltac:(apply (p_dnreg_ok E _ (D + p6_nn n0 6) B33 ltac:(lia) ltac:(lia));
          apply (apresent_writable SEGS);
          eapply (apresent_grows (w_H W)); [exact HG1 | apply HPR; unfold p6_nn, p6_cnt in *; lia])
    ltac:(lazymatch goal with |- all_disjoint _ _ ?rs =>
            let rs' := eval vm_compute in rs in change (all_disjoint E p6_dnreg rs') end;
          cbn [all_disjoint]; unfold extent_disjoint, p6_dnreg;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite B33, B13, B35, B9;
          unfold p6_nn, p6_cnt in *; repeat split; lia)) as HS2.
  clear HS. rename HS2 into HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
  paj_run_tok RUN HS HJ SHOK P6SPAN.
  { p6_awr_store E33 (D + p6_nn n0 6) HBW. }
  pose proof (p_kept_frame _ _ _ _ _ (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) HFr
    ltac:(intros a (r & Hr & Hw);
          lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
          cbn [In] in Hr; repeat destruct Hr as [<- | Hr]; try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?B33, ?B13, ?B35, ?B9 in Hw; lia)) as K2.
  rename HG into HG2. clear HF HFr.
  psrr_branch_tok RUN BR HS SHOK P6SPAN.
  + p6_efact HS 34%nat E34 G34.
    lazymatch type of HS with st_ok_pi _ _ ?Ec _ _ =>
      rewrite branch_ne_U in Hc; apply negb_true_iff, Z.eqb_neq in Hc;
      rewrite (U_atom Ec 34 sv G34) in Hc by lia; rewrite (U_lit Ec 0) in Hc by lia;
      pose proof (st_ok_pi_add_fact Ec _ _ 34%nat (mkAF 7 7 0) HS
        ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite G34, unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS2 end.
    clear HS. rename HS2 into HS.
    paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p6_awr_store E33 (D + p6_nn n0 6) HBW. }
    p6_frame HFr (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 6) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 7 = 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 7)) = p6_cnt n0 7)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = p6_ovv n0 ov0 6).
    { unfold p6_ovv.
      replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 5) with (D + p6_nn n0 6) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
  + paj_run_to_tok RUNTO HS HJ SHOK P6SPAN (AF_reac_box_name + RBN_L6X).
    { p6_awr_store E33 (D + p6_nn n0 6) HBW. }
    p6_frame HFr (D + p6_nn n0 6) (D + p6_nn n0 6 + 1) E33 E13 E35 E9 K3.
    rename HG into HG3. clear HF HFr.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) p6_dnreg) in
      pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
    cbn [ms_mem restrict mkst] in HR0.
    lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
      pose proof (field_of_region Ex _ 33%nat (D + p6_nn n0 6) _ 0 1 0 1 0 1%N (SLit 32) 32 HR0
        ltac:(cbn [extK]; rewrite ?ew_ewset_other by lia; rewrite E33; apply unsigned_lit_small; lia)
        ltac:(cbn [In]; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnew
    end.
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vnew. rewrite Z.add_0_r in Vnew.
    prreg HS (15%bv : bv 5) Q15. prreg HS (12%bv : bv 5) Q12. prreg HS (16%bv : bv 5) Q16.
    prreg HS (23%bv : bv 5) Q23. prreg HS (14%bv : bv 5) Q14. prreg HS (11%bv : bv 5) Q11.
    prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (22%bv : bv 5) Q22.
    prreg HS (0%bv : bv 5) Q0.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ P6KEPT HS ltac:(cbn [extK]; p6_agree HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    lazymatch type of HKr with forall r, _ -> getr ?rr r = _ =>
      assert (HKf : rbn_keep_regs regsE rr [5; 10; 12; 15; 16; 17; 23]) by
        (apply p6_keep_of;
         [ exact HKr
         | apply (p6_kreg _ _ (0%bv : bv 5) 0 (Z_to_bv 64 0)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q0 Q0E)
         | apply (p6_kreg _ _ (11%bv : bv 5) 11 (Z_to_bv 64 48)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q11 R11)
         | apply (p6_kreg _ _ (14%bv : bv 5) 14 (Z_to_bv 64 7)
             ltac:(apply bv_eq; vm_compute; reflexivity) Q14 R14) ]) end.
    assert (Hc2e : p6_cnt n0 6 = 5) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hc3e : p6_cnt n0 7 = 6) by (unfold p6_nn, p6_cnt in *; lia).
    assert (Hwr3 : Z.of_nat (length (p6_wrl n0 7)) = p6_cnt n0 7)
      by (unfold p6_wrl; rewrite length_firstn; rewrite Hc3e; cbn [length rbn_lit6]; lia).
    assert (Hn3 : p6_nn n0 7 = p6_nn n0 6 + 1) by (unfold p6_nn; lia).
    assert (Ho3 : p6_ovv n0 ov0 7 = p6_ovv n0 ov0 6).
    { unfold p6_ovv.
      replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      replace (n0 + 6 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; unfold p6_nn, p6_cnt in *; lia).
      reflexivity. }
    assert (Hw3 : p6_wrl n0 7 = p6_wrl n0 6 ++ [32]).
    { unfold p6_wrl. rewrite Hc2e, Hc3e. reflexivity. }
    pmkst HS.
    apply SRr_ret. unfold p6_next. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    change (6 + 1) with 7. unfold p6_pkg. rewrite Hn3, Ho3.
    split.
    { intros a Ha Hn. rewrite Hwr3, Hc3e in Hn.
      rewrite (K3 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)),
        (K2 a Ha ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 a Ha ltac:(lia)).
      apply HEQ; [exact Ha | rewrite Hwr2, Hc2e; unfold p6_nn, p6_cnt in *; lia]. }
    split.
    { rewrite Hw3. apply p_garr8_snoc; [| | lia].
      - apply (p_garr8_eq (w_H W) memE _ (D + n0) (p6_wrl n0 6)); [|exact HWR].
        intros x Hx. rewrite Hwr2, Hc2e in Hx.
        rewrite (K3 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)),
          (K2 x ltac:(lia) ltac:(unfold p6_nn, p6_cnt in *; lia)), (K1 x ltac:(lia) ltac:(lia)).
        reflexivity.
      - rewrite Hwr2, Hc2e. replace (D + n0 + 5) with (D + p6_nn n0 6) by (unfold p6_nn; lia).
        exact Vnew. }
    split.
    { intros a Ha. eapply apresent_grows; [exact HG3|]. eapply apresent_grows; [exact HG2|].
      eapply apresent_grows; [exact HG1 | apply HPR; exact Ha]. }
    split.
    { intros r Hr Hnin. rewrite (HKf r Hr Hnin). exact (HKEEP r Hr Hnin). }
    split; [rewrite Q15, E15, unsigned_lit_small by lia; reflexivity|].
    split; [rewrite Q12; rewrite (EE 12%nat 12%bv eq_refl); exact R12|].
    split; [rewrite Q16; cbn [rbn_lit6 nth Z.to_nat]; reflexivity|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite Q14; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q13, E13; reflexivity|].
    split; [rewrite Q9, E9; reflexivity|].
    rewrite Q22, E22. reflexivity.
Qed.
Lemma p6_all : forall (regsE : bvmap 5 word) memE mdE,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memE mdE k ->
  p6_pkg 1 regsE memE ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_L6) regsE memE mdE) (p6_next 7).
Proof.
intros regsE memE mdE HJ HP.
eapply SRr_bind; [exact (p6_it1 regsE memE mdE HJ HP)|].
intros Wa ca _ Ha. change (1 + 1) with 2 in Ha.
destruct Ha as (-> & ra & ma & da & -> & Ja & Pa).
replace (if (2 : Z) <=? 6 then 10800 else 10912) with (AF_reac_box_name + RBN_L6) by reflexivity.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it2 ra ma da Ja Pa)|].
intros Wb cb _ Hb. change (2 + 1) with 3 in Hb.
destruct Hb as (-> & rb & mb & db & -> & Jb & Pb).
replace (if (3 : Z) <=? 6 then 10800 else 10912) with (AF_reac_box_name + RBN_L6) by reflexivity.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it3 rb mb db Jb Pb)|].
intros Wc cc _ Hcc. change (3 + 1) with 4 in Hcc.
destruct Hcc as (-> & rc2 & mc & dc & -> & Jc & Pc).
replace (if (4 : Z) <=? 6 then 10800 else 10912) with (AF_reac_box_name + RBN_L6) by reflexivity.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it4 rc2 mc dc Jc Pc)|].
intros Wd cd _ Hd. change (4 + 1) with 5 in Hd.
destruct Hd as (-> & rd & md & dd & -> & Jd & Pd).
replace (if (5 : Z) <=? 6 then 10800 else 10912) with (AF_reac_box_name + RBN_L6) by reflexivity.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
eapply SRr_bind; [exact (p6_it5 rd md dd Jd Pd)|].
intros We ce _ He. change (5 + 1) with 6 in He.
destruct He as (-> & re & me & de & -> & Je & Pe).
replace (if (6 : Z) <=? 6 then 10800 else 10912) with (AF_reac_box_name + RBN_L6) by reflexivity.
replace (BASE + (AF_reac_box_name + RBN_L6)) with (BASE + AF_reac_box_name + RBN_L6) by lia.
exact (p6_it6 re me de Je Pe).
Qed.
Lemma p6_fin_run : forall (mdc : Model) (nF ovF : Z) (wr : list Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 15 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 16 = w64 32 -> getr regs 23 = w64 1 ->
  getr regs 14 = w64 7 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 23)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  p6_nn n0 7 = nF -> p6_ovv n0 ov0 7 = ovF -> p6_wrl n0 7 = wr ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_box_name + RBN_L6) regs memc mdc)
    (rbn_lpost B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L6X
       [5; 10; 12; 15; 16; 17; 23] D n0 wr [(15, nF); (12, ovF)]).
Proof.
intros mdc nF ovF wr HJ R15 R12 R16 R23 R14 R11 R13 R9 R22 HnF HovF HwF.
pose proof HBUF as (HD0 & HD63 & HAPP & HBRA & HBW).
eapply SRr_mono.
{ apply (p6_all regs memc mdc HJ).
  unfold p6_pkg. split; [intros a Ha Hn; reflexivity|].
  split.
  { unfold p6_wrl, p6_cnt. rewrite Z.min_l by lia.
    intros j Hj. vm_compute in Hj. lia. }
  split; [intros a Ha; exact (proj2 (HBW a Ha))|].
  split; [intros r Hr Hnin; reflexivity|].
  split; [unfold p6_nn, p6_cnt; rewrite Z.min_l by lia; rewrite Z.add_0_r; exact R15|].
  split; [unfold p6_ovv; replace (n0 + 1 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
          exact R12|].
  split; [cbn [Z.to_nat rbn_lit6 nth]; exact R16|].
  split; [exact R23|]. split; [exact R14|]. split; [exact R11|]. split; [exact R13|].
  split; [exact R9 | exact R22]. }
intros W2 c2 Hle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2).
destruct HP2 as (HEQ & HWR & HPR & HKEEP & Q15 & Q12 & Q16 & Q23 & Q14 & Q11 & Q13 & Q9 & Q22).
unfold rbn_lpost. split; [reflexivity|]. exists regs2, mem2, md2.
split.
{ unfold rbn_cfg, cfg_at, w64. cbn [Z.leb Z.compare].
  replace (BASE + AF_reac_box_name + RBN_L6X) with (BASE + 10912)
    by (unfold AF_reac_box_name, RBN_L6X; lia).
  reflexivity. }
split; [exact HJ2|]. split; [exact HKEEP|].
split.
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
  - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Q15, HnF. reflexivity.
  - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Q12, HovF. reflexivity. }
rewrite <- HwF. split; [exact HEQ | exact HWR].
Qed.
End S6.
Theorem rbn_l6_fits : rbn_L6_fits B.
Proof.
unfold rbn_L6_fits, rbn_L6_run.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hfit
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP HSLOT HA1D HN0 HOV0 R15 R12 R16 R23 R14 R11 R13 R9 R22.
eapply p6_fin_run; try eassumption.
all: first
  [ solve [unfold p6_nn, p6_cnt; lia]
  | solve [unfold p6_ovv; replace (n0 + 7 - 1 <=? 47) with true by (symmetry; apply Z.leb_le; lia);
           reflexivity]
  | solve [unfold p6_wrl, p6_cnt; replace (Z.min (7 - 1) (47 - n0)) with 6 by lia; reflexivity] ].
Qed.
Theorem rbn_l6_ovf : rbn_L6_ovf B.
Proof.
unfold rbn_L6_ovf, rbn_L6_run.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hovf
  HJ HSRC HAL HA1lo HA1hi HA1lit HBUF HSEP HSLOT HA1D HN0 HOV0 R15 R12 R16 R23 R14 R11 R13 R9 R22.
eapply p6_fin_run; try eassumption.
all: first
  [ solve [unfold p6_nn, p6_cnt; lia]
  | solve [unfold p6_ovv; replace (n0 + 7 - 1 <=? 47) with false by (symmetry; apply Z.leb_gt; lia);
           reflexivity]
  | solve [unfold p6_wrl, p6_cnt; f_equal; f_equal; lia] ].
Qed.

End h.
End f.
End d.
