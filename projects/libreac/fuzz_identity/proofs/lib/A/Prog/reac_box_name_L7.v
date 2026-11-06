(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:61-65, 112-116, for
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
PaTable PaSym PaShadow PaRun PaStep PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentFrame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import reac_box_name reac_box_name_cuts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rl7_regval :=
  cbn [sv_denot]; rewrite ?ew_ewset_other by (clear; lia);
  repeat match goal with Hq : ew ?Ex ?nq = Z_to_bv 64 _ |- context [ew ?Ex ?nq] => rewrite Hq end;
  rewrite ?unsigned_lit_small by lia; unfold w64;
  first [ reflexivity | (f_equal; lia) | (apply bv_eq; vm_compute; reflexivity) ].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma rl7_mb_eq : forall (segs : list Segment) H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros segs H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rl7_garr8_kept : forall (segs : list Segment) H H' (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview segs H' m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H' m') p L.
Proof.
intros segs H H' m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. cbn in Hk. pose proof (Hv k Hk) as Hb.
rewrite (rl7_mb_eq segs H H' m m' (p + Z.of_nat j + Z.of_nat k) (p + Z.of_nat j + Z.of_nat k)); [exact Hb|].
apply HE. lia.
Qed.
Lemma rl7_vm_kept : forall (segs : list Segment) H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros segs H H' m m' a n v HE Hv k Hk.
rewrite (rl7_mb_eq segs H H' m m' (a + Z.of_nat k) (a + Z.of_nat k) (HE (a + Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
Lemma rl7_vm_of_aview : forall (segs : list Segment) H (mem : word -> option byte) a s,
  aview segs H mem a = Some s -> val_mem segs (mrestrict H mem) a 1 s /\ 0 <= s < 256.
Proof.
intros segs H mem a s Hs. unfold aview in Hs.
destruct (mbyte segs (mrestrict H mem) a) as [bb|] eqn:Em; cbn in Hs; [|discriminate].
injection Hs as <-.
pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [|lia].
intros j Hj. assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r, Em. f_equal.
change (YO0f.le_byte (bv_unsigned bb) 1 0) with ((bv_unsigned bb mod 256) mod 256).
rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition rl7_lits : list Z := rbn_lit7 ++ [0].
Definition rl7_litR : YP09.region := YP09.mkRegion (Some 13%nat) 0 6 0 0
  [YP09.mkChunk 0 (CVal 1 (SLit 32)); YP09.mkChunk 1 (CVal 1 (SLit 111)); YP09.mkChunk 2 (CVal 1 (SLit 117));
   YP09.mkChunk 3 (CVal 1 (SLit 116)); YP09.mkChunk 4 (CVal 1 (SLit 41)); YP09.mkChunk 5 (CVal 1 (SLit 0))].
Definition rl7_shR (sh : sv) : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 sh)].
Definition rl7_slotR : YP09.region :=
  YP09.mkRegion (Some 9%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
Definition rl7_dstR : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition rl7_cmn : list (nat * afact) :=
  [(22%nat, mkAF SB SB 0); (12%nat, mkAF 0 1 0); (11%nat, mkAF 48 48 0);
   (13%nat, mkAF 65536 6266872 3); (35%nat, mkAF 6 7 0)].
Definition rl7_shal : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 13 0) (SLit 3)) (SOff 22 0), SOff 34 0).
Definition rl7_regs (j c : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 14%bv (SLit 6)) 16%bv (SOff 23 1)) 21%bv (SLit j)) 15%bv (SLit c).
Definition rl7_ssf (j c : Z) (sh : sv) : sstate :=
  mkSS (AF_reac_box_name + (RBN_L7 + 4)) (rl7_regs j c) [rl7_dstR; rl7_slotR; rl7_litR; rl7_shR sh] None
    (mkFacts ((23%nat, mkAF 0 46 0) :: (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) :: rl7_cmn) []
      [(SAlu ALU_ADD (SOff 33 0) (SOff 23 0), SOff 32 0); rl7_shal]).
Definition rl7_sso (j c : Z) (sh : sv) : sstate :=
  mkSS (AF_reac_box_name + (RBN_L7 + 4)) (rl7_regs j c) [rl7_litR; rl7_shR sh] None
    (mkFacts ((23%nat, mkAF 47 47 0) :: rl7_cmn) [] [rl7_shal]).
Definition rl7_ss0 : sstate := mkSS (AF_reac_box_name + RBN_L7) sr_atoms [] None (mkFacts [] [] []).
Definition rl7_B : sv := SOff 22 0.
Definition rl7_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rl7_SH : list shent := [mkSHE 32 1 0].
Definition rl7_cl : list Z := [5; 10; 12; 15; 16; 17; 21; 23].
Definition rl7_keptl : list (bv 5) :=
  [1; 2; 3; 4; 6; 7; 8; 9; 11; 13; 18; 19; 20; 22; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition rl7_keptl0 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition rl7_E (regs : bvmap 5 word) (dn d sa sv : Z) : env :=
  Eimg (Ereg regs (map (Z_to_bv 64) [dn; d; sa; sv])).
Lemma rl7_ew : forall regs dn d sa sv,
  ew (rl7_E regs dn d sa sv) 32 = Z_to_bv 64 dn /\ ew (rl7_E regs dn d sa sv) 33 = Z_to_bv 64 d /\
  ew (rl7_E regs dn d sa sv) 34 = Z_to_bv 64 sa /\ ew (rl7_E regs dn d sa sv) 35 = Z_to_bv 64 sv /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (rl7_E regs dn d sa sv) k = getr regs r).
Proof.
intros regs dn d sa sv. unfold rl7_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma rl7_af : forall E q v lo hi al, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  v mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E q (mkAF lo hi al).
Proof.
intros E q v lo hi al He Hv Hr Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite He, unsigned_lit_small by lia. auto.
Qed.
Lemma rl7_af0 : forall E q v lo hi, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E q (mkAF lo hi 0).
Proof.
intros E q v lo hi He Hv Hr. apply (rl7_af E q v); [exact He | exact Hv | exact Hr | | lia].
rewrite Z.pow_0_r. apply Z.mod_1_r.
Qed.
Lemma rl7_vm_lit : forall E (m : word -> option byte) a c,
  (0 <=? c) && (c <? 256) = true ->
  val_mem SEGS m (a + 0) (N.to_nat 1) (bv_unsigned (sv_denot E (SLit c)) mod 2 ^ (8 * Z.of_N 1)) ->
  val_mem SEGS m a 1 c.
Proof.
intros E m a c Hc Hv. apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
cbn [sv_denot] in Hv. rewrite unsigned_lit_small in Hv by lia. rewrite Z.add_0_r in Hv.
change (2 ^ (8 * Z.of_N 1)) with 256 in Hv. rewrite Z.mod_small in Hv by lia. exact Hv.
Qed.
Lemma rl7_lit_range : forall i, 0 <= nth i rl7_lits 0 < 256.
Proof.
intros i. destruct i as [|[|[|[|[|[|i]]]]]]; cbn [nth rl7_lits rbn_lit7 app]; try lia.
destruct i; cbn [nth]; lia.
Qed.
Lemma rl7_cover : forall r : Z, 0 <= r < 32 -> ~ In r rl7_cl ->
  r = 0 \/ r = 14 \/ In (Z_to_bv 5 r) rl7_keptl.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [right; left; reflexivity]
        | solve [exfalso; apply Hn; unfold rl7_cl; cbn [In];
                 repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; right; unfold rl7_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Lemma rl7_keep : forall (regs regs2 : bvmap 5 word),
  (forall rr : bv 5, In rr rl7_keptl -> getr regs2 rr = getr regs rr) -> getr regs2 14 = getr regs 14 ->
  rbn_keep_regs regs regs2 rl7_cl.
Proof.
intros regs regs2 HK H14 r Hr Hn. destruct (rl7_cover r Hr Hn) as [-> | [-> | Hin]].
- replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite !getr_zero. reflexivity.
- replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity). exact H14.
- exact (HK _ Hin).
Qed.
Lemma rl7_keep_trans : forall (regs r1 r2 : bvmap 5 word) cl,
  rbn_keep_regs regs r1 cl -> rbn_keep_regs r1 r2 cl -> rbn_keep_regs regs r2 cl.
Proof. intros regs r1 r2 cl H1 H2 z Hz Hn. rewrite (H2 z Hz Hn). exact (H1 z Hz Hn). Qed.
Lemma rl7_kept_reg : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  rbn_keep_regs regs regs2 rl7_cl -> ~ In (bv_unsigned r) rl7_cl -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 r HK Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
pose proof (HK (bv_unsigned r) Hr Hn) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Lemma rl7_shadow_byte : forall (W : world SEGS) memc P,
  rbn_lsrc W memc P (rbn_lit7 ++ [0]) -> P mod 8 = 0 ->
  exists s, val_mem SEGS (mrestrict (w_H W) memc) (SHADOW_OFF + P / 8) 1 s /\ (s = 0 \/ 6 <= s <= 7).
Proof.
intros W memc P (_ & HP0 & _ & _ & HRA) HP8.
destruct (HRA (P + 5)) as (s & Hs & Hok); [cbn [length app rbn_lit7 Z.of_nat]; lia|].
assert (HPq : P = 8 * (P / 8)) by (pose proof (Z.div_mod P 8 ltac:(lia)); lia).
assert (Hq : (P + 5) / 8 = P / 8).
{ rewrite HPq at 1. replace (8 * (P / 8) + 5) with (5 + P / 8 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
assert (Hm : (P + 5) mod 8 = 5).
{ rewrite HPq at 1. replace (8 * (P / 8) + 5) with (5 + P / 8 * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
unfold shadow_of_addr in Hs. rewrite Hq in Hs.
destruct (rl7_vm_of_aview SEGS (w_H W) memc _ s Hs) as [Hv Hr].
exists s. split; [exact Hv|]. unfold saddr_ok in Hok. rewrite Hm in Hok. lia.
Qed.
Lemma rl7_app_not_shadow : forall x a, in_app x 1 -> 0 <= a -> a < 2 ^ 47 -> x <> SHADOW_OFF + a / 8.
Proof.
intros x a Hx H0 Ha Heq.
assert (Hd : 0 <= a / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rl7_src_keep : forall (W : world SEGS) (mem mem' : word -> option byte) P l X,
  rbn_lsrc W mem P l ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> X -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  in_app X 1 -> ~ (P <= X < P + Z.of_nat (length l)) ->
  rbn_lsrc W mem' P l.
Proof.
intros W mem mem' P l X (HG & HP0 & HP63 & HP47 & HRA) HK Hx Hnin.
split; [|split; [exact HP0 | split; [exact HP63 | split; [exact HP47|]]]].
- apply (rl7_garr8_kept SEGS (w_H W) (w_H W) mem mem' P l); [|exact HG].
  intros a Ha. apply HK; [lia | lia].
- intros y Hy. unfold shadow_of_addr.
  rewrite (HK (SHADOW_OFF + y / 8)).
  + apply HRA. lia.
  + assert (Hd : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHADOW_OFF. lia.
  + intros Heq. apply (rl7_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
Qed.
Lemma rl7_buf_keep : forall B STK sp0 FP ly S own lyc Sc (W : world SEGS) (mem mem' : word -> option byte) D n X,
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W mem D n ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> X -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  in_app X 1 -> 0 <= n ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W mem' D n.
Proof.
intros B STK sp0 FP ly S own lyc Sc W mem mem' D n X (HD0 & HD63 & HDapp & HRA & HW) HK HGr Hx Hn.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof HDapp as (HDlo & HDhi).
assert (Hhi : D + n <= 2 ^ 47) by (unfold kLowShadowBeg, kHighMemBeg in HDhi; lia).
split; [exact HD0|]. split; [exact HD63|]. split; [exact HDapp|]. split.
- intros y Hy. unfold shadow_of_addr.
  rewrite (HK (SHADOW_OFF + y / 8)).
  + apply HRA. lia.
  + assert (Hd : 0 <= y / 8 < 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHADOW_OFF. lia.
  + intros Heq. apply (rl7_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
- intros a Ha. split; [exact (proj1 (HW a Ha))|].
  apply (apresent_grows _ _ _ _ HGr). exact (proj2 (HW a Ha)).
Qed.
Lemma rl7_shok : forall E (m : word -> option byte) q,
  ew E 22 = Z_to_bv 64 SB -> ew E 32 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  (q + 1 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  sh_ok SEGS rl7_B rl7_SH E m.
Proof.
intros E m q H22 H32 Hq Ha. constructor; [|constructor].
eapply shent_app_of_app.
- unfold rl7_B. rewrite (U_atom E 22 SB H22) by (unfold SB; lia). reflexivity.
- exact (U_atom E 32 q H32 Hq).
- lia.
- lia.
Qed.
Lemma rl7_lit_ok : forall E (mem : word -> option byte) P,
  garr8 SEGS mem P rl7_lits -> Forall (YP09.chunk_ok SEGS E mem P) (YP09.r_chunks rl7_litR).
Proof.
intros E mem P HG. cbn [rl7_litR YP09.r_chunks].
constructor; [apply (chunk_ok_val SEGS E mem P 0 1 (SLit 32) 32);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 0%nat ltac:(cbn; lia)))]|].
constructor; [apply (chunk_ok_val SEGS E mem P 1 1 (SLit 111) 111);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 1%nat ltac:(cbn; lia)))]|].
constructor; [apply (chunk_ok_val SEGS E mem P 2 1 (SLit 117) 117);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 2%nat ltac:(cbn; lia)))]|].
constructor; [apply (chunk_ok_val SEGS E mem P 3 1 (SLit 116) 116);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 3%nat ltac:(cbn; lia)))]|].
constructor; [apply (chunk_ok_val SEGS E mem P 4 1 (SLit 41) 41);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 4%nat ltac:(cbn; lia)))]|].
constructor; [apply (chunk_ok_val SEGS E mem P 5 1 (SLit 0) 0);
  [reflexivity | cbn; lia | cbn; lia | exact (proj1 (HG 5%nat ltac:(cbn; lia)))]|].
constructor.
Qed.
Lemma rl7_sh_ok : forall E (mem : word -> option byte) sh s sv Sa,
  ew E 35 = Z_to_bv 64 sv -> 0 <= sv < 2 ^ 64 -> ((sh = SLit 0 /\ s = 0) \/ (sh = SOff 35 0 /\ s = sv)) ->
  0 <= s < 256 -> val_mem SEGS mem Sa 1 s ->
  Forall (YP09.chunk_ok SEGS E mem Sa) (YP09.r_chunks (rl7_shR sh)).
Proof.
intros E mem sh s sv Sa E35 Hsv Hsh Hs Vs. cbn [rl7_shR YP09.r_chunks].
constructor; [|constructor].
apply (chunk_ok_val SEGS E mem Sa 0 1 sh s); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vs].
destruct Hsh as [[-> ->] | [-> ->]]; cbn [sv_denot]; [reflexivity|].
rewrite E35, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
Qed.
Lemma rl7_entry_f : forall (W : world SEGS) (regs : bvmap 5 word) memc j c sh s sv A1 D n ov,
  getr regs 21 = w64 j -> getr regs 15 = w64 c -> getr regs 14 = w64 6 -> getr regs 16 = w64 (n + 1) ->
  getr regs 23 = w64 n -> getr regs 12 = w64 ov -> getr regs 11 = w64 48 ->
  getr regs 13 = w64 (VAL (A_OBJ 24)) -> getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  0 <= n <= 46 -> 0 <= ov <= 1 -> 6 <= sv <= 7 ->
  ((sh = SLit 0 /\ s = 0) \/ (sh = SOff 35 0 /\ s = sv)) -> 0 <= s < 256 ->
  65536 <= VAL (A_OBJ 24) <= 6266872 -> VAL (A_OBJ 24) mod 8 = 0 ->
  4096 <= D -> D + n + 1 <= 2 ^ 47 -> 0 <= A1 -> A1 + 128 <= 2 ^ 47 ->
  zpairwise_disjoint [(D + n, D + n + 1); (A1 + 120, A1 + 128); (VAL (A_OBJ 24), VAL (A_OBJ 24) + 6);
    (SHADOW_OFF + VAL (A_OBJ 24) / 8, SHADOW_OFF + VAL (A_OBJ 24) / 8 + 1)] ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 24)) rl7_lits ->
  val_mem SEGS (mrestrict (w_H W) memc) (SHADOW_OFF + VAL (A_OBJ 24) / 8) 1 s ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D ->
  apresent (w_H W) memc (D + n) ->
  st_ok_pi SEGS VAL (rl7_E regs (D + n) D (SHADOW_OFF + VAL (A_OBJ 24) / 8) sv) (rl7_ssf j c sh)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))) memc (seg_rom SEGS))).
Proof.
intros W regs memc j c sh s sv A1 D n ov H21 H15 H14 H16 H23 H12 H11 H13 H9 H22 Hn Hov Hsv Hsh Hs
  HP HP8 HD4 HD47 HA0 HA147 Hz HG Vs Vsl Hp.
rewrite restrict_mkst_fx.
set (P := VAL (A_OBJ 24)) in *.
assert (Hdiv : 8192 <= P / 8 <= 783359)
  by (clear - HP HP8; pose proof (Z.div_mod P 8 ltac:(lia)); lia).
destruct (rl7_ew regs (D + n) D (SHADOW_OFF + P / 8) sv) as (E32 & E33 & E34 & E35 & EE).
assert (E23 : ew (rl7_E regs (D + n) D (SHADOW_OFF + P / 8) sv) 23 = Z_to_bv 64 n)
  by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (HR : regs_ok (rl7_E regs (D + n) D (SHADOW_OFF + P / 8) sv) (rl7_regs j c) regs).
{ unfold rl7_regs.
  apply regs_ok_pin; [| discriminate | cbn [sv_denot]; exact H15].
  apply regs_ok_pin; [| discriminate | cbn [sv_denot]; exact H21].
  apply regs_ok_pin;
    [| discriminate | cbn [sv_denot]; rewrite E23, unsigned_lit_small by (clear - Hn; lia); exact H16].
  apply regs_ok_pin; [unfold rl7_E; apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H14]. }
set (E := rl7_E regs (D + n) D (SHADOW_OFF + P / 8) sv) in *.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E12 : ew E 12 = Z_to_bv 64 ov) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E11 : ew E 11 = Z_to_bv 64 48) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 P) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E9 : ew E 9 = Z_to_bv 64 A1) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (B32 : bv_unsigned (ew E 32) = D + n) by (rewrite E32; apply unsigned_lit_small; clear - HD4 Hn HD47; lia).
assert (B9 : bv_unsigned (ew E 9) = A1) by (rewrite E9; apply unsigned_lit_small; clear - HA0 HA147; lia).
assert (B13 : bv_unsigned (ew E 13) = P) by (rewrite E13; apply unsigned_lit_small; clear - HP; lia).
assert (B34 : bv_unsigned (ew E 34) = SHADOW_OFF + P / 8)
  by (rewrite E34; apply unsigned_lit_small; clear - Hdiv; unfold SHADOW_OFF; lia).
unfold rl7_ssf. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val rl7_dstR rl7_slotR rl7_litR rl7_shR].
  + rewrite B32. split; [clear - HD4 Hn; lia|]. split; [clear - HD47; lia|].
    split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (D + n + o) with (D + n) by (clear - Ho; lia). exact Hp.
  + rewrite B9. split; [clear - HA0; lia|]. split; [clear - HA147; lia|]. split; [intros o Ho; clear - Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A1 120 8 (SOff 33 0) D);
      [cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by (clear - HD4 HD47 Hn; lia); reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HD4 HD47 Hn; lia | cbn; lia | exact Vsl].
  + rewrite B13. split; [clear - HP; lia|]. split; [clear - HP; lia|]. split; [intros o Ho; clear - Ho; lia|].
    exact (rl7_lit_ok E _ P HG).
  + rewrite B34. split; [clear - Hdiv; unfold SHADOW_OFF; lia|]. split; [clear - Hdiv; unfold SHADOW_OFF; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    apply (rl7_sh_ok E _ sh s sv _ E35 ltac:(clear - Hsv; lia) Hsh Hs). exact Vs.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val rl7_dstR rl7_slotR rl7_litR rl7_shR].
  rewrite B32, B9, B13, B34, !Z.add_0_r. exact Hz.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok rl7_cmn].
    split; [apply (rl7_af0 E 23 n); [exact E23 | clear - Hn; lia | clear - Hn; lia]|].
    split; [apply (rl7_af0 E 32 (D + n)); [exact E32 | clear - HD4 Hn HD47; lia | clear - HD4 Hn HD47; lia]|].
    split; [apply (rl7_af0 E 22 SB); [exact E22 | unfold SB; lia | unfold SB; lia]|].
    split; [apply (rl7_af0 E 12 ov); [exact E12 | clear - Hov; lia | clear - Hov; lia]|].
    split; [apply (rl7_af0 E 11 48); [exact E11 | lia | lia]|].
    split; [apply (rl7_af E 13 P); [exact E13 | clear - HP; lia | clear - HP; lia
      | change (2 ^ 3) with 8; exact HP8 | lia]|].
    split; [apply (rl7_af0 E 35 sv); [exact E35 | clear - Hsv; lia | clear - Hsv; lia]|].
    exact I.
  + cbn [f_alias alias_ok rl7_shal]. split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 D E33), (U_atom E 23 n E23), (U_atom E 32 (D + n) E32) by (clear - HD4 Hn HD47; lia).
      apply zcanon_id. unfold M64. clear - HD4 Hn HD47; lia.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
      rewrite (U_atom E 13 P E13), (U_atom E 22 SB E22), (U_atom E 34 (SHADOW_OFF + P / 8) E34)
        by (clear - HP Hdiv; unfold SB, SHADOW_OFF; lia).
      rewrite zcanon_id by (unfold M64; clear - Hdiv; unfold SB; lia). unfold SB, SHADOW_OFF. lia.
Qed.
Lemma rl7_entry_o : forall (W : world SEGS) (regs : bvmap 5 word) memc j c sh s sv ov,
  getr regs 21 = w64 j -> getr regs 15 = w64 c -> getr regs 14 = w64 6 -> getr regs 16 = w64 48 ->
  getr regs 23 = w64 47 -> getr regs 12 = w64 ov -> getr regs 11 = w64 48 ->
  getr regs 13 = w64 (VAL (A_OBJ 24)) -> getr regs 22 = w64 SHADOW_OFF ->
  0 <= ov <= 1 -> 6 <= sv <= 7 -> ((sh = SLit 0 /\ s = 0) \/ (sh = SOff 35 0 /\ s = sv)) -> 0 <= s < 256 ->
  65536 <= VAL (A_OBJ 24) <= 6266872 -> VAL (A_OBJ 24) mod 8 = 0 ->
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 24)) rl7_lits ->
  val_mem SEGS (mrestrict (w_H W) memc) (SHADOW_OFF + VAL (A_OBJ 24) / 8) 1 s ->
  st_ok_pi SEGS VAL (rl7_E regs 0 0 (SHADOW_OFF + VAL (A_OBJ 24) / 8) sv) (rl7_sso j c sh)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))) memc (seg_rom SEGS))).
Proof.
intros W regs memc j c sh s sv ov H21 H15 H14 H16 H23 H12 H11 H13 H22 Hov Hsv Hsh Hs HP HP8 HG Vs.
rewrite restrict_mkst_fx.
set (P := VAL (A_OBJ 24)) in *.
assert (Hdiv : 8192 <= P / 8 <= 783359)
  by (clear - HP HP8; pose proof (Z.div_mod P 8 ltac:(lia)); lia).
destruct (rl7_ew regs 0 0 (SHADOW_OFF + P / 8) sv) as (E32 & E33 & E34 & E35 & EE).
assert (E23 : ew (rl7_E regs 0 0 (SHADOW_OFF + P / 8) sv) 23 = Z_to_bv 64 47)
  by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (HR : regs_ok (rl7_E regs 0 0 (SHADOW_OFF + P / 8) sv) (rl7_regs j c) regs).
{ unfold rl7_regs.
  apply regs_ok_pin; [| discriminate | cbn [sv_denot]; exact H15].
  apply regs_ok_pin; [| discriminate | cbn [sv_denot]; exact H21].
  apply regs_ok_pin; [| discriminate | cbn [sv_denot]; rewrite E23, unsigned_lit_small by lia; exact H16].
  apply regs_ok_pin; [unfold rl7_E; apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H14]. }
set (E := rl7_E regs 0 0 (SHADOW_OFF + P / 8) sv) in *.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E12 : ew E 12 = Z_to_bv 64 ov) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E11 : ew E 11 = Z_to_bv 64 48) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E13 : ew E 13 = Z_to_bv 64 P) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (B13 : bv_unsigned (ew E 13) = P) by (rewrite E13; apply unsigned_lit_small; clear - HP; lia).
assert (B34 : bv_unsigned (ew E 34) = SHADOW_OFF + P / 8)
  by (rewrite E34; apply unsigned_lit_small; clear - Hdiv; unfold SHADOW_OFF; lia).
unfold rl7_sso. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val rl7_litR rl7_shR].
  + rewrite B13. split; [clear - HP; lia|]. split; [clear - HP; lia|]. split; [intros o Ho; clear - Ho; lia|].
    exact (rl7_lit_ok E _ P HG).
  + rewrite B34. split; [clear - Hdiv; unfold SHADOW_OFF; lia|]. split; [clear - Hdiv; unfold SHADOW_OFF; lia|].
    split; [intros o Ho; clear - Ho; lia|].
    apply (rl7_sh_ok E _ sh s sv _ E35 ltac:(clear - Hsv; lia) Hsh Hs). exact Vs.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val rl7_litR rl7_shR].
  rewrite B13, B34. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  split; [|split; exact I]. split; [|exact I]. left. clear - HP Hdiv. unfold SHADOW_OFF. lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok rl7_cmn].
    split; [apply (rl7_af0 E 23 47); [exact E23 | lia | lia]|].
    split; [apply (rl7_af0 E 22 SB); [exact E22 | unfold SB; lia | unfold SB; lia]|].
    split; [apply (rl7_af0 E 12 ov); [exact E12 | clear - Hov; lia | clear - Hov; lia]|].
    split; [apply (rl7_af0 E 11 48); [exact E11 | lia | lia]|].
    split; [apply (rl7_af E 13 P); [exact E13 | clear - HP; lia | clear - HP; lia
      | change (2 ^ 3) with 8; exact HP8 | lia]|].
    split; [apply (rl7_af0 E 35 sv); [exact E35 | clear - Hsv; lia | clear - Hsv; lia]|].
    exact I.
  + cbn [f_alias alias_ok rl7_shal]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3.
    rewrite (U_atom E 13 P E13), (U_atom E 22 SB E22), (U_atom E 34 (SHADOW_OFF + P / 8) E34)
      by (clear - HP Hdiv; unfold SB, SHADOW_OFF; lia).
    rewrite zcanon_id by (unfold M64; clear - Hdiv; unfold SB; lia). unfold SB, SHADOW_OFF. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma rl7_round_f : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A1 D n ov j (Q : world SEGS -> config -> Prop),
  1 <= j <= 5 -> 0 <= n <= 46 -> 0 <= ov <= 1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 24) mod 8 = 0 ->
  CEIL_MIN <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 24) \/ VAL (A_OBJ 24) + 6 <= A1 + 120) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 24) + 6 <= D \/ D + 48 <= VAL (A_OBJ 24)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  getr regs 23 = w64 n -> getr regs 16 = w64 (n + 1) -> getr regs 12 = w64 ov ->
  getr regs 15 = w64 (nth (Z.to_nat (j - 1)) rl7_lits 0) -> getr regs 21 = w64 j ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 24)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (pc : Z),
     pc = AF_reac_box_name + (if j <? 5 then RBN_L7 + 4 else RBN_L7X) ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
     rbn_keep_regs regs regs' rl7_cl ->
     getr regs' 23 = w64 (n + 1) -> getr regs' 12 = w64 ov ->
     getr regs' 15 = w64 (nth (Z.to_nat j) rl7_lits 0) -> getr regs' 21 = w64 (j + 1) ->
     (j < 5 -> getr regs' 16 = w64 (n + 2)) ->
     mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') ->
     (forall a, 0 <= a < 2 ^ 64 -> a <> D + n -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) ->
     val_mem SEGS (mrestrict (w_H W) mem') (D + n) 1 (nth (Z.to_nat (j - 1)) rl7_lits 0) ->
     SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom SEGS)) md') Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n ov j Q Hj Hn Hov HJ Hsrc HP8
  HA1 HA147 Hdsl Hbuf Hdbl Hslot Hdbs H23 H16 H12 H15 H21 H14 H11 H13 H9 H22 K.
pose proof (@paj_run fx _ _ _ _ _ B LAWS) as RUN.
pose proof (pa_obj_img 24 ltac:(lia)) as HPimg.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
set (P := VAL (A_OBJ 24)) in *.
assert (HP : 65536 <= P <= 6266872) by (clear - HPimg; lia).
assert (Hdiv : 8192 <= P / 8 <= 783359)
  by (clear - HP HP8; pose proof (Z.div_mod P 8 ltac:(lia)); lia).
pose proof Hsrc as (HGs & HP0 & HP63 & HP47 & HRAs).
pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
assert (HD4 : 4096 <= D) by (destruct HDapp as [HH _]; exact HH).
assert (HDn47 : D + n + 1 <= 2 ^ 47)
  by (clear - HDapp CR Hn; destruct HDapp as [_ [HL | [HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (HDsh : D + n + 1 <= kLowShadowBeg \/ kHighMemBeg <= D + n)
  by (clear - HDapp Hn; destruct HDapp as [_ [HL | [HH1 HH2]]]; [left | right]; lia).
assert (HA0 : 0 <= A1) by (clear - HA1; lia).
assert (Hz : zpairwise_disjoint [(D + n, D + n + 1); (A1 + 120, A1 + 128); (P, P + 6);
    (SHADOW_OFF + P / 8, SHADOW_OFF + P / 8 + 1)]).
{ cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  split; [split; [clear - Hdbs Hn; lia | split; [clear - Hdbl Hn; lia | split; [|exact I]]]|].
  { clear - HDsh Hdiv. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
  split; [split; [clear - Hdsl; lia | split; [|exact I]]|].
  { clear - HA1 Hdiv. unfold SHADOW_OFF. lia. }
  split; [split; [|exact I]|exact (conj I I)].
  clear - HP Hdiv. unfold SHADOW_OFF. lia. }
destruct (rl7_shadow_byte W memc P Hsrc HP8) as (s & Vs & Hs).
assert (Hsh : exists sh sv, 6 <= sv <= 7 /\ ((sh = SLit 0 /\ s = 0) \/ (sh = SOff 35 0 /\ s = sv))).
{ destruct Hs as [-> | Hs]; [exists (SLit 0), 6 | exists (SOff 35 0), s]; split; try lia;
    [left | right]; split; reflexivity. }
destruct Hsh as (sh & sv & Hsv & Hshc).
assert (Hs256 : 0 <= s < 256) by (clear - Hs; lia).
assert (Hpres : apresent (w_H W) memc (D + n)) by exact (proj2 (HWb (D + n) ltac:(clear - Hn; lia))).
pose proof (rl7_entry_f W regs memc j _ sh s sv A1 D n ov H21 H15 H14 H16 H23 H12 H11 H13 H9 H22 Hn Hov Hsv Hshc
  Hs256 HP HP8 HD4 HDn47 HA0 HA147 Hz HGs Vs Hslot Hpres) as HS.
change (VAL (A_OBJ 24)) with P in HS.
destruct (rl7_ew regs (D + n) D (SHADOW_OFF + P / 8) sv) as (E32 & E33 & E34 & E35 & EE).
set (E := rl7_E regs (D + n) D (SHADOW_OFF + P / 8) sv) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rl7_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [D + n; D; SHADOW_OFF + P / 8; sv])) E)
  by (unfold E, rl7_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 n) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (E12 : ew E 12 = Z_to_bv 64 ov) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (SHOK : sh_ok SEGS rl7_B rl7_SH E (mrestrict (w_H W) memc))
  by (apply (rl7_shok E _ (D + n)); [exact E22 | exact E32 | clear - HD4 Hn HDn47; lia | exact HDsh]).
assert (HUB : U E rl7_B = SHADOW_OFF) by (unfold rl7_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (HU32 : U E (SOff 32 0) = D + n) by (apply (U_atom E 32 (D + n) E32); clear - HD4 Hn HDn47; lia).
clear Hdsl Hdbl Hdbs HDsh HDapp Hz Hs HPimg EE.
destruct Hshc as [[-> ->] | [-> ->]];
  (assert (Hj5 : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by (clear - Hj; lia));
  destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]].
all: paj_run_tok RUN HS HJ SHOK rl7_span.
all: lazymatch goal with
  | |- range_addressable _ _ _ _ =>
      rewrite HU32; eapply (obl_of_range SEGS); [exact HRAb | exact HUB | clear - Hn; lia | clear - Hn; lia]
  | |- awr_ok _ _ _ _ _ _ _ _ _ =>
      lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
      eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n));
        [reflexivity | rewrite E32; apply unsigned_lit_small; clear - HD4 Hn HDn47; lia | | ];
      [ cbn [YP09.r_wlo YP09.r_whi]; intros aq Haq; replace aq with (D + n) by (clear - Haq; lia);
        exact (proj1 (HWb (D + n) ltac:(clear - Hn; lia)))
      | repeat (apply awr_ok_cons_ro; [cbn; clear; lia|]); apply awr_ok_nil ]
  | |- _ =>
      prreg HS (23%bv : bv 5) RG23; prreg HS (12%bv : bv 5) RG12; prreg HS (15%bv : bv 5) RG15;
      prreg HS (21%bv : bv 5) RG21; prreg HS (16%bv : bv 5) RG16; prreg HS (14%bv : bv 5) RG14;
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl7_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr;
      cbn [ms_regs restrict] in HKr;
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> D + n ->
        aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
        by (apply (kept_of_frame E _ (w_H W) memc (ms_mem ms) (fun x => x = D + n) HFr);
            intros bq wlo whi aq Hin Haq;
            cbn [ss_mem rl7_ssf windows map YP09.r_base YP09.r_wlo YP09.r_whi rl7_dstR rl7_slotR rl7_litR rl7_shR] in Hin;
            destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <- <-; cbn [base_val] in Haq;
            [rewrite E32, unsigned_lit_small in Haq by (clear - HD4 Hn HDn47; lia); clear - Haq; lia
            | clear - Haq; lia | clear - Haq; lia | clear - Haq; lia]);
      lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        epose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n) _ 0 1 0 1 0 1%N _
          (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)) as Vq end;
      specialize (Vq ltac:(rewrite ?ew_ewset_other by (clear; lia); rewrite E32; apply unsigned_lit_small;
        clear - HD4 Hn HDn47; lia) (or_introl eq_refl) ltac:(cbn; clear; lia));
      cbn [ms_mem restrict] in Vq;
      pmkst HS;
      eapply K;
      [ reflexivity
      | exact HJ
      | apply rl7_keep; [exact HKr | rewrite RG14, H14; reflexivity]
      | rewrite RG23; rl7_regval
      | rewrite RG12; rl7_regval
      | rewrite RG15; rl7_regval
      | rewrite RG21; rl7_regval
      | first [intros Hjj; exfalso; clear - Hjj; lia | intros Hjj; rewrite RG16; rl7_regval]
      | exact HG
      | exact KEEP
      | eapply rl7_vm_lit; [reflexivity | exact Vq] ]
  end.
Qed.
Lemma rl7_round_o : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) ov j (Q : world SEGS -> config -> Prop),
  1 <= j <= 5 -> 0 <= ov <= 1 ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 24) mod 8 = 0 ->
  getr regs 23 = w64 47 -> getr regs 16 = w64 48 -> getr regs 12 = w64 ov ->
  getr regs 15 = w64 (nth (Z.to_nat (j - 1)) rl7_lits 0) -> getr regs 21 = w64 j ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 24)) ->
  getr regs 22 = w64 SHADOW_OFF ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (pc : Z),
     pc = AF_reac_box_name + RBN_L7X ->
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' k ->
     rbn_keep_regs regs regs' rl7_cl ->
     getr regs' 23 = w64 47 -> getr regs' 12 = w64 1 ->
     mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) ->
     SRr SEGS W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom SEGS)) md') Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ov j Q Hj Hov HJ Hsrc HP8
  H23 H16 H12 H15 H21 H14 H11 H13 H22 K.
pose proof (@paj_run fx _ _ _ _ _ B LAWS) as RUN.
pose proof (pa_obj_img 24 ltac:(lia)) as HPimg.
set (P := VAL (A_OBJ 24)) in *.
assert (HP : 65536 <= P <= 6266872) by (clear - HPimg; lia).
pose proof Hsrc as (HGs & HP0 & HP63 & HP47 & HRAs).
destruct (rl7_shadow_byte W memc P Hsrc HP8) as (s & Vs & Hs).
assert (Hsh : exists sh sv, 6 <= sv <= 7 /\ ((sh = SLit 0 /\ s = 0) \/ (sh = SOff 35 0 /\ s = sv))).
{ destruct Hs as [-> | Hs]; [exists (SLit 0), 6 | exists (SOff 35 0), s]; split; try lia;
    [left | right]; split; reflexivity. }
destruct Hsh as (sh & sv & Hsv & Hshc).
assert (Hs256 : 0 <= s < 256) by (clear - Hs; lia).
pose proof (rl7_entry_o W regs memc j _ sh s sv ov H21 H15 H14 H16 H23 H12 H11 H13 H22 Hov Hsv Hshc
  Hs256 HP HP8 HGs Vs) as HS.
change (VAL (A_OBJ 24)) with P in HS.
destruct (rl7_ew regs 0 0 (SHADOW_OFF + P / 8) sv) as (E32 & E33 & E34 & E35 & EE).
set (E := rl7_E regs 0 0 (SHADOW_OFF + P / 8) sv) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rl7_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [0; 0; SHADOW_OFF + P / 8; sv])) E)
  by (unfold E, rl7_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E23 : ew E 23 = Z_to_bv 64 47) by (rewrite (EE 23%nat 23%bv eq_refl); exact H23).
assert (SHOK : sh_ok SEGS rl7_B [] E (mrestrict (w_H W) memc)) by apply Forall_nil.
clear Hs HPimg EE.
destruct Hshc as [[-> ->] | [-> ->]];
  (assert (Hj5 : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by (clear - Hj; lia));
  destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]].
all: paj_run_tok RUN HS HJ SHOK rl7_span.
all: lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ =>
      lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
        let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
      repeat (apply awr_ok_cons_ro; [cbn; clear; lia|]); apply awr_ok_nil
  | |- _ =>
      prreg HS (23%bv : bv 5) RG23; prreg HS (12%bv : bv 5) RG12; prreg HS (14%bv : bv 5) RG14;
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl7_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr;
      cbn [ms_regs restrict] in HKr;
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
        by (intros a Ha;
            apply (kept_of_frame E _ (w_H W) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | intros []];
            intros bq wlo whi aq Hin Haq;
            cbn [ss_mem rl7_sso windows map YP09.r_base YP09.r_wlo YP09.r_whi rl7_litR rl7_shR] in Hin;
            destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; clear - Haq; lia);
      pmkst HS;
      eapply K;
      [ reflexivity
      | exact HJ
      | apply rl7_keep; [exact HKr | rewrite RG14, H14; reflexivity]
      | rewrite RG23; rl7_regval
      | rewrite RG12; rl7_regval
      | exact HG
      | exact KEEP ]
  end.
Qed.
Lemma rl7_step_list : forall j n, 1 <= j <= 5 -> n <= 46 ->
  firstn (Z.to_nat (47 - n)) (skipn (Z.to_nat (j - 1)) rbn_lit7) =
  nth (Z.to_nat (j - 1)) rl7_lits 0 :: firstn (Z.to_nat (47 - (n + 1))) (skipn (Z.to_nat j) rbn_lit7).
Proof.
intros j n Hj Hn.
replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - (n + 1)))) by lia.
assert (Hj5 : j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
destruct Hj5 as [-> | [-> | [-> | [-> | ->]]]]; reflexivity.
Qed.
Lemma rl7_from : forall (t : nat) (j : Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc0 k
  (regs0 regs : bvmap 5 word) memc mdc A1 D n0 n ov (wr : list Z),
  Z.of_nat t = 5 - j -> 1 <= j ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 24) mod 8 = 0 ->
  CEIL_MIN <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 24) \/ VAL (A_OBJ 24) + 6 <= A1 + 120) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 24) + 6 <= D \/ D + 48 <= VAL (A_OBJ 24)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 -> n0 <= n -> n <= 47 -> 0 <= ov <= 1 ->
  getr regs 23 = w64 n -> getr regs 16 = w64 (n + 1) -> getr regs 12 = w64 ov ->
  getr regs 15 = w64 (nth (Z.to_nat (j - 1)) rl7_lits 0) -> getr regs 21 = w64 j ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 24)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  rbn_keep_regs regs0 regs rl7_cl ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (D + n0 <= a < D + n) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc0 a) ->
  garr8 SEGS (mrestrict (w_H W) memc) (D + n0) wr -> Z.of_nat (length wr) = n - n0 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))) memc (seg_rom SEGS)) mdc)
    (rbn_lpost B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc0 k regs0 RBN_L7X rl7_cl D n0
       (wr ++ firstn (Z.to_nat (47 - n)) (skipn (Z.to_nat (j - 1)) rbn_lit7))
       [(23, Z.min 47 (n + (6 - j))); (12, if 47 <? n + (6 - j) then 1 else ov)]).
Proof.
induction t as [|t IH]; intros j STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc0 k regs0 regs memc mdc A1 D n0 n ov wr
  Ht Hj1 HJ Hsrc HP8 HA1 HA147 Hdsl Hbuf Hdbl Hslot Hdbs Hn0 Hn0n Hn47 Hov H23 H16 H12 H15 H21 H14 H11 H13 H9 H22
  HKP HFR Hgw Hwl.
all: assert (Hj5 : j <= 5) by (clear - Ht; lia).
all: pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
all: pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
all: assert (HD4 : 4096 <= D) by (destruct HDapp as [HH _]; exact HH).
all: assert (HD47 : D + 48 <= 2 ^ 47)
  by (clear - HDapp CR; destruct HDapp as [_ [HL | [HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg in *; lia).
all: destruct (Z_le_gt_dec n 46) as [Hn46 | Hn47'].
- apply (rl7_round_f STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n ov j _
    ltac:(clear - Hj1 Hj5; lia) ltac:(clear - Hn0 Hn0n Hn46; lia) Hov HJ Hsrc HP8 HA1 HA147 Hdsl Hbuf Hdbl Hslot Hdbs
    H23 H16 H12 H15 H21 H14 H11 H13 H9 H22).
  intros regs' mem' md' pc Hpc HJ' HKP' R23 R12 R15 R21 R16 HG' KEEP' Vc.
  assert (Hj : j = 5) by (clear - Ht; cbn in Ht; lia). subst j.
  replace (5 <? 5) with false in Hpc by reflexivity.
  apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
  split; [unfold rbn_cfg, cfg_at, w64; rewrite Hpc, Z.add_assoc; reflexivity|].
  split; [exact HJ'|].
  split; [exact (rl7_keep_trans regs0 regs regs' rl7_cl HKP HKP')|].
  assert (Hlst : firstn (Z.to_nat (47 - n)) (skipn (Z.to_nat (5 - 1)) rbn_lit7) = [41]).
  { replace (Z.to_nat (47 - n)) with (Datatypes.S (Z.to_nat (47 - (n + 1)))) by (clear - Hn46; lia).
    change (skipn (Z.to_nat (5 - 1)) rbn_lit7) with [41]. cbn [firstn]. rewrite firstn_nil. reflexivity. }
  rewrite Hlst.
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R23. f_equal. clear - Hn46. lia.
    - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R12. replace (47 <? n + (6 - 5)) with false by (symmetry; apply Z.ltb_ge; clear - Hn46; lia).
      reflexivity. }
  split.
  { intros a Ha Hout. rewrite length_app in Hout. cbn [length] in Hout.
    rewrite (KEEP' a Ha ltac:(clear - Hout Hwl; lia)). apply HFR; [exact Ha | clear - Hout Hwl; lia]. }
  apply (garr8_app1 SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') (D + n0) wr 41 Hgw).
  + rewrite Hwl. replace (D + n0 + (n - n0)) with (D + n) by (clear; lia). exact Vc.
  + lia.
  + intros a Ha. rewrite Hwl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
    apply KEEP'; [clear - Ha HD4 HD47 Hn0 Hn46; lia | clear - Ha; lia].
- assert (Hn47e : n = 47) by (clear - Hn47 Hn47'; lia). subst n.
  apply (rl7_round_o STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ov j _
    ltac:(clear - Hj1 Hj5; lia) Hov HJ Hsrc HP8 H23 H16 H12 H15 H21 H14 H11 H13 H22).
  intros regs' mem' md' pc Hpc HJ' HKP' R23 R12 HG' KEEP'.
  apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
  split; [unfold rbn_cfg, cfg_at, w64; rewrite Hpc, Z.add_assoc; reflexivity|].
  split; [exact HJ'|].
  split; [exact (rl7_keep_trans regs0 regs regs' rl7_cl HKP HKP')|].
  replace (Z.to_nat (47 - 47)) with 0%nat by reflexivity. rewrite firstn_O, app_nil_r.
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R23. f_equal. clear - Hj5. lia.
    - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R12. replace (47 <? 47 + (6 - j)) with true by (symmetry; apply Z.ltb_lt; clear - Hj5; lia).
      reflexivity. }
  split.
  { intros a Ha Hout. rewrite (KEEP' a Ha). apply HFR; [exact Ha | clear - Hout Hwl; lia]. }
  apply (rl7_garr8_kept SEGS (w_H W) (w_H W) memc mem' (D + n0) wr); [|exact Hgw].
  intros a Ha. apply KEEP'. clear - Ha HD4 HD47 Hn0 Hwl. lia.
- apply (rl7_round_f STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n ov j _
    ltac:(clear - Hj1 Hj5; lia) ltac:(clear - Hn0 Hn0n Hn46; lia) Hov HJ Hsrc HP8 HA1 HA147 Hdsl Hbuf Hdbl Hslot Hdbs
    H23 H16 H12 H15 H21 H14 H11 H13 H9 H22).
  intros regs' mem' md' pc Hpc HJ' HKP' R23 R12 R15 R21 R16 HG' KEEP' Vc.
  assert (Hj4 : j < 5) by (clear - Ht; lia).
  replace (j <? 5) with true in Hpc by (symmetry; apply Z.ltb_lt; exact Hj4).
  rewrite Hpc.
  assert (Happ : in_app (D + n) 1)
    by (apply (in_app_sub D 48); [exact HDapp | clear - Hn0 Hn0n; lia | lia | clear - Hn0 Hn0n Hn46; lia]).
  rewrite (rl7_step_list j n ltac:(clear - Hj1 Hj5; lia) Hn46).
  replace (wr ++ nth (Z.to_nat (j - 1)) rl7_lits 0 :: firstn (Z.to_nat (47 - (n + 1))) (skipn (Z.to_nat j) rbn_lit7))
    with ((wr ++ [nth (Z.to_nat (j - 1)) rl7_lits 0]) ++
          firstn (Z.to_nat (47 - (n + 1))) (skipn (Z.to_nat (j + 1 - 1)) rbn_lit7))
    by (rewrite <- app_assoc; replace (j + 1 - 1) with j by (clear; lia); reflexivity).
  replace (n + (6 - j)) with (n + 1 + (6 - (j + 1))) by (clear; lia).
  apply (IH (j + 1) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc0 k regs0 regs' mem' md' A1 D n0 (n + 1) ov
    (wr ++ [nth (Z.to_nat (j - 1)) rl7_lits 0])).
  + clear - Ht. lia.
  + clear - Hj1. lia.
  + exact HJ'.
  + apply (rl7_src_keep W memc mem' (VAL (A_OBJ 24)) _ (D + n) Hsrc KEEP' Happ).
    cbn [length app rbn_lit7 Z.of_nat]. clear - Hdbl Hn46 Hn0 Hn0n. lia.
  + exact HP8.
  + exact HA1.
  + exact HA147.
  + exact Hdsl.
  + apply (rl7_buf_keep B STK sp0 FP ly S own lyc Sc W memc mem' D 48 (D + n) Hbuf KEEP' HG' Happ). lia.
  + exact Hdbl.
  + apply (rl7_vm_kept SEGS (w_H W) (w_H W) memc mem' (A1 + 120) 8 D); [|exact Hslot].
    intros x Hx. apply KEEP'; [clear - Hx HA147 HA1; lia | clear - Hx Hdbs Hn46 Hn0 Hn0n; lia].
  + exact Hdbs.
  + exact Hn0.
  + clear - Hn0n. lia.
  + clear - Hn46. lia.
  + exact Hov.
  + exact R23.
  + replace (n + 1 + 1) with (n + 2) by lia. exact (R16 Hj4).
  + exact R12.
  + replace (j + 1 - 1) with j by lia. exact R15.
  + exact R21.
  + rewrite (rl7_kept_reg regs regs' 14%bv HKP' ltac:(vm_compute; clear; lia)). exact H14.
  + rewrite (rl7_kept_reg regs regs' 11%bv HKP' ltac:(vm_compute; clear; lia)). exact H11.
  + rewrite (rl7_kept_reg regs regs' 13%bv HKP' ltac:(vm_compute; clear; lia)). exact H13.
  + rewrite (rl7_kept_reg regs regs' 9%bv HKP' ltac:(vm_compute; clear; lia)). exact H9.
  + rewrite (rl7_kept_reg regs regs' 22%bv HKP' ltac:(vm_compute; clear; lia)). exact H22.
  + exact (rl7_keep_trans regs0 regs regs' rl7_cl HKP HKP').
  + intros a Ha Hout. rewrite (KEEP' a Ha ltac:(clear - Hout Hn0n; lia)). apply HFR; [exact Ha | clear - Hout; lia].
  + apply (garr8_app1 SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) mem') (D + n0) wr _ Hgw).
    * rewrite Hwl. replace (D + n0 + (n - n0)) with (D + n) by (clear; lia). exact Vc.
    * apply rl7_lit_range.
    * intros a Ha. rewrite Hwl in Ha. apply (mbyte_of_aview SEGS (w_H W) (w_H W)).
      apply KEEP'; [clear - Ha HD4 HD47 Hn0 Hn46; lia | clear - Ha; lia].
  + rewrite length_app. cbn [length]. clear - Hwl. lia.
- assert (Hn47e : n = 47) by (clear - Hn47 Hn47'; lia). subst n.
  apply (rl7_round_o STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ov j _
    ltac:(clear - Hj1 Hj5; lia) Hov HJ Hsrc HP8 H23 H16 H12 H15 H21 H14 H11 H13 H22).
  intros regs' mem' md' pc Hpc HJ' HKP' R23 R12 HG' KEEP'.
  apply SRr_ret. split; [reflexivity|]. exists regs', mem', md'.
  split; [unfold rbn_cfg, cfg_at, w64; rewrite Hpc, Z.add_assoc; reflexivity|].
  split; [exact HJ'|].
  split; [exact (rl7_keep_trans regs0 regs regs' rl7_cl HKP HKP')|].
  replace (Z.to_nat (47 - 47)) with 0%nat by reflexivity. rewrite firstn_O, app_nil_r.
  split.
  { apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd].
    - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R23. f_equal. clear - Hj5. lia.
    - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite R12. replace (47 <? 47 + (6 - j)) with true by (symmetry; apply Z.ltb_lt; clear - Hj5; lia).
      reflexivity. }
  split.
  { intros a Ha Hout. rewrite (KEEP' a Ha). apply HFR; [exact Ha | clear - Hout Hwl; lia]. }
  apply (rl7_garr8_kept SEGS (w_H W) (w_H W) memc mem' (D + n0) wr); [|exact Hgw].
  intros a Ha. apply KEEP'. clear - Ha HD4 HD47 Hn0 Hwl. lia.
Qed.
Lemma rl7_main : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k
  (regs : bvmap 5 word) A1 D n0 ov0,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  rbn_lsrc W memc (VAL (A_OBJ 24)) (rbn_lit7 ++ [0]) -> VAL (A_OBJ 24) mod 8 = 0 ->
  CEIL_MIN <= A1 + 120 -> A1 + 128 <= 2 ^ 47 ->
  (A1 + 128 <= VAL (A_OBJ 24) \/ VAL (A_OBJ 24) + 6 <= A1 + 120) ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 48 ->
  (VAL (A_OBJ 24) + 6 <= D \/ D + 48 <= VAL (A_OBJ 24)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (A1 + 120) 8 D -> (A1 + 128 <= D \/ D + 48 <= A1 + 120) ->
  0 <= n0 <= 47 -> 0 <= ov0 <= 1 ->
  getr regs 23 = w64 n0 -> getr regs 12 = w64 ov0 -> getr regs 15 = w64 32 -> getr regs 21 = w64 1 ->
  getr regs 14 = w64 6 -> getr regs 11 = w64 48 -> getr regs 13 = w64 (VAL (A_OBJ 24)) ->
  getr regs 9 = w64 A1 -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (rbn_cfg RBN_L7 regs memc mdc)
    (rbn_lpost B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L7X rl7_cl D n0
       (firstn (Z.to_nat (47 - n0)) rbn_lit7) [(23, Z.min 47 (n0 + 5)); (12, if 47 <? n0 + 5 then 1 else ov0)]).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 HJ Hsrc HP8 HA1 HA147 Hdsl Hbuf Hdbl
  Hslot Hdbs Hn0 Hov H23 H12 H15 H21 H14 H11 H13 H9 H22.
pose proof (@paj_run_to fx _ _ _ _ _ B LAWS) as RUNTO.
pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
assert (Happ : in_app D 1) by (apply (in_app_sub D 48); [exact HDapp | lia | lia | lia]).
set (E0 := Eimg (Ereg regs [])).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E0)
  by (unfold E0; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E0 rl7_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L7))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rl7_ss0. apply pa_entry_st_ok_full.
  - unfold E0. apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS rl7_B [] E0 (mrestrict (w_H W) memc)) by apply Forall_nil.
assert (E023 : ew E0 23 = Z_to_bv 64 n0) by (unfold E0; rewrite (ew_Eimg_Ereg_nat regs [] 23 23%bv eq_refl); exact H23).
assert (Hn0' : 0 <= n0 <= 47) by exact Hn0.
unfold rbn_cfg, cfg_at, w64. rewrite <- Z.add_assoc.
paj_run_to_tok RUNTO HS HJ SHOK rl7_span (AF_reac_box_name + (RBN_L7 + 4)).
{ cbn [ss_mem rl7_ss0]. apply awr_ok_nil. }
prreg HS (16%bv : bv 5) RG16.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl7_keptl0 HS ltac:(env_agree_chain HAE)
  ltac:(vm_compute; reflexivity)) as HKr.
cbn [ms_regs restrict] in HKr.
assert (KEEPall : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha.
  apply (kept_of_frame E0 _ (w_H W) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | intros []].
  intros bq wlo whi aq Hin Haq. cbn [ss_mem rl7_ss0 windows map] in Hin. destruct Hin. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> a <> D -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a)
  by (intros a Ha _; exact (KEEPall a Ha)).
pmkst HS.
change (Z_to_bv 64 (BASE + 10972)) with (Z_to_bv 64 (BASE + (AF_reac_box_name + (RBN_L7 + 4)))).
change (firstn (Z.to_nat (47 - n0)) rbn_lit7)
  with ([] ++ firstn (Z.to_nat (47 - n0)) (skipn (Z.to_nat (1 - 1)) rbn_lit7)).
change (n0 + 5) with (n0 + (6 - 1)).
apply (rl7_from 4 1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs (ms_regs ms) (ms_mem ms) _ A1 D n0 n0 ov0 []).
- reflexivity.
- lia.
- exact HJ.
- apply (rl7_src_keep W memc (ms_mem ms) (VAL (A_OBJ 24)) _ D Hsrc KEEP Happ).
  cbn [length app rbn_lit7 Z.of_nat]. clear - Hdbl. lia.
- exact HP8.
- exact HA1.
- exact HA147.
- exact Hdsl.
- apply (rl7_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms) D 48 D Hbuf KEEP HG Happ). lia.
- exact Hdbl.
- apply (rl7_vm_kept SEGS (w_H W) (w_H W) memc (ms_mem ms) (A1 + 120) 8 D); [|exact Hslot].
  intros x Hx. apply KEEP; [clear - Hx HA1 HA147; lia | clear - Hx Hdbs; lia].
- exact Hdbs.
- lia.
- lia.
- lia.
- exact Hov.
- rewrite (HKr 23%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H23.
- rewrite RG16. cbn [sv_denot]. rewrite E023, unsigned_lit_small by (clear - Hn0'; lia). reflexivity.
- rewrite (HKr 12%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H12.
- rewrite (HKr 15%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H15.
- rewrite (HKr 21%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H21.
- rewrite (HKr 14%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H14.
- rewrite (HKr 11%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H11.
- rewrite (HKr 13%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H13.
- rewrite (HKr 9%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H9.
- rewrite (HKr 22%bv ltac:(unfold rl7_keptl0; cbn [In]; repeat first [solve [left; reflexivity] | right])). exact H22.
- intros r Hr Hn. destruct (Z.eq_dec r 0) as [-> | Hr0].
  { replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite !getr_zero. reflexivity. }
  assert (Hr16 : r <> 16) by (intros ->; apply Hn; unfold rl7_cl; cbn; tauto).
  apply HKr. clear - Hr Hr0 Hr16.
  assert (H32 : r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
    r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 17 \/ r = 18 \/ r = 19 \/
    r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
    r = 30 \/ r = 31) by lia.
  repeat (destruct H32 as [-> | H32]); try (subst r); unfold rl7_keptl0; cbn [In];
    repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ].
- intros a Ha _. exact (KEEPall a Ha).
- apply garr8_nil.
- cbn [length Z.of_nat]. clear. lia.
Qed.
Lemma rbn_l7_fits : rbn_L7_fits B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hle.
unfold rbn_L7_run. intros HJ Hsrc HP8 Hcl HA147 Hdsl Hbuf Hdbl Hslot Hdbs Hn0 Hov H23 H12 H15 H21 H14 H11 H13 H9 H22.
assert (HA1 : CEIL_MIN <= A1 + 120) by (pose proof (@YM05.alloc_ceiling_value rc) as Hrc; clear - Hcl Hrc; lia).
assert (Hov' : 0 <= ov0 <= 1) by (clear - Hov; lia).
pose proof (rl7_main STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 HJ Hsrc HP8 HA1 HA147
  Hdsl Hbuf Hdbl Hslot Hdbs Hn0 Hov' H23 H12 H15 H21 H14 H11 H13 H9 H22) as Hm.
replace (firstn (Z.to_nat (47 - n0)) rbn_lit7) with rbn_lit7 in Hm
  by (symmetry; apply firstn_all2; cbn [length rbn_lit7]; clear - Hle; lia).
replace (Z.min 47 (n0 + 5)) with (n0 + 5) in Hm by (clear - Hle; lia).
replace (if 47 <? n0 + 5 then 1 else ov0) with ov0 in Hm
  by (destruct (Z.ltb_spec 47 (n0 + 5)); [clear - Hle H; lia | reflexivity]).
exact Hm.
Qed.
Lemma rbn_l7_ovf : rbn_L7_ovf B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 Hlt.
unfold rbn_L7_run. intros HJ Hsrc HP8 Hcl HA147 Hdsl Hbuf Hdbl Hslot Hdbs Hn0 Hov H23 H12 H15 H21 H14 H11 H13 H9 H22.
assert (HA1 : CEIL_MIN <= A1 + 120) by (pose proof (@YM05.alloc_ceiling_value rc) as Hrc; clear - Hcl Hrc; lia).
assert (Hov' : 0 <= ov0 <= 1) by (clear - Hov; lia).
pose proof (rl7_main STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs A1 D n0 ov0 HJ Hsrc HP8 HA1 HA147
  Hdsl Hbuf Hdbl Hslot Hdbs Hn0 Hov' H23 H12 H15 H21 H14 H11 H13 H9 H22) as Hm.
replace (Z.min 47 (n0 + 5)) with 47 in Hm by (clear - Hlt; lia).
replace (if 47 <? n0 + 5 then 1 else ov0) with 1 in Hm
  by (destruct (Z.ltb_spec 47 (n0 + 5)); [reflexivity | clear - Hlt H; lia]).
exact Hm.
Qed.
End h.
End f.
End d.
