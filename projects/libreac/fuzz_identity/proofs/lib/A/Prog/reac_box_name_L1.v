(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:61-65, 107-112, for
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Lemma rl1_mb_eq : forall (segs : list Segment) H H' (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
intros segs H H' m m' a a' E. unfold aview in E.
destruct (mbyte segs (mrestrict H' m') a') as [b'|], (mbyte segs (mrestrict H m) a) as [b|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma rl1_garr8_kept : forall (segs : list Segment) H H' (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview segs H' m' a = aview segs H m a) ->
  garr8 segs (mrestrict H m) p L -> garr8 segs (mrestrict H' m') p L.
Proof.
intros segs H H' m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. cbn in Hk. pose proof (Hv k Hk) as Hb.
rewrite (rl1_mb_eq segs H H' m m' (p + Z.of_nat j + Z.of_nat k) (p + Z.of_nat j + Z.of_nat k)); [exact Hb|].
apply HE. lia.
Qed.
Lemma rl1_garr8_cons : forall (segs : list Segment) (m : word -> option byte) p v L,
  val_mem segs m p 1 v -> 0 <= v < 256 -> garr8 segs m (p + 1) L -> garr8 segs m p (v :: L).
Proof.
intros segs m p v L Hv Hr HG j Hj. destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
- cbn [nth]. cbn in Hj. destruct (HG j ltac:(lia)) as [Hv' Hr']. split; [|exact Hr'].
  replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by lia. exact Hv'.
Qed.
Lemma rl1_vm_kept : forall (segs : list Segment) H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros segs H H' m m' a n v HE Hv k Hk.
rewrite (rl1_mb_eq segs H H' m m' (a + Z.of_nat k) (a + Z.of_nat k) (HE (a + Z.of_nat k) ltac:(lia))).
exact (Hv k Hk).
Qed.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Definition rl1_B : sv := SOff 22 0.
Definition rl1_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rl1_SH : list shent := [mkSHE 32 1 0].
Definition rl1_ss : sstate :=
  mkSS (AF_reac_box_name + RBN_L1) (sr_set sr_atoms 14%bv (SLit 23))
    [ YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
      YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ] None
    (mkFacts [ (22%nat, mkAF SB SB 0); (24%nat, mkAF 0 23 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0);
               (10%nat, mkAF 1 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0) ] []
      [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0)]).
Definition rl1_E (regs : bvmap 5 word) (dn c b : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [dn; c; b])).
Lemma rl1_VB : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v.
Proof. intros E m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. Qed.
Lemma rl1_ew : forall regs dn c b,
  ew (rl1_E regs dn c b) 32 = Z_to_bv 64 dn /\ ew (rl1_E regs dn c b) 33 = Z_to_bv 64 c /\
  ew (rl1_E regs dn c b) 34 = Z_to_bv 64 b /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (rl1_E regs dn c b) k = getr regs r).
Proof.
intros regs dn c b. unfold rl1_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma rl1_shok : forall E (m : word -> option byte) q,
  ew E 22 = Z_to_bv 64 SB -> ew E 32 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  (q + 1 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  sh_ok SEGS rl1_B rl1_SH E m.
Proof.
intros E m q H22 H32 Hq Ha. constructor; [|constructor].
eapply shent_app_of_app.
- unfold rl1_B. rewrite (U_atom E 22 SB H22) by (unfold SB; lia). reflexivity.
- exact (U_atom E 32 q H32 Hq).
- lia.
- lia.
Qed.
Lemma rl1_ext : forall E K ws n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K n Hn; cbn [extK]; [reflexivity|].
rewrite (IH (ewset E K w) (S K) n ltac:(lia)). apply ew_ewset_other. lia.
Qed.
Lemma rl1_app_not_shadow : forall x a, in_app x 1 -> 0 <= a -> a < 2 ^ 47 -> x <> SHADOW_OFF + a / 8.
Proof.
intros x a Hx H0 Ha Heq.
assert (Hd : 0 <= a / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rl1_src_keep : forall (W : world SEGS) (mem mem' : word -> option byte) P l X,
  rbn_lsrc W mem P l ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> X -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  in_app X 1 -> ~ (P <= X < P + Z.of_nat (length l)) ->
  rbn_lsrc W mem' P l.
Proof.
intros W mem mem' P l X (HG & HP0 & HP63 & HP47 & HRA) HK Hx Hnin.
split; [|split; [exact HP0 | split; [exact HP63 | split; [exact HP47|]]]].
- apply (rl1_garr8_kept SEGS (w_H W) (w_H W) mem mem' P l); [|exact HG].
  intros a Ha. apply HK; [lia | lia].
- intros y Hy. unfold shadow_of_addr.
  rewrite (HK (SHADOW_OFF + y / 8)).
  + apply HRA. lia.
  + assert (Hd : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHADOW_OFF. lia.
  + intros Heq. apply (rl1_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
Qed.
Lemma rl1_buf_keep : forall B STK sp0 FP ly S own lyc Sc (W : world SEGS) (mem mem' : word -> option byte) D n X,
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W mem D n ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> X -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  in_app X 1 -> 0 <= n ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W mem' D n.
Proof.
intros B STK sp0 FP ly S own lyc Sc W mem mem' D n X (HD0 & HD63 & HDapp & HRA & HW) HK HGr Hx Hn.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof HDapp as (HDlo & HDhi).
assert (Hhi : D + n <= 2 ^ 47)
  by (unfold kLowShadowBeg, kHighMemBeg in HDhi; lia).
split; [exact HD0|]. split; [exact HD63|]. split; [exact HDapp|]. split.
- intros y Hy. unfold shadow_of_addr.
  rewrite (HK (SHADOW_OFF + y / 8)).
  + apply HRA. lia.
  + assert (Hd : 0 <= y / 8 < 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHADOW_OFF. lia.
  + intros Heq. apply (rl1_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
- intros a Ha. split; [exact (proj1 (HW a Ha))|].
  apply (apresent_grows _ _ _ _ HGr). exact (proj2 (HW a Ha)).
Qed.
Lemma rl1_keep_of_bv : forall (regs regs2 : bvmap 5 word) (cl : list Z) (l : list (bv 5)),
  (forall rr : bv 5, In rr l -> getr regs2 rr = getr regs rr) ->
  (forall r : Z, 0 <= r < 32 -> ~ In r cl -> r = 0 \/ In (Z_to_bv 5 r) l) ->
  rbn_keep_regs regs regs2 cl.
Proof.
intros regs regs2 cl l HK Hc r Hr Hn. destruct (Hc r Hr Hn) as [-> | Hin]; [reflexivity|].
apply HK. exact Hin.
Qed.
Lemma rl1_byte_at : forall (W : world SEGS) (mem : word -> option byte) a,
  apresent (w_H W) mem a -> exists v, val_mem SEGS (mrestrict (w_H W) mem) a 1 v /\ 0 <= v < 256.
Proof.
intros W mem a Hp.
assert (Hv : aview SEGS (w_H W) mem a <> None) by (apply (aview_some_of_apresent SEGS); exact Hp).
unfold aview in Hv.
destruct (mbyte SEGS (mrestrict (w_H W) mem) a) as [bb|] eqn:Em; [|cbn in Hv; exfalso; exact (Hv eq_refl)].
pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
exists (bv_unsigned bb). split; [|lia].
intros j Hj. assert (j = 0%nat) as -> by lia. rewrite Z.add_0_r, Em. f_equal.
change (YO0f.le_byte (bv_unsigned bb) 1 0) with ((bv_unsigned bb mod 256) mod 256).
rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.


Lemma rl1_entry : forall (W : world SEGS) (regs : bvmap 5 word) memc Q D n c b,
  getr regs 14 = w64 23 -> getr regs 22 = w64 SHADOW_OFF -> getr regs 24 = w64 n -> getr regs 27 = w64 D ->
  getr regs 13 = w64 Q -> getr regs 10 = w64 Q ->
  0 <= n <= 23 -> 1 <= Q <= 2 ^ 47 - 1 -> 4096 <= D -> D + n <= 2 ^ 47 - 1 ->
  val_mem SEGS (mrestrict (w_H W) memc) Q 1 c -> 0 <= c < 256 ->
  val_mem SEGS (mrestrict (w_H W) memc) (D + n) 1 b -> 0 <= b < 256 ->
  apresent (w_H W) memc (D + n) ->
  (Q + 1 <= D + n \/ D + n + 1 <= Q) ->
  st_ok_pi SEGS VAL (rl1_E regs (D + n) c b) rl1_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L1))) memc (seg_rom SEGS))).
Proof.
intros W regs memc Q D n c b H14 H22 H24 H27 H13 H10 Hn HQ HD HDn Vc Rc Vb Rb Hp Hdj.
rewrite restrict_mkst_fx.
destruct (rl1_ew regs (D + n) c b) as (E32 & E33 & E34 & EE).
assert (HR : regs_ok (rl1_E regs (D + n) c b) (sr_set sr_atoms 14%bv (SLit 23)) regs)
  by (apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H14]).
remember (rl1_E regs (D + n) c b) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = Z_to_bv 64 D) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E13 : ew E 13 = Z_to_bv 64 Q) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E10 : ew E 10 = Z_to_bv 64 Q) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
unfold rl1_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E13, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ Q 0 1 (SOff 33 0) c);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vc.
  + cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); replace (D + n + o) with (D + n) by lia; exact Hp|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (D + n) 0 1 (SOff 34 0) b);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Vb.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E13, E32, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E24, E32, E10, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 27 D E27), (U_atom E 24 n E24), (U_atom E 32 (D + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Lemma rl1_src_tail : forall (W : world SEGS) (mem : word -> option byte) P c l,
  rbn_lsrc W mem P (c :: l) -> rbn_lsrc W mem (P + 1) l.
Proof.
intros W mem P c l (HG & H0 & H63 & H47 & HRA).
assert (HL : Z.of_nat (length (c :: l)) = Z.of_nat (length l) + 1) by (try cbn [length]; lia).
change (c :: l) with ([c] ++ l) in HG.
split; [|split; [lia | split; [lia | split; [lia|]]]].
- pose proof (proj1 (garr8_app SEGS (mrestrict (w_H W) mem) P [c] l) HG) as (_ & HG2).
  cbn [length Z.of_nat] in HG2. exact HG2.
- eapply range_addressable_sub; [exact HRA | lia | lia].
Qed.
Ltac rl1_u_atom H n v :=
  lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
    assert (H : U Ev (SOff n 0) = v) by
      (apply (U_atom Ev n v); [rewrite ?ew_ewset_other by lia; assumption | lia]) end.
Ltac rl1_regval :=
  cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
  repeat match goal with Hq : ew ?Ex ?nq = Z_to_bv 64 _ |- context [ew ?Ex ?nq] => rewrite Hq end;
  rewrite ?unsigned_lit_small by lia; unfold w64;
  first [ reflexivity | (f_equal; lia) | (apply bv_eq; vm_compute; reflexivity) ].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition rl1_cl : list Z := [5; 10; 11; 13; 15; 16; 17; 24; 30].
Definition rl1_keptl : list (bv 5) :=
  [1; 2; 3; 4; 6; 7; 8; 9; 12; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 31]%bv.
Lemma rl1_kept_cover : forall r : Z, 0 <= r < 32 -> ~ In r rl1_cl ->
  r = 0 \/ r = 14 \/ In (Z_to_bv 5 r) rl1_keptl.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [right; left; reflexivity]
        | solve [exfalso; apply Hn; unfold rl1_cl; cbn [In];
                 repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; right; unfold rl1_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Lemma rl1_gen : forall (s : list Z) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) P D n0 ov0,
  rbn_L1_run B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (Z.min 23 (n0 + Z.of_nat (length s)))
    (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0)
    (firstn (Z.to_nat (23 - n0)) s).
Proof.
induction s as [|c r IH]; intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0;
  unfold rbn_L1_run; intros HJ Hne Hall Hsrc Hbuf Hdj Hn0 Hov0 H24 H30 H15 H13 H10 H14 H27 H22;
  [exfalso; exact (Hne eq_refl)|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (@paj_run fx _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fx _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI)) as BR.
pose proof Hsrc as (HGs & HP0 & HP63 & HP47 & HRAs).
pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
pose proof HDapp as (HDlo & HDhi).
cbn [hd] in H15.
assert (Hlen : Z.of_nat (length ((c :: r) ++ [0])) = Z.of_nat (length r) + 2)
  by (rewrite length_app; cbn [length]; lia).
assert (HDn : D + n0 <= 2 ^ 47 - 1) by (unfold kLowShadowBeg, kHighMemBeg in HDhi; lia).
assert (HQ : 1 <= P + 1 <= 2 ^ 47 - 1) by lia.
assert (Hcr : 0 < c < 256) by (inversion Hall; assumption).
set (c1 := hd 0 (r ++ [0])).
assert (Vc1 : val_mem SEGS (mrestrict (w_H W) memc) (P + 1) 1 c1 /\ 0 <= c1 < 256).
{ destruct (garr8_nthZ SEGS (mrestrict (w_H W) memc) P ((c :: r) ++ [0]) 1 HGs ltac:(lia) ltac:(lia))
    as (Hv1 & Hr1).
  replace (nth (Z.to_nat 1) ((c :: r) ++ [0]) 0) with c1 in Hv1, Hr1 by
    (subst c1; cbn [app nth Z.to_nat Pos.to_nat Pos.iter_op]; destruct r; reflexivity).
  split; assumption. }
destruct Vc1 as (Vc1 & Rc1).
destruct (rl1_byte_at W memc (D + n0) (proj2 (HWb (D + n0) ltac:(lia)))) as (bb & Vb & Rb).
destruct (rl1_ew regs (D + n0) c1 bb) as (E32 & E33 & E34 & EE).
assert (E22 : ew (rl1_E regs (D + n0) c1 bb) 22 = Z_to_bv 64 SB)
  by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew (rl1_E regs (D + n0) c1 bb) 24 = Z_to_bv 64 n0)
  by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E15 : ew (rl1_E regs (D + n0) c1 bb) 15 = Z_to_bv 64 c)
  by (rewrite (EE 15%nat 15%bv eq_refl); exact H15).
assert (E30 : ew (rl1_E regs (D + n0) c1 bb) 30 = Z_to_bv 64 ov0)
  by (rewrite (EE 30%nat 30%bv eq_refl); exact H30).
assert (E10 : ew (rl1_E regs (D + n0) c1 bb) 10 = Z_to_bv 64 (P + 1))
  by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E13 : ew (rl1_E regs (D + n0) c1 bb) 13 = Z_to_bv 64 (P + 1))
  by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E27 : ew (rl1_E regs (D + n0) c1 bb) 27 = Z_to_bv 64 D)
  by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (Hlencr : Z.of_nat (length (c :: r)) = Z.of_nat (length r) + 1) by (try cbn [length]; lia).
assert (Hdj2 : P + 1 + 1 <= D + n0 \/ D + n0 + 1 <= P + 1) by lia.
assert (HD4 : 4096 <= D) by lia.
assert (Hpres0 : apresent (w_H W) memc (D + n0)) by (exact (proj2 (HWb (D + n0) ltac:(lia)))).
pose proof (rl1_entry W regs memc (P + 1) D n0 c1 bb H14 H22 H24 H27 H13 H10 Hn0 HQ
  HD4 HDn Vc1 Rc1 Vb Rb Hpres0 Hdj2) as HS.
set (E := rl1_E regs (D + n0) c1 bb) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rl1_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [D + n0; c1; bb])) E)
  by (unfold E, rl1_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS rl1_B rl1_SH E (mrestrict (w_H W) memc))
  by (apply (rl1_shok E _ (D + n0)); [exact E22 | exact E32 | lia
      | unfold kLowShadowBeg, kHighMemBeg in HDhi |- *; lia]).
unfold rbn_cfg, cfg_at. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ SHOK rl1_span.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
    [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
  exact (proj1 (HWb (D + n0) ltac:(lia))). }
assert (Happ1 : in_app (D + n0) 1)
  by (apply (in_app_sub D 24); [exact HDapp | lia | lia | lia]).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ apply (kept_of_frame E (ss_mem rl1_ss) (w_H W) memc (ms_mem ms) (fun a => a = D + n0) HFr).
  intros bq wlo whi a Hin Ha.
  cbn [ss_mem rl1_ss windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
    cbn [base_val] in Ha; rewrite ?E13, ?E32, ?unsigned_lit_small in Ha by lia; lia. }
assert (Hsrc1 : rbn_lsrc W (ms_mem ms) P ((c :: r) ++ [0]))
  by (apply (rl1_src_keep W memc (ms_mem ms) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP1 Happ1); lia).
assert (Hbuf1 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms) D 24)
  by (apply (rl1_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms) D 24 (D + n0) Hbuf KEEP1 HG Happ1); lia).
assert (HUB : U E rl1_B = SHADOW_OFF)
  by (unfold rl1_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (HU10 : U E (SOff 10 0) = P + 1) by (apply (U_atom E 10 (P + 1) E10); lia).
assert (HU32 : U E (SOff 32 0) = D + n0) by (apply (U_atom E 32 (D + n0) E32); lia).
assert (HU24 : U E (SOff 24 1) = n0 + 1) by (apply (U_atom_off E 24 n0 1 E24); lia).
assert (HU23 : U E (SLit 23) = 23) by (rewrite U_SLit; reflexivity).
psrr_branch_tok RUN BR HS SHOK rl1_span.
- rewrite branch_ltu_U, HU23, HU24 in Hc. apply Z.ltb_lt in Hc.
  assert (Hn23 : n0 = 23) by lia.
  paj_run_tok RUN HS HJ SHOK rl1_span.
  { rewrite HU10.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rl1_B (P + 1) 1 P (Z.of_nat (length ((c :: r) ++ [0]))));
      [exact (proj2 (proj2 (proj2 (proj2 Hsrc1)))) | exact HUB | lia | lia]. }
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
      [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
    exact (proj1 (HWb (D + n0) ltac:(lia))). }
  rl1_u_atom HU33 33%nat c1.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hnq. rewrite <- (KEEP1 a Ha Hnq).
    lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ (ms_mem ms)) (mrestrict _ (ms_mem ms0)) |- _ =>
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
      [|exact Ha | exact Hnq] end.
    intros bq wlo whi aq Hin Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
      cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
      rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  psrr_branch_tok RUN BR HS SHOK rl1_span.
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    assert (Hc1 : c1 <> 0)
      by (intros Hz; rewrite Hz in Hc0; cbn in Hc0; discriminate Hc0).
    assert (Hrne : r <> []) by (intros Hz; apply Hc1; subst c1; rewrite Hz; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK rl1_span (AF_reac_box_name + RBN_L1).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32 (D + n0));
        [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia
        | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi]. intros aq Haq. replace aq with (D + n0) by lia.
      exact (proj1 (HWb (D + n0) ltac:(lia))). }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP2 a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (Vb3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 bb).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 34 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E34 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP3 a Ha Hnb)].
      rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms1) (D + n0) bb Vb3 Rb).
      rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
    assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG | exact HG0] | exact HG1]).
    assert (Hsrc3 : rbn_lsrc W (ms_mem ms1) P ((c :: r) ++ [0]))
      by (apply (rl1_src_keep W memc (ms_mem ms1) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP3 Happ1); lia).
    assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
      by (apply (rl1_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
            Hbuf KEEP3 GROW3 Happ1); lia).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl1_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (15%bv : bv 5) RG15.
    prreg HS (13%bv : bv 5) RG13. prreg HS (10%bv : bv 5) RG10. prreg HS (14%bv : bv 5) RG14.
    prreg HS (27%bv : bv 5) RG27. prreg HS (22%bv : bv 5) RG22.
    assert (R14v : getr (ms_regs ms1) 14 = w64 23) by (rewrite RG14; rl1_regval).
    pmkst HS.
    replace (Z.min 23 (n0 + Z.of_nat (length (c :: r)))) with 23 by (try cbn [length]; lia).
    assert (Hcond : (23 <? n0 + Z.of_nat (length (c :: r))) = true)
      by (try cbn [length]; apply Z.ltb_lt; lia).
    rewrite Hcond.
    replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
    eapply SRr_mono.
    { replace (BASE + 9756) with (BASE + AF_reac_box_name + RBN_L1)
        by (unfold AF_reac_box_name, RBN_L1; lia).
      eapply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
        (P + 1) D n0 1).
      - exact HJ.
      - exact Hrne.
      - inversion Hall; assumption.
      - apply (rl1_src_tail W (ms_mem ms1) P c (r ++ [0])). exact Hsrc3.
      - exact Hbuf3.
      - lia.
      - lia.
      - lia.
      - rewrite RG24. rl1_regval.
      - rewrite RG30. rl1_regval.
      - rewrite RG15. subst c1. destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl)|].
        cbn [hd app]. rl1_regval.
      - rewrite RG13. rl1_regval.
      - rewrite RG10. rl1_regval.
      - rewrite RG14. rl1_regval.
      - rewrite RG27. rl1_regval.
      - rewrite RG22. rl1_regval. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
    replace (Z.min 23 (n0 + Z.of_nat (length r))) with 23 in Houts2 by lia.
    replace (if 23 <? n0 + Z.of_nat (length r) then 1 else 1) with 1 in Houts2
      by (destruct (23 <? n0 + Z.of_nat (length r)); reflexivity).
    replace (Z.to_nat (23 - n0)) with 0%nat in Hfr2, Hga2 by lia.
    rewrite firstn_O in Hfr2, Hga2. cbn [length] in Hfr2.
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HJ2|].
    split.
    { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
      destruct (rl1_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R14v, H14. reflexivity. }
    split; [exact Houts2|].
    split.
    { intros a Ha Hout. cbn [length] in Hout.
      rewrite (Hfr2 a Ha ltac:(lia)). apply KEEPB. exact Ha. }
    apply garr8_nil.
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    change (zcanon 0) with 0 in Hc0.
    assert (Hc1 : c1 = 0)
      by (apply negb_false_iff, Z.eqb_eq in Hc0; exact Hc0).
    assert (Hr0 : r = []).
    { destruct r as [|c2 r2]; [reflexivity|]. exfalso.
      assert (Hc2 : 0 < c2 < 256) by (inversion Hall as [|? ? Hx Hy]; inversion Hy; assumption).
      subst c1. cbn [hd app] in Hc1. lia. }
    subst r.
    paj_run_to_tok RUNTO HS HJ SHOK rl1_span (AF_reac_box_name + RBN_L1X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32 (D + n0));
        [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia
        | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi]. intros aq Haq. replace aq with (D + n0) by lia.
      exact (proj1 (HWb (D + n0) ltac:(lia))). }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP2 a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (Vb3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 bb).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 34 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E34 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP3 a Ha Hnb)].
      rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms1) (D + n0) bb Vb3 Rb).
      rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl1_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (14%bv : bv 5) RG14.
    assert (R14v : getr (ms_regs ms1) 14 = w64 23) by (rewrite RG14; rl1_regval).
    pmkst HS.
    replace (Z.min 23 (n0 + Z.of_nat (length [c]))) with 23 by (try cbn [length]; lia).
    assert (Hcond : (23 <? n0 + Z.of_nat (length [c])) = true)
      by (try cbn [length]; apply Z.ltb_lt; lia).
    rewrite Hcond.
    replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
    apply SRr_ret. split; [reflexivity|].
    exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdc) mat1 mdc).
    split.
    { unfold rbn_cfg, cfg_at, w64.
      replace (BASE + AF_reac_box_name + RBN_L1X) with (BASE + 9864)
        by (unfold AF_reac_box_name, RBN_L1X; lia).
      reflexivity. }
    split; [exact HJ|].
    split.
    { intros rr Hrr Hnn.
      destruct (rl1_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R14v, H14. reflexivity. }
    split.
    { apply Forall_cons.
      { cbn [fst snd].
        replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG24. rl1_regval. }
      apply Forall_cons; [|apply Forall_nil].
      cbn [fst snd].
      replace (Z_to_bv 5 30) with (30%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite RG30. rl1_regval. }
    split.
    { intros a Ha Hout. apply KEEPB. exact Ha. }
    apply garr8_nil.
- rewrite branch_ltu_U, HU23, HU24 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK rl1_span.
  { rewrite HU10.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rl1_B (P + 1) 1 P (Z.of_nat (length ((c :: r) ++ [0]))));
      [exact (proj2 (proj2 (proj2 (proj2 Hsrc1)))) | exact HUB | lia | lia]. }
  { rewrite HU32.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rl1_B (D + n0) 1 D 24);
      [exact (proj1 (proj2 (proj2 (proj2 Hbuf1)))) | exact HUB | lia | lia]. }
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
      [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
    exact (proj1 (HWb (D + n0) ltac:(lia))). }
  rl1_u_atom HU33 33%nat c1.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hnq. rewrite <- (KEEP1 a Ha Hnq).
    lazymatch goal with HFr0 : frame_of _ _ (mrestrict _ (ms_mem ms)) (mrestrict _ (ms_mem ms0)) |- _ =>
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
      [|exact Ha | exact Hnq] end.
    intros bq wlo whi aq Hin Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
      cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
      rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  assert (Vc2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + n0) 1 c).
  { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
      pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 15 0)
        (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
    cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
    rewrite ?ew_ewset_other in Vq by lia. rewrite E15 in Vq. rewrite !Z.add_0_r in Vq.
    rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
    change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
    change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
  psrr_branch_tok RUN BR HS SHOK rl1_span.
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    assert (Hc1 : c1 <> 0)
      by (intros Hz; rewrite Hz in Hc0; cbn in Hc0; discriminate Hc0).
    assert (Hrne : r <> []) by (intros Hz; apply Hc1; subst c1; rewrite Hz; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK rl1_span (AF_reac_box_name + RBN_L1).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32 (D + n0));
        [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia
        | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi]. intros aq Haq. replace aq with (D + n0) by lia.
      exact (proj1 (HWb (D + n0) ltac:(lia))). }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP2 a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG | exact HG0] | exact HG1]).
    assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 c).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 15 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E15 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    assert (Hsrc3 : rbn_lsrc W (ms_mem ms1) P ((c :: r) ++ [0]))
      by (apply (rl1_src_keep W memc (ms_mem ms1) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP3 Happ1); lia).
    assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
      by (apply (rl1_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
            Hbuf KEEP3 GROW3 Happ1); lia).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl1_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (15%bv : bv 5) RG15.
    prreg HS (13%bv : bv 5) RG13. prreg HS (10%bv : bv 5) RG10. prreg HS (14%bv : bv 5) RG14.
    prreg HS (27%bv : bv 5) RG27. prreg HS (22%bv : bv 5) RG22.
    assert (R14v : getr (ms_regs ms1) 14 = w64 23) by (rewrite RG14; rl1_regval).
    pmkst HS.
    cbn [length]. rewrite Nat2Z.inj_succ.
    replace (n0 + Z.succ (Z.of_nat (length r))) with (n0 + 1 + Z.of_nat (length r)) by lia.
    assert (HNat : Z.to_nat (23 - n0) = Datatypes.S (Z.to_nat (23 - (n0 + 1)))).
    { replace (23 - n0) with (1 + (23 - (n0 + 1))) by lia.
      rewrite Z2Nat.inj_add by lia. reflexivity. }
    rewrite HNat.
    cbn [firstn].
    eapply SRr_mono.
    { replace (BASE + 9756) with (BASE + AF_reac_box_name + RBN_L1)
        by (unfold AF_reac_box_name, RBN_L1; lia).
      eapply (IH STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
        (P + 1) D (n0 + 1) ov0).
      - exact HJ.
      - exact Hrne.
      - inversion Hall; assumption.
      - apply (rl1_src_tail W (ms_mem ms1) P c (r ++ [0])). exact Hsrc3.
      - exact Hbuf3.
      - lia.
      - lia.
      - lia.
      - rewrite RG24. rl1_regval.
      - rewrite RG30. rl1_regval.
      - rewrite RG15. subst c1. destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl)|].
        cbn [hd app]. rl1_regval.
      - rewrite RG13. rl1_regval.
      - rewrite RG10. rl1_regval.
      - rewrite RG14. rl1_regval.
      - rewrite RG27. rl1_regval.
      - rewrite RG22. rl1_regval. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HJ2|].
    split.
    { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
      destruct (rl1_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R14v, H14. reflexivity. }
    split; [exact Houts2|].
    split.
    assert (HlenW : length (c :: firstn (Z.to_nat (23 - (n0 + 1))) r)
      = Datatypes.S (length (firstn (Z.to_nat (23 - (n0 + 1))) r))) by reflexivity.
    { intros a Ha Hout. rewrite HlenW, Nat2Z.inj_succ in Hout.
      assert (Hout2 : ~ (D + (n0 + 1) <= a < D + (n0 + 1)
        + Z.of_nat (length (firstn (Z.to_nat (23 - (n0 + 1))) r)))) by lia.
      rewrite (Hfr2 a Ha Hout2). apply KEEP3; [exact Ha | lia]. }
    apply rl1_garr8_cons.
    { apply (rl1_vm_kept SEGS (w_H W) (w_H W) (ms_mem ms1) mem2 (D + n0) 1 c);
        [|exact Vc3].
      intros x Hx.
      assert (Hout3 : ~ (D + (n0 + 1) <= x < D + (n0 + 1)
        + Z.of_nat (length (firstn (Z.to_nat (23 - (n0 + 1))) r)))) by lia.
      apply (Hfr2 x ltac:(lia) Hout3). }
    { lia. }
    { replace (D + n0 + 1) with (D + (n0 + 1)) by lia. exact Hga2. }
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    change (zcanon 0) with 0 in Hc0.
    assert (Hc1 : c1 = 0)
      by (apply negb_false_iff, Z.eqb_eq in Hc0; exact Hc0).
    assert (Hr0 : r = []).
    { destruct r as [|c2 r2]; [reflexivity|]. exfalso.
      assert (Hc2 : 0 < c2 < 256) by (inversion Hall as [|? ? Hx Hy]; inversion Hy; assumption).
      subst c1. cbn [hd app] in Hc1. lia. }
    subst r.
    paj_run_to_tok RUNTO HS HJ SHOK rl1_span (AF_reac_box_name + RBN_L1X).
    { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32 (D + n0));
        [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia
        | | apply awr_ok_nil].
      cbn [YP09.r_wlo YP09.r_whi]. intros aq Haq. replace aq with (D + n0) by lia.
      exact (proj1 (HWb (D + n0) ltac:(lia))). }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP2 a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E13, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 c).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 15 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E15 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rl1_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (14%bv : bv 5) RG14.
    assert (R14v : getr (ms_regs ms1) 14 = w64 23) by (rewrite RG14; rl1_regval).
    pmkst HS.
    assert (HNat : Z.to_nat (23 - n0) = Datatypes.S (Z.to_nat (23 - (n0 + 1)))).
    { replace (23 - n0) with (1 + (23 - (n0 + 1))) by lia.
      rewrite Z2Nat.inj_add by lia. reflexivity. }
    rewrite HNat. cbn [firstn]. rewrite firstn_nil.
    assert (Hcond : (23 <? n0 + Z.of_nat (length [c])) = false)
      by (try cbn [length]; apply Z.ltb_ge; lia).
    rewrite Hcond.
    replace (Z.min 23 (n0 + Z.of_nat (length [c]))) with (n0 + 1) by (try cbn [length]; lia).
    apply SRr_ret. split; [reflexivity|].
    exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdc) mat1 mdc).
    split.
    { unfold rbn_cfg, cfg_at, w64.
      replace (BASE + AF_reac_box_name + RBN_L1X) with (BASE + 9864)
        by (unfold AF_reac_box_name, RBN_L1X; lia).
      reflexivity. }
    split; [exact HJ|].
    split.
    { intros rr Hrr Hnn.
      destruct (rl1_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R14v, H14. reflexivity. }
    split.
    { apply Forall_cons.
      { cbn [fst snd].
        replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG24. rl1_regval. }
      apply Forall_cons; [|apply Forall_nil].
      cbn [fst snd].
      replace (Z_to_bv 5 30) with (30%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite RG30. rl1_regval. }
    split.
    { intros a Ha Hout. apply KEEP3; [exact Ha | try cbn [length] in Hout; lia]. }
    apply rl1_garr8_cons; [exact Vc3 | lia | apply garr8_nil].
Qed.
Theorem rbn_l1_fits : rbn_L1_fits B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hle.
pose proof (rl1_gen s STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with (n0 + Z.of_nat (length s)) in Hg by lia.
replace (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0) with ov0 in Hg
  by (destruct (Z.ltb_spec 23 (n0 + Z.of_nat (length s))); [lia | reflexivity]).
replace (firstn (Z.to_nat (23 - n0)) s) with s in Hg by (symmetry; apply firstn_all2; lia).
exact Hg.
Qed.
Theorem rbn_l1_ovf : rbn_L1_ovf B.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlt.
pose proof (rl1_gen s STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with 23 in Hg by lia.
replace (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0) with 1 in Hg
  by (destruct (Z.ltb_spec 23 (n0 + Z.of_nat (length s))); [reflexivity | lia]).
exact Hg.
Qed.
End h.
End f.
End d.
