(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths, module names and numbers changed; 361 of its 413 lines of code are new or changed and 1226 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/ReacBoxNameSeg1.v; 1894 of its 1951 lines of code are new or changed and 356 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxNameLoops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition rbnl_B : sv := SOff 22 0.
Definition rbnl_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rbnl_SH : list shent := [mkSHE 32 1 0].
Definition rbn2_ss : sstate :=
  mkSS (AF_reac_box_name + RBN_L2) (sr_set sr_atoms 12%bv (SLit 23))
    [ YP09.mkRegion (Some 21%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
      YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ] None
    (mkFacts [ (22%nat, mkAF SB SB 0); (24%nat, mkAF 0 23 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0);
               (10%nat, mkAF 1 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0) ] []
      [(SAlu ALU_ADD (SOff 27 0) (SOff 24 0), SOff 32 0)]).
Definition rbnl_E (regs : bvmap 5 word) (dn c b : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [dn; c; b])).
Lemma rbnl_VB : forall E m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v.
Proof. intros E m v Hm Hv. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hv. Qed.
Lemma rbnl_ew : forall regs dn c b,
  ew (rbnl_E regs dn c b) 32 = Z_to_bv 64 dn /\ ew (rbnl_E regs dn c b) 33 = Z_to_bv 64 c /\
  ew (rbnl_E regs dn c b) 34 = Z_to_bv 64 b /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (rbnl_E regs dn c b) k = getr regs r).
Proof.
intros regs dn c b. unfold rbnl_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma rbnl_shok : forall E (m : word -> option byte) q,
  ew E 22 = Z_to_bv 64 SB -> ew E 32 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  (q + 1 <= kLowShadowBeg \/ kHighMemBeg <= q) ->
  sh_ok SEGS rbnl_B rbnl_SH E m.
Proof.
intros E m q H22 H32 Hq Ha. constructor; [|constructor].
eapply shent_app_of_app.
- unfold rbnl_B. rewrite (U_atom E 22 SB H22) by (unfold SB; lia). reflexivity.
- exact (U_atom E 32 q H32 Hq).
- lia.
- lia.
Qed.
Definition RBN_L3C : Z := 0x4fc.
Definition rbn3_ss : sstate :=
  mkSS (AF_reac_box_name + RBN_L3)
    (sr_set (sr_set sr_atoms 14%bv (SLit 45)) 15%bv (SLit 23))
    [ YP09.mkRegion (Some 16%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
      YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ] None
    (mkFacts [ (22%nat, mkAF SB SB 0); (26%nat, mkAF 0 23 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0);
               (10%nat, mkAF 0 (2 ^ 47 - 1) 0); (33%nat, mkAF 0 255 0) ] []
      [(SAlu ALU_ADD (SOff 29 0) (SOff 26 0), SOff 32 0)]).
Definition rbn3_ssc : sstate :=
  mkSS (AF_reac_box_name + RBN_L3C)
    (sr_set sr_atoms 15%bv (SLit 23))
    [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ] None
    (mkFacts [ (22%nat, mkAF SB SB 0); (26%nat, mkAF 0 23 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0);
               (5%nat, mkAF 0 255 0) ] []
      [(SAlu ALU_ADD (SOff 29 0) (SOff 26 0), SOff 32 0)]).
Definition rbn_lc (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Lemma rbnl_lower : forall E n c, ew E n = Z_to_bv 64 c -> 0 <= c < 256 ->
  U E (SAlu ALU_ADD (SOff n 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff n (-65)) (SLit 26)) (SLit 5)))
  = rbn_lc c.
Proof.
intros E n c Hn Hc.
assert (H0 : U E (SOff n 0) = c) by (apply (U_atom E n c Hn); lia).
assert (Hm : U E (SOff n (-65)) = (c - 65) mod M64)
  by (rewrite U_SOff, Hn, unsigned_lit_small by lia; reflexivity).
rewrite U_SAlu, H0. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hm, !U_SLit.
change (zcanon 26) with 26. change (zcanon 5) with 5. change (Z.land 5 63) with 5.
unfold rbn_lc.
destruct (Z.leb_spec 65 c) as [H1|H1]; destruct (Z.leb_spec c 90) as [H2|H2]; cbn [andb].
- rewrite (Z.mod_small (c - 65)) by (unfold M64; lia).
  replace (c - 65 <? 26) with true by (symmetry; apply Z.ltb_lt; lia).
  change (zcanon 1) with 1. change (Z.shiftl 1 5) with 32.
  change (zcanon 32) with 32. apply zcanon_id. unfold M64. lia.
- rewrite (Z.mod_small (c - 65)) by (unfold M64; lia).
  replace (c - 65 <? 26) with false by (symmetry; apply Z.ltb_ge; lia).
  change (zcanon 0) with 0. change (Z.shiftl 0 5) with 0.
  change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
- replace ((c - 65) mod M64) with (c - 65 + M64)
    by (rewrite <- (Z_mod_plus_full (c - 65) 1 M64); rewrite Z.mod_small; unfold M64; lia).
  replace (c - 65 + M64 <? 26) with false by (symmetry; apply Z.ltb_ge; unfold M64; lia).
  change (zcanon 0) with 0. change (Z.shiftl 0 5) with 0.
  change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
Qed.
Lemma rbn_lc_range : forall c, 0 <= c < 256 -> 0 <= rbn_lc c < 256.
Proof.
intros c Hc. unfold rbn_lc.
destruct (Z.leb_spec 65 c); destruct (Z.leb_spec c 90); cbn [andb]; lia.
Qed.
Lemma bn_tk_cons : forall sn c l,
  bn_tk sn (c :: l) = if (c =? 45) && negb sn then bn_tk true l else rbn_lc c :: bn_tk sn l.
Proof.
intros sn c l. cbn [bn_tk]. unfold rbn_lc.
destruct ((c =? 45) && negb sn); reflexivity.
Qed.
Lemma rbnl_ext : forall E K ws n, (n < K)%nat -> ew (extK E K ws) n = ew E n.
Proof.
intros E K ws. revert E K. induction ws as [|w ws IH]; intros E K n Hn; cbn [extK]; [reflexivity|].
rewrite (IH (ewset E K w) (S K) n ltac:(lia)). apply ew_ewset_other. lia.
Qed.
Lemma rbnl_app_not_shadow : forall x a, in_app x 1 -> 0 <= a -> a < 2 ^ 47 -> x <> SHADOW_OFF + a / 8.
Proof.
intros x a Hx H0 Ha Heq.
assert (Hd : 0 <= a / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbnl_src_keep : forall (W : world SEGS) (mem mem' : word -> option byte) P l X,
  rbn_lsrc W mem P l ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> X -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  in_app X 1 -> ~ (P <= X < P + Z.of_nat (length l)) ->
  rbn_lsrc W mem' P l.
Proof.
intros W mem mem' P l X (HG & HP0 & HP63 & HP47 & HRA) HK Hx Hnin.
split; [|split; [exact HP0 | split; [exact HP63 | split; [exact HP47|]]]].
- apply (garr8_aview_kept SEGS (w_H W) (w_H W) mem mem' P l); [|exact HG].
  intros a Ha. apply HK; [lia | lia].
- intros y Hy. unfold shadow_of_addr.
  rewrite (HK (SHADOW_OFF + y / 8)).
  + apply HRA. lia.
  + assert (Hd : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    unfold SHADOW_OFF. lia.
  + intros Heq. apply (rbnl_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
Qed.
Lemma rbnl_buf_keep : forall B STK sp0 FP ly S own lyc Sc (W : world SEGS) (mem mem' : word -> option byte) D n X,
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
  + intros Heq. apply (rbnl_app_not_shadow X y Hx ltac:(lia) ltac:(lia)). symmetry. exact Heq.
- intros a Ha. split; [exact (proj1 (HW a Ha))|].
  apply (apresent_grows _ _ _ _ HGr). exact (proj2 (HW a Ha)).
Qed.
Lemma rbnl_keep_of_bv : forall (regs regs2 : bvmap 5 word) (cl : list Z) (l : list (bv 5)),
  (forall rr : bv 5, In rr l -> getr regs2 rr = getr regs rr) ->
  (forall r : Z, 0 <= r < 32 -> ~ In r cl -> r = 0 \/ In (Z_to_bv 5 r) l) ->
  rbn_keep_regs regs regs2 cl.
Proof.
intros regs regs2 cl l HK Hc r Hr Hn. destruct (Hc r Hr Hn) as [-> | Hin]; [reflexivity|].
apply HK. exact Hin.
Qed.
Lemma rbnl_byte_at : forall (W : world SEGS) (mem : word -> option byte) a,
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


Lemma rbn2_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc Q D n c b,
  getr regs 12 = w64 23 -> getr regs 22 = w64 SHADOW_OFF -> getr regs 24 = w64 n -> getr regs 27 = w64 D ->
  getr regs 21 = w64 Q -> getr regs 10 = w64 Q ->
  0 <= n <= 23 -> 1 <= Q <= 2 ^ 47 - 1 -> 4096 <= D -> D + n <= 2 ^ 47 - 1 ->
  val_mem SEGS (mrestrict (w_H W) memc) Q 1 c -> 0 <= c < 256 ->
  val_mem SEGS (mrestrict (w_H W) memc) (D + n) 1 b -> 0 <= b < 256 ->
  apresent (w_H W) memc (D + n) ->
  (Q + 1 <= D + n \/ D + n + 1 <= Q) ->
  st_ok_pi SEGS VAL (rbnl_E regs (D + n) c b) rbn2_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L2))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc Q D n c b H12 H22 H24 H27 H21 H10 Hn HQ HD HDn Vc Rc Vb Rb Hp Hdj.
rewrite restrict_mkst_fx.
destruct (rbnl_ew regs (D + n) c b) as (E32 & E33 & E34 & EE).
assert (HR : regs_ok (rbnl_E regs (D + n) c b) (sr_set sr_atoms 12%bv (SLit 23)) regs)
  by (apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H12]).
remember (rbnl_E regs (D + n) c b) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew E 24 = Z_to_bv 64 n) by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E27 : ew E 27 = Z_to_bv 64 D) by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (E21 : ew E 21 = Z_to_bv 64 Q) by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E10 : ew E 10 = Z_to_bv 64 Q) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
unfold rbn2_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E21, unsigned_lit_small by lia.
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
  rewrite E21, E32, !unsigned_lit_small by lia.
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
Lemma rbnl_src_tail : forall (W : world SEGS) (mem : word -> option byte) P c l,
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
Ltac rbnl_u_atom H n v :=
  lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
    assert (H : U Ev (SOff n 0) = v) by
      (apply (U_atom Ev n v); [rewrite ?ew_ewset_other by lia; assumption | lia]) end.
Ltac rbnl_awrD HWbq E32q Dq nq :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]);
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32 (Dq + nq));
    [reflexivity | rewrite ?ew_ewset_other by lia; rewrite E32q; apply unsigned_lit_small; lia
    | | apply awr_ok_nil];
  cbn [YP09.r_wlo YP09.r_whi];
  let aq := fresh "aq" in let Haq := fresh "Haq" in
  intros aq Haq; replace aq with (Dq + nq) by lia; exact (proj1 (HWbq (Dq + nq) ltac:(lia))).
Ltac rbnl_u_off H n v off :=
  lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
    assert (H : U Ev (SOff n off) = v + off) by
      (apply (U_atom_off Ev n v off); [rewrite ?ew_ewset_other by lia; assumption | lia | lia]) end.
Ltac rbnl_regval :=
  cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
  repeat match goal with Hq : ew ?Ex ?nq = Z_to_bv 64 _ |- context [ew ?Ex ?nq] => rewrite Hq end;
  rewrite ?unsigned_lit_small by lia; unfold w64;
  first [ reflexivity | (f_equal; lia) | (apply bv_eq; vm_compute; reflexivity) ].
Lemma rbn3_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc Q D n c b,
  getr regs 14 = w64 45 -> getr regs 15 = w64 23 -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 26 = w64 n -> getr regs 29 = w64 D -> getr regs 16 = w64 Q -> getr regs 10 = w64 Q ->
  0 <= n <= 23 -> 0 <= Q <= 2 ^ 47 - 1 -> 4096 <= D -> D + n <= 2 ^ 47 - 1 ->
  val_mem SEGS (mrestrict (w_H W) memc) Q 1 c -> 0 <= c < 256 ->
  val_mem SEGS (mrestrict (w_H W) memc) (D + n) 1 b -> 0 <= b < 256 ->
  apresent (w_H W) memc (D + n) ->
  (Q + 1 <= D + n \/ D + n + 1 <= Q) ->
  st_ok_pi SEGS VAL (rbnl_E regs (D + n) c b) rbn3_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L3))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc Q D n c b H14 H15 H22 H26 H29 H16 H10 Hn HQ HD HDn Vc Rc Vb Rb Hp Hdj.
rewrite restrict_mkst_fx.
destruct (rbnl_ew regs (D + n) c b) as (E32 & E33 & E34 & EE).
assert (HR : regs_ok (rbnl_E regs (D + n) c b) (sr_set (sr_set sr_atoms 14%bv (SLit 45)) 15%bv (SLit 23)) regs).
{ apply regs_ok_pin; [|discriminate | cbn [sv_denot]; exact H15].
  apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H14]. }
remember (rbnl_E regs (D + n) c b) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 n) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E29 : ew E 29 = Z_to_bv 64 D) by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
assert (E16 : ew E 16 = Z_to_bv 64 Q) by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E10 : ew E 10 = Z_to_bv 64 Q) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
unfold rbn3_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E16, unsigned_lit_small by lia.
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
  rewrite E16, E32, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E26, E32, E10, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 29 D E29), (U_atom E 26 n E26), (U_atom E 32 (D + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Lemma rbn3c_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word) memc D n c b,
  getr regs 15 = w64 23 -> getr regs 22 = w64 SHADOW_OFF -> getr regs 26 = w64 n -> getr regs 29 = w64 D ->
  getr regs 5 = w64 c ->
  0 <= n <= 23 -> 4096 <= D -> D + n <= 2 ^ 47 - 1 -> 0 <= c < 256 ->
  val_mem SEGS (mrestrict (w_H W) memc) (D + n) 1 b -> 0 <= b < 256 ->
  apresent (w_H W) memc (D + n) ->
  st_ok_pi SEGS VAL (rbnl_E regs (D + n) c b) rbn3_ssc
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_reac_box_name + RBN_L3C))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc D n c b H15 H22 H26 H29 H5 Hn HD HDn Rc Vb Rb Hp.
rewrite restrict_mkst_fx.
destruct (rbnl_ew regs (D + n) c b) as (E32 & E33 & E34 & EE).
assert (HR : regs_ok (rbnl_E regs (D + n) c b) (sr_set sr_atoms 15%bv (SLit 23)) regs)
  by (apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate | cbn [sv_denot]; exact H15]).
remember (rbnl_E regs (D + n) c b) as E eqn:HE. clear HE.
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E26 : ew E 26 = Z_to_bv 64 n) by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E29 : ew E 29 = Z_to_bv 64 D) by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
assert (E5 : ew E 5 = Z_to_bv 64 c) by (rewrite (EE 5%nat 5%bv eq_refl); exact H5).
unfold rbn3_ssc. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable SEGS); replace (D + n + o) with (D + n) by lia; exact Hp|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (D + n) 0 1 (SOff 34 0) b);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Vb.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22, E26, E32, E5, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 29 D E29), (U_atom E 26 n E26), (U_atom E 32 (D + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Definition rbn2_cl : list Z := [10; 11; 13; 14; 15; 16; 21; 24; 30].
Definition rbn2_keptl : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 20; 22; 23; 25; 26; 27; 28; 29; 31]%bv.
Lemma rbn2_kept_cover : forall r : Z, 0 <= r < 32 -> ~ In r rbn2_cl ->
  r = 0 \/ r = 12 \/ In (Z_to_bv 5 r) rbn2_keptl.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [right; left; reflexivity]
        | solve [exfalso; apply Hn; unfold rbn2_cl; cbn [In];
                 repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; right; unfold rbn2_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Lemma rbn2_gen : forall (s : list Z) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) P D n0 ov0,
  rbn_L2_run B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s
    (Z.min 23 (n0 + Z.of_nat (length s)))
    (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0)
    (firstn (Z.to_nat (23 - n0)) s).
Proof.
induction s as [|c r IH]; intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0;
  unfold rbn_L2_run; intros HJ Hne Hall Hsrc Hbuf Hdj Hn0 Hov0 H24 H30 H13 H21 H10 H12 H27 H22;
  [exfalso; exact (Hne eq_refl)|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof Hsrc as (HGs & HP0 & HP63 & HP47 & HRAs).
pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
pose proof HDapp as (HDlo & HDhi).
cbn [hd] in H13.
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
destruct (rbnl_byte_at W memc (D + n0) (proj2 (HWb (D + n0) ltac:(lia)))) as (bb & Vb & Rb).
destruct (rbnl_ew regs (D + n0) c1 bb) as (E32 & E33 & E34 & EE).
assert (E22 : ew (rbnl_E regs (D + n0) c1 bb) 22 = Z_to_bv 64 SB)
  by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E24 : ew (rbnl_E regs (D + n0) c1 bb) 24 = Z_to_bv 64 n0)
  by (rewrite (EE 24%nat 24%bv eq_refl); exact H24).
assert (E13 : ew (rbnl_E regs (D + n0) c1 bb) 13 = Z_to_bv 64 c)
  by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E30 : ew (rbnl_E regs (D + n0) c1 bb) 30 = Z_to_bv 64 ov0)
  by (rewrite (EE 30%nat 30%bv eq_refl); exact H30).
assert (E10 : ew (rbnl_E regs (D + n0) c1 bb) 10 = Z_to_bv 64 (P + 1))
  by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E21 : ew (rbnl_E regs (D + n0) c1 bb) 21 = Z_to_bv 64 (P + 1))
  by (rewrite (EE 21%nat 21%bv eq_refl); exact H21).
assert (E27 : ew (rbnl_E regs (D + n0) c1 bb) 27 = Z_to_bv 64 D)
  by (rewrite (EE 27%nat 27%bv eq_refl); exact H27).
assert (Hlencr : Z.of_nat (length (c :: r)) = Z.of_nat (length r) + 1) by (try cbn [length]; lia).
assert (Hdj2 : P + 1 + 1 <= D + n0 \/ D + n0 + 1 <= P + 1) by lia.
assert (HD4 : 4096 <= D) by lia.
assert (Hpres0 : apresent (w_H W) memc (D + n0)) by (exact (proj2 (HWb (D + n0) ltac:(lia)))).
pose proof (rbn2_entry fq W regs memc (P + 1) D n0 c1 bb H12 H22 H24 H27 H21 H10 Hn0 HQ
  HD4 HDn Vc1 Rc1 Vb Rb Hpres0 Hdj2) as HS.
set (E := rbnl_E regs (D + n0) c1 bb) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rbnl_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [D + n0; c1; bb])) E)
  by (unfold E, rbnl_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS rbnl_B rbnl_SH E (mrestrict (w_H W) memc))
  by (apply (rbnl_shok E _ (D + n0)); [exact E22 | exact E32 | lia
      | unfold kLowShadowBeg, kHighMemBeg in HDhi |- *; lia]).
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ SHOK rbnl_span.
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
{ apply (kept_of_frame E (ss_mem rbn2_ss) (w_H W) memc (ms_mem ms) (fun a => a = D + n0) HFr).
  intros bq wlo whi a Hin Ha.
  cbn [ss_mem rbn2_ss windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
    cbn [base_val] in Ha; rewrite ?E21, ?E32, ?unsigned_lit_small in Ha by lia; lia. }
assert (Hsrc1 : rbn_lsrc W (ms_mem ms) P ((c :: r) ++ [0]))
  by (apply (rbnl_src_keep W memc (ms_mem ms) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP1 Happ1); lia).
assert (Hbuf1 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms) D 24)
  by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms) D 24 (D + n0) Hbuf KEEP1 HG Happ1); lia).
assert (HUB : U E rbnl_B = SHADOW_OFF)
  by (unfold rbnl_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (HU10 : U E (SOff 10 0) = P + 1) by (apply (U_atom E 10 (P + 1) E10); lia).
assert (HU32 : U E (SOff 32 0) = D + n0) by (apply (U_atom E 32 (D + n0) E32); lia).
assert (HU24 : U E (SOff 24 1) = n0 + 1) by (apply (U_atom_off E 24 n0 1 E24); lia).
assert (HU23 : U E (SLit 23) = 23) by (rewrite U_SLit; reflexivity).
psrr_branch_tok RUN BR HS SHOK rbnl_span.
- rewrite branch_ltu_U, HU23, HU24 in Hc. apply Z.ltb_lt in Hc.
  assert (Hn23 : n0 = 23) by lia.
  paj_run_tok RUN HS HJ SHOK rbnl_span.
  { rewrite HU10.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rbnl_B (P + 1) 1 P (Z.of_nat (length ((c :: r) ++ [0]))));
      [exact (proj2 (proj2 (proj2 (proj2 Hsrc1)))) | exact HUB | lia | lia]. }
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
      [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
    exact (proj1 (HWb (D + n0) ltac:(lia))). }
  rbnl_u_atom HU33 33%nat c1.
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
      rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  psrr_branch_tok RUN BR HS SHOK rbnl_span.
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    assert (Hc1 : c1 <> 0)
      by (intros Hz; rewrite Hz in Hc0; cbn in Hc0; discriminate Hc0).
    assert (Hrne : r <> []) by (intros Hz; apply Hc1; subst c1; rewrite Hz; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L2).
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
        rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
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
      by (apply (rbnl_src_keep W memc (ms_mem ms1) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP3 Happ1); lia).
    assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
      by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
            Hbuf KEEP3 GROW3 Happ1); lia).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn2_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (13%bv : bv 5) RG13.
    prreg HS (21%bv : bv 5) RG21. prreg HS (10%bv : bv 5) RG10. prreg HS (12%bv : bv 5) RG12.
    prreg HS (27%bv : bv 5) RG27. prreg HS (22%bv : bv 5) RG22.
    assert (R12v : getr (ms_regs ms1) 12 = w64 23) by (rewrite RG12; rbnl_regval).
    pmkst HS.
    replace (Z.min 23 (n0 + Z.of_nat (length (c :: r)))) with 23 by (try cbn [length]; lia).
    assert (Hcond : (23 <? n0 + Z.of_nat (length (c :: r))) = true)
      by (try cbn [length]; apply Z.ltb_lt; lia).
    rewrite Hcond.
    replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
    eapply SRr_mono.
    { replace (BASE + 15048) with (BASE + AF_reac_box_name + RBN_L2)
        by (unfold AF_reac_box_name, RBN_L2; lia).
      eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
        (P + 1) D n0 1).
      - exact HJ.
      - exact Hrne.
      - inversion Hall; assumption.
      - apply (rbnl_src_tail W (ms_mem ms1) P c (r ++ [0])). exact Hsrc3.
      - exact Hbuf3.
      - lia.
      - lia.
      - lia.
      - rewrite RG24. rbnl_regval.
      - rewrite RG30. rbnl_regval.
      - rewrite RG13. subst c1. destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl)|].
        cbn [hd app]. rbnl_regval.
      - rewrite RG21. rbnl_regval.
      - rewrite RG10. rbnl_regval.
      - rewrite RG12. rbnl_regval.
      - rewrite RG27. rbnl_regval.
      - rewrite RG22. rbnl_regval. }
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
      destruct (rbn2_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R12v, H12. reflexivity. }
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
    paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L2X).
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
        rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
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
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn2_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (12%bv : bv 5) RG12.
    assert (R12v : getr (ms_regs ms1) 12 = w64 23) by (rewrite RG12; rbnl_regval).
    pmkst HS.
    replace (Z.min 23 (n0 + Z.of_nat (length [c]))) with 23 by (try cbn [length]; lia).
    assert (Hcond : (23 <? n0 + Z.of_nat (length [c])) = true)
      by (try cbn [length]; apply Z.ltb_lt; lia).
    rewrite Hcond.
    replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
    apply SRr_ret. split; [reflexivity|].
    exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdc) mat1 mdc).
    split.
    { unfold cfg_at, w64.
      replace (BASE + AF_reac_box_name + RBN_L2X) with (BASE + 15156)
        by (unfold AF_reac_box_name, RBN_L2X; lia).
      reflexivity. }
    split; [exact HJ|].
    split.
    { intros rr Hrr Hnn.
      destruct (rbn2_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R12v, H12. reflexivity. }
    split.
    { apply Forall_cons.
      { cbn [fst snd].
        replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG24. rbnl_regval. }
      apply Forall_cons; [|apply Forall_nil].
      cbn [fst snd].
      replace (Z_to_bv 5 30) with (30%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite RG30. rbnl_regval. }
    split.
    { intros a Ha Hout. apply KEEPB. exact Ha. }
    apply garr8_nil.
- rewrite branch_ltu_U, HU23, HU24 in Hc. apply Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK rbnl_span.
  { rewrite HU10.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rbnl_B (P + 1) 1 P (Z.of_nat (length ((c :: r) ++ [0]))));
      [exact (proj2 (proj2 (proj2 (proj2 Hsrc1)))) | exact HUB | lia | lia]. }
  { rewrite HU32.
    apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rbnl_B (D + n0) 1 D 24);
      [exact (proj1 (proj2 (proj2 (proj2 Hbuf1)))) | exact HUB | lia | lia]. }
  { lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
      [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
    exact (proj1 (HWb (D + n0) ltac:(lia))). }
  rbnl_u_atom HU33 33%nat c1.
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
      rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  assert (Vc2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + n0) 1 c).
  { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
      pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 13 0)
        (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
        ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
        ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
    cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
    rewrite ?ew_ewset_other in Vq by lia. rewrite E13 in Vq. rewrite !Z.add_0_r in Vq.
    rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
    change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
    change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
  psrr_branch_tok RUN BR HS SHOK rbnl_span.
  + rewrite branch_ne_U, HU33, U_SLit in Hc0.
    assert (Hc1 : c1 <> 0)
      by (intros Hz; rewrite Hz in Hc0; cbn in Hc0; discriminate Hc0).
    assert (Hrne : r <> []) by (intros Hz; apply Hc1; subst c1; rewrite Hz; reflexivity).
    paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L2).
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
        rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG | exact HG0] | exact HG1]).
    assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 c).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 13 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E13 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    assert (Hsrc3 : rbn_lsrc W (ms_mem ms1) P ((c :: r) ++ [0]))
      by (apply (rbnl_src_keep W memc (ms_mem ms1) P ((c :: r) ++ [0]) (D + n0) Hsrc KEEP3 Happ1); lia).
    assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
      by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
            Hbuf KEEP3 GROW3 Happ1); lia).
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn2_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (13%bv : bv 5) RG13.
    prreg HS (21%bv : bv 5) RG21. prreg HS (10%bv : bv 5) RG10. prreg HS (12%bv : bv 5) RG12.
    prreg HS (27%bv : bv 5) RG27. prreg HS (22%bv : bv 5) RG22.
    assert (R12v : getr (ms_regs ms1) 12 = w64 23) by (rewrite RG12; rbnl_regval).
    pmkst HS.
    cbn [length]. rewrite Nat2Z.inj_succ.
    replace (n0 + Z.succ (Z.of_nat (length r))) with (n0 + 1 + Z.of_nat (length r)) by lia.
    assert (HNat : Z.to_nat (23 - n0) = Datatypes.S (Z.to_nat (23 - (n0 + 1)))).
    { replace (23 - n0) with (1 + (23 - (n0 + 1))) by lia.
      rewrite Z2Nat.inj_add by lia. reflexivity. }
    rewrite HNat.
    cbn [firstn].
    eapply SRr_mono.
    { replace (BASE + 15048) with (BASE + AF_reac_box_name + RBN_L2)
        by (unfold AF_reac_box_name, RBN_L2; lia).
      eapply (IH fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
        (P + 1) D (n0 + 1) ov0).
      - exact HJ.
      - exact Hrne.
      - inversion Hall; assumption.
      - apply (rbnl_src_tail W (ms_mem ms1) P c (r ++ [0])). exact Hsrc3.
      - exact Hbuf3.
      - lia.
      - lia.
      - lia.
      - rewrite RG24. rbnl_regval.
      - rewrite RG30. rbnl_regval.
      - rewrite RG13. subst c1. destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl)|].
        cbn [hd app]. rbnl_regval.
      - rewrite RG21. rbnl_regval.
      - rewrite RG10. rbnl_regval.
      - rewrite RG12. rbnl_regval.
      - rewrite RG27. rbnl_regval.
      - rewrite RG22. rbnl_regval. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HJ2|].
    split.
    { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
      destruct (rbn2_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R12v, H12. reflexivity. }
    split; [exact Houts2|].
    split.
    assert (HlenW : length (c :: firstn (Z.to_nat (23 - (n0 + 1))) r)
      = Datatypes.S (length (firstn (Z.to_nat (23 - (n0 + 1))) r))) by reflexivity.
    { intros a Ha Hout. rewrite HlenW, Nat2Z.inj_succ in Hout.
      assert (Hout2 : ~ (D + (n0 + 1) <= a < D + (n0 + 1)
        + Z.of_nat (length (firstn (Z.to_nat (23 - (n0 + 1))) r)))) by lia.
      rewrite (Hfr2 a Ha Hout2). apply KEEP3; [exact Ha | lia]. }
    apply garr8_cons_x.
    { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms1) mem2 (D + n0) 1 c);
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
    paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L2X).
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
        rewrite ?E21, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 c).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 13 0)
          (st_ok_pi_region_nth Ev _ _ 1 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E13 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn2_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (24%bv : bv 5) RG24. prreg HS (30%bv : bv 5) RG30. prreg HS (12%bv : bv 5) RG12.
    assert (R12v : getr (ms_regs ms1) 12 = w64 23) by (rewrite RG12; rbnl_regval).
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
    { unfold cfg_at, w64.
      replace (BASE + AF_reac_box_name + RBN_L2X) with (BASE + 15156)
        by (unfold AF_reac_box_name, RBN_L2X; lia).
      reflexivity. }
    split; [exact HJ|].
    split.
    { intros rr Hrr Hnn.
      destruct (rbn2_kept_cover rr Hrr Hnn) as [-> | [-> | Hin]]; [| |exact (HKr1 _ Hin)].
      - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite !getr_zero. reflexivity.
      - replace (Z_to_bv 5 12) with (12%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite R12v, H12. reflexivity. }
    split.
    { apply Forall_cons.
      { cbn [fst snd].
        replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG24. rbnl_regval. }
      apply Forall_cons; [|apply Forall_nil].
      cbn [fst snd].
      replace (Z_to_bv 5 30) with (30%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
      rewrite RG30. rbnl_regval. }
    split.
    { intros a Ha Hout. apply KEEP3; [exact Ha | try cbn [length] in Hout; lia]. }
    apply garr8_cons_x; [exact Vc3 | lia | apply garr8_nil].
Qed.
Definition rbn3_cl : list Z := [5; 6; 7; 10; 11; 12; 13; 16; 17; 26; 28].
Definition rbn3_keptl : list (bv 5) :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 29; 30; 31]%bv.
Lemma rbn3_kept_cover : forall r : Z, 0 <= r < 32 -> ~ In r rbn3_cl ->
  r = 0 \/ r = 14 \/ r = 15 \/ In (Z_to_bv 5 r) rbn3_keptl.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [right; left; reflexivity]
        | solve [right; right; left; reflexivity]
        | solve [exfalso; apply Hn; unfold rbn3_cl; cbn [In];
                 repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; right; right; unfold rbn3_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Lemma rbn3_gen : forall (l : list Z) (sn : bool) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) memc mdc k (regs : bvmap 5 word) N D n0 ov0,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  (1 <= length l)%nat -> Forall (fun c => 0 <= c < 256) l -> rbn_lsrc W memc N l ->
  rbn_lbuf B STK sp0 FP ly S own lyc Sc W memc D 24 ->
  (N + Z.of_nat (length l) <= D \/ D + 24 <= N) ->
  0 <= n0 <= 23 -> (ov0 = 0 \/ ov0 = 1) ->
  getr regs 12 = w64 (if sn then 1 else 0) -> getr regs 26 = w64 n0 -> getr regs 13 = w64 ov0 ->
  getr regs 14 = w64 45 -> getr regs 15 = w64 23 -> getr regs 16 = w64 N -> getr regs 10 = w64 N ->
  getr regs 17 = w64 (Z.of_nat (length l)) -> getr regs 29 = w64 D -> getr regs 22 = w64 SHADOW_OFF ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_box_name + RBN_L3) regs memc mdc)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X rbn3_cl D n0
       (firstn (Z.to_nat (23 - n0)) (bn_tk sn l))
       [(26, Z.min 23 (n0 + Z.of_nat (length (bn_tk sn l))));
        (13, if 23 <? n0 + Z.of_nat (length (bn_tk sn l)) then 1 else ov0)]).
Proof.
induction l as [|c r IH]; intros sn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D n0 ov0
  HJ Hlen Hall Hsrc Hbuf Hdj Hn0 Hov0 H12 H26 H13 H14 H15 H16 H10 H17 H29 H22;
  [exfalso; cbn [length] in Hlen; lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR.
pose proof (@paj_run fq _ _ _ _ _ B LAWS) as RUN.
pose proof (@paj_run_to fq _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
pose proof Hsrc as (HGs & HN0 & HN63 & HN47 & HRAs).
pose proof Hbuf as (HD0 & HD63 & HDapp & HRAb & HWb).
pose proof HDapp as (HDlo & HDhi).
assert (HDn : D + n0 <= 2 ^ 47 - 1) by (unfold kLowShadowBeg, kHighMemBeg in HDhi; lia).
assert (HD4 : 4096 <= D) by lia.
assert (Hlencr : Z.of_nat (length (c :: r)) = Z.of_nat (length r) + 1) by (cbn [length]; lia).
assert (Hcr : 0 <= c < 256) by (inversion Hall; assumption).
assert (HNb : 0 <= N <= 2 ^ 47 - 1) by lia.
assert (Vc : val_mem SEGS (mrestrict (w_H W) memc) N 1 c).
{ destruct (garr8_nthZ SEGS (mrestrict (w_H W) memc) N (c :: r) 0 HGs ltac:(lia)
    ltac:(cbn [length]; lia)) as (Hv & _).
  rewrite Z.add_0_r in Hv. cbn [nth Z.to_nat] in Hv. exact Hv. }
assert (Hpres0 : apresent (w_H W) memc (D + n0)) by (exact (proj2 (HWb (D + n0) ltac:(lia)))).
destruct (rbnl_byte_at W memc (D + n0) Hpres0) as (bb & Vb & Rb).
assert (Hdj2 : N + 1 <= D + n0 \/ D + n0 + 1 <= N) by lia.
destruct (rbnl_ew regs (D + n0) c bb) as (E32 & E33 & E34 & EE).
assert (E22 : ew (rbnl_E regs (D + n0) c bb) 22 = Z_to_bv 64 SB)
  by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E26 : ew (rbnl_E regs (D + n0) c bb) 26 = Z_to_bv 64 n0)
  by (rewrite (EE 26%nat 26%bv eq_refl); exact H26).
assert (E29 : ew (rbnl_E regs (D + n0) c bb) 29 = Z_to_bv 64 D)
  by (rewrite (EE 29%nat 29%bv eq_refl); exact H29).
assert (E16 : ew (rbnl_E regs (D + n0) c bb) 16 = Z_to_bv 64 N)
  by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E10 : ew (rbnl_E regs (D + n0) c bb) 10 = Z_to_bv 64 N)
  by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew (rbnl_E regs (D + n0) c bb) 12 = Z_to_bv 64 (if sn then 1 else 0))
  by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew (rbnl_E regs (D + n0) c bb) 13 = Z_to_bv 64 ov0)
  by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E17 : ew (rbnl_E regs (D + n0) c bb) 17 = Z_to_bv 64 (Z.of_nat (length (c :: r))))
  by (rewrite (EE 17%nat 17%bv eq_refl); exact H17).
pose proof (rbn3_entry fq W regs memc N D n0 c bb H14 H15 H22 H26 H29 H16 H10 Hn0 HNb
  HD4 HDn Vc Hcr Vb Rb Hpres0 Hdj2) as HS.
set (E := rbnl_E regs (D + n0) c bb) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rbnl_E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (map (Z_to_bv 64) [D + n0; c; bb])) E)
  by (unfold E, rbnl_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (SHOK : sh_ok SEGS rbnl_B rbnl_SH E (mrestrict (w_H W) memc))
  by (apply (rbnl_shok E _ (D + n0)); [exact E22 | exact E32 | lia
      | unfold kLowShadowBeg, kHighMemBeg in HDhi |- *; lia]).
assert (Happ1 : in_app (D + n0) 1)
  by (apply (in_app_sub D 24); [exact HDapp | lia | lia | lia]).
assert (HUB : U E rbnl_B = SHADOW_OFF)
  by (unfold rbnl_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (HU10 : U E (SOff 10 0) = N) by (apply (U_atom E 10 N E10); lia).
assert (HU32 : U E (SOff 32 0) = D + n0) by (apply (U_atom E 32 (D + n0) E32); lia).
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_tok RUN HS HJ SHOK rbnl_span.
{ rewrite HU10.
  apply (obl_of_range SEGS (w_H W) memc E rbnl_B N 1 N (Z.of_nat (length (c :: r))));
    [exact HRAs | exact HUB | lia | cbn [length]; lia]. }
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32 (D + n0));
    [reflexivity | rewrite E32; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. replace a with (D + n0) by lia.
  exact (proj1 (HWb (D + n0) ltac:(lia))). }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ apply (kept_of_frame E (ss_mem rbn3_ss) (w_H W) memc (ms_mem ms) (fun a => a = D + n0) HFr).
  intros bq wlo whi a Hin Ha.
  cbn [ss_mem rbn3_ss windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-;
    cbn [base_val] in Ha; rewrite ?E16, ?E32, ?unsigned_lit_small in Ha by lia; lia. }
assert (Hsrc1 : rbn_lsrc W (ms_mem ms) N (c :: r))
  by (apply (rbnl_src_keep W memc (ms_mem ms) N (c :: r) (D + n0) Hsrc KEEP1 Happ1); cbn [length]; lia).
assert (Hbuf1 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms) D 24)
  by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms) D 24 (D + n0)
        Hbuf KEEP1 HG Happ1); lia).
assert (Vb1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (D + n0) 1 bb).
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
assert (COPY : forall (regsx : bvmap 5 word) memx mdx,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memx mdx k ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
     aview SEGS (w_H W) memx a = aview SEGS (w_H W) memc a) ->
  val_mem SEGS (mrestrict (w_H W) memx) (D + n0) 1 bb ->
  mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memx) ->
  (forall rr : bv 5, In rr rbn3_keptl -> getr regsx rr = getr regs rr) ->
  getr regsx 5 = w64 c -> getr regsx 14 = w64 45 -> getr regsx 15 = w64 23 ->
  getr regsx 22 = w64 SHADOW_OFF -> getr regsx 26 = w64 n0 -> getr regsx 29 = w64 D ->
  getr regsx 13 = w64 ov0 -> getr regsx 12 = w64 (if sn then 1 else 0) ->
  getr regsx 16 = w64 N -> getr regsx 10 = w64 N ->
  getr regsx 17 = w64 (Z.of_nat (length (c :: r))) ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + (AF_reac_box_name + RBN_L3C)) regsx memx mdx)
    (rbn_lpost B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs RBN_L3X rbn3_cl D n0
       (firstn (Z.to_nat (23 - n0)) (rbn_lc c :: bn_tk sn r))
       [(26, Z.min 23 (n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn r))));
        (13, if 23 <? n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn r)) then 1 else ov0)])).
{ clear HS SHOK KEEP1 Hsrc1 Hbuf1 Vb1 HJ.
  clear E10 E12 E13 E16 E17 E22 E26 E29 E32 E33 E34 EE HEI HAE HU10 HU32 HUB.
  clear - IH Hall Hsrc Hbuf Hdj Hn0 Hov0 Hcr Hlencr HD4 HDn HDlo HDhi HDapp HD0 HD63 HRAb HWb
    HGs HN0 HN63 HN47 HRAs Hpres0 Vb Rb Happ1 CR Hwx Hsegs RUN RUNTO BR H14 H15 Hlen.
  intros regsx memx mdx HJx KEEPx Vbx GROWx HKx H5x H14x H15x H22x H26x H29x H13x H12x H16x H10x H17x.
  assert (Hpresx : apresent (w_H W) memx (D + n0)) by (apply (apresent_grows _ _ _ _ GROWx); exact Hpres0).
  assert (Hbufx : rbn_lbuf B STK sp0 FP ly S own lyc Sc W memx D 24)
    by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc memx D 24 (D + n0)
          Hbuf KEEPx GROWx Happ1); lia).
  assert (Hsrcx : rbn_lsrc W memx N (c :: r))
    by (apply (rbnl_src_keep W memc memx N (c :: r) (D + n0) Hsrc KEEPx Happ1); cbn [length]; lia).
  pose proof (rbn3c_entry fq W regsx memx D n0 c bb H15x H22x H26x H29x H5x Hn0 HD4 HDn Hcr Vbx Rb Hpresx)
    as HS.
  destruct (rbnl_ew regsx (D + n0) c bb) as (E32 & E33 & E34 & EE).
  assert (E22 : ew (rbnl_E regsx (D + n0) c bb) 22 = Z_to_bv 64 SB)
    by (rewrite (EE 22%nat 22%bv eq_refl); exact H22x).
  assert (E26 : ew (rbnl_E regsx (D + n0) c bb) 26 = Z_to_bv 64 n0)
    by (rewrite (EE 26%nat 26%bv eq_refl); exact H26x).
  assert (E29 : ew (rbnl_E regsx (D + n0) c bb) 29 = Z_to_bv 64 D)
    by (rewrite (EE 29%nat 29%bv eq_refl); exact H29x).
  assert (E5 : ew (rbnl_E regsx (D + n0) c bb) 5 = Z_to_bv 64 c)
    by (rewrite (EE 5%nat 5%bv eq_refl); exact H5x).
  assert (E17 : ew (rbnl_E regsx (D + n0) c bb) 17 = Z_to_bv 64 (Z.of_nat (length (c :: r))))
    by (rewrite (EE 17%nat 17%bv eq_refl); exact H17x).
  assert (E14 : ew (rbnl_E regsx (D + n0) c bb) 14 = Z_to_bv 64 45)
    by (rewrite (EE 14%nat 14%bv eq_refl); exact H14x).
  assert (E15 : ew (rbnl_E regsx (D + n0) c bb) 15 = Z_to_bv 64 23)
    by (rewrite (EE 15%nat 15%bv eq_refl); exact H15x).
  assert (E13 : ew (rbnl_E regsx (D + n0) c bb) 13 = Z_to_bv 64 ov0)
    by (rewrite (EE 13%nat 13%bv eq_refl); exact H13x).
  assert (E12 : ew (rbnl_E regsx (D + n0) c bb) 12 = Z_to_bv 64 (if sn then 1 else 0))
    by (rewrite (EE 12%nat 12%bv eq_refl); exact H12x).
  assert (E16 : ew (rbnl_E regsx (D + n0) c bb) 16 = Z_to_bv 64 N)
    by (rewrite (EE 16%nat 16%bv eq_refl); exact H16x).
  assert (E10 : ew (rbnl_E regsx (D + n0) c bb) 10 = Z_to_bv 64 N)
    by (rewrite (EE 10%nat 10%bv eq_refl); exact H10x).
  set (E := rbnl_E regsx (D + n0) c bb) in *.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, rbnl_E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regsx (map (Z_to_bv 64) [D + n0; c; bb])) E)
    by (unfold E, rbnl_E; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (SHOK : sh_ok SEGS rbnl_B rbnl_SH E (mrestrict (w_H W) memx))
    by (apply (rbnl_shok E _ (D + n0)); [exact E22 | exact E32 | lia
        | unfold kLowShadowBeg, kHighMemBeg in HDhi |- *; lia]).
  assert (HUB : U E rbnl_B = SHADOW_OFF)
    by (unfold rbnl_B; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
  assert (HU32 : U E (SOff 32 0) = D + n0) by (apply (U_atom E 32 (D + n0) E32); lia).
  assert (HU26 : U E (SOff 26 1) = n0 + 1) by (apply (U_atom_off E 26 n0 1 E26); lia).
  assert (HU23 : U E (SLit 23) = 23) by (rewrite U_SLit; reflexivity).
  assert (Hlenb : Z.of_nat (length (c :: r)) <= 2 ^ 47) by lia.
  assert (HU17 : U E (SOff 17 (-1)) = Z.of_nat (length r))
    by (rewrite (U_atom_off E 17 (Z.of_nat (length (c :: r))) (-1) E17) by lia; lia).
  assert (HU0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
  unfold cfg_at.
  paj_run_tok RUN HS HJx SHOK rbnl_span.
  { rbnl_awrD HWb E32 D n0. }
  assert (KEEP1x : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hnq. rewrite <- (KEEPx a Ha Hnq).
    apply (kept_of_frame E (ss_mem rbn3_ssc) (w_H W) memx (ms_mem ms) (fun x => x = D + n0) HFr);
      [|exact Ha | exact Hnq].
    intros bq wlo whi aq Haq2 Haq.
    cbn [ss_mem rbn3_ssc windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
    destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
      cbn [base_val] in Haq; rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  assert (GROW1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)))
    by (eapply mem_grows_trans; [exact GROWx | exact HG]).
  assert (Hbuf1 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms) D 24)
    by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms) D 24 (D + n0)
          Hbuf KEEP1x GROW1 Happ1); lia).
  assert (Hsrc1 : rbn_lsrc W (ms_mem ms) N (c :: r))
    by (apply (rbnl_src_keep W memc (ms_mem ms) N (c :: r) (D + n0) Hsrc KEEP1x Happ1); cbn [length]; lia).
  psrr_branch_tok RUN BR HS SHOK rbnl_span.
  - rewrite branch_ltu_U, HU23, HU26 in Hc. apply Z.ltb_lt in Hc.
    assert (Hn23 : n0 = 23) by lia.
    paj_run_tok RUN HS HJx SHOK rbnl_span.
    { rbnl_awrD HWb E32 D n0. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP1x a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Haq2 Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
      destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (Vb2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + n0) 1 bb).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 34 0)
          (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
      cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
      rewrite ?ew_ewset_other in Vq by lia. rewrite E34 in Vq. rewrite !Z.add_0_r in Vq.
      rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
      change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
    assert (KEEPB2 : forall a, 0 <= a < 2 ^ 64 ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
    { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP2 a Ha Hnb)].
      rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms0) (D + n0) bb Vb2 Rb).
      rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
    assert (GROW2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact GROWx | exact HG] | exact HG0]).
    rbnl_u_off HUc17 17%nat (Z.of_nat (length (c :: r))) (-1).
    psrr_branch_tok RUN BR HS SHOK rbnl_span.
    + rewrite branch_eq_U, U_SLit, HUc17 in Hc0.
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (Hr0 : r = []) by (destruct r as [|c2 r2]; [reflexivity | exfalso; cbn [length] in Hc0; lia]).
      subst r.
      paj_run_to_tok RUNTO HS HJx SHOK rbnl_span (AF_reac_box_name + RBN_L3X).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
      { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb].
        - lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
            pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 34 0)
              (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
              ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
              ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
          cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
          rewrite ?ew_ewset_other in Vq by lia. rewrite E34 in Vq. rewrite !Z.add_0_r in Vq.
          rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
          change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
          change (N.to_nat 1) with 1%nat in Vq.
          rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms1) (D + n0) bb Vq Rb).
          rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity.
        - rewrite <- (KEEPB2 a Ha).
          lazymatch goal with HFrq : frame_of _ _ (mrestrict _ (ms_mem ms0)) (mrestrict _ (ms_mem ms1)) |- _ =>
            apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFrq);
            [|exact Ha | exact Hnb] end.
          intros bq wlo whi aq Haq2 Haq.
          cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
          destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
            cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
            rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsx _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15.
      assert (R14v : getr (ms_regs ms1) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms1) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS.
      replace (Z.min 23 (n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn [])))) with 23
        by (cbn [length bn_tk]; lia).
      assert (Hcond : (23 <? n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn []))) = true)
        by (cbn [length bn_tk]; apply Z.ltb_lt; lia).
      rewrite Hcond.
      replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
      apply SRr_ret. split; [reflexivity|].
      exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdx) mat1 mdx).
      split.
      { unfold cfg_at, w64.
        replace (BASE + AF_reac_box_name + RBN_L3X) with (BASE + 15420)
          by (unfold AF_reac_box_name, RBN_L3X; lia).
        reflexivity. }
      split; [exact HJx|].
      split.
      { intros rr Hrr Hnn.
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - rewrite (HKr1 _ Hin). exact (HKx _ Hin). }
      split.
      { apply Forall_cons.
        { cbn [fst snd].
          replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite RG26. rbnl_regval. }
        apply Forall_cons; [|apply Forall_nil].
        cbn [fst snd].
        replace (Z_to_bv 5 13) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG13. rbnl_regval. }
      split.
      { intros a Ha Hout. apply KEEP3. exact Ha. }
      apply garr8_nil.
    + rewrite branch_eq_U, U_SLit, HUc17 in Hc0.
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
      assert (Hrne : r <> []) by (intros Hz; apply Hc0; rewrite Hz; cbn [length]; lia).
      paj_run_to_tok RUNTO HS HJx SHOK rbnl_span (AF_reac_box_name + RBN_L3).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
        aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
      { intros a Ha Hnb. rewrite <- (KEEP2 a Ha Hnb).
        apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
          [|exact Ha | exact Hnb].
        intros bq wlo whi aq Haq2 Haq.
        cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
        destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
          cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
          rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      assert (Vb3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 bb).
      { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
          pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N (SOff 34 0)
            (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
            ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
            ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq end.
        cbn [ms_mem restrict] in Vq. cbn [sv_denot] in Vq.
        rewrite ?ew_ewset_other in Vq by lia. rewrite E34 in Vq. rewrite !Z.add_0_r in Vq.
        rewrite ?Z_to_bv_bv_unsigned in Vq. rewrite unsigned_lit_small in Vq by lia.
        change (2 ^ (8 * Z.of_N 1)) with 256 in Vq. rewrite Z.mod_small in Vq by lia.
        change (N.to_nat 1) with 1%nat in Vq. exact Vq. }
      assert (KEEPB3 : forall a, 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
      { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP3 a Ha Hnb)].
        rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms1) (D + n0) bb Vb3 Rb).
        rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
      assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
        by (eapply mem_grows_trans; [exact GROW2 | exact HG1]).
      assert (Hsrc3 : rbn_lsrc W (ms_mem ms1) N (c :: r))
        by (apply (rbnl_src_keep W memc (ms_mem ms1) N (c :: r) (D + n0) Hsrc KEEP3 Happ1);
            cbn [length]; lia).
      assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
        by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
              Hbuf KEEP3 GROW3 Happ1); lia).
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsx _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13. prreg HS (12%bv : bv 5) RG12.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15. prreg HS (16%bv : bv 5) RG16.
      prreg HS (10%bv : bv 5) RG10. prreg HS (17%bv : bv 5) RG17. prreg HS (29%bv : bv 5) RG29.
      prreg HS (22%bv : bv 5) RG22.
      assert (R14v : getr (ms_regs ms1) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms1) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS.
      replace (Z.min 23 (n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn r)))) with 23
        by (cbn [length]; lia).
      assert (Hcond : (23 <? n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn r))) = true)
        by (cbn [length]; apply Z.ltb_lt; lia).
      rewrite Hcond.
      replace (Z.to_nat (23 - n0)) with 0%nat by lia. cbn [firstn].
      eapply SRr_mono.
      { replace (BASE + 15276) with (BASE + AF_reac_box_name + RBN_L3)
          by (unfold AF_reac_box_name, RBN_L3; lia).
        eapply (IH sn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
          (N + 1) D n0 1).
        - exact HJx.
        - destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl) | cbn [length]; lia].
        - inversion Hall; assumption.
        - apply (rbnl_src_tail W (ms_mem ms1) N c r). exact Hsrc3.
        - exact Hbuf3.
        - lia.
        - lia.
        - lia.
        - rewrite RG12. rbnl_regval.
        - rewrite RG26. rbnl_regval.
        - rewrite RG13. rbnl_regval.
        - rewrite RG14. rbnl_regval.
        - rewrite RG15. rbnl_regval.
        - rewrite RG16. rbnl_regval.
        - rewrite RG10. rbnl_regval.
        - rewrite RG17. rbnl_regval.
        - rewrite RG29. rbnl_regval.
        - rewrite RG22. rbnl_regval. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
      replace (Z.min 23 (n0 + Z.of_nat (length (bn_tk sn r)))) with 23 in Houts2 by lia.
      replace (if 23 <? n0 + Z.of_nat (length (bn_tk sn r)) then 1 else 1) with 1 in Houts2
        by (destruct (23 <? n0 + Z.of_nat (length (bn_tk sn r))); reflexivity).
      replace (Z.to_nat (23 - n0)) with 0%nat in Hfr2, Hga2 by lia.
      rewrite firstn_O in Hfr2, Hga2. cbn [length] in Hfr2.
      split; [reflexivity|]. exists regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HJ2|].
      split.
      { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - rewrite (HKr1 _ Hin). exact (HKx _ Hin). }
      split; [exact Houts2|].
      split.
      { intros a Ha Hout. rewrite (Hfr2 a Ha ltac:(lia)). apply KEEPB3. exact Ha. }
      apply garr8_nil.
  - rewrite branch_ltu_U, HU23, HU26 in Hc. apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJx SHOK rbnl_span.
    { rewrite HU32.
      apply (obl_of_range SEGS (w_H W) (ms_mem ms) E rbnl_B (D + n0) 1 D 24);
        [exact (proj1 (proj2 (proj2 (proj2 Hbuf1)))) | exact HUB | lia | lia]. }
    { rbnl_awrD HWb E32 D n0. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEP1x a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Haq2 Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
      destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (GROW2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
      by (eapply mem_grows_trans; [exact GROW1 | exact HG0]).
    assert (Vc2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + n0) 1 (rbn_lc c)).
    { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
        pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N
          (SAlu ALU_ADD (SOff 5 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5)))
          (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
          ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
          ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq;
        assert (HLow : U Ev (SAlu ALU_ADD (SOff 5 0)
          (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5))) = rbn_lc c)
          by (apply (rbnl_lower Ev 5 c); [rewrite ?ew_ewset_other by lia; exact E5 | lia]) end.
      cbn [ms_mem restrict] in Vq. unfold U in HLow. rewrite HLow in Vq.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vq.
      rewrite Z.mod_small in Vq by (apply rbn_lc_range; lia).
      change (N.to_nat 1) with 1%nat in Vq. rewrite Z.add_0_r in Vq. exact Vq. }
    rbnl_u_off HUc17 17%nat (Z.of_nat (length (c :: r))) (-1).
    psrr_branch_tok RUN BR HS SHOK rbnl_span.
    + rewrite branch_eq_U, U_SLit, HUc17 in Hc0.
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_eq in Hc0.
      assert (Hr0 : r = []) by (destruct r as [|c2 r2]; [reflexivity | exfalso; cbn [length] in Hc0; lia]).
      subst r.
      paj_run_to_tok RUNTO HS HJx SHOK rbnl_span (AF_reac_box_name + RBN_L3X).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
        aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
      { intros a Ha Hnb. rewrite <- (KEEP2 a Ha Hnb).
        apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
          [|exact Ha | exact Hnb].
        intros bq wlo whi aq Haq2 Haq.
        cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
        destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
          cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
          rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 (rbn_lc c)).
      { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
          pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N
            (SAlu ALU_ADD (SOff 5 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5)))
            (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
            ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
            ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq;
          assert (HLow : U Ev (SAlu ALU_ADD (SOff 5 0)
            (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5))) = rbn_lc c)
            by (apply (rbnl_lower Ev 5 c); [rewrite ?ew_ewset_other by lia; exact E5 | lia]) end.
        cbn [ms_mem restrict] in Vq. unfold U in HLow. rewrite HLow in Vq.
        change (2 ^ (8 * Z.of_N 1)) with 256 in Vq.
        rewrite Z.mod_small in Vq by (apply rbn_lc_range; lia).
        change (N.to_nat 1) with 1%nat in Vq. rewrite Z.add_0_r in Vq. exact Vq. }
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsx _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15.
      assert (R14v : getr (ms_regs ms1) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms1) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS.
      replace (Z.min 23 (n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn [])))) with (n0 + 1)
        by (cbn [length bn_tk]; lia).
      assert (Hcond : (23 <? n0 + Z.of_nat (length (rbn_lc c :: bn_tk sn []))) = false)
        by (cbn [length bn_tk]; apply Z.ltb_ge; lia).
      rewrite Hcond.
      assert (HNat : Z.to_nat (23 - n0) = Datatypes.S (Z.to_nat (23 - (n0 + 1)))).
      { replace (23 - n0) with (1 + (23 - (n0 + 1))) by lia.
        rewrite Z2Nat.inj_add by lia. reflexivity. }
      rewrite HNat. cbn [bn_tk firstn]. rewrite firstn_nil.
      apply SRr_ret. split; [reflexivity|].
      exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy mdx) mat1 mdx).
      split.
      { unfold cfg_at, w64.
        replace (BASE + AF_reac_box_name + RBN_L3X) with (BASE + 15420)
          by (unfold AF_reac_box_name, RBN_L3X; lia).
        reflexivity. }
      split; [exact HJx|].
      split.
      { intros rr Hrr Hnn.
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - rewrite (HKr1 _ Hin). exact (HKx _ Hin). }
      split.
      { apply Forall_cons.
        { cbn [fst snd].
          replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite RG26. rbnl_regval. }
        apply Forall_cons; [|apply Forall_nil].
        cbn [fst snd].
        replace (Z_to_bv 5 13) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG13. rbnl_regval. }
      split.
      { intros a Ha Hout. apply KEEP3; [exact Ha | cbn [length] in Hout; lia]. }
      apply garr8_cons_x; [exact Vc3 | apply rbn_lc_range; lia | apply garr8_nil].
    + rewrite branch_eq_U, U_SLit, HUc17 in Hc0.
      change (zcanon 0) with 0 in Hc0. apply Z.eqb_neq in Hc0.
      assert (Hrne : r <> []) by (intros Hz; apply Hc0; rewrite Hz; cbn [length]; lia).
      paj_run_to_tok RUNTO HS HJx SHOK rbnl_span (AF_reac_box_name + RBN_L3).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
        aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
      { intros a Ha Hnb. rewrite <- (KEEP2 a Ha Hnb).
        apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
          [|exact Ha | exact Hnb].
        intros bq wlo whi aq Haq2 Haq.
        cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
        destruct Haq2 as [Hq | []]; injection Hq as <- <- <-;
          cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
          rewrite ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
        by (eapply mem_grows_trans; [exact GROW2 | exact HG1]).
      assert (Vc3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 (rbn_lc c)).
      { lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
          pose proof (@field_of_region_any SEGS Ev _ 32%nat (D + n0) _ 0 1 0 1 0 1%N
            (SAlu ALU_ADD (SOff 5 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5)))
            (st_ok_pi_region_nth Ev _ _ 0 _ HSq eq_refl)
            ltac:(rewrite ?ew_ewset_other by lia; rewrite E32; apply unsigned_lit_small; lia)
            ltac:(left; reflexivity) ltac:(cbn; lia)) as Vq;
          assert (HLow : U Ev (SAlu ALU_ADD (SOff 5 0)
            (SAlu ALU_SLL (SAlu ALU_SLTU (SOff 5 (-65)) (SLit 26)) (SLit 5))) = rbn_lc c)
            by (apply (rbnl_lower Ev 5 c); [rewrite ?ew_ewset_other by lia; exact E5 | lia]) end.
        cbn [ms_mem restrict] in Vq. unfold U in HLow. rewrite HLow in Vq.
        change (2 ^ (8 * Z.of_N 1)) with 256 in Vq.
        rewrite Z.mod_small in Vq by (apply rbn_lc_range; lia).
        change (N.to_nat 1) with 1%nat in Vq. rewrite Z.add_0_r in Vq. exact Vq. }
      assert (Hsrc3 : rbn_lsrc W (ms_mem ms1) N (c :: r))
        by (apply (rbnl_src_keep W memc (ms_mem ms1) N (c :: r) (D + n0) Hsrc KEEP3 Happ1);
            cbn [length]; lia).
      assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms1) D 24)
        by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms1) D 24 (D + n0)
              Hbuf KEEP3 GROW3 Happ1); lia).
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsx _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13. prreg HS (12%bv : bv 5) RG12.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15. prreg HS (16%bv : bv 5) RG16.
      prreg HS (10%bv : bv 5) RG10. prreg HS (17%bv : bv 5) RG17. prreg HS (29%bv : bv 5) RG29.
      prreg HS (22%bv : bv 5) RG22.
      assert (R14v : getr (ms_regs ms1) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms1) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS.
      cbn [length]. rewrite Nat2Z.inj_succ.
      replace (n0 + Z.succ (Z.of_nat (length (bn_tk sn r)))) with (n0 + 1 + Z.of_nat (length (bn_tk sn r)))
        by lia.
      assert (HNat : Z.to_nat (23 - n0) = Datatypes.S (Z.to_nat (23 - (n0 + 1)))).
      { replace (23 - n0) with (1 + (23 - (n0 + 1))) by lia.
        rewrite Z2Nat.inj_add by lia. reflexivity. }
      rewrite HNat. cbn [firstn].
      eapply SRr_mono.
      { replace (BASE + 15276) with (BASE + AF_reac_box_name + RBN_L3)
          by (unfold AF_reac_box_name, RBN_L3; lia).
        eapply (IH sn fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
          (N + 1) D (n0 + 1) ov0).
        - exact HJx.
        - destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl) | cbn [length]; lia].
        - inversion Hall; assumption.
        - apply (rbnl_src_tail W (ms_mem ms1) N c r). exact Hsrc3.
        - exact Hbuf3.
        - lia.
        - lia.
        - lia.
        - rewrite RG12. rbnl_regval.
        - rewrite RG26. rbnl_regval.
        - rewrite RG13. rbnl_regval.
        - rewrite RG14. rbnl_regval.
        - rewrite RG15. rbnl_regval.
        - rewrite RG16. rbnl_regval.
        - rewrite RG10. rbnl_regval.
        - rewrite RG17. rbnl_regval.
        - rewrite RG29. rbnl_regval.
        - rewrite RG22. rbnl_regval. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
      split; [reflexivity|]. exists regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HJ2|].
      split.
      { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - rewrite (HKr1 _ Hin). exact (HKx _ Hin). }
      split; [exact Houts2|].
      assert (HlenW : length (rbn_lc c :: firstn (Z.to_nat (23 - (n0 + 1))) (bn_tk sn r))
        = Datatypes.S (length (firstn (Z.to_nat (23 - (n0 + 1))) (bn_tk sn r)))) by reflexivity.
      split.
      { intros a Ha Hout. rewrite HlenW, Nat2Z.inj_succ in Hout.
        assert (Hout2 : ~ (D + (n0 + 1) <= a < D + (n0 + 1)
          + Z.of_nat (length (firstn (Z.to_nat (23 - (n0 + 1))) (bn_tk sn r))))) by lia.
        rewrite (Hfr2 a Ha Hout2). apply KEEP3; [exact Ha | lia]. }
      apply garr8_cons_x.
      { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms1) mem2 (D + n0) 1 (rbn_lc c));
          [|exact Vc3].
        intros x Hx.
        assert (Hout3 : ~ (D + (n0 + 1) <= x < D + (n0 + 1)
          + Z.of_nat (length (firstn (Z.to_nat (23 - (n0 + 1))) (bn_tk sn r))))) by lia.
        apply (Hfr2 x ltac:(lia) Hout3). }
      { apply rbn_lc_range; lia. }
      { replace (D + n0 + 1) with (D + (n0 + 1)) by lia. exact Hga2. }
}
unfold cfg_at, w64 in COPY.
rbnl_u_atom HU33 33%nat c.
lazymatch goal with HSq : st_ok_pi _ _ ?Ev _ _ |- _ =>
  assert (HU12 : U Ev (SOff 12 0) = (if sn then 1 else 0)) by
    (apply (U_atom Ev 12 (if sn then 1 else 0));
     [rewrite ?ew_ewset_other by lia; exact E12 | destruct sn; lia]) end.
psrr_branch_tok RUN BR HS SHOK rbnl_span.
- rewrite branch_ne_U, HU33, U_SLit in Hc. change (zcanon 45) with 45 in Hc.
  assert (Hne45 : c <> 45) by (intros Hz; rewrite Hz in Hc; cbn in Hc; discriminate Hc).
  assert (Htk : bn_tk sn (c :: r) = rbn_lc c :: bn_tk sn r).
  { rewrite bn_tk_cons. replace ((c =? 45) && negb sn) with false; [reflexivity|].
    symmetry. apply andb_false_iff. left. apply Z.eqb_neq. exact Hne45. }
  paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L3C).
  { rbnl_awrD HWb E32 D n0. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hnq. rewrite <- (KEEP1 a Ha Hnq).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
      [|exact Ha | exact Hnq].
    intros bq wlo whi aq Haq2 Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
    destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
      cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
      rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  assert (GROW2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
    by (eapply mem_grows_trans; [exact HG | exact HG0]).
  assert (Vb2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + n0) 1 bb).
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
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn3_keptl HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HKr1.
  cbn [ms_regs restrict] in HKr1.
  prreg HS (5%bv : bv 5) RG5. prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15.
  prreg HS (22%bv : bv 5) RG22. prreg HS (26%bv : bv 5) RG26. prreg HS (29%bv : bv 5) RG29.
  prreg HS (13%bv : bv 5) RG13. prreg HS (12%bv : bv 5) RG12. prreg HS (16%bv : bv 5) RG16.
  prreg HS (10%bv : bv 5) RG10. prreg HS (17%bv : bv 5) RG17.
  pmkst HS. rewrite Htk.
  replace (BASE + 15312) with (BASE + (AF_reac_box_name + RBN_L3C))
    by (unfold AF_reac_box_name, RBN_L3C; lia).
  apply (COPY (ms_regs ms0) (ms_mem ms0)).
  + exact HJ.
  + exact KEEP2.
  + exact Vb2.
  + exact GROW2.
  + exact HKr1.
  + rewrite RG5. rbnl_regval.
  + rewrite RG14. rbnl_regval.
  + rewrite RG15. rbnl_regval.
  + rewrite RG22. rbnl_regval.
  + rewrite RG26. rbnl_regval.
  + rewrite RG29. rbnl_regval.
  + rewrite RG13. rbnl_regval.
  + rewrite RG12. rbnl_regval.
  + rewrite RG16. rbnl_regval.
  + rewrite RG10. rbnl_regval.
  + rewrite RG17. rbnl_regval.
- rewrite branch_ne_U, HU33, U_SLit in Hc. change (zcanon 45) with 45 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK rbnl_span.
  { rbnl_awrD HWb E32 D n0. }
  assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hnq. rewrite <- (KEEP1 a Ha Hnq).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => x = D + n0) HFr0);
      [|exact Ha | exact Hnq].
    intros bq wlo whi aq Haq2 Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
    destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
      cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
      rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
  assert (GROWa : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
    by (eapply mem_grows_trans; [exact HG | exact HG0]).
  psrr_branch_tok RUN BR HS SHOK rbnl_span.
  + rewrite branch_ne_U, HU12, U_SLit in Hc0. change (zcanon 0) with 0 in Hc0.
    assert (Hsn : sn = true) by (destruct sn; [reflexivity | cbn in Hc0; discriminate Hc0]).
    assert (Htk : bn_tk sn (c :: r) = rbn_lc c :: bn_tk sn r).
    { rewrite bn_tk_cons, Hsn. cbn [negb]. rewrite andb_false_r. reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L3C).
    { rbnl_awrD HWb E32 D n0. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEPa a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Haq2 Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
      destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (GROW2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [exact GROWa | exact HG1]).
    assert (Vb2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + n0) 1 bb).
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
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn3_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr1.
    cbn [ms_regs restrict] in HKr1.
    prreg HS (5%bv : bv 5) RG5. prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15.
    prreg HS (22%bv : bv 5) RG22. prreg HS (26%bv : bv 5) RG26. prreg HS (29%bv : bv 5) RG29.
    prreg HS (13%bv : bv 5) RG13. prreg HS (12%bv : bv 5) RG12. prreg HS (16%bv : bv 5) RG16.
    prreg HS (10%bv : bv 5) RG10. prreg HS (17%bv : bv 5) RG17.
    pmkst HS. rewrite Htk.
    replace (BASE + 15312) with (BASE + (AF_reac_box_name + RBN_L3C))
      by (unfold AF_reac_box_name, RBN_L3C; lia).
    apply (COPY (ms_regs ms1) (ms_mem ms1)).
    * exact HJ.
    * exact KEEP2.
    * exact Vb2.
    * exact GROW2.
    * exact HKr1.
    * rewrite RG5. rbnl_regval.
    * rewrite RG14. rbnl_regval.
    * rewrite RG15. rbnl_regval.
    * rewrite RG22. rbnl_regval.
    * rewrite RG26. rbnl_regval.
    * rewrite RG29. rbnl_regval.
    * rewrite RG13. rbnl_regval.
    * rewrite RG12. rbnl_regval.
    * rewrite RG16. rbnl_regval.
    * rewrite RG10. rbnl_regval.
    * rewrite RG17. rbnl_regval.
  + rewrite branch_ne_U, HU12, U_SLit in Hc0. change (zcanon 0) with 0 in Hc0.
    assert (Hsn : sn = false)
      by (destruct sn; [cbn in Hc0; discriminate Hc0 | reflexivity]).
    assert (Htk : bn_tk sn (c :: r) = bn_tk true r).
    { rewrite bn_tk_cons, Hsn, Hc. cbn [negb]. rewrite andb_true_r.
      replace (45 =? 45) with true by reflexivity. reflexivity. }
    paj_run_tok RUN HS HJ SHOK rbnl_span.
    { rbnl_awrD HWb E32 D n0. }
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hnq. rewrite <- (KEEPa a Ha Hnq).
      apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun x => x = D + n0) HFr1);
        [|exact Ha | exact Hnq].
      intros bq wlo whi aq Haq2 Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
      destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
        cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
        rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
    assert (GROW2 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [exact GROWa | exact HG1]).
    rbnl_u_off HUc17 17%nat (Z.of_nat (length (c :: r))) (-1).
    psrr_branch_tok RUN BR HS SHOK rbnl_span.
    * rewrite branch_eq_U, U_SLit, HUc17 in Hc1.
      change (zcanon 0) with 0 in Hc1. apply Z.eqb_eq in Hc1.
      assert (Hr0 : r = [])
        by (destruct r as [|c2 r2]; [reflexivity | exfalso; cbn [length] in Hc1; lia]).
      subst r.
      paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L3X).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
        aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
      { intros a Ha Hnb. rewrite <- (KEEP2 a Ha Hnb).
        apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) (fun x => x = D + n0) HFr2);
          [|exact Ha | exact Hnb].
        intros bq wlo whi aq Haq2 Haq.
        cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
        destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
          cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
          rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      assert (Vb3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (D + n0) 1 bb).
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
      assert (KEEPB3 : forall a, 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
      { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP3 a Ha Hnb)].
        rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms2) (D + n0) bb Vb3 Rb).
        rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15.
      assert (R14v : getr (ms_regs ms2) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms2) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS. rewrite Htk.
      replace (bn_tk true (@nil Z)) with (@nil Z) by reflexivity.
      replace (Z.of_nat (length (@nil Z))) with 0 by reflexivity.
      replace (Z.min 23 (n0 + 0)) with n0 by lia.
      replace (23 <? n0 + 0) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite firstn_nil.
      apply SRr_ret. split; [reflexivity|].
      exists (ms_regs ms2), (ms_mem ms2), (with_vm_backing (m_vm_lazy mdc) mat2 mdc).
      split.
      { unfold cfg_at, w64.
        replace (BASE + AF_reac_box_name + RBN_L3X) with (BASE + 15420)
          by (unfold AF_reac_box_name, RBN_L3X; lia).
        reflexivity. }
      split; [exact HJ|].
      split.
      { intros rr Hrr Hnn.
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - exact (HKr1 _ Hin). }
      split.
      { apply Forall_cons.
        { cbn [fst snd].
          replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite RG26. rbnl_regval. }
        apply Forall_cons; [|apply Forall_nil].
        cbn [fst snd].
        replace (Z_to_bv 5 13) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
        rewrite RG13. rbnl_regval. }
      split.
      { intros a Ha Hout. apply KEEPB3. exact Ha. }
      apply garr8_nil.
    * rewrite branch_eq_U, U_SLit, HUc17 in Hc1.
      change (zcanon 0) with 0 in Hc1. apply Z.eqb_neq in Hc1.
      assert (Hrne : r <> []) by (intros Hz; apply Hc1; rewrite Hz; cbn [length]; lia).
      paj_run_to_tok RUNTO HS HJ SHOK rbnl_span (AF_reac_box_name + RBN_L3).
      { rbnl_awrD HWb E32 D n0. }
      assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + n0 ->
        aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
      { intros a Ha Hnb. rewrite <- (KEEP2 a Ha Hnb).
        apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms2) (fun x => x = D + n0) HFr2);
          [|exact Ha | exact Hnb].
        intros bq wlo whi aq Haq2 Haq.
        cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Haq2.
        destruct Haq2 as [Hq | [Hq | []]]; injection Hq as <- <- <-;
          cbn [base_val] in Haq; rewrite ?ew_ewset_other in Haq by lia;
          rewrite ?E16, ?E32, ?unsigned_lit_small in Haq by lia; lia. }
      assert (Vb3 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms2)) (D + n0) 1 bb).
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
      assert (KEEPB3 : forall a, 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a).
      { intros a Ha. destruct (Z.eq_dec a (D + n0)) as [-> | Hnb]; [|exact (KEEP3 a Ha Hnb)].
        rewrite (aview_of_val_mem1 SEGS (w_H W) (ms_mem ms2) (D + n0) bb Vb3 Rb).
        rewrite (aview_of_val_mem1 SEGS (w_H W) memc (D + n0) bb Vb Rb). reflexivity. }
      assert (GROW3 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms2)))
        by (eapply mem_grows_trans; [exact GROW2 | exact HG2]).
      assert (Hsrc3 : rbn_lsrc W (ms_mem ms2) N (c :: r))
        by (apply (rbnl_src_keep W memc (ms_mem ms2) N (c :: r) (D + n0) Hsrc KEEP3 Happ1);
            cbn [length]; lia).
      assert (Hbuf3 : rbn_lbuf B STK sp0 FP ly S own lyc Sc W (ms_mem ms2) D 24)
        by (apply (rbnl_buf_keep B STK sp0 FP ly S own lyc Sc W memc (ms_mem ms2) D 24 (D + n0)
              Hbuf KEEP3 GROW3 Happ1); lia).
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ rbn3_keptl HS ltac:(env_agree_chain HAE)
        ltac:(vm_compute; reflexivity)) as HKr1.
      cbn [ms_regs restrict] in HKr1.
      prreg HS (26%bv : bv 5) RG26. prreg HS (13%bv : bv 5) RG13. prreg HS (12%bv : bv 5) RG12.
      prreg HS (14%bv : bv 5) RG14. prreg HS (15%bv : bv 5) RG15. prreg HS (16%bv : bv 5) RG16.
      prreg HS (10%bv : bv 5) RG10. prreg HS (17%bv : bv 5) RG17. prreg HS (29%bv : bv 5) RG29.
      prreg HS (22%bv : bv 5) RG22.
      assert (R14v : getr (ms_regs ms2) 14 = w64 45) by (rewrite RG14; rbnl_regval).
      assert (R15v : getr (ms_regs ms2) 15 = w64 23) by (rewrite RG15; rbnl_regval).
      pmkst HS. rewrite Htk.
      eapply SRr_mono.
      { replace (BASE + 15276) with (BASE + AF_reac_box_name + RBN_L3)
          by (unfold AF_reac_box_name, RBN_L3; lia).
        eapply (IH true fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms2) _ k (ms_regs ms2)
          (N + 1) D n0 ov0).
        - exact HJ.
        - destruct r as [|c2 r2]; [exfalso; exact (Hrne eq_refl) | cbn [length]; lia].
        - inversion Hall; assumption.
        - apply (rbnl_src_tail W (ms_mem ms2) N c r). exact Hsrc3.
        - exact Hbuf3.
        - lia.
        - lia.
        - lia.
        - rewrite RG12. rbnl_regval.
        - rewrite RG26. rbnl_regval.
        - rewrite RG13. rbnl_regval.
        - rewrite RG14. rbnl_regval.
        - rewrite RG15. rbnl_regval.
        - rewrite RG16. rbnl_regval.
        - rewrite RG10. rbnl_regval.
        - rewrite RG17. rbnl_regval.
        - rewrite RG29. rbnl_regval.
        - rewrite RG22. rbnl_regval. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & Houts2 & Hfr2 & Hga2).
      split; [reflexivity|]. exists regs2, mem2, md2.
      split; [reflexivity|]. split; [exact HJ2|].
      split.
      { intros rr Hrr Hnn. rewrite (HKr2 rr Hrr Hnn).
        destruct (rbn3_kept_cover rr Hrr Hnn) as [-> | [-> | [-> | Hin]]].
        - replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite !getr_zero. reflexivity.
        - replace (Z_to_bv 5 14) with (14%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R14v, H14. reflexivity.
        - replace (Z_to_bv 5 15) with (15%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
          rewrite R15v, H15. reflexivity.
        - exact (HKr1 _ Hin). }
      split; [exact Houts2|].
      split.
      { intros a Ha Hout. rewrite (Hfr2 a Ha Hout). apply KEEPB3. exact Ha. }
      exact Hga2.
Qed.
Theorem rbn_l2_fits : rbn_L2_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hle.
pose proof (rbn2_gen s fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with (n0 + Z.of_nat (length s)) in Hg by lia.
replace (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0) with ov0 in Hg
  by (destruct (Z.ltb_spec 23 (n0 + Z.of_nat (length s))); [lia | reflexivity]).
replace (firstn (Z.to_nat (23 - n0)) s) with s in Hg by (symmetry; apply firstn_all2; lia).
exact Hg.
Qed.
Theorem rbn_l2_ovf : rbn_L2_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0 s Hlt.
pose proof (rbn2_gen s fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs P D n0 ov0) as Hg.
replace (Z.min 23 (n0 + Z.of_nat (length s))) with 23 in Hg by lia.
replace (if 23 <? n0 + Z.of_nat (length s) then 1 else ov0) with 1 in Hg
  by (destruct (Z.ltb_spec 23 (n0 + Z.of_nat (length s))); [reflexivity | lia]).
exact Hg.
Qed.
Theorem rbn_l3_fits : rbn_L3_fits B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l Hle.
unfold rbn_L3_run. intros HJ Hlen Hall Hsrc Hbuf Hdj H12 H26 H13 H14 H15 H16 H10 H17 H29 H22.
pose proof (rbn3_gen l false fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D 0 0
  HJ Hlen Hall Hsrc Hbuf Hdj ltac:(lia) ltac:(left; reflexivity)
  H12 H26 H13 H14 H15 H16 H10 H17 H29 H22) as Hg.
unfold bn_TK in Hle |- *.
replace (Z.min 23 (0 + Z.of_nat (length (bn_tk false l)))) with (Z.of_nat (length (bn_tk false l)))
  in Hg by lia.
replace (if 23 <? 0 + Z.of_nat (length (bn_tk false l)) then 1 else 0) with 0 in Hg
  by (destruct (Z.ltb_spec 23 (0 + Z.of_nat (length (bn_tk false l)))); [lia | reflexivity]).
replace (firstn (Z.to_nat (23 - 0)) (bn_tk false l)) with (bn_tk false l) in Hg
  by (symmetry; apply firstn_all2; lia).
exact Hg.
Qed.
Theorem rbn_l3_ovf : rbn_L3_ovf B.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D l Hlt.
unfold rbn_L3_run. intros HJ Hlen Hall Hsrc Hbuf Hdj H12 H26 H13 H14 H15 H16 H10 H17 H29 H22.
pose proof (rbn3_gen l false fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs N D 0 0
  HJ Hlen Hall Hsrc Hbuf Hdj ltac:(lia) ltac:(left; reflexivity)
  H12 H26 H13 H14 H15 H16 H10 H17 H29 H22) as Hg.
unfold bn_TK in Hlt |- *.
replace (Z.min 23 (0 + Z.of_nat (length (bn_tk false l)))) with 23 in Hg by lia.
replace (if 23 <? 0 + Z.of_nat (length (bn_tk false l)) then 1 else 0) with 1 in Hg
  by (destruct (Z.ltb_spec 23 (0 + Z.of_nat (length (bn_tk false l)))); [reflexivity | lia]).
replace (Z.to_nat (23 - 0)) with 23%nat in Hg by reflexivity.
exact Hg.
Qed.
End h.
End f.
End d.
