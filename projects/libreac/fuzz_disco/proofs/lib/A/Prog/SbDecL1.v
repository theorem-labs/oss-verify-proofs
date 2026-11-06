(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC88.v:61-65, 107-112, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_L1.v, with its module paths and module names changed; 458 of its 549 lines of code are new or changed and 726 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import SbDecLoops.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require sb_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sbdl_wrap64 : forall z, 0 <= z < 2 ^ 64 -> bv_wrap 64 z = z.
Proof.
intros z Hz. unfold bv_wrap. replace (bv_modulus 64) with (2 ^ 64) by reflexivity. apply Z.mod_small. exact Hz.
Qed.
Lemma sbdl_wrap64_neg : forall z, - 2 ^ 64 <= z < 0 -> bv_wrap 64 z = z + 2 ^ 64.
Proof.
intros z Hz. unfold bv_wrap. replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite <- (Z_mod_plus_full z 1 (2 ^ 64)). apply Z.mod_small. lia.
Qed.
Lemma sbdl_swrap64 : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 64) with (2 ^ 63) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma sbdl_swrap32 : forall z, - 2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma sbdl_magic : forall x, 0 <= x < 2 ^ 31 -> x * 1717986919 / 2 ^ 34 = x / 10.
Proof.
intros x Hx.
pose proof (Z.div_mod x 10 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmb.
set (q := x / 10) in *. set (r := x mod 10) in *.
symmetry. apply (Z.div_unique_pos _ _ _ (6 * q + r * 1717986919)); [|nia].
split; [nia|]. change (2 ^ 34) with 17179869184. nia.
Qed.
Definition sbdl_m : sv := SMd M_MUL (SOff 20 0) (SOff 5 0).
Definition sbdl_q : sv := SAluw ALU_ADD (SAlu ALU_SRA sbdl_m (SLit 34)) (SAlu ALU_SRL sbdl_m (SLit 63)).
Definition sbdl_dig : sv := SAlu ALU_ADD (SAluw ALU_SUB (SOff 20 0) (SMd M_MUL sbdl_q (SOff 12 0))) (SLit 48).
Definition sbdl_x28 : sv := SAluw ALU_ADD (SOff 20 0) (SLit (-10)).
Section u.
Variable E : env.
Variable x : Z.
Hypothesis Hx : 0 <= x < 2 ^ 31.
Hypothesis E20 : ew E 20 = Z_to_bv 64 x.
Hypothesis E5 : ew E 5 = Z_to_bv 64 1717986919.
Hypothesis E12 : ew E 12 = Z_to_bv 64 10.
Lemma sbdl_qr : 0 <= x / 10 < 2 ^ 28 /\ 0 <= x mod 10 < 10 /\ x = 10 * (x / 10) + x mod 10.
Proof.
pose proof (Z.div_mod x 10 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmb.
split; [|split; [lia | lia]].
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma U_sbdl_m : U E sbdl_m = x * 1717986919.
Proof.
unfold sbdl_m. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E 20 x E20) by lia. rewrite (U_atom E 5 1717986919 E5) by lia.
apply zcanon_id. unfold M64. nia.
Qed.
Lemma U_sbdl_sra : U E (SAlu ALU_SRA sbdl_m (SLit 34)) = x / 10.
Proof.
pose proof sbdl_qr as (Hq & _ & _).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_sbdl_m, U_SLit.
change (zcanon 34) with 34. change (Z.land 34 63) with 34.
rewrite sbdl_swrap64 by nia. rewrite Z.shiftr_div_pow2 by lia.
rewrite sbdl_magic by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma U_sbdl_srl : U E (SAlu ALU_SRL sbdl_m (SLit 63)) = 0.
Proof.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_sbdl_m, U_SLit.
change (zcanon 63) with 63. change (Z.land 63 63) with 63.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by nia. reflexivity.
Qed.
Lemma U_sbdl_q : U E sbdl_q = x / 10.
Proof.
pose proof sbdl_qr as (Hq & _ & _).
unfold sbdl_q. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite U_sbdl_sra, U_sbdl_srl.
rewrite (Z.mod_small (x / 10)) by lia. rewrite (Z.mod_small 0) by lia.
rewrite Z.add_0_r. rewrite sbdl_swrap32 by lia. apply sbdl_wrap64. lia.
Qed.
Lemma U_sbdl_dig : U E sbdl_dig = 48 + x mod 10.
Proof.
pose proof sbdl_qr as (Hq & Hr & Hx10).
assert (Hmul : U E (SMd M_MUL sbdl_q (SOff 12 0)) = x / 10 * 10).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite U_sbdl_q, (U_atom E 12 10 E12) by lia.
  apply zcanon_id. unfold M64. lia. }
assert (Hin : U E (SAluw ALU_SUB (SOff 20 0) (SMd M_MUL sbdl_q (SOff 12 0))) = x mod 10).
{ rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite Hmul, (U_atom E 20 x E20) by lia.
  rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small (x / 10 * 10)) by lia.
  replace (x - x / 10 * 10) with (x mod 10) by lia.
  rewrite sbdl_swrap32 by lia. apply sbdl_wrap64. lia. }
unfold sbdl_dig. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hin, U_SLit.
change (zcanon 48) with 48. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_sbdl_x28 : U E sbdl_x28 = (if x <? 10 then x - 10 + 2 ^ 64 else x - 10).
Proof.
unfold sbdl_x28. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E 20 x E20) by lia.
rewrite U_SLit. change (zcanon (-10)) with (2 ^ 64 - 10).
rewrite (Z.mod_small x) by lia.
replace ((2 ^ 64 - 10) mod 2 ^ 32) with (2 ^ 32 - 10) by (vm_compute; reflexivity).
unfold bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with (2 ^ 31) by reflexivity.
replace (bv_modulus 32) with (2 ^ 32) by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
replace (x + (2 ^ 32 - 10) + 2 ^ 31) with ((x - 10 + 2 ^ 31) + 1 * 2 ^ 32) by lia.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - 10 + 2 ^ 31)) by lia.
replace (x - 10 + 2 ^ 31 - 2 ^ 31) with (x - 10) by lia.
destruct (Z.ltb_spec x 10).
- rewrite <- (Z_mod_plus_full (x - 10) 1 (2 ^ 64)). rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma sbdl_br1 : (2 ^ 64 - 20 <? U E sbdl_x28) = (x <? 10).
Proof.
rewrite U_sbdl_x28. destruct (Z.ltb_spec x 10).
- apply Z.ltb_lt. lia.
- apply Z.ltb_ge. lia.
Qed.
End u.
Lemma U_addw1 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 30 ->
  U E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = v + 1.
Proof.
intros E n v Hn Hv. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
rewrite (U_atom E n v Hn) by lia. rewrite U_SLit. change (zcanon 1) with 1.
rewrite (Z.mod_small v) by lia. rewrite (Z.mod_small 1) by lia.
rewrite sbdl_swrap32 by lia. apply sbdl_wrap64. lia.
Qed.
Ltac sbdl_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr;
    rewrite (denot_lit_U E) in Hr;
    try fold sbdl_m in Hr; try fold sbdl_q in Hr; try fold sbdl_dig in Hr; try fold sbdl_x28 in Hr
  end.
Ltac sbdl_awr E32q Dq iq HWbq :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32%nat (Dq + iq));
    [reflexivity | rewrite E32q; apply unsigned_lit_small; lia | | apply awr_ok_nil];
  cbn [YP09.r_wlo YP09.r_whi];
  let aq := fresh "aq" in let Haq := fresh "Haq" in
  intros aq Haq; replace aq with (Dq + iq) by lia; exact (proj1 (HWbq (Dq + iq) ltac:(lia))).
Definition sbdl_ss : sstate :=
  mkSS (AF_sb_dec + SBD_L1) sr_atoms
    [ YP09.mkRegion (Some 32%nat) 0 1 0 1 [] ] None
    (mkFacts [ (32%nat, mkAF 0 (2 ^ 63) 0) ] [] [(SAlu ALU_ADD (SOff 14 0) (SOff 15 0), SOff 32 0)]).
Definition sbdl_cl : list Z := [7; 11; 15; 20; 28; 29; 30; 31].
Definition sbdl_keptl : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 8; 9; 10; 12; 13; 14; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma sbdl_kept_cover : forall r : Z, 0 <= r < 32 -> ~ In r sbdl_cl -> r = 0 \/ In (Z_to_bv 5 r) sbdl_keptl.
Proof.
intros r Hr Hn.
assert (H32 : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9 \/
  r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19 \/
  r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29 \/
  r = 30 \/ r = 31) by lia.
repeat (destruct H32 as [-> | H32]); try (subst r);
  first [ solve [left; reflexivity]
        | solve [exfalso; apply Hn; unfold sbdl_cl; cbn [In];
                 repeat first [ solve [left; reflexivity] | right ]]
        | solve [right; unfold sbdl_keptl; cbn [In];
                 repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]] ].
Qed.
Lemma sbdl_keep_of : forall (regs regs2 : bvmap 5 word),
  (forall rr : bv 5, In rr sbdl_keptl -> getr regs2 rr = getr regs rr) ->
  sbd_keep_regs regs regs2 sbdl_cl.
Proof.
intros regs regs2 HK r Hr Hn. destruct (sbdl_kept_cover r Hr Hn) as [-> | Hin].
- replace (Z_to_bv 5 0) with (0%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
  rewrite !getr_zero. reflexivity.
- apply HK. exact Hin.
Qed.
Lemma sbdl_keep_trans : forall (regs r1 r2 : bvmap 5 word) cl,
  sbd_keep_regs regs r1 cl -> sbd_keep_regs r1 r2 cl -> sbd_keep_regs regs r2 cl.
Proof. intros regs r1 r2 cl H1 H2 r Hr Hn. rewrite (H2 r Hr Hn). exact (H1 r Hr Hn). Qed.
Lemma sbdl_lsd_S : forall v j, sb_dec_c.sb_dec_lsd v (S j) =
  (48 + v mod 10) :: (if v <? 10 then [] else sb_dec_c.sb_dec_lsd (v / 10) j).
Proof. reflexivity. Qed.
Lemma sbdl_lsd_len : forall j v, (1 <= length (sb_dec_c.sb_dec_lsd v (S j)) <= S j)%nat.
Proof.
induction j as [|j IH]; intros v; rewrite sbdl_lsd_S.
- destruct (v <? 10); cbn [length sb_dec_c.sb_dec_lsd]; lia.
- destruct (v <? 10); cbn [length]; [lia|]. specialize (IH (v / 10)). lia.
Qed.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition sbdl_E (regs : bvmap 5 word) (Q : Z) : env := Eimg (Ereg regs [w64 Q]).
Lemma sbdl_ew : forall regs Q,
  ew (sbdl_E regs Q) 32 = Z_to_bv 64 Q /\
  (forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (sbdl_E regs Q) k = getr regs r).
Proof.
intros regs Q. unfold sbdl_E.
split; [rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)|].
intros k r Hk. apply ew_Eimg_Ereg_nat. exact Hk.
Qed.
Lemma sbdl_E_img : forall regs Q, img_env VAL A_LIM (sbdl_E regs Q).
Proof. intros. unfold sbdl_E. apply Eimg_env. Qed.
Lemma sbdl_E_agree : forall regs Q, env_agree 32 (Ereg regs [w64 Q]) (sbdl_E regs Q).
Proof.
intros. split; [intros n Hn; unfold sbdl_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.
Lemma sbdl_entry : forall (fq : YK11.FPState) (W : world SEGS) (regs : bvmap 5 word)
  (memc : word -> option byte) (D i : Z),
  getr regs 14 = w64 D -> getr regs 15 = w64 i ->
  0 <= D -> 0 <= i -> D + i + 1 <= 2 ^ 63 ->
  apresent (w_H W) memc (D + i) ->
  st_ok_pi SEGS VAL (sbdl_E regs (D + i)) sbdl_ss
    (restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_L1))) memc (seg_rom SEGS))).
Proof.
intros fq W regs memc D i H14 H15 HD Hi HDi Hp.
rewrite restrict_mkst_fx.
destruct (sbdl_ew regs (D + i)) as (E32 & EE).
assert (HR : regs_ok (sbdl_E regs (D + i)) sr_atoms regs)
  by (unfold sbdl_E; apply regs_ok_Eimg_Ereg).
remember (sbdl_E regs (D + i)) as E eqn:HE. clear HE.
assert (E14 : ew E 14 = Z_to_bv 64 D) by (rewrite (EE 14%nat 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 i) by (rewrite (EE 15%nat 15%bv eq_refl); exact H15).
unfold sbdl_ss. apply pa_entry_st_ok_full.
- exact HR.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E32, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). replace (D + i + o) with (D + i) by lia. exact Hp.
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E32, unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    split; [|exact I]. split; [lia|]. split; [reflexivity | lia].
  + cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 14 D E14), (U_atom E 15 i E15), (U_atom E 32 (D + i) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Lemma sbdl_wbytes_grow : forall STK sp0 FP ly S own lyc Sc (W : world SEGS)
  (memc mem' : word -> option byte) D n,
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc D n ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W mem' D n.
Proof.
intros STK sp0 FP ly S own lyc Sc W memc mem' D n HW HP a Ha.
destruct (HW a Ha) as [H1 H2]. split; [exact H1 | exact (HP a H2)].
Qed.
Lemma sbdl_gen : forall (j : nat) (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
  (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (x D i : Z),
  (1 <= j <= 3)%nat -> i = 3 - Z.of_nat j ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= x < 2 ^ 31 -> 0 <= D -> D + 3 <= 2 ^ 63 ->
  sbd_wbytes B STK sp0 FP ly S own lyc Sc W memc (D + i) (Z.of_nat j) ->
  getr regs 20 = w64 x -> getr regs 15 = w64 i -> getr regs 11 = w64 i -> getr regs 14 = w64 D ->
  getr regs 5 = w64 1717986919 -> getr regs 12 = w64 10 -> getr regs 13 = w64 (-20) -> getr regs 6 = w64 2 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L1) regs memc mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = cfg_at (fx := fq) SEGS (BASE + AF_sb_dec + SBD_L1X) regs2 mem2 md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       sbd_keep_regs regs regs2 sbdl_cl /\
       getr regs2 11 = w64 (i + Z.of_nat (length (sb_dec_c.sb_dec_lsd x j))) /\
       getr regs2 15 = w64 (i + Z.of_nat (length (sb_dec_c.sb_dec_lsd x j))) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (D + i <= a < D + i + Z.of_nat (length (sb_dec_c.sb_dec_lsd x j))) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
       garr8 SEGS (mrestrict (w_H W) mem2) (D + i) (sb_dec_c.sb_dec_lsd x j)).
Proof.
induction j as [|j IH];
intros fq STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs x D i Hj Hi HJ Hx HD HD3 HWb
  H20 H15 H11 H14 H5 H12 H13 H6; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (@SRr_run_pi_AJ fq _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_to_pi_AJ fq _ _ _ _ _ B LAWS) as RUNTOP.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (Hi2 : 0 <= i <= 2) by lia.
assert (HQp : apresent (w_H W) memc (D + i)) by exact (proj2 (HWb (D + i) ltac:(lia))).
pose proof (sbdl_entry fq W regs memc D i H14 H15 HD ltac:(lia) ltac:(lia) HQp) as HS.
set (E := sbdl_E regs (D + i)) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply sbdl_E_img).
assert (HAE : env_agree 32 (Ereg regs [w64 (D + i)]) E) by (unfold E; apply sbdl_E_agree).
destruct (sbdl_ew regs (D + i)) as (E32' & EE').
assert (E32 : ew E 32 = Z_to_bv 64 (D + i)) by exact E32'.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r) by exact EE'.
assert (E20 : ew E 20 = Z_to_bv 64 x) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E5 : ew E 5 = Z_to_bv 64 1717986919) by (rewrite (EE 5%nat 5%bv eq_refl); exact H5).
assert (E12 : ew E 12 = Z_to_bv 64 10) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E15 : ew E 15 = Z_to_bv 64 i) by (rewrite (EE 15%nat 15%bv eq_refl); exact H15).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E14 : ew E 14 = Z_to_bv 64 D) by (rewrite (EE 14%nat 14%bv eq_refl); exact H14).
assert (E6 : ew E 6 = Z_to_bv 64 2) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (E13 : ew E 13 = Z_to_bv 64 (2 ^ 64 - 20)).
{ rewrite (EE 13%nat 13%bv eq_refl), H13. apply bv_eq. vm_compute. reflexivity. }
assert (HUq : U E sbdl_q = x / 10) by (apply U_sbdl_q; assumption).
assert (HUdig : U E sbdl_dig = 48 + x mod 10) by (apply U_sbdl_dig; assumption).
assert (HB1 : (2 ^ 64 - 20 <? U E sbdl_x28) = (x <? 10)) by (apply sbdl_br1; assumption).
assert (HU13 : U E (SOff 13 0) = 2 ^ 64 - 20) by (apply (U_atom E 13 (2 ^ 64 - 20) E13); lia).
assert (HU15 : U E (SOff 15 0) = i) by (apply (U_atom E 15 i E15); lia).
assert (HU6 : U E (SOff 6 0) = 2) by (apply (U_atom E 6 2 E6); lia).
pose proof (sbdl_qr x ltac:(lia)) as HQR. destruct HQR as (Hq10 & Hr10 & Hxqr).
assert (Hdig : 0 <= 48 + x mod 10 < 256) by lia.
unfold cfg_at. rewrite <- Z.add_assoc.
paj_run_sh RUNP HS HJ.
{ sbdl_awr E32 D i HWb. }
cbn [ms_mem mkst] in HF, HFr, HG.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> a <> D + i ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ apply (kept_of_frame E (ss_mem sbdl_ss) (w_H W) memc (ms_mem ms) (fun a => a = D + i) HFr).
  intros bq wlo whi aq Hin Haq.
  cbn [ss_mem sbdl_ss windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Hqq | []]; injection Hqq as <- <- <-;
  cbn [base_val] in Haq; rewrite E32, unsigned_lit_small in Haq by lia; lia. }
psrr_branch_pi RUNP BR HS.
- rewrite branch_ltu_U, HU13 in Hc.
  change (SAluw ALU_ADD (SOff 20 0) (SLit (-10))) with sbdl_x28 in Hc.
  rewrite HB1 in Hc. apply Z.ltb_lt in Hc.
  assert (HL : sb_dec_c.sb_dec_lsd x (S j) = [48 + x mod 10]).
  { rewrite sbdl_lsd_S. replace (x <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  paj_run_to_sh RUNTOP HS HJ (AF_sb_dec + SBD_L1X).
  { sbdl_awr E32 D i HWb. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + i ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hne. rewrite <- (KEEP1 a Ha Hne).
    apply (kept_of_frame E _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun a => a = D + i) HFr0);
      [|exact Ha | exact Hne].
    intros bq wlo whi aq Hin Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Hqq | []]; injection Hqq as <- <- <-;
    cbn [base_val] in Haq; rewrite E32, unsigned_lit_small in Haq by lia; lia. }
  assert (GROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)))
    by (eapply mem_grows_trans; [exact HG | exact HG0]).
  assert (Vq : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + i) 1 (48 + x mod 10)).
  { pose proof (@field_of_region_any SEGS E _ 32%nat (D + i) _ 0 1 0 1 0 1%N sbdl_dig
      (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl)
      ltac:(rewrite E32; apply unsigned_lit_small; lia)
      ltac:(left; reflexivity) ltac:(cbn; lia)) as Vx.
    cbn [ms_mem restrict] in Vx. unfold U in HUdig. rewrite HUdig in Vx.
    change (2 ^ (8 * Z.of_N 1)) with 256 in Vx. rewrite Z.mod_small in Vx by lia.
    change (N.to_nat 1) with 1%nat in Vx. rewrite Z.add_0_r in Vx. exact Vx. }
  pose proof (regs_kept_of_st_ok_pi E _ _ regs _ sbdl_keptl HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as HKr.
  cbn [ms_regs restrict] in HKr.
  sbdl_reg HS (11%bv : bv 5) R11. sbdl_reg HS (15%bv : bv 5) R15.
  rewrite (U_addw1 E 11%nat i E11 ltac:(lia)) in R11.
  rewrite (U_atom_off E 15 i 1 E15 ltac:(lia) ltac:(lia)) in R15.
  pmkst HS. apply SRr_ret. split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
  split.
  { unfold cfg_at, w64.
    replace (BASE + AF_sb_dec + SBD_L1X) with (BASE + 17044)
      by (unfold AF_sb_dec, SBD_L1X; lia). reflexivity. }
  split; [exact HJ|].
  split; [apply sbdl_keep_of; exact HKr|].
  rewrite HL. cbn [length].
  split; [exact R11|]. split; [exact R15|].
  split; [intros a Ha Hout; apply KEEP2; [exact Ha | lia]|].
  split; [intros a Hpa; apply (apresent_grows (w_H W) memc (ms_mem ms0)); [exact GROW | exact Hpa]|].
  apply garr8_cons_x; [exact Vq | lia | apply garr8_nil].
- rewrite branch_ltu_U, HU13 in Hc.
  change (SAluw ALU_ADD (SOff 20 0) (SLit (-10))) with sbdl_x28 in Hc.
  rewrite HB1 in Hc. apply Z.ltb_ge in Hc.
  paj_run_sh RUNP HS HJ.
  { sbdl_awr E32 D i HWb. }
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> D + i ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hne. rewrite <- (KEEP1 a Ha Hne).
    apply (kept_of_frame E _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun a => a = D + i) HFr0);
      [|exact Ha | exact Hne].
    intros bq wlo whi aq Hin Haq.
    cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Hqq | []]; injection Hqq as <- <- <-;
    cbn [base_val] in Haq; rewrite E32, unsigned_lit_small in Haq by lia; lia. }
  psrr_branch_pi RUNP BR HS.
  + rewrite branch_ltu_U, HU15, HU6 in Hc0. apply Z.ltb_lt in Hc0.
    assert (Hj1 : (1 <= j <= 3)%nat) by lia.
    paj_run_to_sh RUNTOP HS HJ (AF_sb_dec + SBD_L1).
    { sbdl_awr E32 D i HWb. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + i ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hne. rewrite <- (KEEP2 a Ha Hne).
      apply (kept_of_frame E _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun a => a = D + i) HFr1);
        [|exact Ha | exact Hne].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hqq | []]; injection Hqq as <- <- <-;
      cbn [base_val] in Haq; rewrite E32, unsigned_lit_small in Haq by lia; lia. }
    assert (GROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG | exact HG0] | exact HG1]).
    assert (Vq : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + i) 1 (48 + x mod 10)).
    { pose proof (@field_of_region_any SEGS E _ 32%nat (D + i) _ 0 1 0 1 0 1%N sbdl_dig
        (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl)
        ltac:(rewrite E32; apply unsigned_lit_small; lia)
        ltac:(left; reflexivity) ltac:(cbn; lia)) as Vx.
      cbn [ms_mem restrict] in Vx. unfold U in HUdig. rewrite HUdig in Vx.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vx. rewrite Z.mod_small in Vx by lia.
      change (N.to_nat 1) with 1%nat in Vx. rewrite Z.add_0_r in Vx. exact Vx. }
    pose proof (regs_kept_of_st_ok_pi E _ _ regs _ sbdl_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    sbdl_reg HS (11%bv : bv 5) R11. sbdl_reg HS (15%bv : bv 5) R15.
    sbdl_reg HS (20%bv : bv 5) R20. sbdl_reg HS (14%bv : bv 5) R14.
    sbdl_reg HS (5%bv : bv 5) R5. sbdl_reg HS (12%bv : bv 5) RT12.
    sbdl_reg HS (13%bv : bv 5) RT13. sbdl_reg HS (6%bv : bv 5) R6.
    rewrite (U_addw1 E 11%nat i E11 ltac:(lia)) in R11.
    rewrite (U_atom_off E 15 i 1 E15 ltac:(lia) ltac:(lia)) in R15.
    rewrite HUq in R20.
    rewrite (U_atom E 14 D E14 ltac:(lia)) in R14.
    rewrite (U_atom E 5 1717986919 E5 ltac:(lia)) in R5.
    rewrite (U_atom E 12 10 E12 ltac:(lia)) in RT12.
    rewrite (U_atom E 6 2 E6 ltac:(lia)) in R6.
    rewrite HU13 in RT13.
    assert (RT13' : getr (ms_regs ms1) 13 = w64 (-20))
      by (rewrite RT13; apply bv_eq; vm_compute; reflexivity).
    assert (HLs : sb_dec_c.sb_dec_lsd x (S j) = (48 + x mod 10) :: sb_dec_c.sb_dec_lsd (x / 10) j).
    { rewrite sbdl_lsd_S. replace (x <? 10) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    pmkst HS.
    eapply SRr_mono.
    { replace (BASE + 16980) with (BASE + AF_sb_dec + SBD_L1) by (unfold AF_sb_dec, SBD_L1; lia).
      eapply (IH fq STK sp0 FP ly St W0 mem0 md0 own lyc Sc W (ms_mem ms1) _ k (ms_regs ms1)
        (x / 10) D (i + 1) Hj1 ltac:(lia) HJ ltac:(lia) HD HD3).
      - intros a Ha. split.
        + exact (proj1 (HWb a ltac:(lia))).
        + apply (apresent_grows (w_H W) memc (ms_mem ms1)); [exact GROW|].
          exact (proj2 (HWb a ltac:(lia))).
      - exact R20.
      - exact R15.
      - exact R11.
      - exact R14.
      - exact R5.
      - exact RT12.
      - exact RT13'.
      - exact R6. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & R11' & R15' & Hout2 & Hpr2 & Hga2).
    split; [reflexivity|]. exists regs2, mem2, md2.
    split; [reflexivity|]. split; [exact HJ2|].
    split.
    { apply (sbdl_keep_trans regs (ms_regs ms1) regs2); [apply sbdl_keep_of; exact HKr | exact HKr2]. }
    rewrite HLs. cbn [length]. rewrite Nat2Z.inj_succ.
    split.
    { rewrite R11'. f_equal. lia. }
    split.
    { rewrite R15'. f_equal. lia. }
    split.
    { intros a Ha Hout. rewrite (Hout2 a Ha ltac:(lia)). apply KEEP3; [exact Ha | lia]. }
    split.
    { intros a Hpa. apply Hpr2. apply (apresent_grows (w_H W) memc (ms_mem ms1)); [exact GROW | exact Hpa]. }
    apply garr8_cons_x; [|lia|].
    { apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) (ms_mem ms1) mem2 (D + i) 1); [|exact Vq].
      intros xa Hxa. apply (Hout2 xa ltac:(lia) ltac:(lia)). }
    { replace (D + i + 1) with (D + (i + 1)) by lia. exact Hga2. }
  + rewrite branch_ltu_U, HU15, HU6 in Hc0. apply Z.ltb_ge in Hc0.
    assert (Hj0 : j = 0%nat) by lia.
    assert (HL : sb_dec_c.sb_dec_lsd x (S j) = [48 + x mod 10]).
    { rewrite sbdl_lsd_S, Hj0. destruct (x <? 10); reflexivity. }
    paj_run_to_sh RUNTOP HS HJ (AF_sb_dec + SBD_L1X).
    { sbdl_awr E32 D i HWb. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> a <> D + i ->
      aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
    { intros a Ha Hne. rewrite <- (KEEP2 a Ha Hne).
      apply (kept_of_frame E _ (w_H W) (ms_mem ms0) (ms_mem ms1) (fun a => a = D + i) HFr1);
        [|exact Ha | exact Hne].
      intros bq wlo whi aq Hin Haq.
      cbn [ss_mem add_cond windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
      destruct Hin as [Hqq | []]; injection Hqq as <- <- <-;
      cbn [base_val] in Haq; rewrite E32, unsigned_lit_small in Haq by lia; lia. }
    assert (GROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)))
      by (eapply mem_grows_trans; [eapply mem_grows_trans; [exact HG | exact HG0] | exact HG1]).
    assert (Vq : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (D + i) 1 (48 + x mod 10)).
    { pose proof (@field_of_region_any SEGS E _ 32%nat (D + i) _ 0 1 0 1 0 1%N sbdl_dig
        (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl)
        ltac:(rewrite E32; apply unsigned_lit_small; lia)
        ltac:(left; reflexivity) ltac:(cbn; lia)) as Vx.
      cbn [ms_mem restrict] in Vx. unfold U in HUdig. rewrite HUdig in Vx.
      change (2 ^ (8 * Z.of_N 1)) with 256 in Vx. rewrite Z.mod_small in Vx by lia.
      change (N.to_nat 1) with 1%nat in Vx. rewrite Z.add_0_r in Vx. exact Vx. }
    pose proof (regs_kept_of_st_ok_pi E _ _ regs _ sbdl_keptl HS ltac:(env_agree_chain HAE)
      ltac:(vm_compute; reflexivity)) as HKr.
    cbn [ms_regs restrict] in HKr.
    sbdl_reg HS (11%bv : bv 5) R11. sbdl_reg HS (15%bv : bv 5) R15.
    rewrite (U_addw1 E 11%nat i E11 ltac:(lia)) in R11.
    rewrite (U_atom_off E 15 i 1 E15 ltac:(lia) ltac:(lia)) in R15.
    pmkst HS. apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst ?rg _ ?mm _) ?mdx] => exists rg, mm, mdx end.
    split.
    { unfold cfg_at, w64.
      replace (BASE + AF_sb_dec + SBD_L1X) with (BASE + 17044)
        by (unfold AF_sb_dec, SBD_L1X; lia). reflexivity. }
    split; [exact HJ|].
    split; [apply sbdl_keep_of; exact HKr|].
    rewrite HL. cbn [length].
    split; [exact R11|]. split; [exact R15|].
    split; [intros a Ha Hout; apply KEEP3; [exact Ha | lia]|].
    split; [intros a Hpa; apply (apresent_grows (w_H W) memc (ms_mem ms1)); [exact GROW | exact Hpa]|].
    apply garr8_cons_x; [exact Vq | lia | apply garr8_nil].
Qed.
Theorem sbd_l1 : sbd_L1_spec B.
Proof.
intros fq STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs v D.
unfold sbd_L1_run. intros HJ Hv HD0 HD3 HWb H20 H15 H11 H14 H5 H12 H13 H6.
eapply SRr_mono.
{ apply (sbdl_gen 3%nat fq STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs v D 0);
  try assumption; try lia.
  replace (D + 0) with D by lia. replace (Z.of_nat 3) with 3 by reflexivity. exact HWb. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HKr2 & R11 & R15 & Hout & Hpr & Hga).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split; [exact HKr2|].
rewrite Z.add_0_l in R11, R15.
split; [exact R11|]. split; [exact R15|].
split.
{ intros a Ha Hout2. apply Hout; [exact Ha|]. rewrite Z.add_0_r. exact Hout2. }
split; [exact Hpr|].
rewrite Z.add_0_r in Hga. exact Hga.
Qed.
End h.
End f.
End d.
